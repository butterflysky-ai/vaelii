;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.assert-entry
  "The per-sentence write entry point: what `vaelii.core/assert` does once it has one
  sentence in one context.

  Three things live together here because the assert path runs them as one step and
  `preview` has to undo all three:

  - **The premise mark**, written to the network node and the record slot together
    (`put-premise-mark`), and resolved from content rather than arrival order
    (`mark-premise` says why a bare re-assert may not downgrade a class).
  - **The rule slots**, reconciled when a rule is stated twice
    (`reconcile-rule-slots!`, `join-engines`).
  - **The dispatch** a sentence takes — imperative, `ist`, rule, or plain fact
    (`assert-one`).

  `*premise-audit*` is the hook a batch rollback reads (`core/rollback-batch!`).

  **`assert-one` takes the re-entry as an argument.**  An `(ist Ctx S)` sentence is not
  stored — it asserts `S` in `Ctx` — so the dispatch re-enters the caller's own entry
  point.  That is `vaelii.core/assert`, and an engine namespace may not require
  `vaelii.core`, so the caller passes it in."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.imperative :as imperative]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

(def ^:dynamic *premise-audit*
  "When bound to an atom, every premise mark on the assert path first records the
  datum's **prior** premise state here — `{handle {:premise? bool :strength kw
  :spellings rec}}`, first writer wins, `:spellings` read only for a prior premise.
  `core/preview`, `core/edit!` and a single `core/assert` bind it, and
  `core/rollback-batch!` reads it (docs/preview.md, \"The mechanism\")."
  nil)

(defn put-premise-mark
  "Write the premise mark on sentex `h` at exactly `strength` — the network's node and
  the record store's slot, which the assert path always moves together.  One function so
  neither half can be marked without the other: the network is what labelling reads and
  the record is what `recover` rebuilds the network from, so a KB whose two halves
  disagreed would answer one thing until it restarted and another afterwards.

  Callers say `mark-premise` instead.  This is the raw write, and the only caller that
  wants it is the one *restoring* a mark it recorded — `rollback-batch!`, putting back a
  class the KB already held rather than stating one."
  [kb h strength]
  (jtms/add-premise (reasoning/tms kb) h strength)
  (p/mark-premise (:records kb) h strength))

(defn- mark-premise
  "Mark sentex `h` a premise, at the **stronger** of the class it already stands at and
  the `strength` offered.  One function so the audit above has one hook rather than
  three, and so neither half can be marked without the other (`put-premise-mark`).

  **Resolved from content, never from arrival order** — the rule
  `reconcile-rule-slots!` states for a re-asserted rule's slots, at the fact entry point, where
  it decides belief rather than what a caller reads back.  A re-assert carrying no
  `:strength` states nothing about the class: the `:default` it falls back to is the
  entry point's fallback and not the caller's claim, so reading that silence as a *downgrade*
  made the same knowledge in two orders reach two sets of beliefs.  Asserting
  `(flies Tweety)` known-true, re-asserting it bare, then asserting the known-true
  negation left the original **defeated**; the same three sentences without the bare
  re-assert in the middle left it believed and the pair an irreducible clash.
  `strength/max` is commutative and idempotent, so the orders agree and a third
  assertion changes nothing.

  Narrowing a class is `retract!` and re-assert, exactly as it is for a rule's
  `:engines`, `:defeasible` and `:strength` (docs/canonicalization.md).  A handle that
  is not a premise stands at nothing — `jtms/premise-strength` reads nil, which ranks 0
  — so it takes the offered class whole, and a retraction therefore leaves no class
  behind for the next assertion to inherit."
  [kb h strength]
  (when-let [audit *premise-audit*]
    (when-not (contains? @audit h)
      (let [tms      (reasoning/tms kb)
            premise? (jtms/premise? tms h)]
        ;; the spellings are read only for a handle that is a premise already, the one
        ;; arm of the undo that restores them.  A handle that is not one is retracted
        ;; instead, and every `assert` runs under an audit, so reading them there would
        ;; add a record-store read to every new fact for nothing.
        (swap! audit (fn [m]
                       (if (contains? m h)
                         m
                         (assoc m h {:premise?  premise?
                                     :strength  (jtms/premise-strength tms h)
                                     :spellings (when premise? (integrate/spellings kb h))})))))))
  (put-premise-mark kb h (strength/max (jtms/premise-strength (reasoning/tms kb) h) strength)))

(defn check-rule-sentence
  "Every pre-storage check a rule must pass, as a step that writes nothing —
  `checks/check-rule!`, the list both storage entry points read (the other being a generator
  firing, `chain/place-conclusion`).  A generator's own three are in that list rather
  than beside it, because a *minted* rule can be a generator too (docs/generators.md)
  and a check only this entry point ran would be one the fixpoint could store around."
  [kb sentence context]
  (checks/check-rule! kb sentence context))

(defn- join-engines
  "The engines a rule stated two ways runs in: the **union** of the two spellings'.

  `#{}` (inert) is the bottom, and the join only ever adds an engine: a backward-only and
  a forward-only spelling come to `#{:forward :backward}`.  A join rather than a pick,
  because the two spellings are two claims about the same rule and a rule that may run
  forwards *and* may run backwards may do both.  A choice or constraint rule is
  `#{:solve}` in every spelling, so the join leaves it there."
  [a b]
  (sx/canonical-engines (into a b)))

(defn- reconcile-rule-slots!
  "Bring a re-asserted rule's `:engines` / `:defeasible` to the value the two
  assertions jointly state, and re-chain it if that newly lets it run forwards.

  These two slots are not in the sentex identity key — a rule is one rule however its
  direction is spelled — so `find-or-create-sentex` hands back the stored record and the
  second spelling would otherwise be dropped.  Dropping it is **arrival-order
  dependent**: a bare `implies` after a `set/inertRule` would stay inert and never fire,
  and after a `set/defaultRule` stay defeasible and lose to a monotonic rival it should
  tie with — the same two assertions reaching two sets of beliefs, which
  `docs/nmtms.md` does not permit.

  So the slots are resolved from **content** instead: the union of the engines
  (`join-engines`), and strict over defeasible — a rule asserted once without
  `set/defaultRule` is a rule somebody stated as holding outright.  Both are commutative
  and idempotent, so the two orders agree and a third assertion changes nothing.

  The record moves, and so does the one derived copy of the defeasibility slot: the
  justifications already fired through this rule carry its contribution as their
  `:strength`, read off the record at fire time (`chain/rule-view-of`), so a
  defeasible→strict resolution must reach them or belief keeps the arrival order this
  fn exists to remove — facts asserted *between* the two spellings would hold
  conclusions at `:default` that the same assertions in the other order hold at
  `:monotonic`.  `special/restrength-firings!` updates that slot and relabels the
  affected region.  The engines join needs no such reach-back: it only ever *adds*
  capability (`join-engines` is a join, never a meet), backward capability is read
  off the record at query time, and new forward capability is the `chain-all` below.

  The index files a rule under its engines too (the rule extent's `[:solve]` node holds
  the rules whose `:engines` take `:solve`), so a join that changes the engines takes the
  record out of the index under the stored engines and back in under the joined ones."
  [kb h stored sentence context opts]
  (let [incoming (res/kb-sentex kb sentence context)
        engines  (join-engines (:engines stored) (:engines incoming))
        def?     (when (and (:defeasible stored) (:defeasible incoming)) true)
        moved?   (not= engines (:engines stored))]
    (when (or moved? (not= (boolean def?) (boolean (:defeasible stored))))
      (let [s' (assoc stored :engines engines :defeasible def?)]
        (when moved? (p/unindex-sentex! (:index kb) stored h))
        (p/put-sentex (:records kb) s')
        (when moved? (p/index-sentex (:index kb) s' h))
        (when (not= (boolean def?) (boolean (:defeasible stored)))
          (special/restrength-firings! kb h)
          ;; a rule's defeasibility decides whether it is a roster rule
          (checks/force-sentexes! kb [s']))
        ;; newly forward-capable: it has never been joined over the facts already stored
        (when (and (:chain? opts true)
                   (rules/forward-sentex? s')
                   (not (rules/forward-sentex? stored)))
          (chain/chain-all kb [h] opts))
        (settle/settle-write kb (:chain? opts true))))))

(defn- assert-rule-sentence
  "Assert a rule **as written** — any `set/*Rule` wrapper included, since the sentex
  constructor canonicalizes it into the record's `:engines` / `:defeasible`.  The
  well-formedness checks run on the bare rule inside the wrappers.

  Idempotent: a re-asserted rule resolves to the existing sentex.  Where the two
  spellings disagree about direction or defeasibility, the slots are resolved from
  content rather than from which arrived first — see `reconcile-rule-slots!`.

  **`opts :strength` reaches the record here exactly as it does at the fact entry point**, and
  it is the rule's *own* defeat class — whether a contradicting default can defeat the
  rule itself.  What a firing confers on its conclusion is a different question with a
  different authority: `chain/rule-view-of` reads it off `:defeasible`, so a rule stored
  at `:monotonic` still concludes at its weakest antecedent unless it is bare.  Nothing
  in the engine defeats a rule, so the slot is one that reads back rather than one that
  moves belief — `docs/nmtms.md` states the absence.

  **Re-marking on the existing branch is the mark itself, not only its class.**  A rule
  can be stored and not be a premise — a generator's stamped rule is a *conclusion*,
  resting on the generator's justification — and asserting it is a second and
  independent ground for it, exactly as asserting an already-derived fact is at the
  other entry point.  Left unmarked, `assert` answered with a handle for a rule that the next
  retraction of the generator took away with it.

  All three slots resolve alike, and from **content**: `:engines` and `:defeasible`
  in `reconcile-rule-slots!`, `:strength` below by taking the stronger.  A re-assert
  carrying no `:strength` states nothing about the class — the `:default` it falls back
  to is the entry point's fallback, not the caller's claim — so reading that silence as a
  downgrade would leave `defeat-class` answering differently for the same two assertions
  in the two orders.  No belief moves either way, nothing defeating a rule; this is what
  a caller reads back.  Narrowing any of the three is `retract!` and re-assert."
  [kb sentence context opts]
  (check-rule-sentence kb sentence context)
  (let [strength   (get opts :strength :default)
        [h s new?] (kb/find-or-create-sentex kb sentence context strength)]
    (if new?
      (do
        (checks/force-sentex! kb s)
        (mark-premise kb h strength)
        (special/index-rule-sentex kb h s)
        ;; A rule naming a predicate or type the closure has **already** merged is
        ;; restated on arrival, exactly as one stored before the merge is restated by it
        ;; (`assert-one`'s own arm, at the fact entry point): `birthplaceOf ⇒ bornIn` changes a
        ;; functor the rule reasons over, so the original is superseded and the twin
        ;; carries the inference.  Without it the same rule, fact and merge fire under the
        ;; representative in the orders that state the rule first and under a retired
        ;; spelling in the rest (docs/equality.md, "Merging predicates and types").  An
        ;; individual-only merge holds a rule back, which `kb/rewritable-sentex?` decides.
        (let [mig (when (kb/rewritable-sentex? kb s) (special/migrate-sentex kb s))]
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          ;; defeasible or not, a forward-capable rule seeds the one agenda: `chain`
          ;; joins it over existing facts (process-datum -> fire-rule) at its own strength
          ;; — and the twin joins beside it, since the spelling this rule was written in
          ;; stops firing the moment the supersession above lands
          (when (and (:chain? opts true) (rules/forward-sentex? s))
            ;; ...and if an antecedent reads a declared-transitive predicate, the partner
            ;; facts go back as triggers too: a rule joined over the store from the
            ;; transitive side sees the stored links only, since its closure is answered
            ;; rather than stored and an open goal on it has no record to lead from
            (chain/chain-all kb (-> (into [h] (:new mig))
                                    (into (special/transitive-rule-seeds kb s)))
                             opts))
          (violations/report kb (:violations mig)))
        (settle/settle-write kb (:chain? opts true)))
      (do
        (reconcile-rule-slots! kb h s sentence context opts)
        ;; `find-or-create-sentex` hands back the stored record and drops the strength
        ;; the second assertion carried, the same way it drops the direction the
        ;; reconcile above puts back — and the mark is worth making for a second reason
        ;; than the class: a stored rule need not be a premise at all (a generator's
        ;; stamped rule is a *conclusion*, resting on the generator's justification), and
        ;; asserting one is an independent ground for it, exactly as asserting an
        ;; already-derived fact is at the fact entry point.
        ;;
        ;; **Resolved from content, like the two slots above it.**  `strength/max` takes
        ;; the stronger, so the two orders agree and a third assertion changes nothing —
        ;; the rule `reconcile-rule-slots!` holds for `:engines` and `:defeasible`, and
        ;; it holds here for the same reason: a re-assert carrying no `:strength` states
        ;; nothing about the class, so reading that silence as a downgrade made
        ;; `defeat-class` answer differently for the same two assertions in either order.
        ;; Narrowing one is `retract!` and re-assert, as it is for the other two.  A
        ;; record with no class yet — nil, so not a premise — ranks 0 and takes the
        ;; incoming class.
        (let [resolved (strength/max (:strength s) strength)]
          (when (not= resolved (:strength s))
            (checks/force-sentex! kb s)
            (mark-premise kb h resolved)
            ;; the mark relabels, and an entry point that moves a label settles before it
            ;; returns.  A class move alone moves none, nothing in the engine defeating
            ;; a rule — but the *first* mark of a rule that was only ever concluded puts
            ;; it IN, and that revives whatever it licenses.
            (settle/settle-write kb (:chain? opts true))))))
    h))

;; A `set/defaultRule` wrapper sets `:defeasible` on the record, so the one rule path
;; below handles every flavour — do not add a second entry point per flavour.

(defn aligned-exception
  "The exception `exc`, in the author's variable names, in the canonical variables of the
  rule whose canonical→author varmap as written is `author-vm`: the query
  `assert-exceptWhen-meta!` stores."
  [exc author-vm]
  (let [inv (set/map-invert author-vm)]                             ; {?x ?var0}
    (sx/canonical-exception (map #(sx/canon (res/substitute % inv)) exc) (keys author-vm))))

(defn assert-exceptWhen-meta!
  "Store one exceptWhen exception against the rule at `rule-handle` as a
  belief-following `(exceptWhen <aligned-query> (sentexHandle rule-handle))`
  meta-sentex, and return its handle.

  `exc` is the exception's conjunct literals in the *author's* variable names (as
  written beside the rule), and `author-vm` is the canonical→author varmap of the rule
  **as written in this assert** — not the rule's stored varmap, which carries whatever
  names the rule was *first* asserted with, so a re-reference under new variable names
  would misalign.  The query is mapped to the rule's canonical variables through it, so
  a firing's bindings substitute straight in; an exception variable no antecedent binds
  is refused (`:exception-not-closed`), as is a quantifier binder the rule also names
  (`:quantifier-not-local`) and one that would close a cycle through
  negation (`check-exceptWhen-stratified`).  Storing it posts the re-check index
  (`index-exceptWhen-meta`) and settles, so any conclusion the new exception now blocks
  is swept before this returns."
  [kb rule-handle exc author-vm context opts]
  (let [rsx (p/get-sentex (:records kb) rule-handle)]
    (when-not (and rsx (rules/rule? rsx))
      (throw (ex-info (str "exceptWhen names handle " rule-handle ", which is not a rule")
                      {:type :not-well-formed :handle rule-handle :exception (vec exc)})))
    ;; the rule's author variables stand in for its antecedents: they are what binds
    (sx/check-exception-closed (vec (vals author-vm)) exc)
    (let [aligned (aligned-exception exc author-vm)
          meta-s  (sx/exceptWhen-meta aligned rule-handle)]
      ;; Each conjunct is held to the naming invariants, like every other literal a
      ;; rule carries.  `check-rule-sentence` runs `nm/check!` on `rules/inner-rule`,
      ;; which has already peeled the query off, and nothing else reached it — so
      ;; `nm/literals`' `:exception` role and the "exceptWhen exception" wording in
      ;; `literal-roles` existed with nothing on the assert path calling them, and
      ;; `(exceptWhen (lives_in ?x cold_place) …)` stored the snake_case-arity-2
      ;; literal `docs/naming.md` says is refused.  The store holding what the front
      ;; entry point refuses is the structure of corruption these checks exist to stop.
      (run! #(nm/check! (:naming kb) % context) aligned)
      (checks/check-no-imperative meta-s)
      (checks/check-no-defeat meta-s)
      (checks/check-exceptWhen-stratified kb rule-handle (rules/watched-predicates aligned) context)
      (let [strength   (get opts :strength :default)
            [h s new?] (kb/find-or-create-sentex kb meta-s context strength)]
        (when new?
          (mark-premise kb h strength)
          (integrate/sentex-added kb s h)          ; index-exceptWhen-meta + queue the re-check
          ;; If the rule already migrated before this exception existed, migration never
          ;; saw the exception — re-point it onto the live twin(s) now, or the twin fires
          ;; unguarded (docs/equality.md, the meta-after-merge case).
          (special/migrate-meta-onto-twins kb s)
          (settle/settle-write kb (:chain? opts true)))  ; sweep what the new exception now blocks
        h))))

(defn ist-parts
  "The `[context sentence]` an `(ist Ctx S)` names, or nil when the form is not one — a
  bare `(ist Ctx)` included.

  `assert` and `check` both read the form here, so a malformed `ist` is one refusal on
  both paths.  Reaching into it positionally is how the two would disagree: `check`
  taking a default and reporting `:shape` while `assert` takes none and throws a bare
  `IndexOutOfBoundsException`, which carries no `:type` for a caller to discriminate on
  and names nothing a writer can act on."
  [sentence]
  (when (and (sequential? sentence)
             (= sx/ist-functor (first sentence))
             (= 3 (count sentence)))
    [(second sentence) (nth sentence 2)]))

(defn ist-shape-problem
  "The `:shape` problem a malformed `ist` is refused with — a value for `check`, and the
  `ex-info` `assert` throws."
  [sentence]
  {:type :shape :sentence sentence
   :message (str "an (ist Ctx S) names a context and a sentence, got " (pr-str sentence))})

(defn storage-context
  "The context a fact whose functor is `pred` is stored in when asserted in `context`:
  CxUniverse for a `forced_decontextualized_predicate`, `context` otherwise.  Reads the
  **global** property on purpose: this decides where the sentex is stored, storage does
  not vary by the writer's visibility, and scoping the placement by what can see the
  declaration would be circular.  `assert-one` places with it, and `vaelii.core`'s
  `fact-problems` and `check-reified-inputs!` read with it, so a check reads the fact
  from the context the store would hold it in."
  [kb pred context]
  (if (and pred (tax/has-prop? (reasoning/taxonomy kb) :forced-decontextualized pred))
    special/universal-context
    context))

;; `(ist Ctx S)` handed to `assert` recurses into `assert` with the inner sentence
;; (`assert-one` below), and `assert` is defined after it — a genuine forward
;; reference, and the only one here: query and settle live below this namespace, in
;; impl.kb and impl.settle.
(defn assert-one
  "Assert a single sentence (any conjunctive-consequent rule is split into one rule
  per conjunct by `assert` before reaching here).  Returns the sentex handle.

  `from` carries what only the caller's entry point knows: `:assert-fn`, re-entered for
  an `(ist Ctx S)` sentence and for nothing else, and `:bulk?`, the caller-guaranteed
  bulk-load mode that turns off the per-fact machinery which only validates or dedups.
  `:bulk?` is a value rather than a var read because the public knob is
  `vaelii.core/*bulk-load?*`, and an engine namespace may not read `vaelii.core`.

  The bulk path reads the `symmetric` mark unscoped: the argument-order fold decides
  the stored key, which every reader shares (docs/canonicalization.md)."
  [kb sentence context opts {:keys [assert-fn bulk?]}]
  (cond
    ;; A `do/` imperative is an instruction, not a fact: nothing is stored, and what
    ;; comes back is the action's result (docs/labeling.md).  First, so no naming or
    ;; well-formedness check ever sees a form that is not a sentence.
    (sx/do-form? sentence)
    (imperative/run kb sentence context)

    ;; (ist Ctx S) is not stored — it finds or creates S in Ctx (ist semantics)
    (and (sequential? sentence) (= sx/ist-functor (first sentence)))
    (if-let [[ctx s] (ist-parts sentence)]
      (assert-fn kb s ctx opts)
      (let [p (ist-shape-problem sentence)]
        (throw (ex-info (:message p) (dissoc p :message)))))

    ;; Every rule flavour takes one path: a bare `(implies ..)` (a :both rule) and
    ;; any `set/*Rule` wrapping of one.  The wrapper is not stripped here — it is
    ;; canonicalized into the record's :engines / :defeasible by the sentex
    ;; constructor.  Routing through the checked rule path also gets
    ;; range-restriction and rule indexing, rather than storing a plain premise.
    (rules/rule-sentence? (rules/inner-rule sentence))
    (assert-rule-sentence kb sentence context opts)

    :else
    ;; A virtual wrapper (`set/*Rule`, `set/defaultRule`, `exceptWhen`) is meaningful
    ;; only around an implication, but the sentex constructor peels it off whatever it
    ;; wraps — so `(set/defaultRule (dog Felix))` *stores* the bare `(dog Felix)`.
    ;; Peel it here too, so the checks below run on the sentence that will actually be
    ;; stored.  Checking the wrapper instead let a fact walk past every definitional
    ;; check: the functor is `set/defaultRule` and the sole argument is a list, so
    ;; naming, arg, disjointness and functionality all matched nothing and passed
    ;; vacuously, and the stripped fact landed in the store unchecked.
    ;;
    ;; A *forced* universal predicate (e.g. genlCx) has its extent placed in
    ;; CxUniverse by force — no justification, the fact simply lives there.
    (let [sentence (rules/inner-rule sentence)
          pred     (nm/functor sentence)
          context  (storage-context kb pred context)
          strength (get opts :strength :default)]
      ;; a `defeat` is refused on the sentence alone, bulk or not: a premise defeat is
      ;; content only the engine writes
      (checks/check-no-defeat sentence)
      ;; Bulk load skips every check below: each only *validates* (none writes), and
      ;; the caller has guaranteed the corpus is well-formed — including the arg
      ;; store query in `constraint-checks`, the dominant per-fact cost (`:bulk?`).
      ;; The checks yield one *value* forward: what the argument constraints entail
      ;; about this sentence's arguments.  It is computed here — where the declarations
      ;; are already being read — and materialized below, because at this point the
      ;; sentex does not exist yet and there is no handle to justify a derived type
      ;; against.  Empty unless assertive argument types are on.
      (let [ents (when-not bulk?
                   (nm/check! (:naming kb) sentence context)
                   (checks/check-ground kb sentence context)
                   (when-let [ps (seq (special/wff-problems (reasoning/taxonomy kb) sentence context))]
                     (throw (ex-info (str "not well-formed: " (str/join "; " ps))
                                     {:type :not-well-formed :sentence sentence})))
                   (checks/check-except-target kb sentence)
                   ;; the rule-set half of well-formedness, for the *other* thing that can
                   ;; close a cycle through negation: a genl / genlCx edge arriving
                   ;; underneath rules already stored (docs/exceptions.md).  Before anything
                   ;; is written and before the taxonomy is touched, so a refusal leaves
                   ;; nothing behind.
                   (checks/check-edge-stratified kb sentence context)
                   ;; ...and the third thing that can: a `closed_extent_predicate` grant
                   ;; arriving underneath rules that read the predicate negatively, which
                   ;; is what turns those reads into negation as failure (docs/naf.md)
                   (checks/check-closed-extent-stratified kb sentence context)
                   (checks/constraint-checks kb sentence context))
            ;; Bulk load skips the dedup trie-walk: a distinct corpus never hits an
            ;; existing sentex, so `create-sentex` directly is the same result the
            ;; `find-or-create` miss branch would take.
            ;; the record is born carrying its strength, so `mark-premise` below has
            ;; nothing to re-store — see `kb/create-sentex`.
            ;;
            ;; **A predicate that permutes keeps the probe.**  `create-sentex` canonicalizes
            ;; the arguments (`res/kb-sentex` sorts a `(symmetric P)` literal, and the
            ;; commuting component of a commutative one), so the bulk row is *stored* in
            ;; canonical order — but skipping the probe stored it beside a permutation
            ;; already there, two records for one proposition, which the caller cannot
            ;; pre-dedup: telling `(siblingOf Bob Ann)` from a stored `(siblingOf Ann Bob)`
            ;; needs exactly the `(symmetric P)` read the fast path is avoiding, and
            ;; `(covering W C A B)` from a stored `(covering W A B C)` the commuting-group
            ;; read.  So for such a functor the row takes `find-or-create` (one taxonomy
            ;; read per row for a rare mark), which is what makes the bulk result identical
            ;; to loading one-by-one (`integrate/commute-existing`, vaelii#61).  Both reads
            ;; are inside the `bulk?` `and`, so `and` short-circuits them away on the
            ;; non-bulk path, which never reaches them.
            [h s _]  (if (and bulk?
                              (not (and pred
                                        (let [tax (reasoning/taxonomy kb)]
                                          (or (tax/has-prop? tax :symmetric pred)
                                              (seq (tax/commuting-groups tax pred)))))))
                       (let [[h s] (kb/create-sentex kb sentence context strength)] [h s true])
                       (kb/find-or-create-sentex kb sentence context strength))
            ;; a predicate a mark permutes may store this assertion under a spelling other
            ;; than the one written, and the row has to remember which, for the mark's
            ;; leaving to hand it back (`integrate/spellings-key`) — read before the mark
            ;; below moves the class the record starts from
            permuted? (integrate/permuting? kb (res/permuted-functor sentence))
            prior    (when permuted? (jtms/premise-strength (reasoning/tms kb) h))]
        ;; the labeller's forced memberships go in before the mark, so a denial of a
        ;; roster literal is never IN (docs/nmtms.md, "The forced-monotonic roster")
        (checks/force-sentex! kb s)
        (mark-premise kb h strength)
        (when permuted?
          (integrate/note-premise-spelling! kb h (:sentence s) sentence strength prior))
        ;; The add-side choke point: the sentex is reflected into every cache
        ;; through the special-predicate table and the exception re-check is queued
        ;; — one call, so no assert path can forget either half.  An equality
        ;; sentex reaches the closure there and migrates what it displaces;
        ;; everything else returns nil.  The three slots it returns are the caller's
        ;; to apply: the twins are chaining seeds, the supersessions are belief, and
        ;; and the violations are reported after `chain-all` so they carry its run id.
        (let [eq (integrate/sentex-added kb s h)
              ;; a fact naming a term the closure has *already* displaced is restated
              ;; on arrival, exactly as a fact asserted before the merge is restated
              ;; by it — otherwise migration would depend on which came first
              own  (when (kb/rewritable-sentex? kb s) (special/migrate-sentex kb s))
              ;; ...and, symmetrically, a handle-naming meta (`except`, a target-following
              ;; reply) whose *target* already migrated: the merge ran before this meta
              ;; existed, so migration never saw it — re-point it onto the live twin(s) now,
              ;; or the twin stays visible / unendorsed (docs/equality.md, the
              ;; meta-after-merge case).  A no-op for a non-meta or an un-migrated target.
              _    (special/migrate-meta-onto-twins kb s)
              ;; ...and the equality a `functional` declaration now infers instead of
              ;; throwing, which merges in its turn
              fnl  (special/derive-functional-equalities kb sentence context h)
              ;; ...and the same inference from the declaration's side, so a
              ;; `(functional P)` arriving after P's facts merges what they already
              ;; licensed rather than only what follows it
              fex  (special/equate-existing kb sentence)
              ;; ...and from the third side: a `genl` edge between predicates brings
              ;; stored sub-predicate facts under a `functional` mark above them
              fdn  (special/equate-under-edge kb sentence)
              ;; ...and the antisymmetric merge, in the same three arrival orders: a fact
              ;; meeting its converse under an `(anti_symmetric P)` mark, the declaration
              ;; meeting the facts, and the `genl` edge bringing them under a mark above
              asym (special/derive-antisymmetric-equalities kb sentence context h)
              axe  (special/antisym-equate-existing kb sentence)
              axd  (special/antisym-equate-under-edge kb sentence)
              ;; ...and the nogoods the settle places under a tuple mark, in the two
              ;; arrival orders a fact's own store does not read: the mark meeting the
              ;; facts, and the edge bringing them under a mark above
              _    (special/offer-marked-existing kb sentence)
              _    (special/offer-marked-under-edge kb sentence)
              ;; ...and the one mark whose retroactive half is a *storage* migration
              ;; rather than a derivation: `(symmetric P)` sorts a literal's arguments at
              ;; the entry point, so the rows stored before it are spelled the way no row stored
              ;; after it will be — and a mirrored pair is two records for one
              ;; proposition, each retractable without the other (vaelii#61)
              sym  (integrate/commute-existing kb sentence h)
              mig  (merge-with into {:new [] :superseded [] :violations []}
                               eq own fnl fex fdn asym axe axd sym)]
          ;; Only when this assert actually merged something.  The reconcile re-examines
          ;; every entry the closure currently displaces, and an assert that merged
          ;; nothing cannot change one: an entry stops being displaced when its terms
          ;; stop rewriting (the closure shrank) or when its restatement stops being
          ;; stored (a deletion), and an assert does neither.  Ungated it is O(merged)
          ;; per assertion — on OpenCyc, 1,489 merges re-examined 780,000 times.
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          ;; the CxUniverse copy, if the predicate is decontextualized — a
          ;; deduction off this sentex and the declaration, so it is a chaining seed
          ;; of its own, and it reports rather than throws when it cannot be admitted
          (let [lift  (special/deduce-lifts kb sentence h context)
                ;; ...and the types the argument constraints entail about this
                ;; sentence's arguments, each a deduction off this sentex and the
                ;; declaration that licensed it.  Both directions, because a
                ;; declaration must reach the facts already stored exactly as it
                ;; reaches the facts that follow: `deduce-arg-types` is this sentence
                ;; meeting the declarations, `entail-existing` is this sentence *being*
                ;; a declaration and meeting the facts.  `ents` are pre-checked: they
                ;; came from `constraint-checks`, so `entailment-check` already ran the
                ;; definitional constraint check over them before the store, and the
                ;; materializer need not run it a second time (special/inadmissible).
                ;; A bulk load draws none of the three orders: `record-arg-types`
                ;; records them after the load, and each mint's admissibility check
                ;; walks the stored rule graph.
                args  (when-not bulk?
                        (merge-with into
                                    (special/deduce-arg-types kb ents h context true)
                                    ;; ...and the declarations stated below this context,
                                    ;; at the contexts that see both
                                    (special/deduce-below kb sentence h context)))
                back  (when-not bulk? (special/entail-existing kb sentence h))
                ;; ...and the third order of the same three ingredients: a `genl` edge
                ;; between predicates brings stored sub-predicate facts under the
                ;; declarations already written above them
                down  (when-not bulk? (special/entail-under-edge kb sentence))
                ;; ...and, when this sentence is a `defn*` collection definition, the
                ;; forward rule(s) it expands into — derived rule sentexes justified by
                ;; this fact, so retracting or defeating it withdraws the rule and
                ;; everything it concluded (docs/defns.md).  A non-`defn*` sentence pays
                ;; one functor read and returns the empty result.
                dfn   (special/materialize-defn-rules kb sentence h context)
                ;; ...and the class membership a metatype route derives, from this
                ;; membership, or from the memberships this `genl` edge or class rise
                ;; brings onto a route (`chain/arity-classes-moved!`)
                cls   (chain/arity-classes-moved! kb [s] false)
                mig   (update mig :violations into
                              (concat (:violations lift) (:violations args)
                                      (:violations back) (:violations down)
                                      (:violations dfn) (:violations cls)))]
            ;; The seeds feed `chain-all` and nothing else, so an assert that does not
            ;; chain computes none.
            (when (:chain? opts true)
              (chain/chain-all
               kb
               (-> [h]
                   ;; a twin `genl` edge is an edge arriving, whichever merge restated it
                   (into (special/minted-seeds kb (:new mig)))
                   (into (:new lift))
                   (into (special/minted-seeds kb (:new down)))
                   ;; the companion rule goes on the agenda so it fires over the
                   ;; facts already stored, the way a minted generator rule does
                   (into (:new dfn))
                   (into (:new cls))
                   ;; a minted type makes this fact matchable at a type it did
                   ;; not have, so it goes on the agenda for the same reason the
                   ;; genl seeds below do — a rule on `(animal ?x)` must fire off
                   ;; a type the entailment minted, within this same assert,
                   ;; and a minted genl edge seeds what it brings under a rule
                   (into (special/minted-seeds kb (:new args)))
                   (into (special/minted-seeds kb (:new back)))
                   ;; a new genl edge makes stored facts matchable at a
                   ;; supertype they did not have — they go back on the agenda,
                   ;; or the same knowledge would derive different things in
                   ;; different arrival orders
                   (into (special/subsumption-seeds kb sentence))
                   ;; ...and a new link of a declared-transitive predicate extends
                   ;; a closure that is answered rather than stored, so no pair of
                   ;; it is ever a datum: the partner triggers of the rules joined
                   ;; to it go back, or the same failure again through a third
                   (into (special/transitive-seeds kb sentence)))
               opts))
            ;; **After** the chain, so the entry carries the run that just ran: a
            ;; violation a merge created — the twin that would have made one individual
            ;; both a dog and a cat — is this assert's to report, and
            ;; `violations/report` stamps each entry with `(:runs @chain-stats)`
            ;; (docs/equality.md, "Interactions — Disjointness").  The ledger itself
            ;; accumulates and is emptied only by `clear-violations!`.
            (violations/report kb (:violations mig))))
        ;; an unchained assert seeds no chaining from the `genlCx` moves it settles, and a
        ;; bulk one draws no argument types over them
        (binding [special/*entail-moves?* (not bulk?)]
          (settle/settle-write kb (:chain? opts true)))
        h))))
