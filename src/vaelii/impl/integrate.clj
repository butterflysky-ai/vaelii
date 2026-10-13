;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrate
  "Store mutation is the boundary: the two choke points everything that stores or
  removes a sentex must pass through.

  Fourth layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle): the table of what each special predicate *means* lives below in
  `vaelii.impl.special`; what lives here is the guarantee that its arms — and the
  exception re-check queue they feed — are never skipped.  exceptWhen correctness
  depends on every mutation path posting a re-check.  Scattering that call across the
  mutation sites makes a missed one invisible — the failure mode is stale excepted
  conclusions, silently, and the next mutation path (a bulk load, a new merge) is one
  forgotten call from that bug.  So the sequence is stated once per direction:

    sentex-added     integrate through the table + queue the re-check — the assert
                     path's reflection of a sentex that just landed (storage and
                     indexing having happened in `kb/create-sentex`, which is the
                     store-side half of the same boundary)
    sentex-removed!  disintegrate + unindex + delete the record + queue the
                     re-check — the one teardown, shared by `retract!` and the
                     excepted-conclusion sweep
    symmetrize-      the third direction, and the only one that moves a record
      existing       without moving a handle: a late `(symmetric P)` mark re-spelling
                     the rows stored before it and folding a mirrored pair into one
                     (see the section at the foot of this namespace)

  The derivation path's twin (`special/derived-sentex-added`) sits beside the table
  instead, because the equality arms are themselves derivation sites and must reach
  it from below.  The triggers that are *not* store mutations stay explicit at
  their own sites: a taxonomy edge change (posted inside the genl / genlCx
  arms — the trigger is the closure moving, not the sentex), rule indexing (posted
  in `special/index-rule-sentex` — the trigger is the rule gaining an exception to
  evaluate), and `recover` (nothing about blocking survives a restart, so it
  re-queues everything wholesale)."
  (:require [vaelii.impl.decide :as decide]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:dynamic *removed-sink*
  "A volatile holding a vector of the sentexes that have left the store, or nil — the
  default, and the removal choke point records nothing.

  What a caller needs when it must act on **the region a teardown touched** rather than
  on the whole KB.  `core`'s reified-NAT orphan sweep is the one that does: an orphaned
  constant is one some departing sentex stopped referencing, so the constants those
  sentexes named are the whole of what it has to ask about.  The removals are not all in
  one place — the dependency-directed sweep produces some, the settle that follows
  produces more (`settle/sweep-excepted!`), and the sweep's own retractions produce more
  again — so recording them where every removal already passes is what makes the
  narrowed question equal to the whole-KB one.

  A volatile rather than an atom: the engine is single-writer, and this sits on the
  teardown path."
  nil)

(defn removal-sink
  "The sink to record a teardown's removals into: the bound one when there is one, a
  fresh volatile otherwise.  **Reused rather than shadowed**, so a nested teardown
  appends to the record its caller is still reading — which is what lets the orphan
  sweep see what its own retractions removed, and so find a cascade.

  `want?` false answers **nil**, and a nil sink is the one that records nothing.  The
  record is read by the reified-NAT sweep, the meta cascade, and a settle reading the
  defeats it removed (`settle/defeat-moves`), and it is not free: it retains every sentex
  a teardown removes for as long as the teardown runs, which on a cascade is the whole
  cascade held in a vector.  The caller passes the gate its readers consult
  (`nat/any-reified-constants?`, a stored `defeat`), so a KB with none of them pays the
  retention of nothing at all."
  ([] (removal-sink true))
  ([want?] (when want? (or *removed-sink* (volatile! [])))))

(defn sentex-added
  "Everything that must happen because a sentex just landed in the store as a
  premise: reflect it into the caches through the special-predicate table, and
  queue the exception re-check its arrival may have flipped.  Returns what the
  table walk returns — the `{:new :superseded :violations}` migration map for an
  equality sentex, nil otherwise.

  Runs whether or not the sentex is newly created: re-asserting an existing
  sentence re-adds premise support, which can flip belief, so the re-check must be
  posted either way (the cache adds are refcounted and idempotent)."
  [kb sentex handle]
  (let [result (special/integrate-sentex kb sentex handle)]
    (special/recheck-on-sentence kb (sx/sentence-of sentex))
    result))

(defn sentex-removed!
  "Everything that must happen because a sentex is leaving the store: reverse its
  cache effects through the table, drop it from every index, delete the record, and
  queue the exception re-check — a fact *leaving* is as much a re-check trigger as
  one arriving, since its departure may be exactly what releases some rule's
  exception.

  Records the sentex into `*removed-sink*` when one is bound, which is how a caller
  learns the region a teardown removed without every removal path having to report it."
  [kb sentex]
  ;; Capture the except target *before* any mutation — the sentex record is about to be
  ;; deleted, so extracting it afterward would depend on the local binding outliving
  ;; storage.  Binding here makes the before/after contract structural.
  (let [except-target (kb/except-target (sx/sentence-of sentex))]
    ;; the removal record, for a caller scoping its own follow-up work to what left
    (when-let [sink *removed-sink*] (vswap! sink conj sentex))
    ;; the sentence the inherited-clash discovery reads for a handle with no record
    (discovery/note-removed! kb sentex)
    (special/disintegrate-sentex! kb sentex)
    (p/unindex-sentex! (:index kb) sentex (:id sentex))
    (p/delete-sentex! (:records kb) (:id sentex))
    ;; the remove-side boundary for an incremental matcher's alpha memories, mirroring the
    ;; add in `kb/create-sentex` — a no-op unless one is engaged
    (observe/notify-remove kb sentex)
    ;; and the change clock, mirroring the same line there
    (observe/note-change)
    ;; the handle cache holds "this sentence is stored at this handle", and this is the
    ;; one event that falsifies it — so the invalidation belongs beside the removal
    ;; itself, not in the caller that happens to have a cache bound
    (observe/forget-handle! (sx/sentence-of sentex) (:context sentex))
    ;; a defeat leaving moves its target's belief, which its watchers re-check
    (special/recheck-defeat-target kb sentex)
    ;; ...and the candidates of the nogood families the settle places
    (decide/note-candidate! kb sentex false)
    ;; ...and the mint family, the remove half of `special/entail-arg-type`'s add, and
    ;; the departure the settle re-derives withheld mints from
    (special/retire-mint! kb sentex)
    (special/note-departure! kb sentex)
    ;; ...and the supersessions the departure moves: a superseded spelling leaving, or an
    ;; equality, a rewrite rule or a `genlCx` edge whose leaving gives spellings back.
    ;; After the record is deleted, which is what drops a departing spelling's entry
    (special/reconcile-removed-supersession! kb sentex)
    ;; An except's departure changes the effective belief of the declaration it hid.
    ;; Run after the roster drop so the common reconcile reads the new visibility state.
    (when except-target
      (special/reconcile-belief-change kb #{except-target}))
    (special/recheck-on-sentence kb (sx/sentence-of sentex))))

;; ## The spellings a permuting mark folded
;;
;; A permuting mark sorts a literal's arguments on the way in, so the row a fact is
;; stored at need not be spelled the way it was written: `(bRel Zed Amy)` under
;; `(symmetric bRel)` is stored as `(bRel Amy Zed)`, and its mirror asserted beside it
;; dedups to the same row.  While the mark holds that is exactly right — the two
;; spellings are one proposition.  When the mark goes, a KB that never held it has one
;; row per spelling written, each answering as written, and the store has to be able to
;; become that KB.  Nothing in the row's sentence, premise mark or justifications says
;; which spellings were written, so the row records them: the provenance entry
;; `spellings-key` holds `{:premise {written strength} :derived {jid written}}` — one
;; entry per premise assertion at its own class, and one per rule firing whose
;; conclusion the sort moved.  `chain/reconcile-spellings!` reads it when a mark leaves
;; and puts each piece back at the row its spelling now canonicalizes to.
;;
;; **Only a piece spelled otherwise than its row is recorded**, so a predicate nothing
;; permutes writes no record and a permuting one pays a provenance write for the facts
;; the sort actually moved.  The premise map is the exception to that: once it exists it
;; lists every premise assertion, the stored spelling's included, because a premise mark
;; is one class on one row and cannot say which of two spellings brought it.  A
;; `:derived` entry naming a justification that has since gone is ignored; a `:premise`
;; map on a row that is no longer a premise is stale and the next assertion replaces it.
;;
;; Provenance because it is the per-handle record every store already keeps durably, so
;; a restart reads the spellings back with no new store method.  `core/provenance`
;; leaves the entry out: it is the store's bookkeeping, not a field a caller wrote.

(def spellings-key
  "The provenance key a row's written spellings are recorded under."
  :vaelii/spellings)

(defn spellings
  "Row `h`'s written-spelling record — `{:premise {written strength} :derived {jid
  written}}` — or nil when every piece of it is spelled as the row is."
  [kb h]
  (get (p/get-provenance (:records kb) h) spellings-key))

(defn put-spellings!
  "Record `rec` as row `h`'s written spellings, dropping empty parts; an empty record
  removes the entry (and the provenance map with it, when nothing else is in it)."
  [kb h rec]
  (let [recs (:records kb)
        prov (p/get-provenance recs h)
        rec  (not-empty (into {} (remove (comp empty? val)) rec))]
    (cond
      rec                           (when-not (= rec (get prov spellings-key))
                                      (p/put-provenance recs h (assoc prov spellings-key rec)))
      (contains? prov spellings-key) (let [prov' (dissoc prov spellings-key)]
                                       (if (seq prov')
                                         (p/put-provenance recs h prov')
                                         (p/delete-provenance! recs h))))))

(defn permuting?
  "Does a stored mark permute `pred`'s arguments — `symmetric`, or a commuting group?

  Read unscoped: the fold decides the stored key, which every reader shares."
  [kb pred]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (and pred (or (tax/has-prop? tax :symmetric pred)
                           (seq (tax/commuting-groups tax pred)))))))

(defn premise-spellings
  "`{written strength}` for row `h`'s premise assertions: the record's, or `stored` at
  `h`'s premise class when the record lists none, or `{}` when `h` is no premise."
  [kb h stored]
  (let [tms (reasoning/tms kb)]
    (if (jtms/premise? tms h)
      (or (not-empty (:premise (spellings kb h))) {stored (jtms/premise-strength tms h)})
      {})))

(defn- queue-respelling!
  "Queue row `h` on `:respell` when a reader of `written`, stored as `stored`, may read
  another spelling (`res/uniform-marks?` false for its predicate's marks): the settle
  that drains the queue puts the row's pieces at the spellings their readers read
  (`chain/reconcile-spellings!`)."
  [kb h stored written]
  (when (not= written stored)
    (let [ents (some->> (res/permuted-functor written) (res/mark-entries (reasoning/taxonomy kb)))]
      (when (and (seq ents) (not (res/uniform-marks? kb ents)))
        (swap! (reasoning/respell kb) conj [:row h])))))

(defn note-premise-spelling!
  "Record that `written` was asserted at `strength` onto row `h`, stored as `stored`.
  `prior` is `h`'s premise class before this assertion, nil when it was none — the
  record's premise map is then stale and starts again.  Writes nothing while every
  premise assertion is spelled as the row is."
  [kb h stored written strength prior]
  (queue-respelling! kb h stored written)
  (let [rec  (spellings kb h)
        live (when prior (not-empty (:premise rec)))]
    (cond
      (or live (not= written stored))
      (let [pm (or live (if prior {stored prior} {}))]
        (put-spellings! kb h (assoc rec :premise (update pm written #(strength/max % strength)))))
      (and (nil? prior) (seq (:premise rec)))
      (put-spellings! kb h (dissoc rec :premise)))))

(defn note-derived-spelling!
  "Record that justification `jid`, a rule firing, concluded `written` onto row `h`."
  [kb h jid written]
  (queue-respelling! kb h (:sentence (p/get-sentex (:records kb) h)) written)
  (put-spellings! kb h (assoc-in (spellings kb h) [:derived jid] written)))

(defn normalized-spellings
  "`rec` for a row stored as `stored`, without what the row's own spelling already says:
  a premise map whose one assertion is `stored`, and every firing written as `stored`."
  [stored {:keys [premise derived]}]
  {:premise (when-not (every? #(= stored %) (keys premise)) premise)
   :derived (into {} (remove (comp #{stored} val)) derived)})

(defn witness-among
  "The believed handle among `supporters` chosen by content — the handle a fold carries a
  folded row's metas on when no declaration arrived to be it.  Nil when none is believed."
  [kb supporters]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> supporters
         (filter #(jtms/in? tms %))
         (keep #(when-let [sx (p/get-sentex recs %)] [(nm/print-key [(:sentence sx) (:context sx)]) %]))
         sort
         first
         second)))

(defn mark-witness
  "A believed statement of a permuting mark on `pred` (`witness-among`), for
  `commute-predicate`.

  The marks are read unscoped, a superset that `witness-among` narrows to a believed
  statement."
  [kb pred]
  (let [tax (reasoning/taxonomy kb)]
    (witness-among kb (concat (tax/prop-supporters tax :symmetric pred)
                              (mapcat #(tax/commuting-supporters tax pred %)
                                      (tax/commuting-groups tax pred))))))

(defn- rule-justification?
  "Is `jid` a rule firing — a justification whose informant is a rule handle?  Only a
  firing's written spelling is recorded; every other justification restates a row it
  rests on, and follows that row wherever its spelling puts it."
  [kb jid]
  (integer? (:informant (jtms/justification (reasoning/tms kb) jid))))

(defn- written-out
  "Row `h`'s record with every piece that is spelled `stored` only implicitly written
  out — its premise assertions and its rule firings — for a caller about to move the
  row off that spelling."
  [kb h stored]
  (let [tms (reasoning/tms kb)
        rec (spellings kb h)]
    (assoc rec
           :premise (premise-spellings kb h stored)
           :derived (reduce (fn [m jid]
                              (if (or (contains? m jid) (not (rule-justification? kb jid)))
                                m
                                (assoc m jid stored)))
                            (:derived rec {})
                            (jtms/supports tms h)))))

;; ## A `symmetric` mark arriving after the facts
;;
;; The third store mutation, and the only one that moves a record without moving a
;; handle.  `(symmetric P)` is not a constraint mark — its effect is
;; **canonicalization**, the argument sort `res/kb-sentex` puts every `P` literal
;; through — so its retroactive half is not a sweep that convicts but a *storage
;; migration*: the rows stored before it have to end up spelled the way the rows stored
;; after it are, or the same knowledge in two arrival orders leaves two physical
;; sentexes for one proposition and the second retraction of the pair has nothing to
;; retract (vaelii#61).
;;
;; It lives here rather than beside the other retroactive arms in `special` because it
;; removes and re-stores records, and the store-mutation boundary is this namespace's whole
;; subject.  Both callers sit above it: `assert-entry/assert-one` for a written declaration and
;; `chain/place-fact-conclusion` for a derived one, exactly as the two call
;; `special/equate-existing`.

(defn- rewritten
  "Written-spelling record `rec` for a row about to be spelled `stored`, each written
  spelling put through `rewrite` and the pieces `stored` already says dropped — or `rec`
  unchanged when `rewrite` is nil.  A permuting mark keeps the spellings as written; a
  reifiable mark moving re-spells them as it re-spells the row (`move-row!`)."
  [rewrite stored {:keys [premise derived] :as rec}]
  (if-not rewrite
    rec
    (normalized-spellings
     stored
     {:premise (reduce-kv (fn [m w st] (update m (rewrite w) #(strength/max % st))) {} premise)
      :derived (update-vals derived rewrite)})))

(defn- respell!
  "Bring one stored sentex into `sentence`, its cache effects walked off the old spelling
  and back on under the new one.  The handle, the TMS node, the premise mark and every
  justification naming it are untouched: for a re-canonicalization, nothing that rests on
  the row is about its spelling except the argument-type mints it triggers, which
  `move-row!` draws again.  `rewrite` is `move-row!`'s."
  [kb sx sentence rewrite]
  ;; the pieces spelled as the row was stop being spelled as the row is
  (put-spellings! kb (:id sx) (rewritten rewrite sentence (written-out kb (:id sx) (:sentence sx))))
  (special/disintegrate-sentex! kb sx)
  (let [sx' (kb/respell-sentex! kb sx sentence)]
    (special/refile-mint! kb sx (:id sx'))
    (special/integrate-sentex kb sx' (:id sx'))
    (special/recheck-on-sentence kb sentence)
    sx'))

(defn- fold-premise!
  "Give `survivor` the premise mark `doomed` carries, at the **stronger** of the two
  classes — `assert-entry/mark-premise`'s rule, and for its reason: the pair is one proposition
  asserted twice, and which of the two assertions the KB keeps must not decide how
  strongly it holds it.  A `doomed` that is not a premise leaves the survivor alone."
  [kb doomed survivor]
  (let [tms (reasoning/tms kb)]
    (when (jtms/premise? tms doomed)
      (let [s (strength/max (jtms/premise-strength tms survivor)
                            (jtms/premise-strength tms doomed))]
        (jtms/add-premise tms survivor s)
        (p/mark-premise (:records kb) survivor s)))))

(defn- fold-dependents!
  "Re-hang every justification that uses `doomed` as an antecedent on `survivor`, so the
  conclusions drawn through the row about to leave keep a witness across the fold rather
  than being swept and re-derived.  Same informant, same bindings, same strength — only
  the antecedent moves, and it moves to the row saying the same thing.

  A justification whose consequence is already `survivor` is skipped: rewritten it would
  name the survivor among its own antecedents, and a datum that grounds itself is
  groundable for ever.  Idempotent through `has-justification?`.

  Copied from the **record**, not from the network: the network keeps `graph-just`, which
  drops the firing's `:bindings` because belief never reads them — and the two things that
  do, an `exceptWhen` query and a NAF antecedent, re-evaluate per firing off the stored
  record.  A copy taken from the graph would leave the fold's justifications unable to
  answer either."
  [kb doomed survivor]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (doseq [jid  (vec (jtms/dependents tms doomed))
            :let [j     (or (p/get-justification recs jid) (jtms/justification tms jid))
                  antes (mapv #(if (= % doomed) survivor %) (:antecedents j))]
            :when (and j (not= (:consequence j) survivor)
                       (not (jtms/has-justification?
                             tms (:informant j) antes (:consequence j)
                             (jtms/justification-key (:informant j) antes (:subsumptions j)))))]
      (let [nid  (p/next-id recs)
            just (jtms/->just nid (:informant j) antes (:consequence j)
                              (:bindings j) (:strength j) (:subsumptions j))]
        (p/put-justification recs just)
        (jtms/add-justification tms just)
        ;; the copy concludes what the original did, spelled as the original was
        (when-let [w (get-in (spellings kb (:consequence j)) [:derived jid])]
          (note-derived-spelling! kb (:consequence j) nid w))))))

(defn- fold-supports!
  "Re-hang every justification that **concludes** `doomed` on `survivor`, so a row a rule
  derived can leave the fold the way a bare premise does.  Same informant, same
  antecedents, same bindings, same strength — only the consequence moves, and it moves to
  the row saying the same thing.

  The consequence-side twin of `fold-dependents!`, and it is what lets `symmetrize-row!`
  fold a mirrored pair both of whose rows a rule concluded.  Nothing about a
  justification is deleted here: it is copied onto the survivor, and `fold-row!`'s
  `take-out!` drops the originals with `doomed`.

  A justification naming `survivor` among its own antecedents is skipped: retargeted it
  would conclude a datum from itself, and a datum that grounds itself is groundable for
  ever.  Skipping it loses no belief, because the row it concluded is the one leaving.
  Idempotent through `has-justification?`, and read from the **record** for
  `fold-dependents!`' reason — the network drops a firing's `:bindings`, which an
  `exceptWhen` query and a NAF antecedent re-evaluate from.  Returns `{jid copy}`, so the
  caller can carry each firing's written spelling onto its copy."
  [kb doomed survivor]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (reduce (fn [copied jid]
              (let [j (or (p/get-justification recs jid) (jtms/justification tms jid))]
                (if (and j (not (some #{survivor} (:antecedents j)))
                         (not (jtms/has-justification?
                               tms (:informant j) (:antecedents j) survivor
                               (jtms/justification-key (:informant j) (:antecedents j)
                                                       (:subsumptions j)))))
                  (let [nid  (p/next-id recs)
                        just (jtms/->just nid (:informant j) (vec (:antecedents j)) survivor
                                          (:bindings j) (:strength j) (:subsumptions j))]
                    (p/put-justification recs just)
                    (jtms/add-justification tms just)
                    (assoc copied jid nid))
                  copied)))
            {}
            (vec (jtms/supports tms doomed)))))

(defn- apply-removals!
  "Delete from the stores what a network removal `r` swept: a `jtms/retract!`,
  `jtms/sweep!` or `jtms/drop-justification!` result."
  [kb {:keys [removed-sentexes removed-justifications] :as r}]
  (let [recs (:records kb)
        gone (into [] (keep #(p/get-sentex recs %)) removed-sentexes)]
    (doseq [sx gone] (sentex-removed! kb sx))
    (doseq [jid removed-justifications] (p/delete-justification! recs jid))
    (special/retire-unjustified-mints! kb r)))

(defn take-out!
  "Take stored row `h` out of the network and the store: drop its premise mark and every
  justification concluding it, retract it, and remove from the store what that swept,
  then the row itself when it is still stored (an inert sentex is no network datum).
  `core/retract!`'s storage half, for a caller inside a write or a settle that runs its
  own follow-through.

  The justifications go first: a row a rule concluded is still groundable after the
  retraction, and deleting its record would leave its node and every justification naming
  it in the network, each naming a handle with no record."
  [kb h]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (p/unmark-premise! recs h)
    (doseq [jid (vec (jtms/supports tms h))]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! recs jid)
        (apply-removals! kb r)))
    (apply-removals! kb (jtms/retract! tms h))
    (when-let [sx (p/get-sentex recs h)] (sentex-removed! kb sx))))

(defn- fold-row!
  "Fold the mirrored row `doomed` into `survivor` and take it out of the store: the
  justifications that conclude it, its premise mark, the conclusions drawn through it,
  and the handle-naming metas that would otherwise be left pointing at a record nothing
  holds.

  Then `jtms/retract!`, which is what `core/retract!` runs and does the same work here —
  drops the premise, relabels the region, and sweeps the row now that nothing is left
  resting on it — with the swept records handed to the removal choke point above.  A row
  the sweep leaves behind goes through that choke point directly, `core/retract!`'s other
  branch: an **inert** sentex (`assert-inert`) was never a TMS datum, so the retraction
  no-ops over it.

  `fold-supports!` runs **first**, so the survivor holds a copy of each justification
  concluding the row before `take-out!` drops the originals."
  [kb doomed survivor witness rewrite]
  ;; read before anything moves: the doomed row's pieces, spelled as it wrote them, go to
  ;; the survivor with everything else it hands over
  (let [dsx     (p/get-sentex (:records kb) doomed)
        ssent   (:sentence (p/get-sentex (:records kb) survivor))
        dpieces (written-out kb doomed (:sentence dsx))
        spieces (written-out kb survivor ssent)
        copied  (fold-supports! kb doomed survivor)]
    (when (seq copied) (special/refile-mint! kb nil survivor))
    (put-spellings! kb survivor
                    (rewritten rewrite (some-> rewrite (apply [ssent]))
                               (assoc spieces
                                      :premise (merge-with strength/max (:premise spieces) (:premise dpieces))
                                      :derived (into (:derived spieces)
                                                     (keep (fn [[jid w]] (when-let [n (copied jid)] [n w])))
                                                     (:derived dpieces))))))
  (fold-dependents! kb doomed survivor)
  (fold-premise! kb doomed survivor)
  ;; with no witness the carried meta rests on the original meta alone
  (special/migrate-handle-metas kb doomed survivor 'rewriteOf [(if witness [witness] [])]
                                (:context (p/get-sentex (:records kb) doomed)))
  (take-out! kb doomed))

(defn- redraw-mints!
  "Bring the argument-type mints row `h` triggers to the spelling it holds now: draw what
  that spelling entails, then drop each mint justification it does not draw
  (`special/redraw-mints`).  `{:new [handle …] :violations [v …]}`, the mints drawn."
  [kb h]
  (let [tms         (reasoning/tms kb)
        [drawn stale] (special/redraw-mints kb h)]
    (doseq [jid stale]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! (:records kb) jid)
        (apply-removals! kb r)))
    drawn))

(defn move-row!
  "Bring one stored row `sx` to the spelling `want`: `{:at handle :new [handle …]
  :violations [v …]}`, the handle the row ends up at, followed in `:new` by the mints its
  new spelling drew (`redraw-mints!`), or nil when it is spelled `want` already.
  `symmetrize-row!` below states the shape and the choice of survivor.  `witness` is the
  mark handle a folded row's metas are carried on, or nil.  `rewrite` re-spells the row's
  written spellings (`rewritten`), nil to keep them as written."
  [kb sx want witness rewrite]
  (when (not= want (sx/sentence-of sx))
    (let [tms    (reasoning/tms kb)
          ctx    (:context sx)
          self   (:id sx)
          mirror (kb/find-sentex-handle kb want ctx)
          ;; the row that can leave: the one standing on nothing but its own premise
          ;; where only one of the two does, and otherwise the later handle — which
          ;; covers a pair a rule concluded on both sides, `fold-supports!` being what
          ;; makes that one foldable
          bare?  (fn [h] (empty? (jtms/supports tms h)))
          doomed (cond (nil? mirror)                          nil
                       (and (bare? self)   (not (bare? mirror))) self
                       (and (bare? mirror) (not (bare? self)))   mirror
                       :else                                    (max self mirror))]
      (let [at (cond
                 ;; nothing to fold: the row is alone under this proposition and only
                 ;; spelled the way the entry point used to spell it
                 (nil? mirror)   (:id (respell! kb sx want rewrite))
                 ;; this row is the one that leaves; the mirror is already the wanted
                 ;; spelling
                 (= doomed self) (do (fold-row! kb self mirror witness rewrite) mirror)
                 ;; the mirror leaves, and this row takes the spelling it vacated
                 :else           (do (fold-row! kb mirror self witness rewrite)
                                     (:id (respell! kb (p/get-sentex (:records kb) self) want rewrite))))
            {:keys [new violations]} (redraw-mints! kb at)]
        {:at at :new (into [at] new) :violations violations}))))

(defn spelling-plan
  "`[home entries respelled]` for a piece of a fact written `w` in `ctx`, read through
  `planner` (`res/spelling-planner`): `home`, the spelling the piece is stored at, with
  `entries`, the marks that spell it (nil: the store's own marks); and `respelled`,
  `{spelling entries}` for every other spelling a reader of the fact reads, each stored
  justified `respell` by the home row (`chain/respell-rows!`).  One spelling read: the
  piece sits at it.  Several: the piece sits at `w` as written."
  [kb planner w ctx]
  (if-let [sp (planner w ctx)]
    (if (= 1 (count sp))
      (let [[sw e] (first sp)] [sw e {}])
      [w #{} (dissoc sp w)])
    [(kb/canonical-sentence kb w ctx) nil {}]))

(defn spelled
  "Call `f` with `res/*spelled-by*` naming `pred` in `ctx` with `entries`, or plainly when
  `entries` is nil, so the store spells `pred`'s literals in `ctx` by those marks.  `f`'s
  value is realized inside the binding."
  [pred ctx entries f]
  (if (some? entries)
    (binding [res/*spelled-by* [pred ctx entries]] (let [v (f)] (if (seq? v) (doall v) v)))
    (f)))

(defn- symmetrize-row!
  "Bring one stored row of a newly symmetric predicate into the argument order its
  readers read (`spelling-plan`'s home, the canonical order while every reader believes
  the mark): `move-row!`'s result, or nil when it is spelled so already.

  With no mirror stored the row is simply re-spelled where it lies.  Nothing else moves,
  which is why the lone case costs no handle: a caller holding it can still retract it,
  and the mirror asserted later now dedups to it instead of storing a second row.  With
  one stored, the pair folds into a single row and that row is re-spelled if it needs it.

  **Which of the pair survives is decided from what supports it, and only then from the
  handle.**  A row that is only a premise leaves cleanly, because `jtms/retract!` is
  exactly the sweep that takes it, so it is preferred as the one to go.  A row a rule
  concluded leaves through `fold-supports!`, which copies the justifications naming it
  as their consequence onto the survivor before the row's own go — belief is recomputed
  from the justifications, never edited around them, and a copy onto the row saying the
  same thing edits nothing.  Between two rows the fold has no other reason to separate,
  the **lower** handle survives: it is the row the KB would hold had the declaration been
  written first, which is the claim being restored.  Nothing keys belief on the number;
  what keys on it is which of two handles a caller can still name, and answering that with
  the earlier one is what makes the issue's `(retract! h1)` mean the same thing in both
  orders.

  **A pair both of whose rows a rule concluded folds too**, on that same lower-handle
  rule.  It takes two rules concluding one proposition's two spellings under a predicate
  nothing had yet declared symmetric, and left unfolded it is the defect this arm exists
  to close: the mark arriving first leaves one record and the mark arriving last leaves
  two, each believed, so the proposition is matched twice."
  [kb planner sx witness]
  (let [ctx          (:context sx)
        [want ents]  (spelling-plan kb planner (:sentence sx) ctx)]
    (spelled (res/permuted-functor (:sentence sx)) ctx ents
             #(move-row! kb sx want witness nil))))

(defn fold-row-home!
  "`symmetrize-row!` for one row a caller walks itself (`chain/respell-rows!`)."
  [kb planner sx witness]
  (symmetrize-row! kb planner sx witness))

(defn- recanonicalizing-subject
  "The predicate whose stored facts a declaration re-spells, or nil when `sentence` is not
  one that moves a spelling.  Four spellings reach one sweep:

  * `(symmetric P)` — the two arguments of a binary `P` sort.
  * `(commutativeInArgAndRest P f)`, `(commutativeInArgs P p …)` and `(commutative P)` —
    the arguments inside the component named sort, at any arity.

  `(commutative P)` installs the group `[:rest 1]` at its own arm (`special/arms`), so it
  re-spells `P`'s stored facts exactly as the other two spellings do and is asked about
  here on the same terms.  The sugar used to be absent, because a core.txt rule derived
  `(commutativeInArgAndRest P 1)` from it and that conclusion reached this sweep through
  `chain/place-fact-conclusion`.  That rule is inert now, so the mark carries the sweep
  itself.

  The mark must also be **installed**, not merely written: a declaration the taxonomy has
  not taken up re-spells nothing, and asking here is what keeps the walk off a store the
  arriving sentex does not actually move.

  The mark is read unscoped: the fold decides the stored key, which every reader
  shares."
  [kb sentence]
  (when (and (sequential? sentence) (symbol? (nm/functor sentence)))
    (let [tax (reasoning/taxonomy kb)
          f   (nm/functor sentence)
          p   (first (nm/args sentence))]
      (when (and (symbol? p) (not (sx/variable? p)))
        (case f
          symmetric                (when (and (= 1 (nm/arity sentence))
                                              (tax/has-prop? tax :symmetric p))
                                     p)
          (commutativeInArgAndRest
           commutativeInArgs
           commutative)            (when (seq (tax/commuting-groups tax p)) p)
          nil)))))

(defn commute-predicate
  "Bring `pred`'s stored rows into the spelling its marks now give them, folding mirrored
  pairs — `commute-existing`'s walk, for a caller that knows the predicate rather than
  the declaration: a mark revived by a relabel, which no declaration arrives to announce
  (`chain/reconcile-spellings!`).  `witness` is the mark handle a folded row's metas are
  carried on.  `{:new [handles] :violations [v]}`, the moved rows and the mints their new
  spellings drew, or nil when `pred` has no stored rows."
  [kb pred witness]
  (let [idx (:index kb)]
    (when (pos? (reads/stored-count-with-functor idx pred))
      ;; snapshotted before the first write: the fold posts to the roots this walk
      ;; reads, and no index backend promises whether a posting read is a snapshot
      (let [planner (res/spelling-planner kb)]
        (transduce (keep (fn [h]
                           (when-let [sx (p/get-sentex (:records kb) h)]
                             (symmetrize-row! kb planner sx witness))))
                   (completing #(merge-with into %1 (select-keys %2 [:new :violations])))
                   {:new [] :violations []}
                   (vec (reads/as-stored-with-functor idx pred)))))))

(defn commute-existing
  "When a declaration that *re-spells* arrives — `symmetric`, or either commutativity
  relation — bring the named predicate's **already stored** facts into the argument order
  the declaration puts every later one in.  `commute-predicate`'s result — the rows whose
  spelling moved, which are new content to every rule that reads the canonical one, and
  the mints their spellings drew — or nil when `sentence` declares nothing that moves a
  spelling.

  A declaration has to reach the facts already stored exactly as it reaches the facts that
  follow, which is `equate-existing`'s rule and holds here for a blunter reason: the entry point
  *sorts* a symmetric literal's arguments, so a declaration arriving second leaves the KB
  holding `(P b a)` where a KB told the same things in the other order holds `(P a b)` —
  and if both spellings were written, two rows for one proposition, each retractable
  without the other (vaelii#61).  Written the ordinary way — declaration first, then the
  facts — this finds an empty extent and costs one index cardinality read.

  **Shape: the storage migrates, rather than an alias recording that two rows mean one.**
  Both answer the issue; they differ in what a *restart* sees.  An alias is derived state,
  so it has to be rebuilt on every `recover` from records that still spell the fact two
  ways, and every reader — matching, retraction, the TMS, the handle entry points — has to
  consult it for ever after.  Migrating instead leaves the records themselves canonical,
  so `recover` reads a store that needs no reconciling and no reader learns a new rule.
  The price is that it is a write, and retracting the mark does not undo it by itself:
  what makes the mark leaving answerable is the record each moved row keeps of the
  spellings it was written in (`spellings-key`), which `chain/reconcile-spellings!` reads
  to split the rows back apart.

  **The extent is `P`'s own stored rows, not its spec subtree.**  `res/kb-sentex` reads
  the mark off the literal's exact functor — a `genl` edge below a symmetric predicate
  does not make the sub-predicate symmetric, and `constraint_descension_test` holds that
  line — so a row this arm re-spelled at a sub-predicate would be one the entry point stores the
  other way round on the very next assertion.

  **Stored, never believed.**  A mirrored pair whose rows are currently defeated merges
  exactly as a believed one does, for `equate-existing`'s reason: a spelling is not a
  claim, and reading belief here would leave the migration missing when the defeat lifts
  — belief depending on the order the defeat and the declaration arrived in.

  On a KB with a large extent under the newly marked predicate this costs one posting-list
  read plus a record fetch and a canonicalization per row, and a store probe per row that
  is out of order.  That is the same shape `equate-existing` pays and the same bound: it
  is a declaration reaching the facts, so it is linear in the facts it reaches, and a
  predicate marked before it has any is free."
  [kb sentence witness]
  (when-let [p (recanonicalizing-subject kb sentence)]
    (commute-predicate kb p witness)))
