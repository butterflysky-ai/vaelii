;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.settle
  "Belief settling: the pass that relabels the TMS and runs the `exceptWhen` re-check
  queue to a joint fixpoint with belief (`pass-work`, `block-work`, `apply-pass!`), the
  seed readers a pass gathers, `settle-finish` and `settle`.  A pass calls `recheck`;
  what a reader reads of the clashes is `vaelii.impl.clashes`.  The top engine layer,
  below `vaelii.core`.  See docs/nmtms.md."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.except :as exc]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.recheck :as recheck]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wiring :as wiring]))

;; ---- the facet contract -------------------------------------------------
;; `predicates/check-facets` runs at this namespace's load (docs/predicates.md says why).

(def facet-check-inputs
  "The cross-layer facts `predicates/check-facets` cannot read for itself.  A var so
  that this call site and `predicates_test` check the same arguments.

  * `:recheck-subjects` — the functors posting exception re-checks through the shared
    path (`special/declaration-subjects`) rather than from an arm of their own.
  * `:family-rosters` — `family -> {roster-name functors}`, every roster that reads a
    mark family as a family (`predicates_test/a-roster-that-enumerates-a-family-is-named-here`)."
  {:recheck-subjects special/recheck-subjects
   :family-rosters   {:argument-constraint
                      {'checks/constraint-declaration-functors
                       checks/constraint-declaration-functors
                       'provers/meta-constraint-functors
                       provers/meta-constraint-functors}}})

(def checked-entries
  "`predicates/entries`, having passed the facet contract at this namespace's load, which
  throws on a violation.  A var rather than a bare call so `predicates_test` can prove
  the check runs here on the live inputs."
  (pr/check-facets pr/entries facet-check-inputs))

;; ---- the exception fixpoint ---------------------------------------------
;; Belief and blocking depend on each other, so `settle` iterates: relabel, re-evaluate
;; the exceptions the triggers queued, relabel again if the blocked set moved.

(def ^:private max-settle-passes
  "Bound on the exception fixpoint's passes.  Termination rests on the stratification
  checks at assert time; a run that reaches this bound logs `::exception-fixpoint`
  instead of looping (docs/exceptions.md)."
  16)

(defn- drain-recheck!
  "Take the queued `{rule-handle -> triggers}` map and clear the queue in one CAS, so a
  re-check is done once and a `swap!` landing during the take is kept for the next pass."
  [kb]
  (let [a (reasoning/recheck kb)]
    (loop []
      (let [old @a]
        (if (compare-and-set! a old {})
          old
          (recur))))))

(def ^:dynamic *touched-sink*
  "An atom holding a set, or nil.  When bound, every settle adds the handles of its
  relabelled region before clearing them.  `core/preview` and
  `core/edit-with-consequences!` bind it (docs/preview.md)."
  nil)

(def ^:dynamic *touched-in-sink*
  "An atom holding a set, or nil: the companion of `*touched-sink*`, collecting which
  handles of that region were believed before the settle (`jtms/touched-in`).
  `core/edit-with-consequences!` binds both."
  nil)

(def ^:dynamic *sweep?*
  "Does a settle delete what a newly-blocked justification solely supported?  False only
  inside `core/preview`, which must hand the KB back at the same handles
  (docs/preview.md)."
  true)

(def ^:dynamic *relabelled-before?*
  "True when labels flipped before the settle by a path that is neither a defeat, a
  block nor a write: `core/preview`'s `jtms/suspend-premise` and its rollback's
  `add-premise`, and `settle`'s drop of a firing over a retired spelling
  (`withdraw-retired-firings!`).  It opens the `belief-moved?` gate (docs/nmtms.md, \"What
  `settle-finish` reconciles\").  A flag the caller binds, rather than a gate that tests
  the region for a taxonomy sentex, because that test would cost a record read per region
  member on every settle for a path only `preview` takes."
  false)

(def ^:dynamic *rebuilding?*
  "True while `recover`'s settles restore a KB rather than react to a change.  The passes
  that report or re-derive what a change moved read it and stand aside, among them the
  cut notices, the revival and un-merge re-seeds, the refusal re-asks
  and the second-route re-derivations.  A rebuild relabels the whole graph, so its region
  is every stored sentex, and the replayed justifications already carry every
  derivation.  The definitional nogood sweep does not read it (docs/taxonomy.md, \"What a
  declaration reaches back over\")."
  false)

(def ^:dynamic ^:private *unmerged-sink*
  "A volatile collecting the spellings an un-merge gave back, and each equality supporter
  believed again with its twins, or nil.  `settle` binds it, `settle-finish` fills it
  from the supersession moves since the last settle (`special/take-supersession-moves!`)
  and from `special/believed-again-sweeps`, and `settle` re-seeds
  what it holds and settles again (docs/nmtms.md, \"The other half: a spelling an
  un-merge gives back\")."
  nil)

(defn- apply-removals!
  "Delete from the stores what a network removal swept, and tear each deleted record down
  (`integrate/sentex-removed!`, which queues its re-check)."
  [kb {:keys [removed-sentexes removed-justifications] :as r}]
  ;; fetch before tearing down: the JTMS hands back handles, and `sentex-removed!` is
  ;; what deletes the record
  (doseq [d removed-sentexes
          :let [sx (p/get-sentex (:records kb) d)]
          :when sx]
    (integrate/sentex-removed! kb sx))
  (doseq [jid removed-justifications] (p/delete-justification! (:records kb) jid))
  (special/retire-unjustified-mints! kb r))

(defn- sweep-excepted!
  "Delete what the newly-blocked justifications were solely supporting, through the JTMS
  sweep (`apply-removals!`), and record each newly-blocked rule firing the sweep deletes
  as a refusal (`chain/record-swept-firing!`), so the trigger that lifts its block
  releases it from its bindings.  Deletes nothing while `*sweep?*` is false."
  [kb newly-blocked]
  (let [tms   (reasoning/tms kb)
        seeds (when *sweep?*
                (into #{} (keep #(:consequence (jtms/justification tms %))) newly-blocked))]
    (when (seq seeds)
      (let [rm   (jtms/sweep! tms seeds)
            gone (set (:removed-justifications rm))]
        (doseq [jid newly-blocked
                :when (contains? gone jid)
                :let [j (p/get-justification (:records kb) jid)]
                :when j]
          (chain/record-swept-firing! kb j))
        (apply-removals! kb rm)))))

(defn- released-rules
  "The informants of the justifications in `was` and not in `new`: the rules whose
  exception this pass lifted.  Called before the sweep, while those justifications are
  still in the TMS."
  [kb was new]
  (let [tms (reasoning/tms kb)]
    (into #{}
          (keep (fn [jid]
                  (let [inf (:informant (jtms/justification tms jid))]
                    (when (integer? inf) inf))))
          (remove new was))))

(defn- region-terms
  "Every symbol standing as an argument of a sentex in `region` — the terms whose
  memberships this settle can have moved."
  [kb region]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(nm/args (:sentence %)))
              (filter symbol?))
        region))

(defn- released-constraint-refusals
  "The `:constraint` refusals the argument constraint no longer convicts, as `[[rule-handle
  entry] …]` for `chain/release-refusal!`.  An entry is re-asked only when a `genl` or
  `genlCx` generation moved since it was stamped or `region` holds a sentex naming its
  convicted term; one still convicted is restamped
  (`chain/redecide-constraint-refusal!`).  Empty during a rebuild, since `recover`
  re-records the refusals by re-firing (`chain/rerecord-refusals!`)."
  [kb region]
  (let [entries (when-not *rebuilding?* (chain/constraint-refusals kb))]
    (if (empty? entries)
      []
      (let [gens  (chain/constraint-generations kb)
            terms (delay (region-terms kb @region))]
        (reduce (fn [acc [rh e]]
                  (if (and (or (not= gens (:gens e)) (contains? @terms (:term e)))
                           (= :free (chain/redecide-constraint-refusal! kb rh e gens)))
                    (conj acc [rh e])
                    acc))
                []
                entries)))))

(defn- released-lifts
  "The decontextualized copies an argument conviction refused that the content this
  settle stored no longer convicts, as new handles to chain from
  (`special/release-lift!`) — re-asked on `released-constraint-refusals`' two triggers,
  since the conviction is the same one."
  [kb region]
  (let [pending (when-not *rebuilding?* (special/lift-refusals kb))]
    (if (empty? pending)
      []
      (let [gens  (chain/constraint-generations kb)
            terms (delay (region-terms kb @region))]
        (into []
              (mapcat (fn [[h e]]
                        (when (or (not= gens (:gens e)) (contains? @terms (:term e)))
                          (:new (special/release-lift! kb h e gens)))))
              pending)))))

(defn- minted-mintable
  "The types the minted `genl` edge `sentence` makes mintable, where `mintable?` answers
  for the hierarchy before the edge: the lower end and its subtypes when the upper end
  is mintable, the lower end is not, and `checks/mintable-type?` reads the lower end as
  mintable now (a mint off a disbelieved fact is not in the hierarchy).  Empty for any
  other sentence."
  [tax mintable? sentence]
  (let [[f sub super] sentence]
    (if (and (= 'genl f) (mintable? super) (not (mintable? sub))
             (checks/mintable-type? tax sub))
      (tax/specs-of-all tax [sub])
      #{})))

(defn- released-mints
  "The types minted by declarations whose type has become mintable since they were
  swept, as new handles to chain from (`special/release-mint!`).  Re-asked only when a
  `genl` or `genlCx` generation has moved since the entry was stamped, since nothing else
  changes what `mintable-type?` answers, and answered from one walk down from `thing`
  taken before the first release (`checks/mintable-types`).  A `genlArg` release mints a
  `genl` edge that walk does not hold: the types the edge makes mintable join the
  answer (`minted-mintable`), and the entries already restamped waiting on one of them
  are released again in the same pass.  Not during a rebuild, for
  `released-constraint-refusals`' reason."
  [kb]
  (let [gens    (chain/constraint-generations kb)
        pending (when-not *rebuilding?* (special/mint-refusals kb gens))]
    (if (empty? pending)
      []
      (let [tax       (reasoning/taxonomy kb)
            walked    (checks/mintable-types tax)
            added     (volatile! #{})
            mintable? #(or (walked %) (contains? @added %))]
        (special/minted-seeds
         kb
         ;; `waiting` holds the restamped entries by the type each waits on
         (loop [todo    (into clojure.lang.PersistentQueue/EMPTY (map first) pending)
                waiting {}
                minted  []]
           (if-let [dh (peek todo)]
             (let [{new :new waits :waits} (special/release-mint! kb dh gens mintable?)
                   grown (reduce (fn [acc h]
                                   (let [g (some->> (p/get-sentex (:records kb) h) :sentence
                                                    (minted-mintable tax mintable?))]
                                     (vswap! added into g)
                                     (into acc g)))
                                 #{} new)
                   waiting (reduce #(update %1 %2 (fnil conj #{}) dh) waiting waits)]
               (recur (into (pop todo) (comp (mapcat waiting) (distinct)) grown)
                      (reduce dissoc waiting grown)
                      (into minted new)))
             minted)))))))

(defn- revived-mark-seeds
  "The merges and lifts a mark, or a `genl` edge under one, in `revived` owes the facts
  stored while it was OUT, as new handles to chain from
  (`special/revived-declaration-sweeps`).  Reconciles the retired spellings and reports
  the violations, as `assert-one` does for the same sweeps on an arrival.  `revived` is
  `revived-seeds`' answer, so a rebuild asks nothing.  The taxonomy is reconciled over
  `revived` first: a datum a relabel inside this settle revived, such as a `genl` edge
  whose void firing a roster declaration released, is in no cache until `settle-finish`,
  and the sweeps read the marks and edges the caches hold."
  [kb revived]
  (when (seq revived)
    (special/reconcile-belief-change kb revived)
    (tax/restore-depths (reasoning/taxonomy kb)))
  (if-let [mig (special/revived-declaration-sweeps kb revived)]
    (do (when (seq (:superseded mig))
          (special/refresh-supersessions kb (:superseded mig)))
        (violations/report kb (:violations mig))
        (special/minted-seeds kb (:new mig)))
    []))

(defn- class-moved-merge-seeds
  "The merges and un-merges a collision member's class moving owes
  (`special/class-moved-merges` over `region`, the pass's `touched` as a delay), as handles
  to chain from: the new twins and the members of each dropped merge.  Applies the
  removals, reconciles the retired spellings and reports the violations, as
  `revived-mark-seeds` does.  `asked` is the settle's record of what it asked.  Empty
  during a rebuild, whose replayed justifications carry every merge."
  [kb region asked]
  (if-let [mig (when-not *rebuilding?* (special/class-moved-merges kb region asked *sweep?*))]
    (let [seeds (into (special/minted-seeds kb (:new mig)) (:members mig))]
      (some->> (:removed mig) (apply-removals! kb))
      (when (seq (:superseded mig))
        (special/refresh-supersessions kb (:superseded mig)))
      (violations/report kb (:violations mig))
      seeds)
    []))

(defn- except-move-seeds
  "The twins owed to the facts an `except` moved an equality's or a merge mark's
  visibility over, and the argument-type derivations it moved, as new handles to chain
  from (`special/drain-except-moves!`).  The derivations it hides are removed here.  The
  supersessions the sweep found wait on `:except-moves` for `settle-finish`; the
  violations are reported here.  A rebuild clears the queue, since it reconciles every
  supersession from the stored twins."
  [kb]
  (if *rebuilding?*
    (do (special/clear-except-moves! kb) [])
    (if-let [mig (special/drain-except-moves! kb *sweep?*)]
      (do (some->> (:removed mig) (apply-removals! kb))
          (violations/report kb (:violations mig))
          (special/minted-seeds kb (:new mig)))
      [])))

(defn- context-move-seeds
  "The chaining seeds the pass's `genlCx` moves owe (`special/drain-context-moves!`): the
  facts they make matchable and the twins and mints their sweeps wrote.  The supersessions
  the sweeps found are reconciled and the violations reported here."
  [kb {:keys [seeds mig]}]
  (when (seq (:superseded mig))
    (special/refresh-supersessions kb (:superseded mig)))
  (violations/report kb (:violations mig))
  (into (vec seeds) (special/minted-seeds kb (:new mig))))

(defn- released-subsumed
  "The mints a record leaving belief or the store no longer lets the KB withhold, as new
  handles to chain from (`special/withheld-releases`).  `withdrawn` is the mints this
  settle withdrew, whose own departure releases nothing.  Empty during a rebuild, which
  drops the queued departures: a restore changes nothing.  `was-in` and `believed?` are
  belief before the settle and now (`pass-belief`)."
  [kb moved was-in believed? asked withdrawn]
  (if *rebuilding?*
    (do (special/drain-departures! kb) [])
    (:new (special/withheld-releases kb moved was-in asked withdrawn believed?))))

(defn- triggered-seeds
  "The entailments a membership or a `genl` edge that came IN this settle triggers over
  the stored facts naming the terms it types, as new handles to chain from
  (`special/triggered-mints`).  `asked` holds the records already asked this settle.
  Empty during a rebuild, which draws no entailment."
  [kb moved was-in believed? asked]
  (if *rebuilding?*
    []
    (let [r (special/triggered-mints kb moved was-in asked believed?)]
      (violations/report kb (:violations r))
      (special/minted-seeds kb (:new r)))))

(defn- drop-surplus-placements!
  "Drop the mint justifications `jids` (`special/surplus-placements`, read by
  `subsumed-blocks`) and delete what the drop sweeps.  Returns `jids` as a vector."
  [kb jids]
  (when (seq jids)
    (let [tms (reasoning/tms kb)]
      (apply-removals! kb (reduce (fn [acc jid]
                                    (let [r (jtms/drop-justification! tms jid)]
                                      (p/delete-justification! (:records kb) jid)
                                      (merge-with into acc r)))
                                  nil jids))))
  (vec jids))

(defn- subsumed-blocks
  "The mint justifications this settle withdraws, and the records they held up:
  `special/subsumed-mint-blocks` over `moved`, the delay of the region's sentexes
  `released-subsumed` reads too."
  [kb moved was-in believed? asked]
  (or (special/subsumed-mint-blocks kb moved was-in asked believed? (not *rebuilding?*))
      {:blocked #{} :withdrawn #{}}))

(defn- defeat-moves
  "`[stored removed]` over the placed handles of `region` (the window, a set) that move a
  handle with no relabel (`kb/placed-targets`): `stored` holds those IN now and not when
  the window opened, and `removed` holds `[target context]` for each handle moved by one
  IN when the window opened and OUT now or gone from the store, the gone ones read off the
  removal record (`integrate/*removed-sink*`)."
  [kb region]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        was  (jtms/touched-in tms)
        ;; only the engine derives a defeat, under one of two informants, so a handle
        ;; with no such justification is no defeat and its record is not read
        placed? (fn [h] (some #(contains? #{exc/nogood-informant exc/guard-informant}
                                          (:informant (jtms/justification tms %)))
                              (jtms/supports tms h)))
        gone (when-let [sink integrate/*removed-sink*]
               (into #{} (mapcat (fn [sx] (when (contains? was (:id sx))
                                            (map #(vector % (:context sx))
                                                 (kb/placed-targets kb (:sentence sx))))))
                     @sink))]
    ;; with no defeat stored and no except beside a placed contradicts, the window holds
    ;; nothing that moves a handle with no relabel
    (if-not (exc/placed-reads? kb)
      [#{} (or gone #{})]
      (reduce (fn [[st rm :as acc] h]
                (let [sx (when (placed? h) (p/get-sentex recs h))
                      ts (some->> sx :sentence (kb/placed-targets kb))]
                  (cond (empty? ts)                                    acc
                        (and (jtms/in? tms h) (not (contains? was h))) [(conj st h) rm]
                        (and (not (jtms/in? tms h)) (contains? was h)) [st (into rm (map #(vector % (:context sx))) ts)]
                        :else                                          acc)))
              [#{} (or gone #{})]
              region))))

(def ^:dynamic *belief-before*
  "`{handle hidden?}` read before a write (`reading-before`), or nil: the own-context belief
  a write's report diffs against for the handles the defeats its sentences can move reach.
  Bound by the write entry points, and by `settle` when none is bound."
  nil)

(def ^:dynamic *batch-reading*
  "A volatile holding the reading a `with-deferred-settle` batch took before its first
  write (`reading-before`), or nil.  The batch does not name its writes in advance, so
  the reading covers every standing defeat's reach.  A settle inside the batch takes it
  again once it has reported, and the batch's closing settle diffs against it."
  nil)

(defn- report-wanted?
  "Does a settle owe a report: a sink is bound or a listener is registered?"
  [kb]
  (boolean (or *touched-sink* *touched-in-sink*
               (and (not *rebuilding?*) (feed/wants-region? kb)))))

(defn- plain-literal?
  "Is `s` a literal over atoms, or the `not` of one, whose functor the engine does not
  interpret (`predicates/entry`) and is no stored disjoint metatype?"
  [tax s]
  (let [atom? #(not (or (sequential? %) (sx/variable? %)))
        lit?  #(and (seq? %) (symbol? (first %)) (atom? (first %)) (nil? (pr/entry (first %)))
                    (every? atom? (rest %))
                    (not (and (= 2 (count %)) (tax/stored-disjoint-metatype? tax (first %)))))]
    (if (and (seq? s) (= sx/not-functor (first s)) (= 2 (count s)))
      (lit? (second s))
      (lit? s))))

(defn- partners
  "The handles a nogood placed over `s` could defeat beside it: those naming an argument of
  `s` (or of its body), and those naming its functor as an argument; the `:default` ones
  only, unless an except is stored, which lowers a class at a reader."
  [kb s]
  (let [idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)
        lit  (if (= sx/not-functor (first s)) (second s) s)
        f    (first lit)
        meta (into [] (comp (mapcat (fn [pos] (some->> (reads/as-stored-predicates-at-arg idx pos f)
                                                       (mapcat #(reads/as-stored-with-args idx % {pos f}))))))
                   [1 2 3])]
    (into #{} (comp cat (filter #(or (reads/stores-any? idx sx/except-functor)
                                     (not= :monotonic (jtms/defeat-class tms %))))
                    (filter #(p/get-sentex recs %)))
          [(mapcat #(reads/as-stored-with-term idx %) (rest lit)) meta])))

(defn- write-seeds
  "The handles a reporting write's reading starts from, or nil for a write no seed set
  places.  `writes` holds `[:assert sentence context strength]` and
  `[:retract handle]`.  A retraction, or an assertion of a stored sentence, seeds its
  handle; a new literal seeds nothing, or its `partners` when it is `:monotonic` or on the
  forced-monotonic roster.  Unplaced: an interpreted functor or a compound argument, a fact
  that fires or re-joins a forward rule (`chain/triggers-rules?`), and any write while an
  equality edge is stored."
  [kb writes]
  (let [tax  (reasoning/taxonomy kb)
        recs (:records kb)]
    (when (and (seq writes) (empty? (tax/equality-edges tax)))
      (reduce (fn [acc [op x c strength]]
                (case op
                  :retract (if-let [sx (p/get-sentex recs x)]
                             (if (plain-literal? tax (:sentence sx)) (conj acc x) (reduced nil))
                             acc)
                  :assert  (if (or (not (symbol? c)) (sx/variable? c) (not (plain-literal? tax x))
                                   (chain/triggers-rules? kb x))
                             (reduced nil)
                             (let [h (kb/find-sentex-handle kb x c)]
                               (cond-> acc
                                 h (conj h)
                                 (or (= :monotonic strength) (decide/roster-literal? tax x))
                                 (into (partners kb x)))))))
              #{} writes))))

(defn- edge-moves
  "The `special/context-move` of each write of `writes`, or nil when one is not a `genlCx`
  edge between two symbols."
  [kb writes]
  (let [recs (:records kb)
        edge (fn [[op x]]
               (let [s (case op
                         :assert  x
                         :retract (:sentence (p/get-sentex recs x)))]
                 (when (and (seq? s) (= 'genlCx (first s)) (= 3 (count s))
                            (symbol? (second s)) (symbol? (nth s 2)))
                   [(second s) (nth s 2)])))
        es   (map edge writes)]
    (when (and (seq writes) (every? some? es))
      (mapv (fn [[a b]] (special/context-move kb a b)) es))))

(defn- edge-write-seeds
  "The handles the `genlCx` edge moves `ms` (`edge-moves`) can move the belief of at their
  own contexts: each move names the contexts whose ancestor sets it changes (`:under`)
  and the contexts it shows or hides (`:moved`, `:raw`).  The seeds are the targets of
  the defeats and the members of the `contradicts` stored in those contexts, and the
  nogood candidates stated under the edge, where a placement it gives or takes hides one
  at its own context (ruling 21)."
  [kb ms]
  (let [recs  (:records kb)
        idx   (:index kb)
        under (into #{} (mapcat #(deref (:under %))) ms)
        ctxs  (into under (mapcat #(concat (:moved %) (:raw %))) ms)
        named (fn [f] (into [] (comp (keep #(p/get-sentex recs %))
                                     (mapcat #(rest (:sentence %)))
                                     (keep sx/handle-id))
                            (reads/as-stored-with-functor-in idx f ctxs)))]
    (-> #{}
        (into (named sx/defeat-functor))
        (into (named 'contradicts))
        (into (decide/handles-at (decide/synced kb) under)))))

(defn- edge-declaration-seeds
  "The handles the `genlCx` edge moves `ms` (`edge-moves`) can move the roster reading
  of: for each predicate a believed declaration stated in a context a move shows or hides
  puts on the roster (`decide/declared`), its stored facts and their stored denials
  stated under that move's edge.  A reader under the edge gains or loses the declaration,
  and an inert denial and a void firing are hidden by the read walk alone."
  [kb ms]
  (let [declared (decide/declared (reasoning/taxonomy kb))]
    (when (seq declared)
      (let [idx  (:index kb)
            recs (:records kb)]
        (into #{} (mapcat (fn [m]
                            (let [shown (into (set (:moved m)) (:raw m))
                                  preds (into #{} (keep (fn [[[_ pred] decls]]
                                                          (when (some shown (vals decls)) pred)))
                                              declared)]
                              (when (seq preds)
                                (let [under @(:under m)]
                                  (concat (mapcat #(reads/as-stored-with-functor-in idx % under) preds)
                                          (filter #(let [d (:sentence (p/get-sentex recs %))]
                                                     (and (sx/negation? d) (contains? preds (nm/functor (second d)))))
                                                  (when (reads/stores-opposed? idx)
                                                    (reads/as-stored-opposed-in idx under)))))))))
              ms)))))

(defn belief-before
  "`{handle hidden?}` for every handle what `writes` can move reaches: `kb/moved-reach` of
  their seeds (`write-seeds`, or `edge-write-seeds` for a batch of `genlCx` edges), and of
  the facts a roster declaration among them moves (`chain/declaration-reach`) or a `genlCx`
  edge among them shows or hides (`edge-declaration-seeds`).  For a
  write no seed set places, or a reach a handle of which moves a placement or queues a
  watched rule (`special/posts-recheck?`), the reach is that of every standing defeat's
  target and every placed `contradicts`' members.  The value is
  whether the handle's own context does not believe it now (`exc/own-hidden-fn`); a handle
  the reading does not hold was hidden by no defeat and no conflict."
  [kb writes]
  (let [recs       (:records kb)
        idx        (:index kb)
        tax        (reasoning/taxonomy kb)
        reads?     (exc/placed-reads? kb)
        conflicts? (pos? (reads/stored-count-with-functor idx 'contradicts))
        everything #(kb/moved-reach
                     kb (into (reads/as-stored-named-global idx sx/defeat-functor)
                              (mapcat (fn [c] (keep sx/handle-id (rest (:sentence (p/get-sentex recs c))))))
                              (when conflicts? (reads/as-stored-with-functor idx 'contradicts))))
        ;; a handle that moves no placement nor exemption by leaving, and queues no watched
        ;; rule by moving
        placed?    (fn [s] (and (or (plain-literal? tax s) (contains? '#{contradicts defeat} (nm/functor s)))
                                (not (special/posts-recheck? kb s))))
        ms         (edge-moves kb writes)
        edges      (when (and ms (or reads? conflicts?)) (edge-write-seeds kb ms))
        seeds      (when (and (nil? edges) (or reads? conflicts?)) (write-seeds kb writes))
        reach      (when (and seeds reads?) (kb/moved-reach kb seeds))
        reach      (cond edges        (kb/moved-reach kb edges)
                         (nil? seeds) (when (or reads? conflicts?) (everything))
                         (not reads?) #{}
                         (and (every? #(or (not= :assert (first %)) (placed? (second %))) writes)
                              (every? #(if-let [sx (p/get-sentex recs %)] (placed? (:sentence sx)) true)
                                      reach))
                         reach
                         :else (everything))
        ;; a roster declaration moves its predicate's readings with no defeat: an inert
        ;; denial and a void firing are hidden by the read walk alone
        declared   (into #{} (mapcat (fn [[op x c]]
                                       (case op
                                         :assert  (chain/declaration-reach kb x c)
                                         :retract (when-let [sx (p/get-sentex recs x)]
                                                    (chain/declaration-reach kb (:sentence sx) (:context sx)))
                                         nil)))
                         writes)
        declared   (cond-> declared ms (into (edge-declaration-seeds kb ms)))
        reach      (cond-> reach (seq declared) (-> set (into (kb/moved-reach kb declared))))
        hid        (exc/own-hidden-fn kb)]
    (into {} (map (fn [h] [h (boolean (and hid (hid h)))])) reach)))

(defn reading-before
  "What a write that reports binds `*belief-before*` to before it writes: the binding in
  force, or `belief-before` over `writes` when a sink is bound or a listener registered,
  else nil.  A defeat moves belief with no relabel, and a retraction moves a defeat before
  its settle opens, so the reading precedes the write (docs/nmtms.md, \"The published
  window\")."
  [kb writes]
  (or *belief-before*
      (some-> *batch-reading* deref)
      (when (report-wanted? kb) (belief-before kb writes))))

(defn- defeat-belief-moves
  "`{:gone :back}`: the targets of the defeats `stored` that their own context no longer
  believes, and the targets of `removed` it believes again (`exc/believed-own?`) — the
  handles a defeat moved with no relabel, which a pass reads as it reads a relabelled
  one."
  [kb [stored removed]]
  (let [recs (:records kb)]
    {:gone (into #{} (comp (keep #(some-> (p/get-sentex recs %) :sentence kb/defeat-target))
                           (remove #(exc/believed-own? kb %)))
                 stored)
     :back (into #{} (comp (map first) (filter #(exc/believed-own? kb %))) removed)}))

(defn- pass-belief
  "`[was-in believed?]` for a pass: the relabelled handles believed before the settle
  (`jtms/touched-in`) with the targets a defeat moved (`moves`, `defeat-belief-moves`)
  folded in, and belief now: the network's, and for a moved target its own context's."
  [kb {:keys [gone back]}]
  (let [tms   (reasoning/tms kb)
        moved (into (set gone) back)]
    [(as-> (jtms/touched-in tms) w
       (into w gone)
       (reduce disj w back))
     (if (empty? moved)
       #(jtms/in? tms %)
       #(and (jtms/in? tms %) (or (not (contains? moved %)) (exc/believed-own? kb %))))]))

(defn- post-defeat-moves!
  "Post the re-check each `defeat` relabelled in `region` (the pass's `touched`, as a
  delay) or among `placed`, the handles this pass placed, and not in `read` (a volatile
  set, which this adds them to, so each is posted once a settle), owes its target's watchers
  (`special/recheck-defeat-target`): a defeat moves the belief of its target, and of what
  rests on the target, with no relabel of either.  While a watched rule is stored, each
  handle of `kb/defeat-reach` over those defeats posts its sentence
  (`special/recheck-on-sentence`): a defeat in a target's closure moves in force with the
  target, so its own target and that target's closure are posted too.  The pass drains
  what this queues, and releases a firing the move unblocks from the refusal record
  (`recheck/released-refusals`).  Reads `region` only while a defeat is stored.  It
  fetches a record per handle read, or per stored `defeat` where fewer are stored."
  [kb region placed read]
  (let [idx (:index kb)
        nd  (reads/stored-count-at idx [sx/defeat-functor])]
    (when (pos? nd)
      (let [recs  (:records kb)
            fresh (into [] (remove @read) (concat @region placed))
            _     (vswap! read into fresh)
            ;; a `recover`'s region is the whole store, and the defeat extent the smaller read
            cands (if (< nd (count fresh))
                    (filter (set (reads/as-stored-with-functor idx sx/defeat-functor)) fresh)
                    fresh)
            ds    (into [] (keep #(let [sx (p/get-sentex recs %)]
                                    (when (kb/defeat-target (:sentence sx)) sx)))
                        cands)]
        (doseq [sx ds] (special/recheck-defeat-target kb sx))
        (when (and (seq ds) (seq (reads/watched-rules idx)))
          (doseq [h (kb/defeat-reach kb (map :id ds) #{})
                  :let [s (p/get-sentex recs h)]
                  :when s]
            (special/recheck-on-sentence kb (sx/sentence-of s))))))))

(defn- revived-seeds
  "The datums `jtms/revived` finds in `region` (the pass's `touched`, as a delay), minus
  `done`, the ones an earlier pass of this settle already re-seeded.  Nil during a
  rebuild (docs/nmtms.md, \"A revived datum is a datum the agenda has not seen\")."
  [kb done region]
  (when-not *rebuilding?*
    (into [] (remove done) (jtms/revived (reasoning/tms kb) @region))))

(defn- departed-handles
  "The handles in `region` (the pass's `touched`, as a delay) that went IN ⇒ OUT this
  settle, by a relabel: the window `departed-seeds` and `defeated-derivation-seeds` both
  read.  Empty during a rebuild."
  [kb region]
  (if *rebuilding?*
    []
    (let [tms (reasoning/tms kb)
          was (jtms/touched-in tms)]
      (into [] (filter #(and (contains? was %) (not (jtms/in? tms %)))) @region))))

(defn- departed-seeds
  "The facts owed a re-join because a `genl` or `genlCx` edge in `out` (`departed-handles`)
  went IN ⇒ OUT or was withdrawn at its own context, minus `done`
  (`special/departed-edge-seeds`).  A verdict sweeps nothing, so this is the re-join a
  retraction gets from `special/resubsumption-seeds`
  (docs/nmtms.md, \"Where the layer stops\")."
  [kb done out]
  (when (seq out)
    (into [] (remove done) (special/departed-edge-seeds kb out))))

(defn- lost-derivation-seeds
  "Draw `justs` (`special/lost-descended-derivations`) again over a route that survives,
  and return the handles that created and each conclusion the new justification brought
  back IN, as seeds.  The second is what makes the pass that drew it productive, so the
  next pass reads the region the new support moved."
  [kb justs]
  (if (seq justs)
    (let [tms (reasoning/tms kb)]
      (into (special/rederive-descended kb justs)
            (comp (map :consequence) (distinct) (filter #(jtms/in? tms %)))
            justs))
    []))

(defn- defeated-derivation-seeds
  "The argument-type entailments and descended equalities a `genl` edge took OUT or
  withdrew at their own context when this settle withdrew it, drawn again over a route
  that survives — `departed-seeds`' twin for the derivations that name the edge rather
  than for the firings.  An equality whose facts a withdrawn merge still supersedes is
  drawn by `settle`'s un-merge round instead, once the spellings are back.

  `out` is `departed-handles`' answer for the pass."
  [kb out]
  (if (seq out)
    (lost-derivation-seeds kb (special/lost-descended-derivations kb out true))
    []))

(defn- narrow-marker?
  "Is `t` a withdrawal marker whose re-derivations a settle chains narrowly rather than
  over the rule's extent: an `except`'s move, chained from the moved target's consequence
  closure (`special/drain-except-moves!`), or a separation move, re-joined over the types
  it moved (`separation-rejoins`)?"
  [t]
  (boolean (and (map? t) (or (::special/except-closure t) (::special/separation t)))))

(defn- separation-rejoins
  "`{rule-handle types}` for the rules of the re-check queue `queued` queued with a
  `{::separation types}` marker, the types of every such marker on one rule merged."
  [queued]
  (into {} (keep (fn [[rh ts]]
                   (when (set? ts)
                     (when-let [ms (seq (keep ::special/separation ts))]
                       [rh (into #{} cat ms)]))))
        queued))

(defn- blanket-recheck-rules
  "The queued rules with no triggering sentence (`:all` or `:all-rejoin`: a taxonomy edge
  moved, or the rule was just indexed) or with a withdrawal marker other than a
  `narrow-marker?`.  They take the coarse re-chain, since nothing says
  whether the move blocked or released."
  [queued]
  (keep (fn [[rh triggers]]
          (when (or (#{:all :all-rejoin} triggers)
                    (some #(and (recheck/withdrawal-marker? %) (not (narrow-marker? %)))
                          triggers))
            rh))
        queued))

(defn- forced-recheck-rules
  "The unconditional rechecks that also owe a fresh join when blocking stayed still."
  [queued]
  (keep (fn [[rh triggers]] (when (= :all-rejoin triggers) rh)) queued))

(defn- rejoin-on-arrival-rules
  "The queued rules an arriving fact can release rather than only block
  (`special/arrival-releasable-rule?`: an aggregate or a nested NAF, in an antecedent or
  an exception), which are re-joined whatever the blocked set did (docs/exceptions.md,
  \"Re-chaining what was released, not what was touched\")."
  [kb queued]
  (keep (fn [[rh _]] (when (special/arrival-releasable-rule? kb rh) rh)) queued))

(defn- released-narrowly?
  "Does a settle release every firing of the rule at `rh` that a queued sentence unblocks,
  from the blocked set and the refusal record alone?  True for a stored rule whose only
  re-check conditions are `exceptWhen` exceptions and `unknown` antecedents, the block
  literals `recheck/exception-candidates` and `recheck/released-refusals` narrow by."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (not (rules/has-different? rsx))
         (not (rules/has-aggregate? rsx))
         (empty? (chain/closed-extent-antecedents kb (:antecedent rsx))))))

(defn rechain-owed
  "The rules of the re-check queue `queued` a teardown re-chains over their extent
  (`rechain-exception-rules`): every one but a rule queued only for `narrow-marker?`
  moves, and a rule queued only for sentences and those moves
  that the settle releases narrowly (`released-narrowly?`): a firing its block refused or
  swept is in the refusal record (`chain/record-swept-firing!`)."
  [kb queued]
  (into [] (keep (fn [[rh ts]]
                   (when-not (and (set? ts) (seq ts)
                                  (or (every? narrow-marker? ts)
                                      (and (not-any? #(and (recheck/withdrawal-marker? %)
                                                           (not (narrow-marker? %)))
                                                     ts)
                                           (released-narrowly? kb rh))))
                     rh)))
        queued))

(defn rechain-exception-rules
  "Re-chain the stored, believed forward rules among `rule-handles` over their whole
  extent, to re-derive what a released exception suppressed.  A firing whose conclusion
  stands or whose exception still holds places nothing.  Each rule costs one join over its
  extent, so callers pass the released rules rather than the queued ones
  (docs/exceptions.md).  Uses `chain`, not `chain-all`: the violations ledger is scoped to
  the caller's run."
  [kb rule-handles]
  (let [live (filter (fn [rh]
                       (let [rsx (p/get-sentex (:records kb) rh)]
                         (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                              (jtms/in? (reasoning/tms kb) rh))))
                     rule-handles)]
    (when (seq live) (chain/chain kb live nil))))

(defn rechain-seeds
  "Re-chain from `seeds`, the datum handles something put back on the agenda, filtered to
  what is still stored and believed.  One join per rule keyed by each datum's predicate,
  as an assert pays (docs/nmtms.md, \"A revived datum is a datum the agenda has not
  seen\").  Uses `chain`, not `chain-all`, as `rechain-exception-rules` does."
  [kb seeds]
  ;; `distinct`: each genlCx move of a pass seeds the facts its readers see, and on a
  ;; loaded ontology those are the same facts for every move
  (let [live (into [] (comp (distinct)
                            (filter (fn [h] (and (p/get-sentex (:records kb) h)
                                                 (jtms/in? (reasoning/tms kb) h)))))
                   seeds)]
    (when (seq live) (chain/chain kb live nil))))

(defn- settle-finish
  "Reconcile the derived caches with settled belief, publish the moved region to the
  sinks and the feed, and clear the touched window.  `belief-moved?` gates the first
  `refresh-beliefs` reconcile.  Returns the spellings superseded since the last settle,
  for `settle` to withdraw the firings over (`withdraw-retired-firings!`); empty on a
  rebuild and with `*sweep?*` off.  The order and each gate: docs/nmtms.md, \"What
  `settle-finish` reconciles\"."
  [kb region passes moved belief-moved?]
  ;; the depth repair a `with-deferred-settle` batch owes; free when nothing deferred
  (tax/restore-depths (reasoning/taxonomy kb))
  (let [extra    (volatile! #{})     ; region members no relabel recorded
        extra-in (volatile! #{})     ; ...of which these were believed until this settle
        opened   (volatile! {})      ; the superseded map when the window opened
        retired  (volatile! [])]     ; the spellings superseded since the last settle
    ;; forces the region only on a timing run (`settle_region_cost_test` counts reads)
    (when (phases/profiling?) (phases/note-region! (count @region)))
    (when belief-moved?
      (special/reconcile-belief-change kb @region)
      ;; the reconcile can open or close a cycle (docs/taxonomy.md)
      (tax/restore-depths (reasoning/taxonomy kb)))
    ;; an equality supporter a reconcile found believed again restates its class, as its
    ;; arrival does; `settle` re-seeds the supporter and its twins
    (when-let [hs (tax/take-believed-again! (reasoning/taxonomy kb))]
      (when-not *rebuilding?*
        (let [mig (special/believed-again-sweeps kb hs)]
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          (violations/report kb (:violations mig))
          (vswap! extra into (:new mig))
          (some-> *unmerged-sink* (vswap! into (concat hs (special/minted-seeds kb (:new mig))))))))
    ;; the write path reconciles every supersession a stored or removed sentence moves;
    ;; the settle owes it only for an `except` that moved (`special/take-except-moves!`)
    ;; and an equality edge that moved in belief
    (let [ex (special/take-except-moves! kb)]
      (when (or ex (tax/equality-moves? (reasoning/taxonomy kb) :supersessions))
        (special/refresh-supersessions kb (:extra ex) (when-not (:full? ex) (set (:region ex))))))
    ;; `moved` is every datum whose supersession entry changed since the last settle
    ;; finished, and `was` its entry before the first change, so `before` and `after` are
    ;; the superseded maps of the last settle and this one
    (let [after  (jtms/superseded (reasoning/tms kb))
          {:keys [moved was]} (or (special/take-supersession-moves! kb) {:moved #{} :was {}})
          before (vreset! opened (reduce (fn [m d] (if-let [e (get was d)] (assoc m d e) (dissoc m d)))
                                         after moved))]
      (vswap! extra into moved)
      ;; a datum superseded since the last settle was believed until now, and no relabel
      ;; says so, unless this window stored it
      (let [born (jtms/touched-new (reasoning/tms kb))]
        (vswap! extra-in into (filter #(and (contains? after %) (not (contains? before %))
                                            (not (contains? born %))))
                moved))
      ;; a merge supersedes a declaration with no label moving, after the reconcile above
      (when (seq moved)
        (special/reconcile-belief-change kb (into @region moved)))
      ;; the spellings an un-merge gave back, for `settle` to re-seed
      (when-let [sink (and (not *rebuilding?*) *unmerged-sink*)]
        (vswap! sink into
                (filter #(and (contains? before %) (not (contains? after %))
                              (jtms/in? (reasoning/tms kb) %)))
                moved))
      ;; ...and the spellings a merge retired, for `settle` to withdraw the firings over
      (when (and *sweep?* (not *rebuilding?*))
        (vreset! retired (filterv #(and (contains? after %) (not (contains? before %))) moved))))
    ;; the window is built only when a sink is bound or a listener registered
    (let [sink    *touched-sink*
          in-sink *touched-in-sink*
          fed?    (and (not *rebuilding?*) (feed/wants-region? kb))]
      (when (or sink in-sink fed?)
        (let [tms    (reasoning/tms kb)
              ;; what a defeat can move with no relabel: what the defeats stored before
              ;; the write reach, read then, and what the window's defeats reach now
              snap   (or *belief-before* {})
              [stored removed] (defeat-moves kb @region)
              reach  (into (kb/defeat-reach kb stored removed) (keys snap))
              moved  (-> @extra (into @region) (into reach))
              ;; a spelling superseded when the window opened was not believed, whatever
              ;; its label: `touched-in` records the label, and a handle outside the
              ;; region keeps its label from before; a handle no defeat reached before the
              ;; write was not hidden by one
              open?  #(not (contains? @opened %))
              ;; a handle the reading does not hold that the declared roster alone hides
              ;; now was hidden before: a write that moves a declaration reads its reach
              roster (exc/roster-hidden-own-fn kb)
              hidden #(if (contains? snap %) (get snap %) (boolean (and roster (roster %))))
              was-in (into #{} (remove hidden)
                           (-> @extra-in
                               (into (filter open?) (jtms/touched-in tms))
                               (into (filter #(and (not (contains? @region %)) (jtms/in? tms %)
                                                   (open? %)))
                                     reach)))]
          (when sink    (swap! sink into moved))
          (when in-sink (swap! in-sink into was-in))
          (when fed?    (feed/note-region! kb moved was-in)))))
    (discovery/note-window! kb @extra)
    (jtms/reset-touched! (reasoning/tms kb))
    (swap! (reasoning/settle-stats kb)
           (fn [s] (-> s
                       (assoc :iterations moved :passes passes)
                       (update-in [:histogram moved] (fnil inc 0)))))
    ;; the pass count says whether the KB's exceptions have started to interact
    (trove/log! {:level :debug :id ::settled
                 :data {:passes     passes
                        :iterations moved
                        :moved?     belief-moved?}})
    @retired))

(defn- finish-settle
  "Close one settle: note the pass count for `settle-phases`, run `settle-finish` inside
  the `:finish` span, and file this settle's record.  Every `settle*` return runs
  through here."
  [kb passes moved belief-moved?]
  (phases/note-passes! passes)
  ;; one materialized region for the finish's reads
  (let [region (delay (jtms/touched (reasoning/tms kb)))
        r      (phases/with-phase :finish
                 (settle-finish kb region passes moved belief-moved?))]
    (phases/end-settle!)
    r))

;; ---- one pass -------------------------------------------------------------------
;; A pass reads what it owes (`pass-work`), what the queued exceptions block
;; (`block-work`), and applies both (`apply-pass!`).  It has converged when it queues,
;; blocks and owes nothing.

(def ^:private owed
  "The keys of `pass-work` a pass applies whatever the blocked set does: the datums whose
  belief came back, the facts a departed edge owes a re-join, the refusals a constraint
  no longer convicts, the mints, lifts and merges owed, and the mint placements a
  `genlCx` edge displaced (`:dropped`, applied by `pass-work` itself), so the pass after
  a drop drains what the drop queued."
  [:revived :departed :cfree :mnew :dropped])

(defn- owes-nothing?
  "Is every key of `ks` empty in the pass work `w`?"
  [w ks]
  (every? #(empty? (get w %)) ks))

(defn- pass-work
  "One pass's reads, before anything is blocked or re-chained, as a map: the inherited
  clashes found and placed first (`chain/place-inherited!`); the drained re-check queue
  (`:queued`); every key of `owed`; the targets a removed defeat gave back (`:back`); and
  the mints this pass withdraws (`:wdrawn`, `subsumed-blocks`).  `:region` is the relabelled window, read
  again when a merge this pass owed moved it.  The second argument is the settle's
  state: `:region`, `:reseeded` (what earlier passes seeded), the window `:win` of the
  handles the placement and the defeat re-checks read, and the volatiles of `:asked`."
  [kb {:keys [region reseeded win asked]}]
  ;; the merges a collision member's class moving owes, before the discovery reads the
  ;; pairs they reconcile
  (let [remerge (class-moved-merge-seeds kb region (:merge asked))
        region  (if (seq remerge) (delay (jtms/touched (reasoning/tms kb))) region)
        ;; the `genlCx` moves since the last pass, each handed to every family it moves
        ;; (`special/drain-context-moves!`): their re-checks are queued before the drain
        ;; below, and the placement families read their reach
        moves   (special/drain-context-moves! kb (:genlcx win) *rebuilding?*)
        ;; the inherited clashes found and placed, before the other families place
        inh     (phases/with-phase :discovery (chain/place-inherited! kb region moves))
        ;; the nogoods whose placement can have moved, placed again; a defeat stored
        ;; there posts its target's re-check before the drain
        negs    (into inh (when-not *rebuilding?* (chain/place-nogoods! kb region (:negations win) moves)))
        ;; a defeat stored or relabelled moves its target's belief with no relabel of the
        ;; target, and queues the rules watching it for the drain below
        _       (post-defeat-moves! kb region negs (:defeats win))
        queued  (drain-recheck! kb)
        ;; the targets whose own-context belief a defeat moved with no relabel
        dmoves  (if *rebuilding?* {} (defeat-belief-moves kb (defeat-moves kb (set @region))))
        ;; the datums whose belief came back, and the targets a removed defeat gave back;
        ;; `reseeded` seeds each once per settle, since the window spans the settle.  A
        ;; given-back target is re-chained only when the taxonomy derives from it
        ;; (`tax/derives-from?`): the network kept it IN, so a rule's firings over it stand
        rs      (vec (revived-seeds kb reseeded region))
        back    (into [] (remove reseeded) (:back dmoves))
        revived (into rs (filter #(tax/derives-from? (reasoning/taxonomy kb) %)) back)
        ;; the facts under an edge a firing named that this settle defeated, whose second
        ;; route nothing else re-joins (`departed-seeds`)
        out      (departed-handles kb region)
        departed (departed-seeds kb reseeded out)
        ;; the firings an argument constraint dropped that the content this settle stored
        ;; no longer convicts (`released-constraint-refusals`)
        cfree   (released-constraint-refusals kb region)
        ;; the types a declaration could not mint until its type reached `thing`, the
        ;; merges and lifts a revived mark owes the facts that arrived while it was OUT,
        ;; the twins an `except` that began or stopped hiding an equality or a merge mark
        ;; owes, and the entailments and equalities a defeated genl edge took OUT while a
        ;; second route still licenses them
        mnew    (-> (released-mints kb)
                    (into (released-lifts kb region))
                    (into (revived-mark-seeds kb (into rs back)))
                    (into (except-move-seeds kb))
                    (into (context-move-seeds kb moves))
                    (into (defeated-derivation-seeds kb out))
                    (into remerge)
                    (into negs))
        ;; the relabelled records and the targets a defeat moved, read once for both
        ;; halves of the subsumption question
        rsx     (delay (into [] (keep #(p/get-sentex (:records kb) %))
                             (-> (set @region) (into (:gone dmoves)) (into (:back dmoves)))))
        [was-in believed?] (pass-belief kb dmoves)
        mnew    (-> mnew
                    (into (released-subsumed kb rsx was-in believed? (:release asked)
                                             @(:withdrawn asked)))
                    ;; the interArg and homogeneity entailments a trigger arriving
                    ;; after its facts owes them
                    (into (triggered-seeds kb rsx was-in believed? (:trigger asked))))
        ;; the other direction of the subsumption question: the mints a membership
        ;; arriving this settle has made redundant, whose justifications this pass blocks
        ;; so the sweep collects the records
        wdrawn  (subsumed-blocks kb rsx was-in believed? (:subsumption asked))
        ;; the mint placements a `genlCx` edge arriving this settle left below a more
        ;; general one
        dropped (drop-surplus-placements! kb (:surplus wdrawn))]
    {:region region :queued queued :revived revived :back back :departed departed
     :cfree cfree :mnew mnew :wdrawn wdrawn :dropped dropped}))

(defn- guarded-records
  "The records of the rule firings among `cands`: the firings a guard, or a contrary
  claim of an inherited antecedent, can block."
  [kb cands]
  (let [tms (reasoning/tms kb)]
    (into [] (comp (filter #(integer? (:informant (jtms/justification tms %))))
                   (keep #(p/get-justification (:records kb) %)))
          cands)))

(defn- block-work
  "`w` with what its queued exceptions block: the blocked set as it is (`:was`) and as the
  queue and the withdrawn mints leave it (`:new`), the visibility transitions that owe the
  blanket re-join whether or not anything blocked (`:forced`), the rules an arrival can
  release (`:aggs`), and the refusals the queue released (`:free`, and `:over` for an
  overflowed rule), the targets whose guard defeats moved (`:gmoved`), and the rules a
  separation move re-joins over the types it moved (`:sep`)."
  [kb {:keys [queued wdrawn] :as w}]
  (let [was  (jtms/blocked (reasoning/tms kb))
        cands (recheck/exception-candidates kb queued)
        new  (into (recheck/exception-blocked-set kb queued cands) (:blocked wdrawn))
        ;; the re-decided guarded firings place their guard defeats, before the sweep
        ;; deletes the blocked ones
        gmoved (chain/place-guard-defeats!
                kb (map (fn [j] [j (not (contains? new (:id j)))]) (guarded-records kb cands))
                *sweep?*)
        aggs (rejoin-on-arrival-rules kb queued)
        {free :free over :overflow} (recheck/released-refusals kb queued)]
    (assoc w :was was :new new :gmoved gmoved :forced (vec (forced-recheck-rules queued))
           :aggs aggs :free free :over over :sep (separation-rejoins queued))))

(defn- apply-pass!
  "Block what `w` blocks, sweep what that excepts, and re-chain what the pass owes: the
  released refusals, the revived datums and the mints on one agenda; the departed facts
  silently, as the retraction path's re-join is; and the rules the pass released.
  `asked` takes the mints withdrawn."
  [kb {:keys [was new wdrawn queued free cfree revived mnew departed aggs over sep]}
   asked]
  ;; read before the sweep, which deletes justifications — and so are the re-joins the
  ;; withdrawn mints' firings owe (`special/withdrawn-edge-seeds`)
  (let [released (released-rules kb was new)
        wseeds   (when-not *rebuilding?*
                   (not-empty (special/withdrawn-edge-seeds kb (:withdrawn wdrawn))))]
    (vswap! (:withdrawn asked) into (:withdrawn wdrawn))
    (jtms/set-blocked (reasoning/tms kb) new)
    (sweep-excepted! kb (into #{} (remove was) new))
    ;; the rules the sweep queued; what the re-chains below queue the next pass drains
    ;; and re-decides narrowly
    (let [swept (keys @(reasoning/recheck kb))
          seeds (-> (into [] (mapcat (fn [[rh e]] (chain/release-refusal! kb rh e)))
                          (concat free cfree))
                    (into revived)
                    (into mnew))]
      (when (seq seeds) (rechain-seeds kb seeds))
      ;; the re-join a defeated witness owes, silent where it places nothing
      ;; (`chain/*report-no-placement?*`)
      (when (seq departed)
        (binding [chain/*report-no-placement?* false] (rechain-seeds kb departed)))
      ;; ...and the one a withdrawn mint's firings owe, as silent for the same reason
      (when wseeds
        (binding [chain/*report-no-placement?* false] (rechain-seeds kb wseeds)))
      ;; only the rules this pass released, never every rule it touched: a rule seed
      ;; joins over the whole extent, except a rule a separation move alone queued, which
      ;; joins over the types it moved
      (let [full (into (set released) (concat (blanket-recheck-rules queued) aggs over swept))]
        (binding [chain/*separation-moved* (apply dissoc sep full)]
          (rechain-exception-rules kb (into full (keys sep))))))))

(defn- settle*
  "Relabel, find the inherited clashes, and re-evaluate the `exceptWhen` exceptions the
  triggers queued, to a joint fixpoint of at most `max-settle-passes` passes.  A pass
  that leaves the blocked set as it was (`set-blocked` replaces) and queues, revives and
  releases nothing ends the loop; every other pass counts in `settle-stats`'
  `:iterations`.  Returns the spellings superseded since the last settle
  (`settle-finish`)."
  [kb]
  ;; one `settle-phases` record per settle, filed by `finish-settle` at each return
  (phases/begin-settle!)
  ;; belief moves by a block change or a caller's relabel before the settle, and
  ;; `moved?` is the `belief-moved?` gate over them
  (let [moved? (fn [moved] (or *relabelled-before?* (pos? moved)))]
    ;; reconcile the caches with what a caller relabelled before discovery reads them: a
    ;; revived `genl` or `genlCx` edge can make a pair jointly visible.  The region is
    ;; read once per pass into a delay (docs/nmtms.md, "The runtime view").
    (let [region (delay (jtms/touched (reasoning/tms kb)))
          _      (phases/with-phase :belief
                   (when *relabelled-before?*
                     (special/reconcile-belief-change kb @region)
                     (tax/restore-depths (reasoning/taxonomy kb))))
          ;; the records asked the subsumption question this settle, in each direction
          ;; (`subsumed-blocks`, `released-subsumed`), the merges asked, the mints it
          ;; withdrew, and the records asked what they trigger (`triggered-seeds`)
          asked  {:subsumption (volatile! #{}) :release (volatile! #{})
                  :merge (volatile! #{}) :withdrawn (volatile! #{}) :trigger (volatile! #{})}
          ;; the window handles `chain/place-nogoods!` has read, those whose defeats'
          ;; watchers the settle posted, and the `genlCx` supporter labels the context-move
          ;; drain read, across the passes
          win    {:negations (volatile! #{}) :defeats (volatile! #{}) :genlcx (volatile! #{})}]
      (loop [pass 1, moved 0, reseeded #{}, region region]
        (let [w (pass-work kb {:region region :reseeded reseeded :win win :asked asked})]
          (if (and (empty? (:queued w)) (empty? (:blocked (:wdrawn w))) (owes-nothing? w owed))
            (finish-settle kb pass moved (moved? moved))
            (let [w (block-work kb w)]
              (if (and (= (:new w) (:was w))
                       (owes-nothing? w (into owed [:forced :aggs :free :over :gmoved :sep])))
                (finish-settle kb pass moved (moved? moved))   ; unproductive pass: converged
                (do (apply-pass! kb w asked)
                    (if (< pass max-settle-passes)
                      (recur (inc pass) (inc moved)
                             (-> reseeded (into (:revived w)) (into (:back w)) (into (:departed w)))
                             (delay (jtms/touched (reasoning/tms kb))))
                      (do (trove/log! {:level :warn :id ::exception-fixpoint
                                       :msg  (str "exception re-check did not converge in "
                                                  max-settle-passes " passes; giving up")
                                       :data {:passes pass :blocked (count (:new w))}})
                          (finish-settle kb pass (inc moved) (moved? (inc moved))))))))))))))

(def ^:private max-unmerge-rounds
  "How many times `settle` re-seeds an un-merge and settles again before it logs
  `::unmerge-fixpoint` and stops (docs/nmtms.md, \"The other half: a spelling an un-merge
  gives back\")."
  8)

(defn- merge-support
  "The handles the merges superseding `retired` rest on: each restatement of a spelling in
  `retired` (a `rewriteOf` or `except` justification whose first antecedent it is) names
  its merges as the other antecedents, and this is those merges with their justification
  ancestors."
  [tms retired]
  (loop [todo (into []
                    (comp (mapcat (fn [d] (keep #(jtms/justification tms %) (jtms/dependents tms d))))
                          (filter #(#{'rewriteOf 'except} (:informant %)))
                          (mapcat #(rest (:antecedents %))))
                    retired)
         seen #{}]
    (if-let [h (peek todo)]
      (if (contains? seen h)
        (recur (pop todo) seen)
        (recur (into (pop todo)
                     (mapcat #(some-> (jtms/justification tms %) jtms/rests-on))
                     (jtms/supports tms h))
               (conj seen h)))
      seen)))

(defn- withdraw-retired-firings!
  "Drop each rule firing that names a spelling in `retired` as an antecedent or as its
  rule, and delete what the drop sweeps (`apply-removals!`).  A superseded spelling
  fires nothing (`chain/process-datum`), so the KB then holds the firings it holds when
  the merge arrived first.  A firing the superseding merge rests on (`merge-support`)
  stays, since no order makes that merge without it.  A dropped firing that climbed a
  retired `genl` edge is drawn again over the edge's twin (`special/withdrawn-edge-seeds`,
  read before the drop).  Returns true when a firing was dropped."
  [kb retired]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        held (delay (merge-support tms retired))
        jids (into (sorted-set)
                   (comp (mapcat #(jtms/dependents tms %))
                         (filter #(let [j (jtms/justification tms %)]
                                    (and (integer? (:informant j))
                                         (not (contains? @held (:consequence j)))))))
                   retired)
        wseeds (when (seq jids) (not-empty (special/withdrawn-edge-seeds kb retired)))]
    (doseq [jid jids
            ;; an earlier drop can have swept this one with its antecedent
            :when (jtms/justification tms jid)]
      (let [rm (jtms/drop-justification! tms jid)]
        (p/delete-justification! recs jid)
        (apply-removals! kb rm)))
    (when wseeds
      (binding [chain/*report-no-placement?* false] (rechain-seeds kb wseeds)))
    (boolean (seq jids))))

(defn- respelled-seeds
  "Drain the `:respell` queue, the predicates whose permuting marks moved in the settle
  just run, the `[:row h]` rows a write stored while their readers disagree on a mark,
  and the `[:reifiable f]` functions whose reifiable mark moved, through
  `chain/reconcile-spellings!` and `chain/reconcile-reified!`, and return the handles they
  made.  A rebuild clears the queue and respells nothing, since a recovered store was
  spelled when written.  With `*sweep?*` off the queue is kept, so `core/preview`'s
  rollback settle drains it against the restored KB and the handles stay the same."
  [kb]
  (let [q (reasoning/respell kb)]
    (when (seq @q)
      (cond
        *rebuilding?*    (do (reset! q #{}) nil)
        (not *sweep?*)   nil
        :else            (let [moved @q
                               tagged (fn [k] (into [] (comp (filter #(and (vector? %) (= k (first %))))
                                                             (map second))
                                                    moved))
                               fns    (tagged :reifiable)]
                           (reset! q #{})
                           (into (chain/reconcile-spellings! kb (remove vector? moved) (tagged :row))
                                 (when (seq fns) (chain/reconcile-reified! kb fns))))))))

(defn- hold-belief!
  "Hold the belief `kb` holds now for every other thread until `publish-belief!`, and
  return the hold, or nil when nothing is held: on a rebuild, and when a hold is open on
  the network already.  The network (`jtms/hold!`) and the candidate index, whose
  inherited clashes the settle re-finds (`observe/hold-atom!`), are held before
  `observe/open-hold!` registers the hold, so a reader switches to both at once (docs/nmtms.md, \"Two representations of the same
  network\")."
  [kb]
  (when-not *rebuilding?*
    (let [tms (reasoning/tms kb)
          sd  (reasoning/nogood-candidates kb)
          h   (observe/new-hold)]
      (when (jtms/hold! tms h)
        (observe/hold-atom! sd h)
        (observe/open-hold! h)
        [tms h sd]))))

(defn- publish-belief!
  "Publish what the settle decided under `held` (`hold-belief!`'s answer): close the hold,
  so every reader reads the belief the settle reached in one step, then drop what the
  network and the candidate index kept for it."
  [held]
  (when-let [[tms h sd] held]
    (observe/close-hold! h)
    (jtms/release! tms h)
    (observe/release-atom! sd)))

(defn settle
  "Settle belief (`settle*`) under a belief hold, re-settle while an un-merge gives
  spellings back or a merge retires spellings that fired (at most `max-unmerge-rounds`
  rounds), then deliver the moved region to the feed listeners, outside the relabel so a
  listener's write starts a fresh settle.  Returns nil.  The rounds: docs/nmtms.md,
  \"The other half: a spelling an un-merge gives back\"."
  [kb]
  (let [held (hold-belief! kb)]
    ;; the removals a settle makes, whose defeats moved their targets' belief with no
    ;; label to read it off (`defeat-moves`), and the belief a report diffs against
    (binding [integrate/*removed-sink* (or integrate/*removed-sink*
                                           (integrate/removal-sink (exc/placed-reads? kb)))
              *belief-before*          (reading-before kb nil)]
      (try
        (loop [round 1, dropped? false]
          (let [seeds   (volatile! #{})
                ;; a dropped firing relabelled its region outside a settle, so the next
                ;; settle reconciles the caches with it before discovery reads them
                retired (binding [*unmerged-sink*       seeds
                                  *relabelled-before?* (or *relabelled-before?* dropped?)]
                          (settle* kb))
                back    (into (vec @seeds) (respelled-seeds kb))
                dropped (withdraw-retired-firings! kb retired)]
            (cond
              (and (empty? back) (not dropped)) nil
              (>= round max-unmerge-rounds)
              (trove/log! {:level :warn :id ::unmerge-fixpoint
                           :msg  (str "un-merge re-seeding did not converge in "
                                      max-unmerge-rounds " rounds; giving up")
                           :data {:rounds round :seeds (count back)}})
              ;; a given-back spelling is also a fact a descended equality is drawn
              ;; from, and the merge it rests on may have lost its route while the
              ;; spelling was superseded (`lost-derivation-seeds`)
              :else (do (when (seq back)
                          (rechain-seeds
                           kb (into back (lost-derivation-seeds
                                          kb (special/lost-descended-derivations kb back false)))))
                        (recur (inc round) dropped)))))
        (finally
          (publish-belief! held))))
    (feed/deliver! kb)
    ;; a settle inside a deferred batch reported against the batch's reading; the next
    ;; one diffs against the belief it published
    (when (and *batch-reading* wiring/*defer-settle?* (report-wanted? kb))
      (vreset! *batch-reading* (belief-before kb nil)))
    nil))
