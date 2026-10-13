;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.recovery
  "Build the in-memory JTMS and taxonomy for the persistent stores — the store-to-belief
  `recover`, which installs a reasoning image (`vaelii.impl.reasoning-image`) or rebuilds from
  the records and writes one.

  It sits just below `vaelii.core`, above `settle`, so the two callers that recover a store
  both reach it downward and neither reaches up: `vaelii.core` exposes it as the public
  `recover`, and `vaelii.impl.io.import` recovers the records a dump just landed
  (docs/namespaces.md, \"The layering\").  `recover` orchestrates the layers below —
  `rebuild-tms` over the JTMS, `special/rebuild-taxonomy`, the roster rebuilds in `kb`, and
  the closing `settle` — so the top of that orchestration lives here rather than inside any
  one of them.  The contract `recover` holds to is on `vaelii.core/recover`; docs/taxonomy.md
  and docs/nmtms.md carry the mechanism."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as reasoning-image]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- stopping a background rebuild --------------------------------------------

(def ^:dynamic ^:private *abandon?*
  "A thunk the belief rebuild binds, answering true once the rebuild has been asked to
  stop, or nil outside a rebuild.  `check-abandoned!` reads it."
  nil)

(defn- check-abandoned!
  "Throw an `ex-info` carrying `::abandoned` when the rebuild running on this thread has
  been asked to stop.  Called through the network replay and before the closing settle.
  A background rebuild writes no record (`start-rebuild!`), so one abandoned at any point
  leaves the stores as it found them."
  []
  (when-let [a *abandon?*]
    (when (a)
      ;; a key rather than a `:type`: the throw never leaves `start-rebuild!`, so it is no
      ;; word of the refusal vocabulary a caller catches on
      (throw (ex-info "belief rebuild abandoned" {::abandoned true})))))

(defn abandoning?
  "Has the belief rebuild running on this thread been asked to stop?  False outside a
  rebuild.  A `*before-install*` function reads it."
  []
  (boolean (when-let [a *abandon?*] (a))))

(def ^:dynamic *before-install*
  "A function of the rebuilt KB, called on the rebuild thread before the rebuilt belief
  replaces the installed image's, or nil.  Nil everywhere but a test, which binds it
  around `open-kb` to hold the rebuild while it reads the KB the image answers for."
  nil)

;; ---- progress -----------------------------------------------------------------

(def ^:private recover-steps
  "The steps of a recover from the records, in the order `recover-from-records` runs
  them, each with the phrase a progress line names it by."
  [[:network  "rebuilding the belief network"]
   [:taxonomy "replaying the taxonomy"]
   [:depths   "repairing the taxonomy depths"]
   [:rosters  "rebuilding the derived rosters"]
   [:settle   "settling belief"]
   [:refusals "re-recording refusals"]])

(def ^:private rebuild-steps
  "The steps of a belief rebuild behind an installed image: the recover's, then the two
  `rebuild-and-install!` adds."
  (into recover-steps [[:install "installing the rebuilt belief"]
                       [:image   "writing the reasoning image"]]))

(def ^:private step-index
  (into {} (map-indexed (fn [i [k _]] [k i])) rebuild-steps))

(def ^:private step-label (into {} rebuild-steps))

(def ^:private logged-recover-size
  "The sentex count from which a recover logs each step at `:info` rather than `:debug`.
  A recover over a million sentexes runs for minutes."
  1000000)

(def ^:dynamic ^:private *on-step*
  "A function of a step key from `rebuild-steps`, called as that step begins, or nil.  The
  belief rebuild binds it (`rebuild-reporter`); a recover with none bound logs its steps."
  nil)

(defn- minutes [ms] (/ (double ms) 60000.0))

(defn- step-marker
  "A function that marks the start of a recover step when given its key, and the end of
  the last step when given nil.  Each start goes to `*on-step*`, or is logged when none is
  bound: at `:info` over a store of `logged-recover-size` sentexes or more, else at
  `:debug`.  The end files the step durations in `kb`'s `:unrecovered` atom as
  `:last-recover` `{:ms total :steps {key ms}}`, which the reasoning image's stamp carries."
  [kb]
  (let [on-step *on-step*
        level   (when-not on-step
                  (if (>= (long (cap/count-sentexes (:records kb))) (long logged-recover-size))
                    :info
                    :debug))
        t0      (System/nanoTime)
        marks   (volatile! [])
        ms      (fn [a b] (quot (- (long b) (long a)) 1000000))]
    (fn [k]
      (let [now (System/nanoTime)]
        (vswap! marks conj [k now])
        (cond
          (nil? k)
          (swap! (:unrecovered kb) assoc :last-recover
                 {:ms    (ms t0 now)
                  :steps (into {} (map (fn [[[k a] [_ b]]] [k (ms a b)])) (partition 2 1 @marks))})

          on-step (on-step k)

          :else
          (trove/log! {:level level :id ::recover-step
                       :msg (format "recover of %s: step %d/%d, %s (%.1f min in)"
                                    (or (:snapshot-dir kb) "an in-memory KB")
                                    (inc (long (step-index k))) (count recover-steps)
                                    (step-label k) (minutes (ms t0 now)))}))))))

(defn- rebuild-reporter
  "The `*on-step*` a belief rebuild of `kb` binds: file the step under `:rebuild` in `kb`'s
  `:unrecovered` atom, where `rebuild-progress` reads it, and log it at `:info`."
  [kb]
  (fn [k]
    (let [now (System/currentTimeMillis)
          r   (:rebuild (swap! (:unrecovered kb) update :rebuild assoc
                               :key k :step-started-at now))
          exp (get-in r [:image :recover :ms])]
      (trove/log! {:level :info :id ::rebuild-step
                   :msg (format "belief rebuild of %s: step %d/%d, %s (%.1f min in%s)"
                                (:snapshot-dir kb) (inc (long (step-index k)))
                                (count rebuild-steps) (step-label k)
                                (minutes (- now (long (:started-at r))))
                                (if exp
                                  (format "; the recover the image records took %.1f min"
                                          (minutes exp))
                                  ""))}))))

(defn rebuild-progress
  "Where the belief rebuild behind `kb`'s installed image has got to, or nil when none runs.
  A rebuild that threw is reported until a `recover` replaces it, with `:failed` added and
  its clock stopped at the throw.

    :step :of :key :label    the step running now, 1-based, of `rebuild-steps`; step 0 is
                             the moment between the open and the first step.  After a
                             throw, the step the rebuild was in
    :failed                  after a throw: `{:at :class :message}`, when (epoch ms), the
                             exception's class name, and its message
    :started-at :elapsed-ms  when the rebuild began (epoch ms), and how long ago, or how
                             long it ran before the throw
    :image                   the installed image's `:source` digest, its `:written-at`, and
                             its `:recover`, the step timings of the recover it was written
                             after, when the image records them
    :source                  the running build's source digest
    :expected-ms :fraction   from the image's `:recover`, when present: that recover's
                             total, and the share of it the steps done so far took there"
  [kb]
  (let [u @(:unrecovered kb)]
    (when-let [r (and (:stale-belief u) (:rebuild u))]
      (let [now      (long (or (get-in r [:failed :at]) (System/currentTimeMillis)))
            k        (:key r)
            i        (when k (long (step-index k)))
            expected (get-in r [:image :recover])
            fraction (when-let [steps (not-empty (:steps expected))]
                       (let [total   (reduce + 0 (vals steps))
                             before  (reduce + 0 (keep #(get steps (first %))
                                                       (take (or i 0) rebuild-steps)))
                             in-step (min (long (get steps k 0))
                                          (- now (long (or (:step-started-at r) now))))]
                         (when (pos? (long total))
                           (min 1.0 (/ (double (+ (long before) (if i in-step 0)))
                                       (double total))))))]
        (cond-> (-> r
                    (dissoc :step-started-at)
                    (assoc :step (if i (inc (long i)) 0) :of (count rebuild-steps)
                           :label (if k (step-label k) "starting")
                           :elapsed-ms (- now (long (:started-at r)))))
          expected (assoc :expected-ms (:ms expected))
          fraction (assoc :fraction fraction))))))

(defn- recovered-supersessions
  "Every stored sentex the rebuilt equality closure displaces, as `refresh-supersessions`
  wants it.

  Recovery cannot read supersession back — it is derived from the closure, and recovery
  lands with the map empty (a fresh network holds none), exactly as it lands unblocked.
  Left that way, *both* spellings of every merged fact would be believed, which is a
  worse state than the merge simply being forgotten.  So the displaced sentexes are
  nominated once here and `supersession-map` filters them down to the ones whose twin
  is genuinely stored.

  Two sources, matching the two ways `rewrite-term` displaces a sentence: a **symbol
  merge** (walk the equality classes for every member's sentexes) and a **schematic
  rewrite** (a stored sentex the rule's LHS head reaches whose normal form differs).
  `supersession-map` re-derives the actual displacement — `rewrite-term` normalizes both
  — so this only has to name candidates.

  It names them by **class membership alone**, without asking whether the global
  election displaces the term.  Displacement is the *reader's*, and the global answer is
  not a superset of the scoped ones: a term can be the head of its whole class and still
  be retired inside a context whose visible edges elect someone else, when the
  `rewriteOf` that made it preferred is one that context cannot see.  Filtering here
  on the global read would drop exactly those, and recovery would come back believing
  both spellings."
  [kb]
  (concat
   (for [[a _] (tax/equality-edges (reasoning/taxonomy kb))
         t     (tax/equiv-class (reasoning/taxonomy kb) a)
         sx    (kb/find-sentexes kb t)
         :when (kb/rewritable-sentex? kb sx)]
     [(:id sx) {}])
   (for [{:keys [lhs]} (tax/rewrite-rules (reasoning/taxonomy kb))
         sx (kb/find-sentexes kb (first lhs))
         :when (kb/rewritable-sentex? kb sx)]
     [(:id sx) {}])))

(defn- rebuild-tms
  "Rebuild the network from the store: a node per stored sentex, a premise per rostered
  handle, and a justification per stored justification.  Belief is the composition of the
  region relabels the adds run, not a separate whole-graph pass.

  **No whole-graph relabel closes this.**  `add-justification` relabels its consequence's
  affected region as it lands, and a region relabel over the affected closure is equal to a
  global one (`jtms/relabel-region*`); premises are marked before any justification, so each
  add already reads its antecedents' final belief.  The region relabels therefore compose to
  the fixpoint a whole-graph `jtms/relabel` computes, and a global pass on top of them only
  recomputes what is already settled — measured at a third of `rebuild-tms` on a disk corpus
  (`scale-100m.md`, the recover decomposition's step 4).

  **And no reset of blocking or supersession either — recovery lands unblocked because it
  starts fresh.**  A network opened for recovery is empty, blocked and superseded sets
  included, so the region relabels above already label unblocked.  Neither is stored
  (docs/nmtms.md), so a rebuild cannot read either back; it need not clear them because the
  two are re-derived **wholesale** rather than merged — `recheck-every-exception` queues
  every exception-bearing rule and the settle *replaces* the blocked set (`jtms/set-blocked`),
  and `refresh-supersessions` replaces the supersession map — so not even a `core/reindex`
  over a live network can carry a stale one past the settle.

  **A justification naming a sentex this store does not hold is left out**, and this is
  the one path that can meet one.  Everywhere else a justification is built by a firing,
  whose antecedents are records the caller has in hand; here they are numbers off a
  store, and a store can hold a justification whose records are gone — `delete-sentex!`
  is on the protocol, and another dialect's loader is under no obligation to be
  consistent.  `add-justification` does not refuse one: the reference representation
  grows a phantom node for the missing datum and the dense one is not specified there
  (`vaelii.impl.dense-jtms`), and a justification *concluding* the phantom makes it IN —
  so the KB comes back believing a handle it cannot show anyone, and everything derived
  from it.  Skipped and counted instead, which is the policy `io.import` takes at the
  other end of the same store.

  A rule-handle informant is checked with the antecedents (`jtms/rests-on`): the network
  treats it as an implicit antecedent and lists the justification under its node, so a
  justification whose rule is gone is left out as one whose fact is gone would be."
  [kb]
  (let [tms     (reasoning/tms kb)
        rec     (:records kb)
        ;; `sentex-ids` is *the live handle set* by the RecordStore contract, and
        ;; `premise-ids` a subset of it — every backend's `mark-premise` guards on the
        ;; record existing before rostering the handle (memory.clj, disk record-store).
        ;; So neither loop re-reads the whole record to prove it is there: the node loop
        ;; trusts the set, and the premise loop tests membership in it (O(1), no fetch)
        ;; rather than fetching a frame per premise only to check for nil.  A fetch here
        ;; costs ~1 s of a 313k `recover` on disk and hours over a network store, all of
        ;; it to re-derive a fact the enumerator already answered.  A **justification** is
        ;; the one thing a store can hold over a sentex it does not (a `delete-sentex!`, a
        ;; foreign loader under no consistency obligation) — that loop keeps `stored?`.
        live    (p/sentex-ids rec)
        ;; The roster is checked first and the fetch is the fallback, not the test: a
        ;; store rosters a handle only once the record is stored, so membership in `live`
        ;; **is** storedness and the fetch below it can only confirm what the set already
        ;; said.  It stays for the handle the set does not name — the case this loop keeps
        ;; `stored?` for at all — where nil is the answer and a fetch is the only way to
        ;; it.  On a store whose fetch is a round trip that ordering is the difference
        ;; between one read of the roster and a trip per antecedent of every justification.
        stored? (fn [h] (or (not (integer? h))
                            (contains? live h)
                            (some? (p/get-sentex rec h))))
        skipped (volatile! 0)]
    ;; The replay is `settle-phases`' `:belief` centre for a `recover`: `add-justification`
    ;; relabels each consequence's region as it lands, and the region relabels compose to
    ;; the fixpoint (no closing whole-graph pass and no chaining), so this is the belief
    ;; work a partition-relabel candidate would divide.  Off a timing run, one `nil?` check.
    (phases/with-phase :belief
      (doseq [id live]
        (jtms/ensure-node tms id 0))
      (doseq [id (p/premise-ids rec) :when (contains? live id)]
        (jtms/add-premise tms id (p/premise-strength rec id)))
      ;; Every stored justification is fetched here, so a store that can warm many at one
      ;; cost is told a chunk ahead — ungated, as in `reindex`: this walk reads every handle
      ;; it is given.  Nil for a store without the capability, and then this is
      ;; `(p/justification-ids rec)`.
      (doseq [id (cap/hinting (cap/justification-prefetcher rec) cap/recovery-hint-chunk
                              (p/justification-ids rec))
              :let [d (p/get-justification rec id)] :when d]
        (check-abandoned!)
        (if (and (stored? (:consequence d)) (every? stored? (jtms/rests-on d)))
          (jtms/add-justification tms d)
          (vswap! skipped inc))))
    (when (pos? (long @skipped))
      (trove/log! {:level :warn :id ::justifications-unrooted
                   :msg  (str @skipped " stored justifications name a sentex this store"
                              " does not hold and are left out of the network")
                   :data {:skipped @skipped}}))
    tms))

(defn- recover-from-records
  "Rebuild the in-memory JTMS and taxonomy from the persistent stores — what `recover`
  runs whenever it installs no reasoning image.

  What the taxonomy ends up holding is a **composition**, and the contract is the whole
  of it rather than either half.  The JTMS is rebuilt first, so there is belief to read.
  The taxonomy then installs the believed side of every key the index's supporter
  families hold (`special/rebuild-taxonomy`), which reads labels and no record but the
  equality declarations; the supporters, believed or not, stay in the index, so a
  supporter coming back IN later revives its entry (docs/taxonomy.md).  Belief is settled
  last."
  [kb]
  ;; The taxonomy's closures are one weighted LRU (`tax/closure-memo-limit`), so a cold
  ;; rebuild that reads the corpus from every context at once keeps its hot closures —
  ;; the upper types every walk passes — and evicts the cold ones, rather than holding
  ;; every closure it walks, which on a large import is a set per type and fills the heap.
  (let [step! (step-marker kb)]
    (step! :network)
    (rebuild-tms kb)
    (check-abandoned!)
    ;; The rebuild installs every believed `genl` / `genlCx` edge, so it is a bulk load
    ;; and pays what one pays: repairing the depth potential per edge costs that edge's
    ;; descendants.  Defer it and repair once, exactly as `with-deferred-settle` does —
    ;; and repair *here* rather than leaning on the settle below, so the intervening
    ;; rebuilds never read a loose relation.  The reconcile shares that one repair, which
    ;; is why it sits inside the same deferral: dropping an edge can dissolve a component.
    ;; `*defer-cycle-scc?*` extends the same deferral to a cycle-closing edge, which
    ;; `activate` otherwise repairs eagerly per edge (O(V+E) each) for a `placement-rep`
    ;; reader no recovery step runs before `restore-depths`; the single repair below
    ;; computes `:scc` for the whole replay instead (see the var).
    (binding [tax/*defer-depths?*    true
              tax/*defer-cycle-scc?* true]
      (step! :taxonomy)
      (special/rebuild-taxonomy kb)
      ;; The rebuild installed the roster properties, and the network replayed above holds
      ;; every premise at the strength it was written at: the forced memberships the
      ;; roster gives the stored content go in now, before anything reads belief
      ;; (docs/nmtms.md, "The forced-monotonic roster").
      (checks/force-roster! kb)
      ;; Now reconcile the caches with belief again, and **unconditionally**: the forced
      ;; memberships just written move labels, and no settle event records them.  The
      ;; region-scoped arm of `refresh-beliefs` reconciles what a settle moved; recovery
      ;; is the caller holding no region that the `nil` arm exists for, and it costs one
      ;; belief lookup per stored supporter — what the rebuild above just paid.
      ;; Before the settle rather than after it, so everything the settle reads — nogoods,
      ;; placement, exception queries — reads a taxonomy that already agrees with belief;
      ;; the settle's own reconcile then keeps the two together across whatever it moves.
      (tax/refresh-beliefs (reasoning/taxonomy kb) (partial jtms/in? (reasoning/tms kb))))
    (step! :depths)
    (tax/restore-depths (reasoning/taxonomy kb))
    ;; Nothing about an exception is stored, so blocking cannot be read back: recovery lands
    ;; unblocked (a fresh network holds no blocks, and the settle below re-derives them) and the
    ;; window in between believes an excepted conclusion.  Queue every exception-bearing rule so the settle
    ;; below re-evaluates and withdraws them.  This is recovery, not a store mutation,
    ;; so it is a deliberate explicit trigger rather than the choke-point extension point: no
    ;; sentence arrived or left — the whole in-memory blocking state did.
    (step! :rosters)
    (special/recheck-every-exception kb)
    ;; ...and the same for supersession, which is derived from the equality closure and
    ;; is likewise not readable back from the store.  Seeded before the settle, since
    ;; `refresh-supersessions` only re-examines the entries it already holds.
    (special/refresh-supersessions kb (recovered-supersessions kb) nil)
    ;; ...and the candidates of the nogood families the settle places, which no store
    ;; holds either (`vaelii.impl.decide`)
    (decide/rebuild-candidates! kb)
    ;; The first cache reconcile ran before the visibility roster existed, so it
    ;; could narrow only against JTMS belief. Re-run through the common transition
    ;; boundary now that recovery can also answer which declarations are excepted.
    (special/reconcile-belief-change kb)
    ;; the last point a background rebuild can stop at before the settle below, which can
    ;; place a conclusion; a background rebuild's records refuse that write
    (check-abandoned!)
    ;; ...and the settle that finishes the rebuild is told it *is* one, so the passes that
    ;; report or re-derive what a change moved stay out of it: a restore changes nothing
    ;; (`settle/*rebuilding?*`).
    (binding [settle/*rebuilding?* true]
      ;; `rebuild-tms` made a node for every stored sentex and nothing has cleared the
      ;; touched set since, so this settle's region is the whole store and its retroactive
      ;; sweeps add no candidate (`discovery/*whole-store-region?*`).  The re-fire's settle
      ;; below is not bound: its region is only what the re-fire moved.
      (step! :settle)
      (binding [discovery/*whole-store-region?* true]
        (settle/settle kb))
      ;; The **refusal** record is the other in-memory state no store holds: a firing
      ;; refused at derive time left no justification, so replaying the stored ones cannot
      ;; put it back, and a KB restarted with refusals standing would answer a later
      ;; release differently from one that never restarted.  Re-firing the rules that can
      ;; refuse re-records what they refuse, and it runs after the settle above because a
      ;; refusal is a claim about what the KB *believes*.  A re-fire that placed something
      ;; the narrowed re-chain had not owes a second settle.
      (step! :refusals)
      (let [{:keys [derived]} (chain/rerecord-refusals! kb)]
        ;; ...and the lifts and declarations still waiting on an absent type,
        ;; which that re-fire does not reach
        (special/rebuild-pending! kb)
        (when (pos? (long (or derived 0))) (settle/settle kb))))
    ;; the settle above places the inherited clashes and stands aside from the other
    ;; families, and a store written with no belief holds none placed: the nogoods the
    ;; rebuilt index queued are placed where they stand (`chain/place-nogoods!`)
    (when (chain/placement-queued? kb) (settle/settle kb))
    (step! nil)
    kb))

;; ---- rebuilding belief behind an installed image ------------------------------

(defn- install-rebuilt!
  "Replace `kb`'s belief with the belief the KB `from` rebuilt, by one `vreset!` of `kb`'s
  `:reasoning` volatile, and return what the replacement moved (`dense/moved-between`).  The
  rebuilt taxonomy's visibility callbacks already read the rebuilt belief
  (`kb/rebuild-kb`), so the value is installed as the rebuild left it.  The install then
  retires `:install-pending`, which `kb/read-view` reads, so a public read begun before
  the `vreset!` reads the installed belief to its end."
  [kb from]
  (let [installed (reasoning/of kb)
        rebuilt   (reasoning/of from)]
    (vreset! (:reasoning kb) rebuilt)
    (swap! (:unrecovered kb) dissoc :install-pending)
    (observe/note-change)
    (dense/moved-between (:tms installed) (:tms rebuilt))))

(defn- deliver-moved!
  "Tell `kb`'s change-feed listeners what an installed rebuild moved, as a settle tells
  them what it relabelled."
  [kb {:keys [moved was-in]}]
  (when (feed/wants-region? kb)
    (feed/note-region! kb (into #{} (map long) moved) (into #{} (map long) was-in))
    (feed/deliver! kb)))

(defn- rebuild-write-refusal
  "The refusal a background rebuild's record store throws for the write `op`."
  [op]
  (let [msg (str "the belief rebuild on its own thread writes no record, and this build"
                 " places one the image's records lack (" op " refused).  (recover kb)"
                 " rebuilds belief on the calling thread, which writes it")]
    (ex-info msg {:type :unrecovered-kb :hazards [:stale-belief] :operation op
                  :repair 'recover :message msg})))

(defn- read-only-records
  "`records` refusing every write with `rebuild-write-refusal`."
  [records]
  (frozen/frozen-records records rebuild-write-refusal))

(defn- rebuild-and-install!
  "Recover `kb`'s belief on a second KB over its stores (`kb/rebuild-kb`, its record store
  passed through `wrap-records`), install it into `kb` (`install-rebuilt!`), write `kb`'s
  image, and retire the `:stale-belief` hazard.  The rebuilt KB holds no `:snapshot-dir`
  (`kb/rebuild-own`), so its settles offer the index image no refresh.  Returns the source digest the image
  carries.  Throws an `ex-info` carrying `::abandoned` when the rebuild is asked to stop
  before its install."
  [kb wrap-records]
  (let [rebuilt (kb/rebuild-kb kb wrap-records)]
    (recover-from-records rebuilt)
    (when-let [f *before-install*] (f rebuilt))
    (check-abandoned!)
    (when-let [f *on-step*] (f :install))
    (let [moved  (install-rebuilt! kb rebuilt)
          ;; the rebuilt KB's step timings, for the image's stamp
          _      (swap! (:unrecovered kb) assoc :last-recover
                        (:last-recover @(:unrecovered rebuilt)))
          _      (when-let [f *on-step*] (f :image))
          ;; the image before the hazard is retired, so no write lands while it is written
          source (or (:source (reasoning-image/save! kb)) (reasoning-image/source-digest))]
      (kb/note-hazards! kb {:no-belief false :stale-belief false})
      (deliver-moved! kb moved)
      source)))

(defn- rebuild-failed!
  "Log the throw that ended `kb`'s belief rebuild, and file it under `:rebuild` as
  `:failed`, where `rebuild-progress` reports it: a failed rebuild leaves `:stale-belief`
  standing, and without the record a caller polling progress reads the failure as no
  rebuild at all.  The log comes first, so a caller that reads `:failed` reads it after
  the log line is written."
  [kb ^Throwable t]
  (trove/log! {:level :error :id ::belief-rebuild-failed :error t
               :msg (str "the belief rebuild for " (:snapshot-dir kb) " failed ("
                         (.getMessage t) "). The KB answers from the image an earlier build"
                         " wrote and refuses writes; (recover kb) rebuilds belief under this"
                         " build in place.")})
  (swap! (:unrecovered kb) update :rebuild assoc
         :failed {:at      (System/currentTimeMillis)
                  :class   (.getName (class t))
                  :message (.getMessage t)}))

(defn- start-rebuild!
  "Rebuild belief under this build for `kb`, whose open installed an image written under
  other engine source (`reasoning-image/install!`'s `:stale`), on a daemon thread, and return
  nil.  Until the rebuilt belief is installed, `kb` answers from the image and refuses writes
  (`:stale-belief`).  `kb/stop-rebuild!` and the directory close both stop the rebuild,
  and return once it has stopped.  The rebuild KB's records refuse every write
  (`read-only-records`), so the rebuild writes no record and no index posting from this
  thread.  A rebuild whose belief places a conclusion, and a rebuild that throws for any
  other reason, leave the image answering and writes refused, and file the throw as
  `:failed` under `:rebuild` (`rebuild-failed!`); `recover` then rebuilds on the calling
  thread.

  `image` is the installed image's `:source`, `:written-at` and `:recover`, and `source`
  the running build's digest; both are filed under `:rebuild` for `rebuild-progress`, and
  each step is logged at `:info` as it begins (`rebuild-reporter`)."
  [kb image source-now]
  (let [dir    (:snapshot-dir kb)
        cancel (atom false)
        done   (promise)
        source (atom nil)
        stop!  (fn [] (reset! cancel true) @done nil)
        run    (bound-fn []
                 (let [t0 (System/nanoTime)]
                   (try
                     (binding [*abandon?* #(deref cancel)
                               *on-step*  (rebuild-reporter kb)]
                       (reset! source (rebuild-and-install! kb read-only-records)))
                     (trove/log! {:level :info :id ::belief-rebuilt
                                  :msg (format (str "rebuilt the belief for %s under this build in"
                                                    " %.1f min and installed it; writes are accepted")
                                               dir (/ (- (System/nanoTime) t0) 6e10))})
                     (catch clojure.lang.ExceptionInfo e
                       (if (::abandoned (ex-data e))
                         (trove/log! {:level :info :id ::belief-rebuild-stopped
                                      :msg (str "the belief rebuild for " dir " stopped before"
                                                " its install; the next open recovers")})
                         (rebuild-failed! kb e)))
                     (catch Throwable t (rebuild-failed! kb t))
                     (finally
                       ;; a failed rebuild keeps its `:rebuild` entry, `:failed` included,
                       ;; until a `recover` replaces it
                       (swap! (:unrecovered kb)
                              #(cond-> (dissoc % :stop-rebuild)
                                 (not (get-in % [:rebuild :failed])) (dissoc :rebuild)))
                       (deliver done true)))))]
    ;; `:install-pending` is filed before the open returns, so every public read of the
    ;; KB runs against a view of one belief (`kb/read-view`); `install-rebuilt!` retires
    ;; it, on this thread or on the one a `recover` runs the rebuild on.
    (kb/note-hazards! kb {:no-belief false :stale-belief true :stop-rebuild stop!
                          :install-pending true
                          :rebuild {:started-at (System/currentTimeMillis)
                                    :image      image
                                    :source     source-now}})
    (reasoning-image/register-rebuild-close! kb stop! #(deref source))
    (doto (Thread. ^Runnable run (str "vaelii-belief-rebuild " dir))
      (.setDaemon true)
      (.start))
    nil))

(defn recover
  "The implementation of `vaelii.core/recover` — build the in-memory JTMS and taxonomy for
  the persistent stores.  The public contract, and when a caller runs it, are on
  `vaelii.core/recover`; the mechanism is here, in `vaelii.impl.reasoning-image` and in
  docs/taxonomy.md.

  A `:disk-snapshot` KB whose reasoning image still describes its records, its source and
  its policies installs the image and recovers nothing (`reasoning-image/install!`).  Every
  other KB, and that one whenever the image is declined, recovers from the records
  (`recover-from-records`) and then writes an image for the next open
  (`reasoning-image/save!`, a no-op for a KB that takes none).  Both paths register the
  close-time refresh (`reasoning-image/register-close!`).

  Under `kb/*background-belief?*`, which `open-kb` binds for `:recover? :background`, an
  image declined only for its engine source is installed anyway, and `start-rebuild!`
  rebuilds belief under this build behind it.  A call while such a rebuild runs stops the
  rebuild and runs it on the calling thread instead."
  [kb]
  (kb/stop-rebuild! kb)
  (if (:stale-belief @(:unrecovered kb))
    (do ;; the progress of a stopped or failed background rebuild; this one runs here
      (swap! (:unrecovered kb) dissoc :rebuild)
      (reasoning-image/register-close! kb (rebuild-and-install! kb identity))
      kb)
    (let [t0 (System/nanoTime)
          {:keys [reasoning reason source image-source image]}
          (reasoning-image/install! kb (if kb/*background-belief?* #{:source-differs} #{}))
          ms #(/ (- (System/nanoTime) t0) 1e6)]
      (case reasoning
        :installed
        (do (trove/log! {:level :info :id ::reasoning-image-installed
                         :msg (format "installed the reasoning image for %s in %.0f ms"
                                      (:snapshot-dir kb) (ms))})
            ;; carried into the next image this KB writes, which no recover precedes
            (swap! (:unrecovered kb) assoc :last-recover (:recover image))
            (reasoning-image/register-close! kb source))

        :stale
        (do (trove/log! {:level :info :id ::reasoning-image-stale
                         :msg (format (str "installed the reasoning image for %s in %.0f ms; it was"
                                           " written under engine source %s, so belief is being"
                                           " rebuilt under this build, and writes are refused"
                                           " until the rebuilt belief is installed")
                                      (:snapshot-dir kb) (ms)
                                      (subs (str image-source) 0 (min 12 (count (str image-source)))))})
            (start-rebuild! kb image source))

        (do (when (reasoning-image/applies? kb)
              (trove/log! {:level :info :id ::reasoning-image-declined
                           :msg (str "reasoning image for " (:snapshot-dir kb)
                                     " not installed (" (name reason)
                                     ") — recovering from the records")}))
            ;; the settles write no mid-life image refresh (`kb/*defer-index-refresh?*`);
            ;; the one refresh runs here, after them.  A process killed before it reopens
            ;; from the records, as it would from any image not yet written.
            (binding [kb/*defer-index-refresh?* true]
              (recover-from-records kb))
            (kb/refresh-index-image! kb)
            (reasoning-image/register-close! kb (or (:source (reasoning-image/save! kb)) source))))
      ;; Belief now exists over whatever the store holds, so the write entry points stop
      ;; refusing on that count.  Only that count: a **derived** index is not rebuilt here —
      ;; `recover` reads it rather than writing it — so a KB recovered over one still mints a
      ;; second handle per assert, and `reindex` is the call that clears the other half.  A
      ;; `:stale` install leaves `:stale-belief` standing, which `start-rebuild!` set.
      (kb/note-hazards! kb {:no-belief false})
      kb)))

(defn recover-with-image
  "`recover`, trying the reasoning image in `dir` first — an export dump's, which
  `vaelii.impl.io.import` lands the records of.  `records` is the content fingerprint of
  the records the import landed, `{:sentexes fp :justifications fp}`, in the form the
  dump's manifest carries.  Returns `{:reasoning :installed}` or `{:reasoning :recovered
  :reason r}`, `r` the reason `reasoning-image/install-from!` gave for declining the image."
  [kb dir records]
  (let [{:keys [reasoning reason source]} (reasoning-image/install-from!
                                           kb dir (constantly records))]
    (if (= :installed reasoning)
      (do (reasoning-image/register-close! kb source)
          (kb/note-hazards! kb {:no-belief false})
          {:reasoning :installed})
      (do (recover kb)
          {:reasoning :recovered :reason reason}))))

(defn register-fresh-store!
  "Register the reasoning image's close-time save for `kb` when it opened over an empty
  store, and return `kb`.  Such a KB builds its belief assert by assert and never runs
  `recover`, so without this its first image would wait for the next open's recover.  A
  KB opened over a populated store registers inside `recover` instead, and one opened
  with `:recover? false` over a populated store registers nowhere: it holds no belief to
  write.  `reasoning-image/save!` refuses a KB whose network does not cover its records, so
  a loader that fills this KB and skips the recover leaves nothing to write."
  [kb]
  (when (and (reasoning-image/applies? kb) (nil? (cap/some-sentex-id (:records kb))))
    (reasoning-image/register-close! kb nil))
  kb)
