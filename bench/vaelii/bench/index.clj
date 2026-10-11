;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.index
  "One corpus, one workload, N index layouts — the bake-off a layout proposal is judged
  by.

  The precedent is the columnar trie, which was chosen by a bake-off that ran *before*
  the build (`vaelii.bench.densetrie`, docs/density.md).  A plausible design and a good
  one differed by an order of magnitude and only a measurement separated them.  This
  generalizes that from \"which representation\" to \"which shape\": hold the corpus and
  the question set fixed, vary the layout, and report what each costs.

  ## The gate: a layout may change cost and may not change answers

  Mechanical, not reviewed.  Every layout answers the identical probe set, and each
  probe's answer is fingerprinted as `[handle-count (hash handle-set)]` — content, not
  order, since two layouts may return one set in two orders.  A layout whose fingerprint
  differs from the reference's is reported as **WRONG** and its timings mean nothing.

  A projection comparison has a hole that this shape of harness inherits in a worse
  form, and `index_dump_test` already names it: **a layout that quietly falls back to a
  coarser access path answers identically and is merely slower.**  Read as a duration
  that is a fair loss; read as a path it is a misconfiguration.  So the access-path
  report is printed **first**, before any number that could be mistaken for a verdict,
  and a layout whose path histogram diverges from the reference's is called out by name.
  `vaelii.impl.profile`'s `:goals` tally is where it comes from — keyed by shape *and*
  by the path the shape chose, with `test/vaelii/profile_test.clj` pinning each of the
  nine labels.

  ## What is measured, and what is measured elsewhere

  * **Retrieval time per goal shape**, per layout, as a ratio against the reference.
  * **Build time, resident bytes, and bytes per sentex** — jol retained heap of the
    index store, which docs/density.md trusts under contention where it declines to
    trust wall-clock.
  * **Estimator quality as a q-error curve**, `max(est/actual, actual/est)` per join
    depth, computed by `vaelii.bench.plan` and not rebuilt here.  The reading that
    matters is whether q is **flat in the depth** — flat means the estimates compose,
    growing means no better ordering over them would rescue the plan — rather than
    whether it is small.  §4.4 of the paper is why a layout that retrieves faster and
    estimates worse can be a net loss no retrieval microbenchmark shows.
  * **Index reads by family**, so a layout that answers from a different family says so.

  Two quantities are deliberately absent because they exist:

  * **Write cost per assert, per family** is `test/vaelii/assert_cost_test.clj`, which
    pins the exact operation counts, and `lein bench-profile`, which reads them out over
    a whole corpus.  Deriving a second write number here would be a second answer to a
    settled question.
  * **Allocations per lookup** is `vaelii.bench.alloc`.  The choice of instrument is deliberate: that
    namespace drives the same arms by reaching `#'vaelii.bench.index/layouts` and
    `#'vaelii.bench.index/open-layout!`, so the two harnesses compare the same layouts
    over the same corpora rather than two spellings of them.

  ## The columnar arm reports no index reads

  This matters more here than anywhere else in the repo, so it is handled explicitly
  rather than noted.  **Only the `:goals` tally is index-independent** (docs/profile.md):
  it is taken above the index, in `resolution`.  `:reads`, `:fan`, `:writes` and
  `:retracts` are `KvIndexStore`'s methods, and the columnar store's trie is native — its
  `lookup` and its three count probes report no read and no fan, and its writes bypass
  `KvIndexStore` entirely.

  So comparing a columnar layout against a flat-map one on `:reads` would report a
  fabricated result: the columnar arm would look like an index nobody reads.  Every
  layout carries a `:kv-index-store?` flag, the read table prints **`n/a  (native trie — no
  `KvIndexStore`)`** rather than `0` for a layout that has none, and the access-path
  and answer-set reports — which are index-independent — are the ones that span all of
  them.  A zero and an absence are different readings and are printed differently.

  ## Methodology, taken from `vaelii.bench.perf`

  Four of that gate's decisions were each learned from a *comfortable pass* that turned
  out to be a measurement error, and three of them transfer directly:

  * **Warm every layout to the same amount.**  Warming proportionally to the work a
    layout happens to do hands the slow one a JVM that has JIT-compiled the code being
    timed while the fast one is still climbing to it.  Here the analogue is the inner
    repetition count: it is calibrated **once, on the reference layout**, and every
    layout then runs that same count.
  * **Summarize the tail rather than the run**, over a fixed window at every layout, so
    two answers cover windows of equal width.  The summary is the **median** rather than
    perf.clj's mean, and the difference is that perf.clj re-runs a check that exceeded
    its bound and keeps the better run.  Nothing here has a bound to exceed, so one GC
    pause in the *reference's* window would scale a whole row — which it did, once, by
    3x — and a median over the same window is that defence with no verdict to hang it on.
  * **Report `noise` below the floor rather than a green light.**  A ratio between two
    readings that are mostly timer jitter means nothing, so a timed unit is padded with
    inner repetitions until it clears the floor by two orders of magnitude, and a unit
    that still cannot is printed as `noise` and not as a result.

  The fourth — pick a small size at which the measured thing has barely started — is
  about a two-size growth ratio, and this harness has no second size: it compares
  layouts at one corpus.  What it inherits instead is the same warning in the other
  direction: **a corpus too small for the layouts to differ reports that they do not**,
  which is a fact about the corpus.  The starter is 1,500-odd sentexes and is a
  smoke test of the harness; `generated` and a converted corpus are where a difference
  can exist.

  A fifth decision is this harness's own and follows from the same argument.  **The
  timings are interleaved by group, not by layout**: measuring every group of layout A
  before any group of layout B puts tens of seconds between the two readings a ratio is
  taken over, so drift over the run — heap growth as each layout's KB stays resident, a
  background process, thermal throttling — lands on the layout axis and is indistinguishable from a layout
  difference.  Group by group, the compared readings are seconds apart.

  **Build wall-clock is the least trustworthy number here** and is labelled so in its own
  table.  Two discarded starter loads precede the first measured build, which removes
  most of the JIT skew, but the layouts are built in order and each one's KB stays
  resident for the workload, so the last build runs against a fuller heap than the first.
  The tell is `deep-terms`: it writes a strictly larger key set than `kv` and cannot be
  faster to build, so a run where it reads faster is a run whose build column is
  measuring the JVM.

  The literal cache is bound **off** for the whole measured workload.  `matches-visible`
  caches its answers per KB keyed by the literal and the three retrieval switches
  (`vaelii.impl.literal-cache`), so with it on the second pass over a probe set measures
  a hash lookup and every layout ties.

  ## What this harness cannot see

  In the spirit of `vaelii.bench.perf`'s own list, because a harness whose limits are
  not written down reads as covering more than it does.

  * **Anything on the write path.**  A layout change that moves cost from the read path
    to the write path is invisible to a read-only workload, and every workload here is
    read-only.  Build time is the only write reading, and it is one number for a whole
    corpus rather than a per-family count: `assert_cost_test` is the instrument for that.
  * **What the context ancestor set costs.**  Every probe is asked at `?ctx`, so the
    `genlCx` up-closure is never walked.  A layout question about the context level
    is not answered by these numbers.
  * **Allocations, objects and bytes on the walk.**  Retrieval time is wall-clock, and
    wall-clock is the reading docs/density.md declines to trust under contention, so the
    read path is held here to the weaker standard.  `vaelii.bench.alloc` is the
    structural counterpart.
  * **A family this workload does not read.**  The term index and the term roster are
    read by `terms` / `find-terms` / `find-sentexes` and by no reasoning at all, so a
    layout that moves them — `:deep-terms` moves exactly that — shows up here as bytes
    and as nothing else.  `lein bench-profile`'s interactive arm is the one that reads
    them.
  * **The difference between two layouts that both estimate correctly.**  The q-error
    arm runs on `vaelii.bench.plan`'s 1:1 chain, where a correct estimator scores exactly
    1.00 at every depth, so the arm fails a layout whose counts diverge and cannot rank
    one against another.
  * **A cost that is not the index, which is most of what is timed.**  Unification,
    belief filtering, the taxonomy closures, the record fetch and the frontier the walk
    rebuilds at every level are all inside every reading here, and every one of them is
    *common to both arms of every ratio*.  A ratio divides a shared cost out, so a layout
    that is 5% of the total cannot move the total by more than 5%, and a row that reads
    1.05x may be a layout that is twice as expensive at the part it owns.

    This is `perf.clj`'s \"a baseline large enough to already carry the cost being
    measured\" arriving as a *denominator* rather than as a small size, and it is the
    same trap in a second place.  `vaelii.bench.alloc` hit it head-on measuring the same
    two layouts by allocation: bytes per lookup separated the flat map and the columnar
    trie by 1.2 to 1.5x, and the marginal bytes per *extra frontier node* — the quantity
    with the shared cost removed — separated them by more.  Every number in this file is
    a total of that kind.  Read a ratio here as a floor on the layout's contribution, and
    read the counts, the paths and the retained bytes as the quantities that are not
    diluted.
  * **The four `KvIndexStore` tallies on a layout that is not one**, which is the
    columnar caveat above.

  Run:

      lein bench-index [corpus] [workload] [args …]

      corpus    starter | generated [facts] [rules] | corpus <dir> [profile]
      workload  shapes (default) | heads | local | all

        shapes  every binding pattern over sampled facts of the busiest predicates,
                asked at level 4 — `res/matches-visible`, which is the set-algebra
                matcher and 81 to 100 percent of the retrieval traffic every corpus
                profiled so far.  Synthetic on purpose: its question is what a shape
                costs, not which shapes arrive.
        heads   each rule's own consequent, asked at level 4.  A rule's consequent is
                the question the rule exists to answer, so the set is a workload the KB
                declared for itself.
        local   `shapes` at level 2 — `res/raw-match`, the `candidate-handles` matcher,
                which is the minority path and the one `lein bench-profile`'s balanced
                probe drives.
        all     the three.

  A corpus run wants a heap, and `:bench` pins `-Xmx6g`.  An environment `JVM_OPTS` is
  placed before the project's own options and loses to it silently, so edit the vector on
  the way past — `with-profile` first, `update-in` second.  The `corpus` arm reads
  `:cyc-corpus`, so link the reader first (`scripts/link-checkouts.sh`):

      lein with-profile +bench update-in :jvm-opts conj '\"-Xmx32g\"' -- \\
        run -m vaelii.bench.index corpus shapes <dir>"
  (:require [clojure.string :as str]
            [vaelii.bench.plan]
            [vaelii.bench.postings :as postings]
            [vaelii.bench.profile]
            [vaelii.core :as v]
            [vaelii.impl.levels :as levels]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]))

;; ---- borrowed rather than rebuilt ---------------------------------------
;;
;; The corpus arms and the probe construction are `vaelii.bench.profile`'s, and the
;; q-error curve is `vaelii.bench.plan`'s.  Taken by var rather than copied, because the
;; whole value of a bake-off is that its corpus is the *same* corpus the profile reads —
;; two harnesses that generate their own Zipf corpora are two corpora, and a finding here
;; could not then be checked against a reading there.  Each is private in its own
;; namespace for the ordinary reason (nothing in the engine calls it); a measurement is
;; the one caller that has to.

(def ^:private load-starter!    #'vaelii.bench.profile/load-starter!)
(def ^:private load-generated!  #'vaelii.bench.profile/load-generated!)
(def ^:private load-corpus!     #'vaelii.bench.profile/load-corpus!)
(def ^:private sample-facts     #'vaelii.bench.profile/sample-facts)
(def ^:private probe-pattern    #'vaelii.bench.profile/probe-pattern)
(def ^:private adornments       #'vaelii.bench.profile/adornments)
(def ^:private rule-goals       #'vaelii.bench.profile/rule-goals)
(def ^:private families         @#'vaelii.bench.profile/families)
(def ^:private plan-build!      #'vaelii.bench.plan/build!)
(def ^:private plan-conjunction #'vaelii.bench.plan/conjunction)
(def ^:private plan-q-errors    #'vaelii.bench.plan/q-errors)

(defn- ms ^double [t0] (/ (- (System/nanoTime) (long t0)) 1e6))
(defn- mb ^double [^long b] (/ b 1048576.0))

(defn- banner [s]
  (println)
  (println (str "── " s " " (apply str (repeat (max 0 (- 76 (count s))) "─")))))

;; ---- the layouts --------------------------------------------------------
;;
;; Two tiers, and the split is not cosmetic.  A **physical** layout is a different index:
;; it builds its own KB, so build time and resident bytes are its own.  An **access**
;; layout is the *same* index read differently — the reference KB, with one retrieval
;; switch withdrawn — so it has no build time and no bytes of its own, and quoting either
;; would be quoting the reference's.  Sharing the KB is also what makes it the sharper
;; experiment: the stored index is held byte-identical and only the path varies.
;;
;; `:kv-index-store?` is the columnar caveat made data.  False means the four
;; `KvIndexStore` tallies do not fire for this layout, so a zero from them is an absence
;; and not a reading.

(def ^:private layouts
  [{:id :kv :axis :physical :kv-index-store? true
    :label "kv-trie (shipped)"
    :opts {:backend :memory}
    :note "the flat-map KvIndexStore — the reference every other row is a ratio against"}
   {:id :dense :axis :physical :kv-index-store? true
    :label "dense postings"
    :opts {:backend :memory-dense}
    :note "same families, sorted int[] postings instead of boxed handle sets"}
   {:id :columnar :axis :physical :kv-index-store? false
    :label "columnar trie"
    :opts {:backend :memory-columnar}
    :note "a native CSR trie over an int dictionary — no `KvIndexStore` implementation on the trie"}
   {:id :deep-terms :axis :physical :kv-index-store? true
    :label "kv-trie, term floor 0"
    :opts {:backend :memory}
    :bindings {:min-indexed-depth 0}
    :note "every literal earns its own whole-compound term key — a strictly larger key set"}
   {:id :no-arg-roots :axis :access :kv-index-store? true :shares :kv
    :label "no argument roots"
    :bindings {:arg-roots false}
    :note "a ground argument after an open one falls back to a leading-variable trie fan"}
   {:id :no-structural :axis :access :kv-index-store? true :shares :kv
    :label "no structural narrowing"
    :bindings {:structural false}
    :note "a compound argument is answered by the functor extent, the looser superset"}
   {:id :fan-out :axis :access :kv-index-store? true :shares :kv
    :label "reference fan-out"
    :bindings {:hierarchical false}
    :note "the |specs| x |context-up| product instead of the set-algebra retrieval"}])

(def ^:private reference-id
  "The layout every ratio is against and every answer set is compared to."
  :kv)

(defn- with-layout*
  "Run `f` under `layout`'s switches.  All four are bound on every layout rather than
  only the ones a layout moves, so a row's configuration is what this map says and not
  what the ambient bindings happened to be."
  [layout f]
  (let [b (:bindings layout {})]
    (binding [sx/*min-indexed-depth*       (get b :min-indexed-depth 1)
              res/*arg-root-retrieval*     (get b :arg-roots true)
              res/*structural-index*       (get b :structural true)
              res/*hierarchical-retrieval* (get b :hierarchical true)]
      (f))))

(defmacro ^:private with-layout [layout & body]
  `(with-layout* ~layout (fn [] ~@body)))

(defn- open-layout!
  "A KB on `layout`'s backend, on its own memory space and emptied first.  `!` because
  `clear!` destroys whatever the space held — which on a bench space is nothing, and the
  guarantee is that it is nothing.

  Public-by-var for `vaelii.bench.alloc`: the allocation harness measures the same
  layouts, and a second way of opening them would be a second experiment."
  [layout ^long space]
  (let [kb (v/open-kb (assoc (:opts layout) :space space :recover? false))]
    (v/clear! kb)
    kb))

;; ---- the corpus ---------------------------------------------------------

(defn- load-into!
  "Load `mode` into `kb` under `layout`'s switches, returning the load's wall clock.  The
  switches wrap the *load* as well as the workload, because one of them
  (`*min-indexed-depth*`) is read at write time and is the whole of what `:deep-terms`
  changes."
  ^double [kb layout mode args]
  (let [t0 (System/nanoTime)]
    (with-layout layout
      (case mode
        "generated" (load-generated! kb
                                     (or (some-> (first args) Long/parseLong) 30000)
                                     (or (some-> (second args) Long/parseLong) 3000))
        "corpus"    (load-corpus! kb (first args) (keyword (or (second args) "ontology")))
        (load-starter! kb)))
    (ms t0)))

;; ---- the workload -------------------------------------------------------
;;
;; Built **once**, off the reference KB, and handed to every layout.  A probe set derived
;; per layout would be a different workload per layout, which is the one thing a bake-off
;; may not do — and it would do it silently, since every layout loads the same corpus and
;; the sets would agree until the day one of them did not.

(defn- shape-groups
  "`shapes`: one group per `[arity, binding pattern]`, each holding the patterns that ask
  that shape of `k` sampled facts on each of the busiest `preds`.  Grouped rather than
  flat because a *shape* is the unit the report is per, and timing a mixed set would
  report an average over a distribution this harness deliberately does not claim to know."
  [kb preds ^long k]
  (let [by-arity (group-by #(long (dec (count %))) (mapcat #(sample-facts kb % k) preds))]
    (vec (for [[ar facts] (sort by-arity)
               :when (<= 1 ar 3)
               ad (adornments ar)
               :let [pats (vec (keep #(probe-pattern % ad) facts))]
               :when (seq pats)]
           {:label (str ar "-ary " ad) :level 4 :pats pats}))))

(defn- head-group
  "`heads`: each rule's own consequent, as written.  One group — a rule head is a real
  question rather than a shape, so splitting it by adornment would report the corpus's
  rule spelling and call it a workload."
  [kb ^long limit]
  (let [gs (vec (rule-goals kb limit))]
    (when (seq gs) [{:label "rule heads" :level 4 :pats gs}])))

(defn- workload-groups
  "The probe groups for `workload`, off the reference KB."
  [kb preds workload k heads]
  (vec (concat (when (#{"shapes" "all"} workload) (shape-groups kb preds k))
               (when (#{"heads" "all"} workload)  (head-group kb heads))
               (when (#{"local" "all"} workload)
                 (map #(assoc % :level 2 :label (str (:label %) " @2"))
                      (shape-groups kb preds k))))))

(defn- run-group
  "Force one group's whole answer, discarding the results but not the work.  Returns the
  answer count, so nothing here can be elided by a compiler that notices the results go
  nowhere."
  ^long [kb {:keys [level pats]}]
  (reduce (fn [^long n pat] (+ n (long (count (levels/lookup kb level pat '?ctx)))))
          0 pats))

;; ---- measurement --------------------------------------------------------

(def ^:private noise-floor-ns
  "Below this a timed unit is mostly timer and scheduler jitter, and the ratio of two
  such units says nothing.  A unit that lands here is reported as `noise` and not as a
  result — the same rule `vaelii.bench.perf` states, for the same reason."
  20000)                                                    ; 20µs

(def ^:private target-unit-ns
  "What one timed unit is padded up to, by repeating the group inside it.  Two orders of
  magnitude above the floor, so a unit is never near it and the calibration does not have
  to be right to within a factor."
  2000000)                                                  ; 2ms

(def ^:private warm-units 4)

(def ^:private unit-reps
  "Timed units per group per layout, of which the last `tail-units` are the answer."
  20)

(def ^:private tail-units
  "How many units from the **end** of a run the answer is taken over.  The end, and the
  same count at every layout, so two answers are summaries of windows of equal width
  rather than of a fraction of two runs of different length."
  10)

(defmacro ^:private nanos [& body]
  `(let [t# (System/nanoTime)] ~@body (- (System/nanoTime) t#)))

(defn- tail-figure
  "The **median** of the last `tail-units` readings.

  `perf.clj` takes the mean of its tail and defends against a GC pause landing in one
  window by re-running a check that exceeded its bound and keeping the better run.  This
  harness has no bound to exceed — every row is a ratio against the reference, so there
  is nothing to trip a re-run — and one pause in the *reference's* window scales a whole
  row.  It happened on the first interleaved run: a `2-ary bb` reading three times its
  neighbours' put every other layout in that row at 0.4x.  A median over the same window
  is the same defence with no verdict to hang it on."
  ^double [xs]
  (let [v (vec xs)
        k (min (count v) (max 1 tail-units))
        w (vec (sort (subvec v (- (count v) k))))
        n (count w)]
    (if (odd? n)
      (double (nth w (quot n 2)))
      (/ (+ (double (nth w (dec (quot n 2)))) (double (nth w (quot n 2)))) 2.0))))

(defn- calibrate
  "How many passes over the group one timed unit holds.  Calibrated on the **reference**
  layout and then used unchanged at every other one, which is this harness's form of
  `perf.clj`'s rule that both sizes warm to the same amount: an inner count derived per
  layout would give a slow layout fewer, larger units and a fast one more, smaller ones,
  and the two would not be the same measurement."
  ^long [f]
  (f)
  (let [one (max 1 (long (nanos (f))))]
    (max 1 (min 512 (long (Math/ceil (/ (double target-unit-ns) (double one))))))))

(defn- unit-readings
  "`unit-reps` timed units of `inner` passes each, after `warm-units` discarded ones."
  [f ^long inner]
  (let [unit (fn [] (nanos (dotimes [_ inner] (f))))]
    (dotimes [_ warm-units] (unit))
    (System/gc)
    (vec (repeatedly unit-reps unit))))

;; ---- the answer gate ----------------------------------------------------

(defn- fingerprint
  "One entry per probe: `[answer-count (hash handle-set)]`.  Content rather than order —
  two layouts may return one set in two orders and both are right — and a hash rather
  than the set, because the reference's answer to every probe over a real corpus is not
  a thing to hold in memory beside the KB that produced it."
  [kb {:keys [level pats]}]
  (mapv (fn [pat]
          (let [hs (into #{} (map :handle) (levels/lookup kb level pat '?ctx))]
            [(count hs) (hash hs)]))
        pats))

(defn- first-divergence
  "The index of the first probe whose fingerprint differs, or nil."
  [ref got]
  (first (keep-indexed (fn [i x] (when (not= x (nth got i nil)) i)) ref)))

;; ---- the reports --------------------------------------------------------

(defn- path-tally
  "`:goals` folded to `{access-path count}` over one profiled pass of the whole workload.
  Index-independent: `:goals` is taken above the index, so this row means the same thing
  on the columnar arm as on the flat one, which is exactly why it is the report the
  bake-off leads with."
  [kb groups]
  (prof/start)
  (doseq [g groups] (run-group kb g))
  (let [snap (prof/stop)]
    {:paths (reduce (fn [m [k n]] (update m (nth k 3) (fnil + 0) n)) {} (:goals snap))
     :reads (:reads snap)
     :fan   (let [f (:fan snap)]
              {:calls  (reduce + 0 (map (comp long :calls val) f))
               :visits (reduce + 0 (map (comp long #(or (:visits %) 0) val) f))})}))

(defn- access-path-report
  "**The report a result is trusted on.**  A layout that quietly falls back to a coarser
  path answers identically and is merely slower, which every duration in this harness
  would report as a fair loss.  So the paths are printed before the durations are, and a
  divergence from the reference is named rather than left to be spotted in a column."
  [rows]
  (banner "ACCESS PATHS — which path each goal took, before how long it took")
  (println "  `vaelii.impl.profile`'s :goals tally, keyed by shape and by the path the shape")
  (println "  chose.  Index-independent (taken above the index), so every layout is comparable")
  (println "  here including the columnar one.")
  (let [paths (vec (sort (into #{} (mapcat (comp keys :paths second)) rows)))
        ids   (mapv first rows)]
    (println)
    (println (format "    %-22s %s" "access path"
                     (str/join " " (map #(format "%14s" (name %)) ids))))
    (println (str "    " (apply str (repeat (+ 22 (* 15 (count ids))) "-"))))
    (doseq [pth paths]
      (println (format "    %-22s %s" (name pth)
                       (str/join " " (map (fn [[_ r]]
                                            (format "%14s"
                                                    (if-let [n (get (:paths r) pth)]
                                                      (format "%,d" n)
                                                      "·")))
                                          rows)))))
    (println)
    (let [ref (:paths (get (into {} rows) reference-id))]
      (doseq [[id r] rows
              :when (not= id reference-id)]
        (if (= ref (:paths r))
          (println (format "    %-16s same path histogram as %s" (name id) (name reference-id)))
          (println (format "    %-16s ** DIVERGES from %s — this layout answers by a different path,"
                           (name id) (name reference-id))))))
    (println)
    (println "    A divergence is not a failure: `no-arg-roots` and `fan-out` exist to move the")
    (println "    path, and their rows are what the move looks like.  It is a failure when a")
    (println "    layout that was not supposed to move it did — that is the misconfiguration a")
    (println "    duration alone would have reported as a fair loss.")))

(defn- answer-report [rows groups]
  (banner "THE GATE — a layout may change cost and may not change answers")
  (let [ref (get (into {} rows) reference-id)]
    (doseq [[id r] rows]
      (let [bad (keep (fn [[gi g]]
                        (when-let [i (first-divergence (nth (:fp ref) gi) (nth (:fp r) gi))]
                          [gi g i]))
                      (map-indexed vector groups))]
        (if (empty? bad)
          (println (format "    %-16s %,10d answers over %,d probes, %,d sentexes — identical to %s"
                           (name id) (:answers r) (:probes r) (:sentexes r) (name reference-id)))
          (do
            (println (format "    %-16s ** WRONG — %d of %d groups differ; every timing below is void"
                             (name id) (count bad) (count groups)))
            (doseq [[gi g i] (take 3 bad)
                    :let [pat (nth (:pats g) i)]]
              (println (format "        %-24s %s" (:label g) (pr-str pat)))
              (println (format "        %s answered %s, %s answered %s — re-run both as"
                               (name reference-id) (pr-str (first (nth (nth (:fp ref) gi) i)))
                               (name id) (pr-str (first (nth (nth (:fp r) gi) i)))))
              (println (format "        (levels/lookup kb %d '%s '?ctx)" (:level g) (pr-str pat))))))))))

(defn- build-report [rows]
  (banner "BUILD AND BYTES — what the layout costs to hold")
  (println "  jol retained heap of the index store.  Structural, so it is the reading")
  (println "  docs/density.md trusts under contention where it declines to trust wall-clock;")
  (println "  the build column beside it is wall-clock and is not.  Every measured build is")
  (println "  preceded by two discarded starter loads, so no layout pays the JIT for the rest.")
  (println "  An access-path layout reads the reference's own index, so it has neither.")
  (println)
  (println (format "    %-18s %12s %14s %12s %10s  %s"
                   "layout" "build ms" "index MB" "bytes/sentex" "vs kv" "note"))
  (println (str "    " (apply str (repeat 100 "-"))))
  (let [ref (get (into {} rows) reference-id)]
    (doseq [[id r] rows]
      (if (= :access (:axis r))
        (println (format "    %-18s %12s %14s %12s %10s  %s"
                         (name id) "shared" "shared" "shared" "—" (:note r)))
        (println (format "    %-18s %12.0f %14s %12s %10s  %s"
                         (name id) (:build-ms r)
                         (if-let [b (:bytes r)] (format "%,.1f" (mb b)) "skipped")
                         (if-let [b (:bytes r)]
                           (format "%,.0f" (/ (double b) (max 1 (:sentexes r))))
                           "—")
                         (if (and (:bytes r) (:bytes ref) (not= id reference-id))
                           (format "%.2fx" (/ (double (:bytes r)) (double (:bytes ref))))
                           "—")
                         (:note r)))))))

(defn- timing-report [rows groups]
  (banner "RETRIEVAL TIME PER GOAL SHAPE")
  (println (format "  Per-probe nanoseconds: the median of the last %d of %d timed units, each unit a"
                   tail-units unit-reps))
  (println "  fixed number of passes calibrated once on the reference layout and used unchanged")
  (println "  at every other.  A unit under the noise floor prints `noise`.  Interleaved by group,")
  (println "  so the readings a ratio compares are seconds apart rather than a whole run apart.")
  (println "  Wall-clock, so it is the UNTRUSTED half of this harness; the counts above and the")
  (println "  paths below are the structural half.")
  (let [ids (mapv first rows)]
    (println)
    (println (format "    %-22s %8s %s" "shape" "probes"
                     (str/join " " (map #(format "%16s" (name %)) ids))))
    (println (str "    " (apply str (repeat (+ 31 (* 17 (count ids))) "-"))))
    (doseq [[gi g] (map-indexed vector groups)]
      (println (format "    %-22s %8d %s" (:label g) (count (:pats g))
                       (str/join " "
                                 (map (fn [[id r]]
                                        (let [{:keys [ns-per-probe unit-ns]} (nth (:timings r) gi)]
                                          (format "%16s"
                                                  (cond
                                                    (< (double unit-ns) noise-floor-ns) "noise"
                                                    (= id reference-id) (format "%,.0f" ns-per-probe)
                                                    :else
                                                    (format "%.2fx"
                                                            (/ ns-per-probe
                                                               (max 1.0 (:ns-per-probe
                                                                         (nth (:timings (get (into {} rows) reference-id)) gi)))))))))
                                      rows))))))
  (println)
  (println (format "    The %s column is ns per probe; every other column is a ratio against it."
                   (name reference-id))))

(defn- read-report
  "Index reads by family — and the one table where a layout without a `KvIndexStore`
  must not be printed as a zero.  `n/a` is an absence and `0` is a reading, and the whole
  point of the distinction is that the columnar arm would otherwise look like an index
  nobody touches."
  [rows]
  (banner "INDEX READS BY FAMILY — and where the instrument cannot see")
  (println "  Only :goals (above) is index-independent.  These are `KvIndexStore`'s methods, so")
  (println "  a layout whose trie is native reports n/a rather than 0 — see docs/profile.md.")
  (let [ids (mapv first rows)]
    (println)
    (println (format "    %-18s %s" "family"
                     (str/join " " (map #(format "%14s" (name %)) ids))))
    (println (str "    " (apply str (repeat (+ 18 (* 15 (count ids))) "-"))))
    (doseq [f families]
      (println (format "    %-18s %s" (name f)
                       (str/join " " (map (fn [[_ r]]
                                            (format "%14s"
                                                    (if (:kv-index-store? r)
                                                      (format "%,d" (long (get (:reads r) f 0)))
                                                      "n/a")))
                                          rows)))))
    (println)
    (println (format "    %-18s %s" "trie walks"
                     (str/join " " (map (fn [[_ r]]
                                          (format "%14s"
                                                  (if (:kv-index-store? r)
                                                    (format "%,d" (:calls (:fan r)))
                                                    "n/a")))
                                        rows))))
    (println (format "    %-18s %s" "node probes"
                     (str/join " " (map (fn [[_ r]]
                                          (format "%14s"
                                                  (if (:kv-index-store? r)
                                                    (format "%,d" (:visits (:fan r)))
                                                    "n/a")))
                                        rows))))
    (println)
    (println "    n/a = a native trie with no `KvIndexStore`.  Its flat families do tally,")
    (println "    delegating to an embedded KvIndexStore, so a mixed row is expected:")
    (println "    the flat numbers are real and the trie ones are not there to be read.")))

;; ---- the q-error arm ----------------------------------------------------

(defn- q-error-arm
  "`max(est/actual, actual/est)` per join depth, per layout, on `vaelii.bench.plan`'s own
  1:1 chain corpus rather than on the bake-off's.  Its corpus, because a q-error curve
  needs a join whose true cardinality at every prefix is known by construction, and the
  bake-off corpora are chosen for the opposite property.

  This is the quantity that decides whether a layout is **admissible at all**: the trie
  is the cost model's substrate, so a layout that retrieves faster and estimates worse
  can be a net loss no retrieval microbenchmark shows.

  **On that corpus the arm can fail a layout and cannot rank two.**  The chain is 1:1, so
  every prefix's true count is exactly the count the trie holds and a correct estimator
  scores 1.00 at every depth.  A layout whose counts diverge shows up immediately; two
  layouts that both count correctly are indistinguishable here, and separating them would
  need a corpus the estimator can be wrong about."
  [layouts* ^long space0]
  (banner "ESTIMATOR QUALITY — the q-error curve per join depth")
  (println "  Flat in the depth is the claim that the estimates compose; growing in the depth")
  (println "  withdraws it, and no better ordering over them would rescue the plan.  Read the")
  (println "  SHAPE of the row, not the size of the numbers.")
  (println "  The corpus is plan.clj's 1:1 chain, where a correct estimator scores exactly 1.00")
  (println "  at every depth — so this arm FAILS a layout whose counts diverge and cannot rank")
  (println "  two layouts that both count correctly.")
  (println)
  (println (format "    %-18s %-8s %-44s %10s" "layout" "lits" "q at k = 1, 2, …" "last/first"))
  (println (str "    " (apply str (repeat 84 "-"))))
  (doseq [[i layout] (map-indexed vector layouts*)]
    (let [physical (if (= :access (:axis layout))
                     (first (filter #(= (:shares layout) (:id %)) layouts*))
                     layout)]
      (doseq [width [2 3 4 5]]
        (let [kb (open-layout! physical (+ space0 (* 4 (long i)) (- (long width) 2)))
              qs (with-layout layout
                   (binding [lc/*enabled* false]
                     (plan-build! kb width 300 40)
                     (plan-q-errors kb (plan-conjunction width))))]
          (println (format "    %-18s %-8s %-44s %10s"
                           (if (= width 2) (name (:id layout)) "")
                           (inc (long width))
                           (str/join "  " (map #(format "%.2f" %) qs))
                           (if (and (seq qs) (pos? (double (first qs))))
                             (format "%.2fx" (/ (double (last qs)) (double (first qs))))
                             "—")))))
      (println))))

;; ---- the run ------------------------------------------------------------

(defn- jol-cap
  "Above this many sentexes the jol walk is skipped.  `GraphLayout/parseInstance` walks
  every reachable object, so on a corpus-sized index it is a measurement with its own
  memory problem — which is the failure mode `vaelii.bench.profile`'s exact-floor
  computation refuses in the same way."
  ^long [] 1200000)

(defn- measure-layout
  "The counted half of one layout's row: the path tally, the answer fingerprints, the
  resident bytes.  Everything here is a count or a structural size, so it is the half
  this harness trusts, and it is taken before any clock starts."
  [layout kb groups build-ms]
  (with-layout layout
    (binding [lc/*enabled* false]
      (let [n   (long (v/sentex-count kb))
            fps (mapv #(fingerprint kb %) groups)]
        (merge (select-keys layout [:axis :kv-index-store? :note])
               (path-tally kb groups)
               {:build-ms build-ms
                :sentexes n
                :bytes    (when (and (not= :access (:axis layout)) (<= n (jol-cap)))
                            (postings/retained [(:index kb)]))
                :fp       fps
                :probes   (reduce + 0 (map (comp count :pats) groups))
                :answers  (reduce + 0 (map (fn [fp] (reduce + 0 (map first fp))) fps))})))))

(defn- time-groups
  "The timed half, **interleaved by group rather than by layout**.

  This harness's own methodological decision, and it is the same argument `perf.clj`
  makes about warming: measuring every group of layout A before any group of layout B
  puts tens of seconds between the two readings a ratio is taken over, so any drift over
  the run — heap growth as each layout's KB stays resident, a background process, thermal
  throttling — lands on the *layout* axis and is read as a layout difference.  Taken
  group by group, the readings a ratio compares are seconds apart and the drift is
  common to all of them.

  Returns `{layout-id [{:unit-ns :ns-per-probe} …]}`, one entry per group."
  [layouts* kb-of groups]
  (reduce
   (fn [acc g]
     (let [ref-layout (first (filter #(= reference-id (:id %)) layouts*))
           ;; the inner count is calibrated once, on the reference, and used unchanged at
           ;; every layout — a count derived per layout would give the slow one fewer,
           ;; larger units and the fast one more, smaller ones
           inner (with-layout ref-layout
                   (binding [lc/*enabled* false]
                     (calibrate #(run-group (kb-of ref-layout) g))))]
       (reduce (fn [a layout]
                 (let [kb   (kb-of layout)
                       unit (with-layout layout
                              (binding [lc/*enabled* false]
                                (tail-figure (unit-readings #(run-group kb g) inner))))]
                   (update a (:id layout) (fnil conj [])
                           {:unit-ns      unit
                            :ns-per-probe (/ unit (double (* (long inner) (count (:pats g)))))})))
               acc layouts*)))
   {} groups))

(defn -main [& args]
  (let [mode     (or (first args) "starter")
        workload (or (second args) "shapes")
        rest*    (drop 2 args)
        corpus?  (= "corpus" mode)]
    (println (format "vaelii bench-index — %s / %s, %d layouts, max heap %.1f GB"
                     mode workload (count layouts)
                     (/ (.maxMemory (Runtime/getRuntime)) 1073741824.0)))
    (when-not (#{"shapes" "heads" "local" "all"} workload)
      (println "  unknown workload; want shapes | heads | local | all")
      (System/exit 2))

    ;; **One discarded load before any measured one**, and it is the same argument
    ;; `perf.clj`'s `warm!` makes about warming both sizes to the large one.  The
    ;; assert and index paths are cold when the first layout builds and hot when the
    ;; last one does, so an unwarmed run flatters whichever layout is listed last — on
    ;; the starter it read 1,432 ms for the first build and 440 ms for the fourth, over
    ;; four builds of the identical corpus.  The starter is the warm-up at every mode
    ;; because what needs compiling is the write path, which a corpus load then reuses,
    ;; and a second corpus load would cost minutes to learn nothing more.
    (let [_     (dotimes [_ 2]
                  (let [kb (open-layout! (first layouts) 59)]
                    (with-layout (first layouts) (load-starter! kb))
                    (v/clear! kb)))
          built (reduce (fn [m [i layout]]
                          (if (= :access (:axis layout))
                            m
                            (let [kb (open-layout! layout (+ 60 (long i)))
                                  t  (load-into! kb layout mode rest*)]
                              (assoc m (:id layout) {:kb kb :build-ms t}))))
                        {} (map-indexed vector layouts))
          kb-of  (fn [layout] (get-in built [(or (:shares layout) (:id layout)) :kb]))
          ref-kb (kb-of (first (filter #(= reference-id (:id %)) layouts)))
          preds  (take 12 (sort-by #(- (long (p/count-with-functor (:index ref-kb) %)))
                                   (into [] (comp (map #(p/get-sentex (:records ref-kb) %))
                                                  (keep (fn [s] (when (nil? (:antecedent s))
                                                                  (let [b (sx/body s)]
                                                                    (when (and (sequential? b) (seq b)
                                                                               (symbol? (first b)))
                                                                      (first b))))))
                                                  (distinct))
                                         (p/sentex-ids (:records ref-kb)))))
          ;; ONE workload, derived once off the reference KB and handed to every layout
          groups (workload-groups ref-kb preds workload (if corpus? 40 20) (if corpus? 400 200))]
      (when (empty? groups)
        (println "  no probes — this corpus has nothing the workload can ask")
        (System/exit 1))
      (println (format "  %d probe groups, %,d probes, over %d predicates"
                       (count groups) (reduce + 0 (map (comp count :pats) groups)) (count preds)))

      (let [timings (time-groups layouts kb-of groups)
            rows    (mapv (fn [layout]
                            [(:id layout)
                             (assoc (measure-layout layout (kb-of layout) groups
                                                    (get-in built [(:id layout) :build-ms] 0.0))
                                    :timings (get timings (:id layout)))])
                          layouts)]
        (access-path-report rows)
        (answer-report rows groups)
        (build-report rows)
        (timing-report rows groups)
        (read-report rows))

      (q-error-arm layouts 90)

      (banner "what this harness cannot see")
      (println "  * the write path.  A layout change that moves cost from the read path to the")
      (println "    write path is invisible to a read-only workload, and every workload here is")
      (println "    one.  test/vaelii/assert_cost_test.clj pins the per-family assert cost.")
      (println "  * allocations and bytes on the walk — vaelii.bench.alloc, which drives these")
      (println "    same layouts through #'vaelii.bench.index/layouts.")
      (println "  * the context ancestor set: every probe is asked at ?ctx, so nothing here walks the")
      (println "    genlCx up-closure.")
      (println "  * a family this workload never reads.  The term index and the term roster are")
      (println "    read by terms / find-terms / find-sentexes and by no reasoning at all, so a")
      (println "    layout that moves them shows up here as bytes and as nothing else.")
      (println "  * the four KvIndexStore tallies on a layout that is not one — see the n/a")
      (println "    column above.")
      (println "  * a corpus too small for the layouts to differ, which reports that they do")
      (println "    not.  That is a reading of the corpus.")
      (println "  * the difference between two layouts that both estimate correctly.  The")
      (println "    q-error arm's corpus is 1:1, so it fails a layout and does not rank one.")
      (println "  * how much of a ratio is the layout.  Unification, belief filtering, the")
      (println "    record fetch and the rebuilt frontier are common to both arms of every")
      (println "    ratio above and divide out of it, so a row is a FLOOR on what the layout")
      (println "    contributes, never the whole of it.")
      (shutdown-agents))))
