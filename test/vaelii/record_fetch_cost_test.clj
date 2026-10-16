;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.record-fetch-cost-test
  "What an operation costs the **record store**, as counted fetches — the other index,
  and the one `assert_cost_test` cannot see.

  That gate counts `IndexStore` reads and this one counts `RecordStore` fetches, and the
  two come apart exactly where it hurts.  `kb/find-sentex-handle` asked the trie for a
  sentence's handle with `p/lookup`, whose wildcard token fans over every stored sentex of
  the same *shape*, and then read the record of each to find the one that was actually
  this sentence.  By `:reads` that is **one** index read and unimpeachable; by what it
  cost it was 2,779 µs against 13 µs per call at 800 candidates, because the eight hundred
  records behind those handles were paged one at a time.  On the durable store each of
  those is a positional slot read, a positional frame read and a nippy thaw past the LRU —
  orders above what any index read costs — and nothing counted them.

  `p/leaf-at` is the fix and the budgets below are the gate: a non-ground `handle-of`
  fetches **no** records, because the exact leaf of an α-renamed key holds only sentexes
  that share the sentence's shape and a KB of ground facts stores none there.  A change
  back to a matching read makes that number the size of the extent.

  ## Why a count, and why exact

  `assert_cost_test`'s reasons, unchanged: the quantity is an integer the engine computes,
  so there is no warm-up, no tail mean and no tolerance, and it reads the same on a loaded
  box.  Exact equality rather than a ceiling, so a legitimate improvement **fails this
  gate** and is re-pinned by the commit that earns it, carrying its own size as data.

  ## What it does not catch

  - **What a fetch costs.**  One `get-sentex` counts once whether it hits the disk store's
    LRU or pages a frame, and the two differ by orders.  This counts how many a caller
    asks for, which is the quantity a caller controls.
  - **A store's own internal reads.**  The tally sits on the protocol method, so
    `mark-premise` re-fetching inside the durable store is not counted where the RAM store
    reaching into its state map is not either — a tally that counted both would be a
    reading of which backend is running rather than of what the engine asked for.
  - **A configuration other than the shipped one**, and a backend other than `:memory`.
    Both are pinned below for `assert_cost_test`'s reasons."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

;; the instrument is process-wide, so a test that threw while collecting would hand the
;; next namespace a running tally
(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(def ^:private n
  "Operations per workload.  Large enough that a per-operation fetch lands as a
  three-digit difference, small enough that five workloads are a second or two."
  100)

(def ^:private fetch-space
  "The KB every workload runs on: in-RAM, its own space, the reference TMS — pinned for
  `assert_cost_test`'s reasons.  The **backend**, because a budget is a claim about one
  store and the durable one answers a fetch from an LRU whose contents depend on what ran
  before it; the **TMS**, because `VAELII_TEST_TMS=dense` walks a different support graph
  and fetches a different number of justifications."
  (-> tu/plain-memory-space
      (update :space conj ::record-fetch)
      (assoc :tms :reference)))

(defn- fresh [] (doto (v/open-kb fetch-space) (tu/clear-kb!)))

(defn- ind [prefix i] (symbol (str prefix i)))

;; ---- the workloads -------------------------------------------------------
;;
;; Each returns a **thunk**, so everything the workload needs in place is built before the
;; instrument starts and only the operation being priced is counted.

(defn- ground-assert
  "A binary fact of fresh individuals — the floor, and the one a fetch added to the assert
  path is clearest on."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'rfPlain (ind "RfA" i) (ind "RfB" i)) 'CxPerf {})))))

(defn- ground-handle-of
  "`handle-of` for a **ground** sentence that is stored.  A ground sentence keys the trie
  exactly, so its leaf holds its own handle alone and the first candidate is the answer —
  no record is read to tell it apart from anything."
  []
  (let [kb (fresh)]
    (dotimes [i n] (v/assert kb (list 'rfCand (ind "RfC" i) 'RfVal) 'CxPerf {}))
    (fn [] (dotimes [i n]
             (v/handle-of kb (list 'rfCand (ind "RfC" i) 'RfVal) 'CxPerf)))))

(defn- nonground-handle-of
  "**The workload the regression is priced by.**  `handle-of` for a sentence carrying a
  variable, over a KB holding `n` ground facts of exactly that shape.

  The pattern α-renames to `(rfCand ?0 RfVal)` and no sentex is stored at that key, so the
  exact leaf is empty and the answer is nil with **no record read at all**.  Asked as a
  *match* instead, the variable is a wildcard: the walk returns all `n` ground handles and
  the caller then reads a record apiece to find that none of them is this sentence.  That
  is the structure of the fix, and `n` is what this budget reads if it comes back."
  []
  (let [kb (fresh)]
    (dotimes [i n] (v/assert kb (list 'rfCand (ind "RfC" i) 'RfVal) 'CxPerf {}))
    (fn [] (dotimes [_ n]
             (v/handle-of kb '(rfCand ?x RfVal) 'CxPerf)))))

(defn- retraction
  "The `ground-assert` workload's facts, retracted in the order they arrived."
  []
  (let [kb (fresh)
        hs (mapv (fn [i] (v/assert kb (list 'rfPlain (ind "RfA" i) (ind "RfB" i)) 'CxPerf {}))
                 (range n))]
    (fn [] (doseq [h hs] (v/retract! kb h)))))

(defn- rule-fired
  "A fact arriving through one forward rule, so each assert stores **two** sentexes — the
  datum and the conclusion.  The derived half is where a fetch is easiest to add without
  noticing, since nothing a caller wrote is on that path: the chainer reads the datum's
  record, each candidate rule's record, and each matched fact's record again to place the
  conclusion."
  []
  (let [kb (fresh)]
    (v/assert kb (rules/rule-sentence ['(rfSrc ?x ?y)] '(rfDst ?x ?y))
              'CxPerf {:direction :forward :strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'rfSrc (ind "RfR" i) (ind "RfS" i)) 'CxPerf {})))))

;; ---- the budgets ---------------------------------------------------------
;;
;; Measured, not designed, at `n` = 100 — what the engine does today, written down so the
;; next change to any of these numbers is visible.  A failure prints the delta per kind.
;;
;; A kind is **absent rather than pinned at 0**, and that is the stronger claim: a kind a
;; workload never fetches is a key the tally never emits, so one fetch of it fails the
;; budget.  The two `handle-of` budgets are empty maps for exactly that reason, and they
;; are the point of the file.

(def ^:private budgets
  [{:name :ground-assert
    :build ground-assert
    ;; two sentex fetches per assert — the dedup probe and the settle's read of the
    ;; sentex it just stored — plus one provenance read
    :fetches {:sentex 200 :provenance 100}}

   {:name :ground-handle-of
    :build ground-handle-of
    ;; nothing: a ground key's leaf holds its own handle and `stored-at` returns it
    :fetches {}}

   {:name :nonground-handle-of
    :build nonground-handle-of
    ;; nothing, and this is the budget that would read 100 if the exact-leaf read went
    ;; back to a wildcard match
    :fetches {}}

   {:name :retraction
    :build retraction
    ;; one per retraction: the record the teardown is about
    :fetches {:sentex 100}}

   {:name :rule-fired
    :build rule-fired
    ;; six per assert, for two stored sentexes — the datum, the candidate rule, the
    ;; matched facts and the placement's re-reads.  The justification's content sort
    ;; reads the antecedent facts alone, not the rule it drops from the stored vector.
    :fetches {:sentex 600 :provenance 100}}])

;; ---- measuring -----------------------------------------------------------

(defn- measure
  "Run one workload under the instrument and return its fetch tally.  The KB is built
  inside the pinned configuration too: a corpus laid down under one reader and priced
  under another would be a workload nobody runs."
  [build]
  (tu/with-shipped-config
    (let [thunk (build)
          _     (prof/start)
          _     (thunk)
          snap  (prof/stop)]
      (into {} (:fetches snap)))))

(defn- delta-report
  "The kinds whose count moved, as a table — every kind either side names, so one that
  appeared from nowhere reads as `0 -> 100` rather than going missing."
  [expected actual]
  (->> (sort (into (set (keys expected)) (keys actual)))
       (keep (fn [k]
               (let [e (get expected k 0), a (get actual k 0)]
                 (when (not= e a)
                   (format "    %-16s %6d -> %-6d  (%+d)" (name k) e a (- a e))))))
       (str/join "\n")))

(deftest record-fetch-cost-is-what-it-was
  (doseq [{:keys [name build fetches]} budgets]
    (testing (str "the " (clojure.core/name name) " workload")
      (let [got (measure build)]
        (is (= fetches got)
            (format (str "%s: the record-fetch budget moved.\n%s\n"
                         "  If this change is intended, re-pin the number — the diff is "
                         "the change's own record-store cost.\n"
                         "  If it is not, an operation started paging records the index "
                         "was already answering for, which no `:reads` budget can see.")
                    (clojure.core/name name) (delta-report fetches got)))))))

(deftest a-nonground-handle-of-reads-the-exact-leaf-and-nothing-else
  ;; The claim above as a *shape* beside the constant: the fetch count must not track the
  ;; extent.  A wildcard match reads one record per stored sentex of the pattern's shape,
  ;; so it grows with the corpus where the exact leaf does not — which is the difference
  ;; between 13 µs and 2,779 µs at 800 candidates, and the reason this file exists.
  (tu/with-shipped-config
    (let [probe (fn [population]
                  (let [kb (fresh)]
                    (dotimes [i population]
                      (v/assert kb (list 'rfWide (ind "RfW" i) 'RfVal) 'CxPerf {}))
                    (prof/start)
                    (dotimes [_ 10] (v/handle-of kb '(rfWide ?x RfVal) 'CxPerf))
                    (let [snap (prof/stop)]
                      {:fetches (reduce + 0 (vals (:fetches snap)))
                       :answer  (v/handle-of kb '(rfWide ?x RfVal) 'CxPerf)})))
          narrow (probe 20)
          wide   (probe 200)]
      (is (nil? (:answer narrow)) "no sentex is stored at the α-renamed key")
      (is (zero? (long (:fetches narrow)))
          "an empty leaf is an empty candidate set, so nothing is paged to sift it")
      (is (= (:fetches narrow) (:fetches wide))
          (str "the fetch count must be flat in the extent of the pattern's shape — a "
               "wildcard read is back (" (:fetches narrow) " -> " (:fetches wide) ")")))))

(deftest a-declaration-pages-no-instance-it-does-not-believe
  ;; A dump imported `{:belief? :stored}` holds its records with the network empty until
  ;; a `recover`, and an install asserts its ontology into that state.  The clash pass
  ;; reads what a `genl` edge puts in question as the *believed* members below it, and it
  ;; paged each member's record before asking belief — every member of the type, since
  ;; none passes and so none spends the instance budget, so an install into a large
  ;; store paged the store.  Asked of the handle first, it pages none.
  (tu/with-shipped-config
    (let [probe (fn [population]
                  (let [dir (str (java.nio.file.Files/createTempDirectory
                                  "rf-stored" (make-array java.nio.file.attribute.FileAttribute 0)))
                        src (fresh)]
                    (dotimes [i population]
                      (v/assert src (list 'rf_dog (ind "RfD" i)) 'CxPerf {:strength :monotonic}))
                    (v/export! src dir {})
                    (let [kb (fresh)]
                      (v/import! kb dir {:belief? :stored})
                      (binding [v/*write-unrecovered?* true]
                        (v/assert kb '(disjoint rf_animal rf_plant) 'CxPerf {:strength :monotonic})
                        (prof/start)
                        (v/assert kb '(genl rf_dog rf_animal) 'CxPerf {:strength :monotonic})
                        (let [snap (prof/stop)]
                          {:fetches  (reduce + 0 (vals (:fetches snap)))
                           :believed (v/query? kb '(rf_dog RfD0) 'CxPerf)})))))
          narrow (probe 20)
          wide   (probe 200)]
      (is (false? (:believed wide)) "the imported members are stored and not believed")
      (is (= (:fetches narrow) (:fetches wide))
          (str "the edge's fetches must be flat in how many unbelieved members sit below "
               "it — a record is paged before its belief is asked again ("
               (:fetches narrow) " -> " (:fetches wide) ")")))))

(deftest a-genl-edge-pages-the-mint-roster-not-the-extent-below-it
  ;; A `genl` edge asks whether it made a minted membership redundant, and a member below
  ;; its sub-type can only be asked about a mint it holds.  It paged every membership below
  ;; the sub-type to learn its term and then looked the term up in the roster — during an
  ;; ontology install into a large store, half of a settle.  The edge's other reads page the
  ;; members too, for reasons of their own, so what is priced is the difference pruning
  ;; makes: with one mint in the roster, it must not grow with the members.
  (tu/with-shipped-config
    (let [probe (fn [population prune?]
                  (binding [checks/*assertive-arg-types?* true
                            checks/*prune-subsumed-mints?* prune?]
                    (let [kb (fresh)]
                      (v/assert kb '(genlCx CxPerf CxUniverse) 'CxUniverse)
                      (v/assert kb '(genl rf_owner thing) 'CxPerf {:strength :monotonic})
                      (v/assert kb '(arg rfOwns 1 rf_owner) 'CxPerf {:strength :monotonic})
                      (v/assert kb '(rfOwns RfA RfThing) 'CxPerf {})
                      (dotimes [i population]
                        (v/assert kb (list 'rf_sub (ind "RfM" i)) 'CxPerf {}))
                      (prof/start)
                      (v/assert kb '(genl rf_sub rf_super) 'CxPerf {:strength :monotonic})
                      (let [snap (prof/stop)]
                        {:fetches (reduce + 0 (vals (:fetches snap)))
                         :minted  (some? (v/handle-of kb '(rf_owner RfA) 'CxPerf))}))))
          pruning (fn [population]
                    (- (long (:fetches (probe population true)))
                       (long (:fetches (probe population false)))))]
      (is (:minted (probe 20 true)) "the declaration minted its membership, so the roster holds one")
      (is (= (pruning 20) (pruning 200))
          (str "what pruning pages on a genl edge must be flat in the members below it that "
               "hold no mint (" (pruning 20) " -> " (pruning 200) ")")))))

(deftest a-context-edge-pages-the-marked-facts-not-the-context
  ;; A `genlCx` edge equates what a functional predicate's facts force across the contexts
  ;; it joins, so its candidates are the facts of marked predicates in the widened
  ;; ancestor set.  It paged every fact in those contexts and then asked each for a mark:
  ;; an edge into a large store's context paged every fact of it, once per edge of an
  ;; ontology install.  The edge's other reads page the believed facts for reasons of
  ;; their own, so what is priced is the difference the declaration makes: with one
  ;; marked fact, it must not grow with the unmarked ones.
  (tu/with-shipped-config
    (let [probe (fn [population functional?]
                  (let [kb (fresh)]
                    (v/assert kb '(genlCx CxRfBig CxUniverse) 'CxUniverse)
                    (when functional?
                      (v/assert kb '(functional rfMotherOf) 'CxUniverse {:strength :monotonic}))
                    (v/assert kb '(rfMotherOf RfKid RfMum) 'CxRfBig {})
                    (dotimes [i population]
                      (v/assert kb (list 'rfLikes (ind "RfX" i) 'RfY) 'CxRfBig {}))
                    (prof/start)
                    (v/assert kb '(genlCx CxRfSmall CxRfBig) 'CxUniverse {:strength :monotonic})
                    (let [snap (prof/stop)]
                      (reduce + 0 (vals (:fetches snap))))))
          marking (fn [population] (- (long (probe population true)) (long (probe population false))))]
      (is (= (marking 20) (marking 200))
          (str "what the functional mark pages on a genlCx edge must be flat in the unmarked "
               "facts of the contexts it widens (" (marking 20) " -> " (marking 200) ")")))))

(deftest a-recover-walks-the-types-under-its-edges-once
  ;; A `recover` brings every record IN in one settle, so every `genl` edge asks at once
  ;; which mints it gave a new route, and each asked for the types under its own sub: a
  ;; closure walk and a count read per type, per edge.  Over a subtree many edges leave
  ;; from, that is the subtree once per edge, so a recover grows with edges times subtree
  ;; rather than with the taxonomy.  Each edge moved still costs pruning a read or so of
  ;; its own, so what is priced is what one more edge adds, and it must not grow with the
  ;; subtree under it.  The walk reads index counts, not records, so both are summed.
  (tu/with-shipped-config
    (let [probe (fn [depth edges prune?]
                  (binding [checks/*assertive-arg-types?* true
                            checks/*prune-subsumed-mints?* prune?]
                    (let [dir (str (java.nio.file.Files/createTempDirectory
                                    "rf-recover" (make-array java.nio.file.attribute.FileAttribute 0)))
                          src (fresh)]
                      (v/assert src '(genlCx CxPerf CxUniverse) 'CxUniverse)
                      (v/assert src '(genl rf_owner thing) 'CxPerf {:strength :monotonic})
                      (v/assert src '(arg rfOwns 1 rf_owner) 'CxPerf {:strength :monotonic})
                      (v/assert src '(rfOwns RfA RfThing) 'CxPerf {})
                      (dotimes [i depth]
                        (v/assert src (list 'genl (ind "rf_chain" i) (ind "rf_chain" (inc i)))
                                  'CxPerf {:strength :monotonic}))
                      (dotimes [i edges]
                        (v/assert src (list 'genl (ind "rf_chain" depth) (ind "rf_up" i))
                                  'CxPerf {:strength :monotonic}))
                      (v/export! src dir {})
                      ;; stored, not believed: the recover brings every record IN, as a
                      ;; build's finish stage does
                      (let [kb (fresh)]
                        (v/import! kb dir {:belief? :stored})
                        (prof/start)
                        (v/recover kb)
                        (let [snap (prof/stop)]
                          {:cost   (+ (reduce + 0 (vals (:fetches snap)))
                                      (reduce + 0 (vals (:reads snap))))
                           :minted (some? (v/handle-of kb '(rf_owner RfA) 'CxPerf))})))))
          pruning (fn [depth edges]
                    (- (long (:cost (probe depth edges true)))
                       (long (:cost (probe depth edges false)))))
          per-30  (fn [depth] (- (pruning depth 40) (pruning depth 10)))]
      (is (:minted (probe 5 10 true)) "the declaration minted its membership, so the roster holds one")
      (is (= (per-30 5) (per-30 20))
          (str "what thirty more edges add to pruning in a recover must not grow with the "
               "subtree under them (" (per-30 5) " -> " (per-30 20) ")")))))

(deftest a-recover-pages-the-defeats-not-the-store
  ;; A `recover`'s settle relabels every stored sentex, and the settle posts the re-check
  ;; each relabelled `defeat` owes its target.  What is priced is the difference one
  ;; stored defeat makes, and it must not grow with the facts beside it.
  (tu/with-shipped-config
    (let [probe (fn [population defeat?]
                  (let [kb (fresh)]
                    (dotimes [i population]
                      (v/assert kb (list 'rfPlain (ind "RfP" i) 'RfQ) 'CxPerf {}))
                    (when defeat?
                      (v/assert kb '(rf_denied RfN) 'CxPerf {})
                      (v/assert kb '(not (rf_denied RfN)) 'CxPerf {:strength :monotonic}))
                    (prof/start)
                    (v/recover kb)
                    (reduce + 0 (vals (:fetches (prof/stop))))))
          defeat (fn [population] (- (long (probe population true)) (long (probe population false))))]
      (is (= (defeat 20) (defeat 200))
          (str "what a stored defeat pages in a recover must be flat in the facts beside it ("
               (defeat 20) " -> " (defeat 200) ")")))))

(deftest a-recover-pages-the-mints-not-the-store
  ;; A `recover`'s settle brings every record IN, and the mint withdrawal asks the stored
  ;; mints the whole question when fewer are stored than the region holds.  What is priced
  ;; is the difference one stored mint makes, and it must not grow with the facts beside it.
  (tu/with-shipped-config
    (binding [checks/*assertive-arg-types?* true
              checks/*prune-subsumed-mints?* true]
      (let [probe (fn [population mint?]
                    (let [kb (fresh)]
                      (dotimes [i population]
                        (v/assert kb (list 'rfPlain (ind "RfP" i) 'RfQ) 'CxPerf {}))
                      (when mint?
                        (v/assert kb '(genl rf_owner thing) 'CxPerf {:strength :monotonic})
                        (v/assert kb '(arg rfOwns 1 rf_owner) 'CxPerf {:strength :monotonic})
                        (v/assert kb '(rfOwns RfA RfThing) 'CxPerf {}))
                      (prof/start)
                      (v/recover kb)
                      (reduce + 0 (vals (:fetches (prof/stop))))))
            mint  (fn [population] (- (long (probe population true)) (long (probe population false))))]
        (is (= (mint 20) (mint 200))
            (str "what a stored mint pages in a recover must be flat in the facts beside it ("
                 (mint 20) " -> " (mint 200) ")"))))))

(deftest the-instrument-counts-nothing-when-off
  ;; The budgets are only meaningful if the call sites add no work when nobody is collecting.
  (testing "a workload outside `start`/`stop` records no fetch"
    (is (false? (prof/profiling?)))
    ((ground-assert))
    (is (nil? (prof/snapshot)))))
