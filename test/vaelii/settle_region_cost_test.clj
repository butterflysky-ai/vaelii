;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-region-cost-test
  "What a settle costs, as call counts rather than durations, for `assert_cost_test`'s
  reason: a count is a property of the algorithm and a millisecond a property of the
  box (docs/nmtms.md, \"The runtime of a settle\").

  * The relabelled region is materialized at most `passes + 1` times: one delay per pass
    that reads it, and one at the finish.
  * A `genl` or `genlCx` edge no standing clash depends on re-derives none of them, and a
    `genlCx` edge reads no opposed body.  The bound is zero, which cannot drift upward; a
    plain fact retracted beside each edge is the control, and `clash_oracle_test` /
    `negation_oracle_test` hold the answers.
  * A `genl` edge no `functional` or `anti_symmetric` mark stands above hands no fact
    below it to a merge derivation and recomputes no arity candidate.
  * A definitional clash is re-asked at a reader only once the reader withdraws a ground.
  * The phase clock charges six buckets, and a settle's total is the sum of its own.
  * A settle reads the standing merges and `except`s only where they moved: a batch of
    merges reads the region once per settle, an un-merge re-examines its own class, a
    settle that moves no equality premise calls no supersession reconcile, and
    resolution's flip check reads no `except` root when the region is smaller.
  * The placement settle a `recover` closes with walks each subsumption its nogoods'
    routes climb, and each `genlCx` reach their placements see over, once per scope,
    however many nogoods share it.  A witness walk expands a bounded number of nodes off
    its target's down-closure, and what a placement pass holds does not grow with the
    targets' down-closures.
  * Nogoods placed below their ingredients over one shared subsumption read its routes
    once per pass.
  * A settle's tuple placement reads the `genl` edges' lower ends against the marks with
    one closure per marked predicate, however many edges the settle relabels.
  * The arity placement reads its candidates' functors against those lower ends with no
    closure walk, and the candidates a `genlCx` move reaches cut each predicate above
    them to the exact-length holders once."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private n
  "Standing dilemmas per workload, so a per-pair term shows as a three-digit count."
  60)

;; ---- how many times the region is materialized ---------------------------

(defn- region-reads
  "`jtms/touched` calls made while `f` runs.  The read is what materializes the region, so
  the read is what is counted; `jtms/revived`'s one-arity reads through this var too."
  [f]
  (let [calls (atom 0)
        orig  jtms/touched]
    (with-redefs [jtms/touched (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(def ^:private one-pass-reads
  "Region materializations of a one-pass settle: the finish's.  A pass forces its own
  delay only when something it reads needs the region, and a pass that owes nothing reads
  none."
  1)

(deftest a-settle-materializes-its-region-once-per-pass-and-once-at-the-finish
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        ;; one write outside the count, so no reading below is a class-loading first call
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (testing "a plain fact — nothing derived, nothing opposed, nothing merged"
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_plain SrmA) 'CxUniverse {})))))
        (testing "a forward rule firing"
          (v/assert-rule kb ['(srm_trig ?x)] '(srm_concl ?x) 'CxUniverse {:direction :forward})
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_trig SrmB) 'CxUniverse {}))))
          (is (v/ask? kb '(srm_concl SrmB) 'CxUniverse) "the firing must have placed"))
        (testing "and a retraction"
          (let [h (v/handle-of kb '(srm_plain SrmA) 'CxUniverse)]
            (is (= one-pass-reads (region-reads #(v/retract! kb h)))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-batch-is-charged-per-settle-and-not-per-write
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (is (= one-pass-reads
               (region-reads #(v/with-deferred-settle kb
                                (dotimes [i 50]
                                  (v/assert kb (list 'srm_batch (symbol (str "SrmZ" i)))
                                            'CxUniverse {})))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-defeat-takes-two-passes-and-a-revival-one
  ;; a negation pair is placed in the pass that discovers it, and the placed sentexes are
  ;; chained in a second; the target a removed defeat gives back is not re-chained, so a
  ;; revival takes one pass.  Each pass reads the region, as the finish does: the growth
  ;; term is the pass, not the belief move
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_neg SrmX) 'CxUniverse {})
        (testing "the defeat takes two passes, each reading the region"
          (is (= (+ 2 one-pass-reads)
                 (region-reads #(v/assert kb '(not (srm_neg SrmX)) 'CxUniverse
                                          {:strength :monotonic}))))
          (is (not (v/ask? kb '(srm_neg SrmX) 'CxUniverse)) "the default must have lost"))
        (testing "the revival takes one pass"
          (let [h (v/handle-of kb '(not (srm_neg SrmX)) 'CxUniverse)]
            (is (= one-pass-reads (region-reads #(v/retract! kb h)))))
          (is (v/ask? kb '(srm_neg SrmX) 'CxUniverse) "the default must be believed again")))
      (finally (tu/clear-kb! kb)))))

;; ---- the clash memo ------------------------------------------------------

(defn- clash-kb
  "n individuals each holding two separated types, so the KB carries n standing
  definitional dilemmas — plus the two victims: one `genl` edge with nothing above or
  below it, and one plain fact."
  [kb]
  (v/assert kb '(disjoint srca_t srcb_t) 'CxUniverse {:strength :monotonic})
  (dotimes [i n]
    (let [x (symbol (str "SRC" i))]
      (v/assert kb (list 'srca_t x) 'CxUniverse {})
      (v/assert kb (list 'srcb_t x) 'CxUniverse {})))
  (v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(src_plain SrcTarget) 'CxUniverse {})
  kb)

(defn- nogood-reads
  "Terms whose membership nogoods `membership/term-nogoods` derives while `f` runs: a
  settle re-derives a term's nogoods only through it."
  [f]
  (let [terms (atom [])
        orig  @#'membership/term-nogoods]
    (with-redefs [membership/term-nogoods
                  (fn [tax w c x] (swap! terms conj x) (orig tax w c x))]
      (f))
    @terms))

(deftest a-genl-edge-elsewhere-re-derives-no-standing-clash
  (let [kb (tu/fresh)]
    (try
      (clash-kb kb)
      (is (= n (count (v/contradictions kb)))
          "the standing set is standing, or the counts below are about an empty candidate index")
      (testing "retracting the lone genl edge derives no term's nogoods"
        (let [h (v/handle-of kb '(genl srcvictim_t srctop_t) 'CxUniverse)]
          (is (empty? (nogood-reads #(v/retract! kb h))))))
      (testing "and asserting it back derives none either"
        (is (empty? (nogood-reads
                     #(v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse
                                {:strength :monotonic})))))
      (testing "the control: a plain fact leaving is already free"
        (let [h (v/handle-of kb '(src_plain SrcTarget) 'CxUniverse)]
          (is (empty? (nogood-reads #(v/retract! kb h))))))
      (testing "an edge above a standing type re-derives each term holding it"
        (let [e '(genl srca_t srcabove_t)]
          (is (= n (count (set (nogood-reads #(v/assert kb e 'CxUniverse
                                                        {:strength :monotonic}))))))
          (v/retract! kb (v/handle-of kb e 'CxUniverse))))
      (is (= n (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

;; ---- the negation pairs -------------------------------------------------

(defn- negation-kb
  "n P/¬P dilemmas in one context and n across two contexts a third sees, sharing no
  body, plus the two victims: one `genlCx` edge with nothing below it, and one plain fact.
  No separation, so the clash memo is not asked."
  [kb]
  (doseq [[c up] '[[CxSrL CxUniverse] [CxSrR CxUniverse] [CxSrJ CxSrL] [CxSrJ CxSrR]]]
    (v/assert kb (list 'genlCx c up) 'CxUniverse {}))
  (dotimes [i n]
    (let [pr (symbol (str "srneg" i))
          px (symbol (str "srnegx" i))
          x  (symbol (str "SRN" i))]
      (v/assert kb (list pr x) 'CxUniverse {})
      (v/assert kb (list 'not (list pr x)) 'CxUniverse {})
      (v/assert kb (list px x) 'CxSrL {})
      (v/assert kb (list 'not (list px x)) 'CxSrR {})))
  (v/assert kb '(genlCx CxSrVictim CxUniverse) 'CxUniverse {})
  (v/assert kb '(sr_plain SrTarget) 'CxUniverse {})
  kb)

(defn- body-reads
  "Opposed bodies read off the index while `f` runs: `negation/polarity-handles` is the only
  site that reads one."
  [f]
  (let [calls (atom 0)
        orig  @#'negation/polarity-handles]
    (with-redefs [negation/polarity-handles (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-genlCx-edge-elsewhere-reads-no-opposed-body
  (let [kb (tu/fresh)]
    (try
      (negation-kb kb)
      (is (= (* 2 n) (count (v/contradictions kb)))
          "the standing set is standing, or the counts below are about an empty index")
      (testing "retracting the lone genlCx edge reads no body"
        (let [h (v/handle-of kb '(genlCx CxSrVictim CxUniverse)
                             'CxUniverse)]
          (is (zero? (body-reads #(do (v/retract! kb h) (v/contradictions kb)))))))
      (testing "and asserting it back reads none either"
        (is (zero? (body-reads
                    #(do (v/assert kb '(genlCx CxSrVictim CxUniverse) 'CxUniverse {})
                         (v/contradictions kb))))))
      (testing "the control: a plain fact leaving is already free"
        (let [h (v/handle-of kb '(sr_plain SrTarget) 'CxUniverse)]
          (is (zero? (body-reads #(v/retract! kb h))))))
      (is (= (* 2 n) (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

;; ---- a genl edge's merge sweeps ------------------------------------------

(defn- edge-sweep-calls
  "Facts handed to the two merge derivations, and arity recomputes, while `f` runs."
  [f]
  (let [calls (atom {})
        vs    [#'special/derive-functional-equalities #'special/derive-antisymmetric-equalities
               #'arity/recompute-arity]]
    (with-redefs-fn (into {} (map (fn [v] (let [orig @v]
                                            [v (fn [& args]
                                                 (swap! calls update (:name (meta v)) (fnil inc 0))
                                                 (apply orig args))])))
                          vs)
      f)
    @calls))

(deftest a-genl-edge-under-no-merge-mark-re-derives-no-fact-below-it
  ;; each fact below the edge is an exact-arity membership, so a fact handed back to every
  ;; candidate family recomputes its predicate's arity candidates
  (let [kb   (tu/fresh)
        m    {:strength :monotonic}
        edge (fn [top] (edge-sweep-calls
                        #(v/assert kb (list 'genl 'sre_rel top) 'CxUniverse m)))]
    (try
      (v/assert kb '(functional sreFn) 'CxUniverse m)
      (v/assert kb '(anti_symmetric sreAnti) 'CxUniverse m)
      (v/assert kb '(genl binary_predicate sre_rel) 'CxUniverse m)
      (v/assert kb '(binary_predicate sreRel0) 'CxUniverse m)
      (let [small (edge 'sre_top1)]
        (dotimes [i n]
          (v/assert kb (list 'binary_predicate (symbol (str "sreRel" (inc i)))) 'CxUniverse m))
        (is (= small (edge 'sre_top2)) "flat in the facts below the edge")
        (is (not (contains? small 'recompute-arity)) "the edge brings no length"))
      (finally (tu/clear-kb! kb)))))

(defn- seeds-sent
  "Chaining seeds `special/subsumption-seeds` returns while `f` runs."
  [f]
  (let [sent (atom 0)
        orig special/subsumption-seeds]
    (with-redefs [special/subsumption-seeds (fn [kb s] (let [r (orig kb s)]
                                                         (swap! sent + (count r))
                                                         r))]
      (f))
    @sent))

(deftest a-genl-edge-under-no-rule-reading-above-it-seeds-no-fact-below-it
  ;; the rule reads a predicate the edge does not reach, so the roster is not empty
  (let [kb   (tu/fresh)
        m    {:strength :monotonic}
        edge (fn [top] (seeds-sent #(v/assert kb (list 'genl 'sss_low top) 'CxUniverse m)))]
    (try
      (v/assert kb '(implies (sss_else ?x) (sss_seen ?x)) 'CxUniverse {:direction :forward})
      (v/assert kb '(sss_low SssA0) 'CxUniverse m)
      (let [small (edge 'sss_top1)]
        (dotimes [i n]
          (v/assert kb (list 'sss_low (symbol (str "SssA" (inc i)))) 'CxUniverse m))
        (is (zero? small))
        (is (zero? (edge 'sss_top2)) "flat in the facts below the edge")
        (v/assert kb '(implies (sss_top3 ?x) (sss_seen ?x)) 'CxUniverse {:direction :forward})
        (is (= (inc n) (edge 'sss_top3)) "a rule above the edge is seeded every fact below it")
        (is (seq (v/sentexes-matching kb (list 'sss_seen (symbol (str "SssA" n))) 'CxUniverse))))
      (finally (tu/clear-kb! kb)))))

;; ---- the phase clock -----------------------------------------------------

(deftest the-phase-clock-partitions-each-settle-into-its-buckets
  (let [kb (tu/fresh)]
    (try
      (phases/start)
      (v/assert kb '(srp_fact SrpA) 'CxUniverse {})
      (v/assert kb '(not (srp_fact SrpA)) 'CxUniverse {})
      (let [{:keys [run settles]} (phases/stop)]
        (is (= #{:belief :discovery :chaining :finish :glue :outside}
               (set (keys run))))
        (is (seq settles))
        (doseq [s settles]
          (is (= (:total s) (reduce + (vals (:nanos s)))))
          (is (pos? (:passes s)))))
      (finally (phases/stop) (tu/clear-kb! kb)))))

;; ---- the scans a settle runs over a standing population ---------------------

(defn- calls-to
  "Calls made to the var `v` while `f` runs, each call's arguments kept."
  [v f]
  (let [calls (atom [])
        orig  @v]
    (with-redefs-fn {v (fn [& args] (swap! calls conj args) (apply orig args))} f)
    @calls))

(defn- merge-kb
  "`kb` holding `n` standing `sameAs` merges, each displacing one fact of its own, asserted
  under one deferred settle.  Returns the displaced facts' handles."
  [kb n]
  (let [hs (volatile! [])]
    (v/with-deferred-settle kb
      (dotimes [i n]
        (vswap! hs conj (v/assert kb (list 'srmBorn (symbol (str "SrmHi" i)) 'SrmPlace)
                                  'CxUniverse {}))
        (v/assert kb (list 'sameAs (symbol (str "SrmAa" i)) (symbol (str "SrmHi" i)))
                  'CxUniverse {})))
    @hs))

(deftest a-batch-of-merges-reads-the-region-once-per-settle
  ;; the write path's supersession reconcile leaves the window to the batch's settle
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (let [reads (fn [tag n]
                      (region-reads
                       #(v/with-deferred-settle kb
                          (dotimes [i n]
                            (v/assert kb (list 'srmBorn (symbol (str "SrmZ" tag i)) 'SrmPlace)
                                      'CxUniverse {})
                            (v/assert kb (list 'sameAs (symbol (str "SrmC" tag i))
                                               (symbol (str "SrmZ" tag i)))
                                      'CxUniverse {})))))]
          ;; each merge displaces its fact: `SrmC…` sorts first and represents the class
          (is (= (reads "a" 1) (reads "b" 20)))))
      (finally (tu/clear-kb! kb)))))

(deftest an-un-merge-re-examines-the-class-it-split-and-no-standing-merge
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [standing (set (merge-kb kb n))
              f        (v/assert kb '(srmBorn SrmVHi SrmPlace) 'CxUniverse {})
              e        (v/assert kb '(sameAs SrmVAa SrmVHi) 'CxUniverse {})
              examined (into #{} (map #(nth % 2))
                             (calls-to #'special/displacement #(v/retract! kb e)))]
          (is (contains? examined f) "the split class's own displaced fact is re-examined")
          (is (empty? (set/intersection standing examined)))
          (is (v/ask? kb '(srmBorn SrmVHi SrmPlace) 'CxUniverse)
              "the spelling the un-merge gave back is believed")))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-hands-the-belief-reconcile-no-supersession-it-did-not-move
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [standing (set (merge-kb kb n))
              handed   (into #{} (comp (map second) cat)
                             (calls-to #'special/reconcile-belief-change
                                       #(v/assert kb '(srm_plain SrmUnrelated) 'CxUniverse {})))]
          (is (every? #(jtms/superseded? (reasoning/tms kb) %) standing))
          (is (empty? (set/intersection standing handed)))))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-that-moves-no-equality-premise-calls-no-supersession-reconcile
  ;; the write path reconciles what a stored or removed sentence moves
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (merge-kb kb n)
        (is (empty? (calls-to #'special/refresh-supersessions
                              #(v/assert kb '(srm_plain SrmNoMerge) 'CxUniverse {}))))
        (is (empty? (calls-to #'special/refresh-supersessions
                              #(v/retract! kb (v/handle-of kb '(srm_plain SrmNoMerge)
                                                           'CxUniverse))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-over-standing-excepts-reads-no-except-root-when-its-region-is-smaller
  ;; no resolution defeats an `except`, so the settle reads no `except` root at all
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (dotimes [i n]
          (let [h (v/assert kb (list 'srm_decoy (symbol (str "SrmD" i))) 'CxUniverse
                            {:strength :monotonic})]
            (v/assert kb (list 'except (sx/sentex-handle h)) 'CxUniverse {:strength :monotonic})))
        (is (empty? (filter #(= sx/except-functor (second %))
                            (calls-to #'reads/believed-with-functor
                                      #(v/assert kb '(srm_plain SrmAfterExcepts) 'CxUniverse {}))))))
      (finally (tu/clear-kb! kb)))))

;; ---- the placement settle a recover closes with -----------------------------

(deftest a-recovers-placement-settle-walks-each-subsumption-once-per-vantage
  ;; CxUniverse  (disjoint srw_a srw_b) M, srw_a2 → srw_a1 → srw_a and srw_b2 → srw_b1 →
  ;; srw_b, and n terms each in srw_a2 and srw_b2: n membership nogoods, every one placed
  ;; over the same two subsumptions from the one vantage.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/with-deferred-settle kb
          (v/assert kb '(disjoint srw_a srw_b) 'CxUniverse {:strength :monotonic})
          (doseq [[s u] '[[srw_a1 srw_a] [srw_a2 srw_a1] [srw_b1 srw_b] [srw_b2 srw_b1]]]
            (v/assert kb (list 'genl s u) 'CxUniverse {}))
          (dotimes [i n]
            (let [x (symbol (str "SrwT" i))]
              (v/assert kb (list 'srw_a2 x) 'CxUniverse {})
              (v/assert kb (list 'srw_b2 x) 'CxUniverse {}))))
        (let [walks (into [] (comp (map #(vec (take 4 (rest %)))) (filter #(= :genl (first %))))
                          (calls-to #'tax/reach-support #(v/recover kb)))]
          (is (= n (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= #{[:genl 'srw_a2 'srw_a 'CxUniverse] [:genl 'srw_b2 'srw_b 'CxUniverse]}
                 (set walks)))
          (is (= 2 (count walks)))))
      (finally (tu/clear-kb! kb)))))

(deftest a-recovers-placement-settle-walks-each-genlCx-reach-once
  ;; CxSrvR → CxUniverse, (disjoint srv_a srv_b) M and srv_a1 → srv_a, srv_b1 → srv_b in
  ;; CxUniverse, and n terms each in srv_a1 and srv_b1 in CxSrvR: n membership nogoods
  ;; placed in CxSrvR, each seeing its ingredients in CxUniverse over the one edge.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(genlCx CxSrvR CxUniverse) 'CxUniverse {:strength :monotonic})
        (v/with-deferred-settle kb
          (v/assert kb '(disjoint srv_a srv_b) 'CxUniverse {:strength :monotonic})
          (v/assert kb '(genl srv_a1 srv_a) 'CxUniverse {})
          (v/assert kb '(genl srv_b1 srv_b) 'CxUniverse {})
          (dotimes [i n]
            (let [x (symbol (str "SrvT" i))]
              (v/assert kb (list 'srv_a1 x) 'CxSrvR {})
              (v/assert kb (list 'srv_b1 x) 'CxSrvR {}))))
        ;; the five-argument arity calls the six-argument one through the var
        (let [walks (into [] (comp (filter #(= 6 (count %))) (map #(vec (take 4 (rest %))))
                                   (filter #(= :genlCx (first %))))
                          (calls-to #'tax/reach-support #(v/recover kb)))]
          (is (= n (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= [[:genlCx 'CxSrvR 'CxUniverse 'CxSrvR]] walks))))
      (finally (tu/clear-kb! kb)))))

(deftest a-witness-walk-expands-a-bounded-number-of-nodes-off-the-targets-down-closure
  ;; CxUniverse  srp_sub → srp_mid → srp_top, and srp_sub → srp_side_i for 300 sides, none
  ;; of them under srp_top.  The sides sort after srp_mid, so a breadth-first walk from
  ;; srp_sub reaches every side before srp_top.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/with-deferred-settle kb
          (v/assert kb '(genl srp_sub srp_mid) 'CxUniverse {})
          (v/assert kb '(genl srp_mid srp_top) 'CxUniverse {})
          (dotimes [i 300]
            (v/assert kb (list 'genl 'srp_sub (symbol (str "srp_side_" i))) 'CxUniverse {})))
        (let [tx    (reasoning/taxonomy kb)
              path  (atom nil)
              sorts (count (calls-to #'nm/sort-by-content-key
                                     #(reset! path (tax/reach-support tx :genl 'srp_sub 'srp_top 'CxUniverse))))]
          (is (= [(v/handle-of kb '(genl srp_mid srp_top) 'CxUniverse)
                  (v/handle-of kb '(genl srp_sub srp_mid) 'CxUniverse)]
                 (mapv first @path)))
          (is (< sorts 100))))
      (finally (tu/clear-kb! kb)))))

(deftest a-tuple-placement-reads-genl-ends-against-the-marks-with-a-closure-per-mark
  ;; CxUniverse  srtFnSub2 → srtFnSub1 → srtFn under a `functional`, `functionalInArg` and
  ;; `irreflexive` mark, two srtFnSub2 tuples one determinant apart, and 3n `genl` edges
  ;; between collections in the same settle: the placement reads every edge's lower end.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [inside? (atom false)
              walks   (atom 0)
              ends    (atom #{})
              mark    @#'chain/mark-ends
              closure @#'tax/closure-of]
          (with-redefs-fn {#'chain/mark-ends (fn [& args]
                                               (reset! inside? true)
                                               (try (let [r (apply mark args)] (swap! ends into r) r)
                                                    (finally (reset! inside? false))))
                           #'tax/closure-of  (fn [& args]
                                               (when @inside? (swap! walks inc))
                                               (apply closure args))}
            #(v/with-deferred-settle kb
               (doseq [s '[(functional srtFn) (functionalInArg srtFn 2) (irreflexive srtFn)
                           (genl srtFnSub1 srtFn) (genl srtFnSub2 srtFnSub1)]]
                 (v/assert kb s 'CxUniverse {:strength :monotonic}))
               (dotimes [i (* 3 n)]
                 (v/assert kb (list 'genl (symbol (str "srt_c" (inc i))) (symbol (str "srt_c" (quot i 3))))
                           'CxUniverse {}))
               (v/assert kb '(srtFnSub2 SrtA SrtB) 'CxUniverse {})
               (v/assert kb '(srtFnSub2 SrtA SrtC) 'CxUniverse {})))
          (is (= 1 (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= '#{srtFn srtFnSub1 srtFnSub2} @ends))
          ;; one closure, the marked predicate's subtypes, where each end built its own
          (is (= 1 @walks))))
      (finally (tu/clear-kb! kb)))))

(deftest an-arity-placement-reads-its-candidates-against-genl-ends-with-no-closure-walk
  ;; CxUniverse  (arity sraRel 2) and k sub-predicates of sraRel, each holding a ternary
  ;; tuple, and 3n `genl` edges between collections in the same settle: the arity
  ;; placement reads every candidate's functor against every edge's lower end.
  (let [kb (tu/isolated-fresh)
        k  12]
    (try
      (tu/with-shipped-config
        (let [inside? (atom false)
              walks   (atom 0)
              found   (atom #{})
              under   @#'arity/members-under
              closure @#'tax/closure-of]
          (with-redefs-fn {#'arity/members-under (fn [& args]
                                                   (reset! inside? true)
                                                   (try (let [r (apply under args)] (swap! found into r) r)
                                                        (finally (reset! inside? false))))
                           #'tax/closure-of      (fn [& args]
                                                   (when @inside? (swap! walks inc))
                                                   (apply closure args))}
            #(v/with-deferred-settle kb
               (v/assert kb '(arity sraRel 2) 'CxUniverse {:strength :monotonic})
               (dotimes [i k]
                 (let [q (symbol (str "sraSub" i))]
                   (v/assert kb (list 'genl q 'sraRel) 'CxUniverse {:strength :monotonic})
                   (v/assert kb (list q 'SraA 'SraB 'SraC) 'CxUniverse {})))
               (dotimes [i (* 3 n)]
                 (v/assert kb (list 'genl (symbol (str "sra_c" (inc i))) (symbol (str "sra_c" (quot i 3))))
                           'CxUniverse {}))))
          (is (= k (count @found)))
          (is (zero? @walks))))
      (finally (tu/clear-kb! kb)))))

(deftest the-candidates-a-move-reaches-cut-each-predicate-above-them-once
  ;; CxSrbR → CxUniverse, (arity srbTop 2) in CxSrbR over a chain of 20 predicates in
  ;; CxUniverse, and k sub-predicates of the chain's foot, each holding a ternary tuple:
  ;; the candidates a move to CxSrbR reaches climb the same chain.
  (let [kb (tu/isolated-fresh)
        k  12
        l  20]
    (try
      (tu/with-shipped-config
        (v/assert kb '(genlCx CxSrbR CxUniverse) 'CxUniverse {:strength :monotonic})
        (v/with-deferred-settle kb
          (v/assert kb '(arity srbTop 2) 'CxSrbR {:strength :monotonic})
          (dotimes [i l]
            (v/assert kb (list 'genl (symbol (str "srbL" (inc i))) (if (zero? i) 'srbTop (symbol (str "srbL" i))))
                      'CxUniverse {:strength :monotonic}))
          (dotimes [i k]
            (let [q (symbol (str "srbSub" i))]
              (v/assert kb (list 'genl q (symbol (str "srbL" l))) 'CxUniverse {:strength :monotonic})
              (v/assert kb (list q 'SrbA 'SrbB 'SrbC) 'CxUniverse {}))))
        (let [tax  (reasoning/taxonomy kb)
              c    (decide/synced kb)
              hits (atom nil)
              cuts (count (calls-to #'arity/exact-bound?
                                    #(reset! hits (arity/reached kb (decide/write-view tax) c #{'CxSrbR}))))]
          (is (= k (count @hits)))
          ;; each predicate on the chain once, and each candidate's own functor
          (is (<= cuts (+ k l 2)) (str cuts " exact-length probes"))))
      (finally (tu/clear-kb! kb)))))

(defn- held-by-passes
  "The terms each reading pass's neighbour cache holds once its walks return
  (`tax/with-neighbours`), over the settle of `f`."
  [f]
  (let [held (atom [])
        orig @#'tax/with-neighbours]
    (with-redefs-fn {#'tax/with-neighbours
                     (fn [nc g] (let [r (orig nc g)]
                                  (swap! held conj (transduce (comp (map val) (filter coll?) (map count)) + @nc))
                                  r))}
      f)
    @held))

(deftest an-arity-placement-pass-holds-no-targets-down-closure
  ;; CxUniverse  (arity shaTop_t 2) on 3 tops, each over `fans` predicates of its own,
  ;; shaMid under every top, and 2 predicates under shaMid and under 70 sides that sort
  ;; after it, each holding a ternary tuple: every route walk from one passes its first
  ;; 64 expansions and prunes, and what the pass holds does not grow with the fans.
  (let [held (fn [fans]
               (let [kb (tu/isolated-fresh)
                     m  {:strength :monotonic}]
                 (try
                   (tu/with-shipped-config
                     (let [h (held-by-passes
                              #(v/with-deferred-settle kb
                                 (dotimes [t 3]
                                   (let [top (symbol (str "shaTop" t))]
                                     (v/assert kb (list 'arity top 2) 'CxUniverse m)
                                     (v/assert kb (list 'genl 'shaMid top) 'CxUniverse m)
                                     (dotimes [j fans]
                                       (v/assert kb (list 'genl (symbol (str "shaTop" t "F" j)) top) 'CxUniverse m))))
                                 (dotimes [i 2]
                                   (let [q (symbol (str "shaQ" i))]
                                     (v/assert kb (list 'genl q 'shaMid) 'CxUniverse m)
                                     (dotimes [j 70]
                                       (v/assert kb (list 'genl q (symbol (str "shaSide" j))) 'CxUniverse m))
                                     (v/assert kb (list q 'ShaA 'ShaB 'ShaC) 'CxUniverse {})))))]
                       [(count (v/sentexes-with-functor kb 'contradicts)) (reduce + h)]))
                   (finally (tu/clear-kb! kb)))))
        [n10 w10] (held 10)
        [n40 w40] (held 40)]
    (is (= 2 n10 n40))
    (is (= w10 w40) (str w10 " terms held over 10 fans, " w40 " over 40"))))

(deftest descent-placements-over-a-shared-subsumption-read-its-routes-once
  ;; CxSrdD → CxUniverse, (arity srdTop 2) and n ternary srdQ tuples in CxUniverse, and
  ;; (genl srdQ srdTop) in CxSrdD alone: CxUniverse sees no route, so each of the n arity
  ;; nogoods is placed below it, in CxSrdD, over the one subsumption.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(genlCx CxSrdD CxUniverse) 'CxUniverse {:strength :monotonic})
        (let [searches (count (calls-to #'tax/reach-supports
                                        #(v/with-deferred-settle kb
                                           (v/assert kb '(arity srdTop 2) 'CxUniverse {:strength :monotonic})
                                           (v/assert kb '(genl srdQ srdTop) 'CxSrdD {:strength :monotonic})
                                           (dotimes [i n]
                                             (v/assert kb (list 'srdQ (symbol (str "SrdA" i)) 'SrdB 'SrdC)
                                                       'CxUniverse {})))))
              placed   (v/sentexes-with-functor kb 'contradicts)]
          (is (= n (count placed)))
          (is (every? #(= 'CxSrdD (:context %)) placed))
          ;; one search per placement pass that reads them, where each nogood read its own
          (is (<= searches 2) (str searches " route searches for " n " nogoods"))))
      (finally (tu/clear-kb! kb)))))
