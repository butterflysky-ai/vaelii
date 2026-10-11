;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.closure-join-test
  "Forward chaining over a `genl` or `genlCx` antecedent reads the cached closure.

  A query answers `(genl t t)` and a pair two edges apart from the closure
  (`TransitivityProver`).  A forward rule with the same literal in its antecedent answers
  it the same way whenever the join has bound an end: the reflexive pair and the pair no
  edge states both fire, the firing names the edges of one path, and an arriving or
  departing edge re-joins the rule.  With both ends open the stored edges answer alone."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(defn- pair-rule
  "*A pair whose first member is below its second qualifies* — both ends of the `genl`
  literal bound by the first antecedent."
  [pairOf qualifies]
  (list 'set/forwardRule
        (list 'implies (list 'and (list pairOf '?a '?b) (list 'genl '?a '?b))
              (list qualifies '?a '?b))))

(defn- holds? [kb s ctx] (boolean (v/ask? kb s ctx)))

(tu/deftest-kb a-join-that-binds-both-ends-reads-the-reflexive-pair
  (tu/with-terms [pairOf qualifies pug]
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list pairOf pug pug) U)
    (is (holds? kb (list 'genl pug pug) U) "the query answers the reflexive pair")
    (is (holds? kb (list qualifies pug pug) U) "and the forward join agrees")
    (testing "the reflexive pair rests on no edge"
      (let [h     (v/handle-of kb (list qualifies pug pug) U)
            named (set (map :sentence (tree-seq map? #(mapcat :because (:support %))
                                                (v/why kb h))))]
        (is (= #{(list qualifies pug pug) (list pairOf pug pug)} named))))))

(tu/deftest-kb a-join-that-binds-both-ends-reads-a-pair-two-edges-apart
  (tu/with-terms [pairOf qualifies pug dog mammal]
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list 'genl pug dog) U)
    (let [far (v/assert kb (list 'genl dog mammal) U)]
      (v/assert kb (list pairOf pug mammal) U)
      (is (holds? kb (list qualifies pug mammal) U))
      (testing "the firing names the edges of the path"
        (let [h     (v/handle-of kb (list qualifies pug mammal) U)
              named (set (tree-seq coll? seq (v/why kb h)))]
          (is (contains? named far))))
      (testing "and a path edge going takes the conclusion"
        (v/retract! kb far)
        (is (nil? (v/handle-of kb (list qualifies pug mammal) U)))))))

(tu/deftest-kb a-join-that-binds-one-end-reads-that-ends-closure
  (tu/with-terms [picked qualifies pug dog mammal]
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) U)
    (testing "the lower end bound: every supertype, the term itself included"
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list picked '?a) (list 'genl '?a '?b))
                               (list qualifies '?a '?b)))
                U)
      (v/assert kb (list picked pug) U)
      (is (= #{pug dog mammal}
             (set (map '?y (v/query kb (list qualifies pug '?y) U))))
          "the same set the query answers")
      (is (= (set (map '?y (v/query kb (list 'genl pug '?y) U)))
             (set (map '?y (v/query kb (list qualifies pug '?y) U))))))))

(tu/deftest-kb a-join-that-binds-the-upper-end-reads-its-subtypes
  (tu/with-terms [picked qualifies pug dog mammal]
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) U)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list picked '?b) (list 'genl '?a '?b))
                             (list qualifies '?a '?b)))
              U)
    (v/assert kb (list picked mammal) U)
    (is (= #{pug dog mammal} (set (map '?x (v/query kb (list qualifies '?x mammal) U)))))))

(tu/deftest-kb a-join-with-both-ends-open-reads-the-stored-edges
  ;; The closure over every pair is quadratic in a chain's length, so an antecedent with
  ;; neither end bound is answered by the stored edges, as a transitive predicate's is.
  ;; Read off storage rather than `query`: `set/forwardRule` runs backward too, and a
  ;; backward proof reads the closure the forward join declines.
  (tu/with-terms [qualifies pug dog mammal]
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) U)
    (v/assert kb (list 'set/forwardRule (list 'implies (list 'genl '?a '?b) (list qualifies '?a '?b)))
              U)
    (let [stored? (fn [x y] (some? (v/handle-of kb (list qualifies x y) U)))]
      (is (stored? pug dog))
      (is (stored? dog mammal))
      (is (not (stored? pug mammal)) "no edge states the far pair")
      (is (not (stored? pug pug)) "no edge states the reflexive pair"))))

(tu/deftest-kb the-closure-join-reads-the-same-whichever-ingredient-arrived-last
  (let [orders {"rule, pair, near edge, far edge" [:rule :pair :near :far]
                "rule, pair, far edge, near edge" [:rule :pair :far :near]
                "edges, pair, rule"               [:near :far :pair :rule]
                "edges, rule, pair"               [:far :near :rule :pair]}]
    (doseq [[label order] orders]
      (testing label
        (tu/with-terms [pairOf qualifies pug dog mammal]
          (let [step {:rule #(v/assert kb (pair-rule pairOf qualifies) U)
                      :pair #(v/assert kb (list pairOf pug mammal) U)
                      :near #(v/assert kb (list 'genl pug dog) U)
                      :far  #(v/assert kb (list 'genl dog mammal) U)}]
            (doseq [k order] ((step k)))
            (is (holds? kb (list qualifies pug mammal) U))))))))

(tu/deftest-kb a-second-path-re-derives-what-a-departed-edge-licensed
  (tu/with-terms [pairOf qualifies pug dog pet mammal]
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list pairOf pug mammal) U)
    (let [edges (mapv #(v/assert kb % U)
                      [(list 'genl pug dog) (list 'genl dog mammal)
                       (list 'genl pug pet) (list 'genl pet mammal)])]
      (is (holds? kb (list qualifies pug mammal) U))
      (v/retract! kb (edges 1))
      (is (holds? kb (list qualifies pug mammal) U) "the path through pet still licenses it")
      (v/retract! kb (edges 3))
      (is (not (holds? kb (list qualifies pug mammal) U)) "and with both paths gone, nothing does"))))

(tu/deftest-kb the-conclusion-lands-where-the-path-is-visible
  (tu/with-terms [pairOf qualifies pug dog mammal CxStory]
    (v/assert kb (list 'genlCx CxStory U) U)
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list pairOf pug mammal) U)
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) CxStory)
    (is (= #{CxStory} (set (v/contexts-of kb (list qualifies pug mammal)))))
    (is (not (holds? kb (list qualifies pug mammal) U))
        "CxUniverse sees no path, and does not answer the genl query either")
    (is (not (holds? kb (list 'genl pug mammal) U)))))

(tu/deftest-kb a-genlCx-join-reads-the-reflexive-pair-and-the-far-pair
  (tu/with-terms [pairOf qualifies CxMid CxLow]
    (v/assert kb (list 'genlCx CxMid U) U)
    (let [low (v/assert kb (list 'genlCx CxLow CxMid) U)]
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list pairOf '?a '?b) (list 'genlCx '?a '?b))
                               (list qualifies '?a '?b)))
                U)
      (v/assert kb (list pairOf CxLow CxLow) U)
      (v/assert kb (list pairOf CxLow U) U)
      (is (holds? kb (list qualifies CxLow CxLow) U) "reflexive")
      (is (holds? kb (list qualifies CxLow U) U) "two edges apart")
      (testing "the far pair names the edges of the path"
        (let [h (v/handle-of kb (list qualifies CxLow U) U)]
          (is (contains? (set (tree-seq coll? seq (v/why kb h))) low)))))))

;; ---- a disjoint antecedent reads the separations ---------------------------

(defn- separated-rule
  "*A pair of separated types qualifies* — both ends of the `disjoint` literal bound by
  the first antecedent."
  [pairOf qualifies]
  (list 'set/forwardRule
        (list 'implies (list 'and (list pairOf '?a '?b) (list 'disjoint '?a '?b))
              (list qualifies '?a '?b))))

(tu/deftest-kb a-disjoint-antecedent-matches-every-separation-a-query-answers
  (doseq [[label separate]
          {"a partition"                    (fn [w a b _] [(list 'partition w a b)])
           "a separating roster"            (fn [w a b _] [(list 'separating w a b)])
           "a disjoint_metatype"            (fn [_ a b m] [(list 'disjoint_metatype m)
                                                           (list m a) (list m b)])
           "a sibling_disjoint parent"      (fn [w a b _] [(list 'sibling_disjoint w)
                                                           (list 'genl a w) (list 'genl b w)])
           "a disjoint over two supertypes" (fn [w a b m] [(list 'genl a w) (list 'genl b m)
                                                           (list 'disjoint w m)])}]
    (testing label
      (tu/with-terms [pairOf qualifies whole qa qb kind]
        (doseq [s (separate whole qa qb kind)] (v/assert kb s U))
        (v/assert kb (separated-rule pairOf qualifies) U)
        (v/assert kb (list pairOf qa qb) U)
        (is (holds? kb (list 'disjoint qa qb) U) "the query answers the pair")
        (is (holds? kb (list qualifies qa qb) U) "and the forward join agrees")))))

(tu/deftest-kb a-type-below-two-parts-of-a-partition-fires-the-issue-rule
  (tu/with-terms [whole qa qb qc emptied]
    (v/assert kb (list 'partition whole qa qb) U {:strength :monotonic})
    (v/assert kb (list 'genl qc qa) U)
    (v/assert kb (list 'genl qc qb) U)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list 'genl '?c '?a) (list 'genl '?c '?b)
                                            (list 'disjoint '?a '?b))
                             (list emptied '?c)))
              U)
    (is (holds? kb (list emptied qc) U))))

(tu/deftest-kb a-join-that-binds-one-end-reads-every-type-separated-from-it
  (tu/with-terms [picked qualifies whole qa qb pug]
    (v/assert kb (list 'partition whole qa qb) U)
    (v/assert kb (list 'genl pug qb) U)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list picked '?a) (list 'disjoint '?a '?b))
                             (list qualifies '?a '?b)))
              U)
    (v/assert kb (list picked qa) U)
    (is (= (set (map '?y (v/query kb (list 'disjoint qa '?y) U)))
           (set (map '?y (v/query kb (list qualifies qa '?y) U)))
           #{qb pug}))))

(tu/deftest-kb a-separation-firing-rests-on-the-roster-and-the-edges-it-climbed
  (tu/with-terms [pairOf qualifies whole qa qb pug]
    (let [roster (v/assert kb (list 'partition whole qa qb) U)
          edge   (v/assert kb (list 'genl pug qa) U)]
      (v/assert kb (separated-rule pairOf qualifies) U)
      (v/assert kb (list pairOf pug qb) U)
      (is (holds? kb (list qualifies pug qb) U))
      (let [named (set (tree-seq coll? seq (v/why kb (v/handle-of kb (list qualifies pug qb) U))))]
        (is (contains? named roster))
        (is (contains? named edge)))
      (testing "the edge going takes the conclusion"
        (v/retract! kb edge)
        (is (nil? (v/handle-of kb (list qualifies pug qb) U))))
      (testing "and so does the roster going"
        (v/assert kb (list pairOf qa qb) U)
        (is (holds? kb (list qualifies qa qb) U))
        (v/retract! kb roster)
        (is (not (holds? kb (list qualifies qa qb) U)))))))

(tu/deftest-kb an-exception-withdraws-a-separation-firing-and-its-retraction-restores-it
  (tu/with-terms [pairOf qualifies whole qa qb]
    (v/assert kb (list 'partition whole qa qb) U)
    (v/assert kb (separated-rule pairOf qualifies) U)
    (v/assert kb (list pairOf qa qb) U)
    (is (holds? kb (list qualifies qa qb) U))
    (let [exc (v/assert kb (list 'siblingDisjointException qa qb) U)]
      (is (not (holds? kb (list 'disjoint qa qb) U)))
      (is (not (holds? kb (list qualifies qa qb) U)) "the exempted pair matches nothing")
      (v/retract! kb exc)
      (is (holds? kb (list qualifies qa qb) U) "and the separation is back"))))

(def ^:private marks
  "Two marks that spare a pair one of whose types is a `genl` of the other, each as a fn
  of the parent or metatype and the two types."
  {"a sibling_disjoint parent" (fn [m a b] [(list 'sibling_disjoint m)
                                            (list 'genl a m) (list 'genl b m)])
   "a disjoint_metatype"       (fn [m a b] [(list 'disjoint_metatype m)
                                            (list m a) (list m b)])})

(tu/deftest-kb an-edge-between-two-marked-types-leaving-separates-them-in-every-order
  ;; With the edge never stated, the mark separates the pair and the rule fires.  An edge
  ;; stated and then retracted leaves the same knowledge, so the rule fires there too,
  ;; whichever ingredient arrived first.  A defeated edge still relates the two types in
  ;; the global closure the genl-relatedness guard reads, so there the query answers no
  ;; separation, and the rule answers what the query answers.
  (doseq [[label mark] marks
          order [[:mark :rule :pair :edge] [:edge :mark :pair :rule] [:rule :edge :pair :mark]]
          leave [:never :retract :defeat]]
    (testing (str label ", " order ", " leave)
      (tu/with-terms [pairOf qualifies kind qa qb]
        (let [edge (atom nil)
              step {:mark #(doseq [s (mark kind qa qb)] (v/assert kb s U))
                    :rule #(v/assert kb (separated-rule pairOf qualifies) U)
                    :pair #(v/assert kb (list pairOf qa qb) U)
                    :edge #(when-not (= :never leave)
                             (reset! edge (v/assert kb (list 'genl qa qb) U)))}]
          (doseq [k order] ((step k)))
          (case leave
            :never   nil
            :retract (v/retract! kb @edge)
            :defeat  (v/assert kb (list 'not (list 'genl qa qb)) U {:strength :monotonic}))
          (when-not (= :defeat leave)
            (is (holds? kb (list 'disjoint qa qb) U)))
          (is (= (holds? kb (list 'disjoint qa qb) U) (holds? kb (list qualifies qa qb) U))
              "the forward join answers what the query answers"))))))

(tu/deftest-kb an-edge-arriving-between-two-marked-types-withdraws-the-firing
  (doseq [[label mark] marks]
    (testing label
      (tu/with-terms [pairOf qualifies kind qa qb]
        (doseq [s (mark kind qa qb)] (v/assert kb s U))
        (v/assert kb (separated-rule pairOf qualifies) U)
        (v/assert kb (list pairOf qa qb) U)
        (is (holds? kb (list qualifies qa qb) U))
        (v/assert kb (list 'genl qa qb) U)
        (is (not (holds? kb (list 'disjoint qa qb) U)))
        (is (not (holds? kb (list qualifies qa qb) U)))))))

(tu/deftest-kb the-separation-join-reads-the-same-whichever-ingredient-arrived-last
  (let [orders {"rule, pair, edge, roster" [:rule :pair :edge :roster]
                "roster, rule, pair, edge" [:roster :rule :pair :edge]
                "roster, edge, pair, rule" [:roster :edge :pair :rule]
                "rule, roster, edge, pair" [:rule :roster :edge :pair]}]
    (doseq [[label order] orders]
      (testing label
        (tu/with-terms [pairOf qualifies whole qa qb pug]
          (let [step {:rule   #(v/assert kb (separated-rule pairOf qualifies) U)
                      :pair   #(v/assert kb (list pairOf pug qb) U)
                      :edge   #(v/assert kb (list 'genl pug qa) U)
                      :roster #(v/assert kb (list 'partition whole qa qb) U)}]
            (doseq [k order] ((step k)))
            (is (holds? kb (list qualifies pug qb) U))))))))
