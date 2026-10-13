;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.emptiness-test
  "`empty` and `nonempty` partition `unary_predicate` by extension: an `empty` type has no
  instance, and a `nonempty` type has at least one."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(defn- stored?
  "Whether `sentence` is answered facts-only from CxUniverse: stated, concluded by a forward
  rule, or inherited along a `transitiveInArg` declaration."
  [kb sentence]
  (boolean (seq (v/query kb sentence U {:max-depth 0}))))

(defn- clashes-on
  "The exposed clashes whose term is `term`."
  [kb term]
  (filter #(= term (get-in % [:detail :term])) (v/exposed-clashes kb)))

;; ---- the partition ------------------------------------------------------

(tu/deftest-kb empty-and-nonempty-partition-unary-predicate
  (testing "each part is a subtype of unary_predicate"
    (is (v/genl? kb 'empty 'unary_predicate))
    (is (v/genl? kb 'nonempty 'unary_predicate)))
  (testing "the two parts are disjoint"
    (is (v/disjoint? kb 'empty 'nonempty)))
  (testing "each part holds types of any order"
    (doseq [t '[empty nonempty]]
      (is (v/isa? kb t 'variable_order_type))
      (is (v/isa? kb t 'at_least_metatype)))))

(tu/deftest-kb a-type-stated-both-empty-and-nonempty-is-an-exposed-clash
  (tu/with-terms [both_kind]
    (v/assert kb (list 'genl both_kind 'thing) U)
    (v/assert kb (list 'empty both_kind) U)
    (is (empty? (clashes-on kb both_kind)))
    (v/assert kb (list 'nonempty both_kind) U)
    (is (= [:disjoint] (map :violation (clashes-on kb both_kind))))))

(tu/deftest-kb an-empty-type-does-not-contradict-orthogonal
  ;; orthogonal says two types could share an instance, and an empty type shares none
  (tu/with-terms [unicorn horse]
    (v/assert kb (list 'genl unicorn 'thing) U)
    (v/assert kb (list 'genl horse 'thing) U)
    (v/assert kb (list 'orthogonal unicorn horse) U)
    (v/assert kb (list 'empty unicorn) U)
    (is (stored? kb (list 'empty unicorn)))
    (is (empty? (clashes-on kb unicorn)))
    (is (empty? (v/conflicts kb)))
    (is (= :orthogonal (v/subsumption-status kb unicorn horse)))))

(tu/deftest-kb one-type-empty-in-one-context-and-nonempty-in-a-sibling-is-no-clash
  ;; an empty claim holds for the context it is stated in, so two contexts no reader joins
  ;; may disagree
  (tu/with-terms [hobbit CxRealWorld CxMiddleEarth]
    (v/assert kb (list 'genl hobbit 'thing) U)
    (v/assert kb (list 'genlCx CxRealWorld U) U)
    (v/assert kb (list 'genlCx CxMiddleEarth U) U)
    (v/assert kb (list 'empty hobbit) CxRealWorld)
    (v/assert kb (list 'nonempty hobbit) CxMiddleEarth)
    (is (seq (v/query kb (list 'empty hobbit) CxRealWorld {:max-depth 0})))
    (is (seq (v/query kb (list 'nonempty hobbit) CxMiddleEarth {:max-depth 0})))
    (is (empty? (v/query kb (list 'nonempty hobbit) CxRealWorld {:max-depth 0})))
    (is (empty? (clashes-on kb hobbit)))
    (is (empty? (v/conflicts kb)))))

(tu/deftest-kb empty-and-nonempty-are-related-to-the-disjointness-terms
  (is (stored? kb '(termsRelated empty nonempty disjoint orthogonal))))

;; ---- along genl ------------------------------------------------------------

(tu/deftest-kb an-empty-type-makes-each-subtype-empty
  (tu/with-terms [outer_kind inner_kind leaf_kind]
    (v/assert kb (list 'genl outer_kind 'thing) U)
    (v/assert kb (list 'genl inner_kind outer_kind) U)
    (v/assert kb (list 'genl leaf_kind inner_kind) U)
    (v/assert kb (list 'empty outer_kind) U)
    (is (stored? kb (list 'empty inner_kind)))
    (is (stored? kb (list 'empty leaf_kind)))
    (is (not (stored? kb (list 'empty 'thing))) "emptiness does not climb to a supertype")))

(tu/deftest-kb a-nonempty-type-makes-each-supertype-nonempty
  (tu/with-terms [top_kind outer_kind inner_kind leaf_kind]
    (v/assert kb (list 'genl top_kind 'thing) U)
    (v/assert kb (list 'genl outer_kind top_kind) U)
    (v/assert kb (list 'genl inner_kind outer_kind) U)
    (v/assert kb (list 'genl leaf_kind inner_kind) U)
    (v/assert kb (list 'nonempty inner_kind) U)
    (is (stored? kb (list 'nonempty outer_kind)))
    (is (stored? kb (list 'nonempty top_kind)))
    (is (not (stored? kb (list 'nonempty leaf_kind))) "nonemptiness does not descend to a subtype")))

;; The partition makes `(nonempty inner)` a denial of the `(empty inner)` that
;; `(empty outer)` reaches, and `(empty outer)` a denial of the `(nonempty outer)` that
;; `(nonempty inner)` reaches.  CxUniverse states both declarations `:monotonic`, so a reading
;; over a known-true claim and edge is known-true.
(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(tu/deftest-kb a-subtype-stated-nonempty-below-a-type-stated-empty-is-an-inherited-clash-in-every-order
  ;; Known-true throughout, the two clashes are conflicts.  A `:default` `(nonempty inner)`
  ;; is the unique weakest member of the first clash and is not believed.
  (is (= {:monotonic #{[#{'(empty inner) '(nonempty outer)} true]}
          :default   #{[#{} false]}}
         (into {}
               (for [strength [:monotonic :default]]
                 [strength
                  (into #{}
                        (for [order (permutations [:empty :edge :nonempty])]
                          (tu/with-terms [outer_kind inner_kind]
                            (v/assert kb (list 'genl outer_kind 'thing) U)
                            (doseq [op order]
                              (case op
                                :empty    (v/assert kb (list 'empty outer_kind) U
                                                    {:strength :monotonic})
                                :edge     (v/assert kb (list 'genl inner_kind outer_kind) U
                                                    {:strength :monotonic})
                                :nonempty (v/assert kb (list 'nonempty inner_kind) U
                                                    {:strength strength})))
                            (let [role {outer_kind 'outer inner_kind 'inner}]
                              [(into #{}
                                     (comp (filter #(= :inherited (:kind %)))
                                           (map #(walk/postwalk-replace
                                                  role (:sentence (:inherited %))))
                                           (filter #(some '#{outer inner} %)))
                                     (concat (v/conflicts kb) (v/contradictions kb)))
                               (v/ask? kb (list 'nonempty inner_kind) U)]))))])))))

;; ---- below two disjoint types ---------------------------------------------

(tu/deftest-kb a-type-below-two-disjoint-types-is-empty
  (tu/with-terms [plant_kind mineral_kind both_kind mid_kind deep_kind]
    (doseq [k [both_kind mid_kind deep_kind]] (v/assert kb (list 'unary_predicate k) U))
    (v/assert kb (list 'genl plant_kind 'thing) U)
    (v/assert kb (list 'genl mineral_kind 'thing) U)
    (v/assert kb (list 'disjoint plant_kind mineral_kind) U)
    (testing "a type directly below both"
      (v/assert kb (list 'genl both_kind plant_kind) U)
      (v/assert kb (list 'genl both_kind mineral_kind) U)
      (is (stored? kb (list 'empty both_kind))))
    (testing "a type below one of the two through an intermediate type"
      (v/assert kb (list 'genl mid_kind plant_kind) U)
      (v/assert kb (list 'genl deep_kind mid_kind) U)
      (is (not (stored? kb (list 'empty deep_kind))))
      (v/assert kb (list 'genl deep_kind mineral_kind) U)
      (is (stored? kb (list 'empty deep_kind))))
    (testing "the disjoint types themselves stay open"
      (is (not (stored? kb (list 'empty plant_kind))))
      (is (not (stored? kb (list 'empty mineral_kind)))))))

(tu/deftest-kb a-type-below-subtypes-of-two-disjoint-types-is-empty
  (tu/with-terms [plant_kind mineral_kind tree_kind crystal_kind both_kind]
    (v/assert kb (list 'unary_predicate both_kind) U)
    (v/assert kb (list 'genl plant_kind 'thing) U)
    (v/assert kb (list 'genl mineral_kind 'thing) U)
    (v/assert kb (list 'disjoint plant_kind mineral_kind) U)
    (v/assert kb (list 'genl tree_kind plant_kind) U)
    (v/assert kb (list 'genl crystal_kind mineral_kind) U)
    (v/assert kb (list 'genl both_kind tree_kind) U)
    (v/assert kb (list 'genl both_kind crystal_kind) U)
    (is (stored? kb (list 'empty both_kind)))))

(tu/deftest-kb a-type-below-two-parts-of-a-partition-is-empty
  (tu/with-terms [whole_kind plant_kind mineral_kind both_kind]
    (v/assert kb (list 'unary_predicate both_kind) U)
    (v/assert kb (list 'partition whole_kind plant_kind mineral_kind) U {:strength :monotonic})
    (v/assert kb (list 'genl both_kind plant_kind) U)
    (v/assert kb (list 'genl both_kind mineral_kind) U)
    (is (stored? kb (list 'empty both_kind)))))

(tu/deftest-kb emptiness-from-a-separation-is-concluded-in-the-context-of-the-separation
  ;; a separation stated in a context below CxUniverse concludes the emptiness there, and
  ;; nowhere above it.  `(unary_predicate both_kind)` has a copy in CxUniverse
  ;; (`decontextualized_predicate`), and a firing on the copy reads the separation, which
  ;; only the lower context sees, so it concludes there too.
  (tu/with-terms [CxSeparation plant_kind mineral_kind both_kind]
    (v/assert kb (list 'genlCx CxSeparation 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'unary_predicate both_kind) CxSeparation)
    (v/assert kb (list 'genl plant_kind 'thing) CxSeparation)
    (v/assert kb (list 'genl mineral_kind 'thing) CxSeparation)
    (v/assert kb (list 'disjoint plant_kind mineral_kind) CxSeparation)
    (v/assert kb (list 'genl both_kind plant_kind) CxSeparation)
    (v/assert kb (list 'genl both_kind mineral_kind) CxSeparation)
    (is (= #{CxSeparation}
           (set (map :context (v/sentexes-matching kb (list 'empty both_kind) '?ctx)))))))

;; ---- against the metatype ladder ------------------------------------------

(tu/deftest-kb empty-and-nonempty-are-orthogonal-to-the-metatype-ladder
  ;; a type of each order may have instances or have none
  (doseq [part '[empty nonempty]
          t    '[type metatype meta_metatype fixed_order_type variable_order_type
                 at_least_metatype disjoint_metatype]]
    (is (= :orthogonal (v/subsumption-status kb part t)) (str part " and " t))))
