;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.semantics-test
  "The transitivity uses: isa? via genl, arg constraint checking, specificity
  in matching, genlCx context placement, and rule-as-sentex retraction."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- type-hierarchy [kb {:keys [animal thing physical-object person dog]}]
  ;; make CxNaturalWorld see CxUniverse so context-scoped constraint checks apply
  (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
  (doseq [g [(list 'genl animal thing) (list 'genl physical-object thing)
             (list 'genl animal physical-object) (list 'genl person animal)
             (list 'genl dog animal)]]
    (v/assert kb g 'CxUniverse)))

(tu/deftest-kb isa-via-genl
  (let [animal (tu/tmp-type) thing 'thing physical-object (tu/tmp-type)
        person (tu/tmp-type) dog (tu/tmp-type)
        muffet (tu/tmp-ind) tom (tu/tmp-ind)]
    (type-hierarchy kb {:animal animal :thing thing :physical-object physical-object
                        :person person :dog dog})
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (v/assert kb (list person tom) 'CxNaturalWorld)
    (testing "transitive type membership"
      (is (v/isa? kb muffet animal))
      (is (v/isa? kb muffet thing))
      (is (v/isa? kb tom thing))
      (is (not (v/isa? kb tom dog)))
      (is (not (v/isa? kb muffet person))))
    (testing "a compound term is a member through the fact that names it"
      (let [pup (list (tu/tmp-ind "PuppyFn") muffet)]
        (v/assert kb (list dog pup) 'CxNaturalWorld)
        (is (v/isa? kb pup animal 'CxNaturalWorld))
        (is (not (v/isa? kb pup person 'CxNaturalWorld)))))))

(tu/deftest-kb arg-constraints-use-transitivity
  ;; Pinned to the constraint reading: transitivity is asserted here through a refusal, and
  ;; with the entailment on a symbol argument is minted rather than convicted
  ;; (docs/argtypes.md).  The entailment reads the same closure — argtype_entail_test's
  ;; a-subsuming-membership-does-not-suppress-the-entailment is that half.
  (tu/without-entailing
   (let [animal (tu/tmp-type) thing 'thing physical-object (tu/tmp-type)
         person (tu/tmp-type) dog (tu/tmp-type)
         likesPet (tu/tmp-pred) tom (tu/tmp-ind) muffet (tu/tmp-ind)]
     (type-hierarchy kb {:animal animal :thing thing :physical-object physical-object
                         :person person :dog dog})
     (v/assert kb (list 'arg likesPet 1 person) 'CxUniverse)
     (v/assert kb (list person tom) 'CxNaturalWorld)
     (v/assert kb (list dog muffet) 'CxNaturalWorld)
     (testing "a person satisfies the arg-1 person constraint"
       (is (v/assert kb (list likesPet tom muffet) 'CxNaturalWorld)))
     (testing "a dog in arg 1 violates it (dog is-a thing but not is-a person)"
       (is (thrown? clojure.lang.ExceptionInfo
                    (v/assert kb (list likesPet muffet tom) 'CxNaturalWorld)))))))

(tu/deftest-kb specificity-in-matching
  (let [dog (tu/tmp-type) animal (tu/tmp-type) breathes (tu/tmp-pred) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog muffet) 'CxUniverse)
    (testing "a rule about animals fires on a dog (subtype), without materializing (animal Muffet)"
      (is (seq (v/sentexes-matching kb (list breathes muffet) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list animal muffet) 'CxUniverse))))))

(tu/deftest-kb context-placement-in-forward-inference
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxBio 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z)
                   'CxUniverse {:direction :forward :chain? false})            ; universal rule
    (v/assert kb (list parentOf tom bob) 'CxBio)             ; specific facts
    (v/assert kb (list parentOf bob ann) 'CxBio)
    (testing "justification lands in the maximal context that sees rule + facts"
      (is (seq   (v/sentexes-matching kb (list grandparentOf tom ann) 'CxBio)))
      (is (empty? (v/sentexes-matching kb (list grandparentOf tom ann) 'CxUniverse))))))

(tu/deftest-kb forward-combines-specificity-and-context
  (let [dog (tu/tmp-type) animal (tu/tmp-type) breathes (tu/tmp-pred) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'genlCx 'CxBio 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'CxUniverse {:direction :forward :chain? false})  ; universal rule
    (v/assert kb (list dog muffet) 'CxBio)                    ; specific, subtype fact
    (testing "the dog (subtype) fires the animal rule, and the justification lands in CxBio"
      (is (seq   (v/sentexes-matching kb (list breathes muffet) 'CxBio)))
      (is (empty? (v/sentexes-matching kb (list breathes muffet) 'CxUniverse))))))

(tu/deftest-kb retracting-a-rule-removes-its-justifications
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)
        rule-h (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'CxUniverse {:direction :forward})]
    (v/assert kb (list parentOf tom bob) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'CxUniverse)))
    (v/retract! kb rule-h)
    (testing "the rule's derivation vanishes but the fact remains"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list parentOf tom bob) 'CxUniverse))))))
