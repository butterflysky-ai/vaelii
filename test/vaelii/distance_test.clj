;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.distance-test
  "Qualitative distance (`vaelii.impl.distance`): the computed composition table against
  sampled real distances, and refutation over a KB.  The claims all four spatial calculi
  share are tables in `space_test`."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.distance :as dist]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core!)
                        (v/add-prover (dist/distance-prover)))))

(def ^:private C 'CxUniverse)

(def ^:private eps
  "A step that lands just above a class's exclusive lower bound and short of its upper."
  1.0E-6)

(defn- samples-in
  "Numeric distances drawn from class `c`: just above its exclusive lower bound, at its
  inclusive upper bound, and one in between.  `:co` is exactly zero, and the unbounded last
  class is sampled by multiples of its lower bound."
  [c]
  (let [[lo hi] (dist/class-bounds c)]
    (cond
      (= c :co)   [0.0]
      (= hi ##Inf) [(+ lo eps) (* 10.0 lo) (* 1000.0 lo)]
      :else       [(+ lo eps) (/ (+ lo hi) 2.0) (double hi)])))

(def ^:private all-samples
  "Every sampled distance, across every class — the candidate third sides of a triangle."
  (vec (mapcat samples-in dist/class-order)))

(def ^:private derived-composition
  "The composition table computed from sampled real distances: for every pair of classes,
  the class of every sampled third distance the triangle inequality
  |d1 - d2| <= d3 <= d1 + d2 admits.  Nothing here reads `distance/compose`."
  (delay
    (into {}
          (for [c1 dist/class-order]
            [c1 (into {}
                      (for [c2 dist/class-order]
                        [c2 (into #{}
                                  (for [d1 (samples-in c1)
                                        d2 (samples-in c2)
                                        d3 all-samples
                                        :when (and (<= (Math/abs (double (- d1 d2))) d3)
                                                   (<= d3 (+ d1 d2)))]
                                    (dist/classify d3)))]))]))))

(deftest the-seven-classes-tile-the-non-negative-reals
  (is (= 7 (count dist/all-classes)))
  (is (= dist/all-classes (set dist/class-order)))
  (testing "each class starts where the one before it ends, so the chain has no gap and no
            overlap"
    (doseq [[a b] (partition 2 1 dist/class-order)]
      (is (= (second (dist/class-bounds a)) (first (dist/class-bounds b)))
          (str a " must end where " b " begins"))))
  (testing "so every distance falls in exactly one class"
    (doseq [d (concat all-samples [0.0 0.25 3.0 42.0 999.0 123456.0])]
      (is (= 1 (count (filter (fn [c]
                                (let [[lo hi] (dist/class-bounds c)]
                                  (and (< lo d) (<= d hi))))
                              dist/class-order)))
          (str d " must fall in exactly one class"))
      (is (some? (dist/classify d)))))
  (testing "and zero is the co-located class, while a negative number is no distance"
    (is (= :co (dist/classify 0)))
    (is (= :very-far (dist/classify 1.0E12)))
    (is (nil? (dist/classify -1)))))

(deftest the-composition-table-matches-the-triangle-inequality
  (let [derived @derived-composition]
    (testing "every class real arithmetic produces is in the table: soundness"
      (doseq [c1 dist/class-order c2 dist/class-order]
        (is (set/subset? (get-in derived [c1 c2]) (dist/compose #{c1} #{c2}))
            (str c1 " ∘ " c2))))
    (testing "and every class the table admits is produced by some real triangle: tightness"
      (doseq [c1 dist/class-order c2 dist/class-order]
        (is (= (get-in derived [c1 c2]) (dist/compose #{c1} #{c2}))
            (str c1 " ∘ " c2))))))

(deftest composition-is-computed-from-the-bounds
  (testing "the chain composes weakly — two mid-range classes leave several open"
    (is (= #{:co :very-close :close :near} (dist/compose #{:close} #{:close})))
    (is (= #{:very-close :close :near} (dist/compose #{:very-close} #{:close}))))
  (testing "but it still rules things out, which is the point of it"
    (is (= #{:co :very-close :close} (dist/compose #{:very-close} #{:very-close}))
        "two very short legs cannot reach further than close")
    (is (not (contains? (dist/compose #{:very-close} #{:very-close}) :very-far)))
    (is (= #{:far :very-far} (dist/compose #{:very-close} #{:very-far}))
        "a short leg off a very long one lands very near the far end"))
  (testing "and only a pair of legs that can be equal reaches zero"
    (is (contains? (dist/compose #{:close} #{:close}) :co))
    (is (not (contains? (dist/compose #{:close} #{:near}) :co))
        "a close leg and a near leg are never the same length"))
  (testing "and composing a result onward does not associate"
    (is (not= (dist/compose (dist/compose #{:moderate} #{:close}) #{:close})
              (dist/compose #{:moderate} (dist/compose #{:close} #{:close}))))))

(deftest scaling-the-bounds-leaves-the-composition-table-unchanged
  (let [table  #(into {} (for [a dist/class-order b dist/class-order]
                           [[a b] (dist/compose #{a} #{b})]))
        scaled (fn [k] (update-vals dist/class-bounds (fn [[lo hi]] [(* k lo) (* k hi)])))
        base   (table)]
    (doseq [k [0.5 3 1000]]
      (is (= base (with-redefs [dist/class-bounds (scaled k)] (table))) (str "factor " k)))
    (testing "while changing the ratio between two neighbours moves it"
      (is (not= base (with-redefs [dist/class-bounds (assoc dist/class-bounds
                                                            :very-close [0 9] :close [9 10])]
                       (table)))))))

(deftest the-converse-of-a-distance-is-itself
  (doseq [c dist/all-classes]
    (is (= #{c} (dist/converse-set #{c}))))
  (is (= #{:far :very-far} (dist/converse-set #{:far :very-far}))))

(tu/deftest-kb the-zero-class-carries-a-distance-across
  (tu/with-terms [A B D]
    (v/assert kb (list 'coLocatedWith A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "co-located is the identity, so A is exactly as far from D as B is"
      (is (= #{:close} (qkb/possible dist/qualitative-distance kb C A D)))
      (is (= :close (qkb/definite dist/qualitative-distance kb C A D)))
      (is (v/ask? kb (list 'closeTo A D) C)))
    (testing "so a class the network excludes is not answered"
      (is (not (v/ask? kb (list 'nearTo A D) C)))
      (is (not (v/ask? kb (list 'coLocatedWith A D) C))))))

(tu/deftest-kb the-triangle-inequality-refutes-a-distance
  (tu/with-terms [A B D]
    (v/assert kb (list 'veryCloseTo A B) C)
    (v/assert kb (list 'veryCloseTo B D) C)
    (testing "two very short legs compose to a short one, however they are laid out"
      (is (= #{:co :very-close :close} (qkb/possible dist/qualitative-distance kb C A D)))
      (is (= :unknown (qkb/definite dist/qualitative-distance kb C A D))))
    (testing "so nothing at the far end of the chain is possible, which is the refutation
              this calculus is for"
      (is (not (v/ask? kb (list 'veryFarFrom A D) C)))
      (is (not (v/ask? kb (list 'farFrom A D) C)))
      (is (not (v/ask? kb (list 'beyondFarDistanceFrom A D) C))))
    (testing "and the range that covers every survivor is entailed, though no class is"
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C))
      (is (not (v/ask? kb (list 'veryCloseTo A D) C)))
      (is (not (v/ask? kb (list 'coLocatedWith A D) C))))))

(tu/deftest-kb a-distance-the-triangle-inequality-forbids-is-an-inconsistency
  (tu/with-terms [A B D]
    (v/assert kb (list 'veryCloseTo A B) C)
    (v/assert kb (list 'veryCloseTo B D) C)
    (v/assert kb (list 'veryFarFrom A D) C)
    (is (qkb/inconsistent? dist/qualitative-distance kb C))
    (is (= :inconsistent (qkb/definite dist/qualitative-distance kb C A D)))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'veryCloseTo A B) C)))
      (is (not (v/ask? kb (list 'coLocatedWith A A) C))))
    (testing "retracting the impossible claim gives the rest their answers back"
      (v/retract! kb (v/handle-of kb (list 'veryFarFrom A D) C))
      (is (not (qkb/inconsistent? dist/qualitative-distance kb C)))
      (is (v/ask? kb (list 'veryCloseTo A B) C))
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C)))))

(tu/deftest-kb a-distance-reads-the-same-both-ways-round
  (tu/with-terms [A B]
    (v/assert kb (list 'farFrom A B) C)
    (testing "the converse of a distance is itself, so one fact answers both orders"
      (is (v/ask? kb (list 'farFrom A B) C))
      (is (v/ask? kb (list 'farFrom B A) C))
      (is (= (qkb/possible dist/qualitative-distance kb C A B) (qkb/possible dist/qualitative-distance kb C B A))))
    (testing "and the derived ranges follow, in both directions"
      (is (v/ask? kb (list 'beyondFarDistanceFrom A B) C))
      (is (v/ask? kb (list 'beyondFarDistanceFrom B A) C))
      (is (v/ask? kb (list 'atSomeDistanceFrom A B) C))
      (is (not (v/ask? kb (list 'withinNearDistanceOf A B) C))))))

(tu/deftest-kb a-chain-of-short-legs-still-bounds-a-long-one
  (tu/with-terms [A B D]
    (v/assert kb (list 'closeTo A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "close∘close spans four classes — this chain composes weakly, and says so"
      (is (= #{:co :very-close :close :near} (qkb/possible dist/qualitative-distance kb C A D)))
      (is (= :unknown (qkb/definite dist/qualitative-distance kb C A D))))
    (testing "which is still enough to entail the range covering them"
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C))
      (is (not (v/ask? kb (list 'moderatelyFarFrom A D) C)))
      (is (not (v/ask? kb (list 'beyondFarDistanceFrom A D) C))))))

(tu/deftest-kb an-open-argument-enumerates-the-entailed-things
  (tu/with-terms [A B D]
    (v/assert kb (list 'coLocatedWith A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "(closeTo A ?y) — everything A is entailed to be close to"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'closeTo A '?y) C)))]
        (is (= #{D} ys) "D by composition; B is co-located and A is not close to itself")))
    (testing "(withinNearDistanceOf ?x D) — everything entailed to be no further than near"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'withinNearDistanceOf '?x D) C)))]
        (is (= #{A B D} xs) "D included: the diagonal is the zero class, which is within")))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'closeTo '?x '?y) C)))]
        (is (= #{[A D] [D A] [B D] [D B]} pairs)
            "symmetric, so each entailed pair is answered both ways round")))))
