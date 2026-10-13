;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.relative-test
  "Relative direction (`vaelii.impl.relative`): the computed composition table against
  the coordinate definitions, entailment over a KB, and the context as the frame of
  reference.  The claims all four spatial calculi share are tables in `space_test`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.relative :as rel]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core!)
                        (v/add-prover (rel/relative-prover)))))

(def ^:private C 'CxUniverse)

(def ^:private by-coordinates
  "Each base relation as the inequalities over two places `[lr fb]` that define it, the
  coordinates growing rightwards and frontwards: a statement of the algebra that shares
  nothing with `relative/relation->axes`."
  {:left         (fn [alr afb blr bfb] (and (< alr blr) (= afb bfb)))
   :right        (fn [alr afb blr bfb] (and (> alr blr) (= afb bfb)))
   :front        (fn [alr afb blr bfb] (and (= alr blr) (> afb bfb)))
   :behind       (fn [alr afb blr bfb] (and (= alr blr) (< afb bfb)))
   :front-left   (fn [alr afb blr bfb] (and (< alr blr) (> afb bfb)))
   :front-right  (fn [alr afb blr bfb] (and (> alr blr) (> afb bfb)))
   :behind-left  (fn [alr afb blr bfb] (and (< alr blr) (< afb bfb)))
   :behind-right (fn [alr afb blr bfb] (and (> alr blr) (< afb bfb)))
   :eq           (fn [alr afb blr bfb] (and (= alr blr) (= afb bfb)))})

(def ^:private places
  "Every place on a 3×3 grid.  A layout of three things is a weak ordering of three
  coordinates on each axis independently, so three values per axis realize every one."
  (vec (for [lr (range 3) fb (range 3)] [lr fb])))

(defn- holding [[alr afb] [blr bfb]]
  (into #{} (keep (fn [[rel pred]] (when (pred alr afb blr bfb) rel))) by-coordinates))

(defn- relation-of [a b] (first (holding a b)))

(def ^:private derived-composition
  "The composition table computed from `by-coordinates`: lay out three things every way
  they can be laid out on the grid, read off the three relations, and record that r1 ∘ r2
  admits r3."
  (delay
    (reduce (fn [tbl [a b c]]
              (update-in tbl [(relation-of a b) (relation-of b c)]
                         (fnil conj #{}) (relation-of a c)))
            {}
            (for [a places b places c places] [a b c]))))

(deftest the-nine-relations-are-jointly-exhaustive-and-pairwise-disjoint
  (testing "exactly one holds of any two places"
    (doseq [a places b places]
      (is (= 1 (count (holding a b)))
          (str a " and " b " stand in " (holding a b)))))
  (testing "and every one of the nine is realized by some pair, so none is vacuous"
    (is (= rel/all-relations
           (set (for [a places b places] (relation-of a b)))))))

(deftest the-composition-table-matches-the-coordinate-definitions
  ;; a wrong projection or point-algebra entry composes to a wrong entailment, not a crash
  (let [derived @derived-composition]
    (testing "every pair of relations composes to something, and to the same something"
      (doseq [r1 rel/all-relations r2 rel/all-relations]
        (is (= (get-in derived [r1 r2]) (rel/compose #{r1} #{r2}))
            (str r1 " ∘ " r2))))
    (testing "and the derivation reaches all 81 pairs"
      (is (= rel/all-relations (set (keys derived))))
      (doseq [[_ row] derived]
        (is (= rel/all-relations (set (keys row)))))))
  (testing "the four unconstrained entries are the opposite corners, which disagree on
            both axes at once"
    (is (= #{[:front-left :behind-right] [:behind-right :front-left]
             [:front-right :behind-left] [:behind-left :front-right]}
           (set (for [r1 rel/all-relations r2 rel/all-relations
                      :when (= rel/all-relations (rel/compose #{r1} #{r2}))]
                  [r1 r2]))))))

(deftest composition-is-computed-from-the-two-axis-projections
  (testing "two perpendicular relations combine into the corner between them"
    (is (= #{:front-left} (rel/compose #{:left} #{:front})) "left then in front is front-left")
    (is (= #{:front-left} (rel/compose #{:front} #{:left})) "and so is in front then left")
    (is (= #{:behind-right} (rel/compose #{:behind} #{:right}))))
  (testing "an axis the two disagree on loses all information on that axis"
    (is (= #{:left :eq :right} (rel/compose #{:left} #{:right}))
        "left then right lands somewhere on the frame's front-back line")
    (is (= rel/all-relations (rel/compose #{:front-left} #{:behind-right}))
        "opposite corners disagree on both axes at once, so nothing at all is left")))

(deftest the-converse-flips-both-axes
  (is (= #{:right} (rel/converse-set #{:left})))
  (is (= #{:behind-right} (rel/converse-set #{:front-left})))
  (is (= #{:eq} (rel/converse-set #{:eq})) "coincidence is its own converse")
  (testing "it agrees with reading the coordinates backwards"
    (doseq [a places b places]
      (is (= #{(relation-of b a)} (rel/converse-set #{(relation-of a b)}))))))

(tu/deftest-kb composition-derives-an-unasserted-relation
  (tu/with-terms [Mouse Lion Rock]
    (v/assert kb (list 'leftOf Mouse Lion) C)
    (v/assert kb (list 'leftOf Lion Rock) C)
    (testing "left∘left = left, so the mouse is left of the rock though nobody said so"
      (is (v/ask? kb (list 'leftOf Mouse Rock) C)))
    (testing "and the computed table pins it to exactly that"
      (is (= #{:left} (qkb/possible rel/relative kb C Mouse Rock)))
      (is (= :left (qkb/definite rel/relative kb C Mouse Rock))))
    (testing "so a relation the network excludes is not answered"
      (is (not (v/ask? kb (list 'rightOf Mouse Rock) C)))
      (is (not (v/ask? kb (list 'inFrontOf Mouse Rock) C)))
      (is (not (v/ask? kb (list 'sameRelativePositionAs Mouse Rock) C))))))

(tu/deftest-kb two-perpendicular-facts-compose-into-a-corner
  (tu/with-terms [A B D]
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'inFrontOf B D) C)
    (is (= #{:front-left} (qkb/possible rel/relative kb C A D)))
    (is (v/ask? kb (list 'frontLeftOf A D) C))
    (testing "and the converse corner holds the other way round"
      (is (v/ask? kb (list 'behindRightOf D A) C)))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'frontLeftOf A B) C)
    (v/assert kb (list 'frontLeftOf B D) C)
    (testing "#{:front-left} sits inside every denotation that contains it"
      (is (v/ask? kb (list 'leftwardOf A D) C))
      (is (v/ask? kb (list 'frontwardOf A D) C)))
    (testing "and outside the two denotations that do not"
      (is (not (v/ask? kb (list 'rightwardOf A D) C)))
      (is (not (v/ask? kb (list 'rearwardOf A D) C))))
    (testing "the converse derived predicates hold the other way round"
      (is (v/ask? kb (list 'rightwardOf D A) C))
      (is (v/ask? kb (list 'rearwardOf D A) C)))))

(tu/deftest-kb a-derived-predicate-can-be-the-only-thing-entailed
  (tu/with-terms [A B D]
    ;; the front-back axis disagrees and the left-right axis does not, so the pair is
    ;; #{:behind-left :left :front-left} — three base relations, no one of them entailed,
    ;; and yet every one of them is leftward
    (v/assert kb (list 'frontLeftOf A B) C)
    (v/assert kb (list 'behindLeftOf B D) C)
    (is (= #{:behind-left :left :front-left} (qkb/possible rel/relative kb C A D)))
    (is (= :unknown (qkb/definite rel/relative kb C A D)))
    (testing "no base relation is entailed"
      (is (not (v/ask? kb (list 'leftOf A D) C)))
      (is (not (v/ask? kb (list 'frontLeftOf A D) C)))
      (is (not (v/ask? kb (list 'behindLeftOf A D) C))))
    (testing "but the disjunction covering all three is"
      (is (v/ask? kb (list 'leftwardOf A D) C))
      (is (not (v/ask? kb (list 'rightwardOf A D) C)))
      (is (not (v/ask? kb (list 'frontwardOf A D) C))))))

(tu/deftest-kb the-converse-is-derived-with-the-fact
  (tu/with-terms [A B]
    (v/assert kb (list 'leftOf A B) C)
    (testing "one asserted relation constrains the pair both ways round"
      (is (v/ask? kb (list 'leftOf A B) C))
      (is (v/ask? kb (list 'rightOf B A) C)))
    (testing "and rules the opposite readings out"
      (is (not (v/ask? kb (list 'rightOf A B) C)))
      (is (not (v/ask? kb (list 'leftOf B A) C)))
      (is (not (v/ask? kb (list 'frontwardOf A B) C))
          "directly left is level on the front-back axis, so no forward component"))))

(tu/deftest-kb coincidence-carries-a-relation-across
  (tu/with-terms [A B D]
    (v/assert kb (list 'sameRelativePositionAs A B) C)
    (v/assert kb (list 'leftOf B D) C)
    (testing "eq is the identity, so A stands where B does"
      (is (= #{:left} (qkb/possible rel/relative kb C A D)))
      (is (v/ask? kb (list 'leftOf A D) C)))))

(tu/deftest-kb a-frame-of-reference-is-a-context-and-does-not-leak
  (tu/with-terms [Mouse Lion CxFromTheLion CxFromTheMouse]
    (v/assert kb (list 'genlCx CxFromTheLion C) C)
    (v/assert kb (list 'genlCx CxFromTheMouse C) C)
    (v/assert kb (list 'leftOf Mouse Lion) CxFromTheLion)
    (v/assert kb (list 'rightOf Mouse Lion) CxFromTheMouse)
    (testing "each frame answers its own way"
      (is (= #{:left} (qkb/possible rel/relative kb CxFromTheLion Mouse Lion)))
      (is (= #{:right} (qkb/possible rel/relative kb CxFromTheMouse Mouse Lion)))
      (is (v/ask? kb (list 'leftOf Mouse Lion) CxFromTheLion))
      (is (v/ask? kb (list 'rightOf Mouse Lion) CxFromTheMouse)))
    (testing "and refuses what the other frame says"
      (is (not (v/ask? kb (list 'rightOf Mouse Lion) CxFromTheLion)))
      (is (not (v/ask? kb (list 'leftOf Mouse Lion) CxFromTheMouse))))
    (testing "neither frame is incoherent — the two claims never meet"
      (is (not (qkb/inconsistent? rel/relative kb CxFromTheLion)))
      (is (not (qkb/inconsistent? rel/relative kb CxFromTheMouse))))
    (testing "and the context both of them see sees neither: visibility runs upwards"
      (is (= rel/all-relations (qkb/possible rel/relative kb C Mouse Lion)))
      (is (not (v/ask? kb (list 'leftOf Mouse Lion) C)))
      (is (not (v/ask? kb (list 'rightOf Mouse Lion) C))))))

(tu/deftest-kb a-context-seeing-two-frames-at-once-is-incoherent
  (tu/with-terms [Mouse Lion CxFromTheLion CxFromTheMouse CxBothWays]
    (v/assert kb (list 'genlCx CxBothWays CxFromTheLion) C)
    (v/assert kb (list 'genlCx CxBothWays CxFromTheMouse) C)
    (v/assert kb (list 'leftOf Mouse Lion) CxFromTheLion)
    (v/assert kb (list 'rightOf Mouse Lion) CxFromTheMouse)
    (is (qkb/inconsistent? rel/relative kb CxBothWays))
    (is (= #{} (qkb/possible rel/relative kb CxBothWays Mouse Lion)))
    (testing "while the two frames it sees are each still coherent on their own"
      (is (not (qkb/inconsistent? rel/relative kb CxFromTheLion)))
      (is (not (qkb/inconsistent? rel/relative kb CxFromTheMouse))))))

(tu/deftest-kb an-open-argument-enumerates-the-entailed-things
  (tu/with-terms [A B D]
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'leftOf B D) C)
    (testing "(leftOf A ?y) — everything A is entailed to be left of"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'leftOf A '?y) C)))]
        (is (= #{B D} ys) "B by assertion and D by composition; not A itself")))
    (testing "(leftwardOf ?x D) — everything entailed to lie somewhere left of D"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'leftwardOf '?x D) C)))]
        (is (= #{A B} xs))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'leftwardOf '?x '?y) C)))]
        (is (= #{[A B] [A D] [B D]} pairs))))))
