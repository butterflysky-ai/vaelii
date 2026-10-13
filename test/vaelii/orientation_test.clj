;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.orientation-test
  "Cardinal direction (`vaelii.impl.orientation`): the computed composition table against
  the axis definitions, and entailment over a KB.  The claims all four spatial calculi
  share are tables in `space_test`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core!)
                        (v/add-prover (dir/orientation-prover)))))

(def ^:private C 'CxUniverse)

(def ^:private by-axes
  "Each base direction as the inequalities over two places `[ew ns]` that define it, the
  coordinates growing eastward and northward: a statement of the algebra that shares
  nothing with `orientation/direction->xy`."
  {:n  (fn [aew ans bew bns] (and (= aew bew) (> ans bns)))
   :s  (fn [aew ans bew bns] (and (= aew bew) (< ans bns)))
   :e  (fn [aew ans bew bns] (and (> aew bew) (= ans bns)))
   :w  (fn [aew ans bew bns] (and (< aew bew) (= ans bns)))
   :ne (fn [aew ans bew bns] (and (> aew bew) (> ans bns)))
   :nw (fn [aew ans bew bns] (and (< aew bew) (> ans bns)))
   :se (fn [aew ans bew bns] (and (> aew bew) (< ans bns)))
   :sw (fn [aew ans bew bns] (and (< aew bew) (< ans bns)))
   :eq (fn [aew ans bew bns] (and (= aew bew) (= ans bns)))})

(def ^:private places
  "Every place on a 3×3 grid.  A layout of three things is a weak ordering of three
  coordinates on each axis independently, so three values per axis realize every one."
  (vec (for [ew (range 3) ns (range 3)] [ew ns])))

(defn- holding [[aew ans] [bew bns]]
  (into #{} (keep (fn [[dir pred]] (when (pred aew ans bew bns) dir))) by-axes))

(defn- direction-of [a b] (first (holding a b)))

(def ^:private derived-composition
  "The composition table computed from `by-axes`: lay out three places every way they can
  sit on the grid, read off the three directions, and record that r1 ∘ r2 admits r3."
  (delay
    (reduce (fn [tbl [a b c]]
              (update-in tbl [(direction-of a b) (direction-of b c)]
                         (fnil conj #{}) (direction-of a c)))
            {}
            (for [a places b places c places] [a b c]))))

(deftest composition-is-computed-from-the-two-axis-projections
  (testing "two perpendicular directions combine into the diagonal between them"
    (is (= #{:ne} (dir/compose #{:n} #{:e})) "north then east is northeast")
    (is (= #{:ne} (dir/compose #{:e} #{:n})) "and so is east then north")
    (is (= #{:nw} (dir/compose #{:n} #{:w}))))
  (testing "an axis the two disagree on loses all information on that axis"
    (is (= #{:n :eq :s} (dir/compose #{:n} #{:s}))
        "north then south lands somewhere on the meridian — east-west still agrees")
    (is (= dir/all-directions (dir/compose #{:ne} #{:sw}))
        "opposite diagonals disagree on both axes at once, so nothing at all is left")))

(deftest the-composition-table-matches-the-axis-definitions
  ;; a permuted projection still passes the bijection check, and only this comparison
  ;; reddens on it
  (let [derived @derived-composition]
    (testing "every pair of directions composes to the same set the definitions give"
      (doseq [r1 dir/all-directions r2 dir/all-directions]
        (is (= (get-in derived [r1 r2]) (dir/compose #{r1} #{r2}))
            (str r1 " ∘ " r2))))
    (testing "and the derivation reaches all 81 pairs"
      (is (= dir/all-directions (set (keys derived))))
      (doseq [[_ row] derived]
        (is (= dir/all-directions (set (keys row))))))))

(deftest the-converse-flips-both-axes
  (is (= #{:s} (dir/converse-set #{:n})))
  (is (= #{:sw} (dir/converse-set #{:ne})))
  (is (= #{:eq} (dir/converse-set #{:eq})) "coincidence is its own converse"))

(tu/deftest-kb composition-derives-an-unasserted-direction
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "ne∘ne = ne, so A is northeast of D though nobody said so"
      (is (v/ask? kb (list 'northeastOf A D) C)))
    (testing "and the computed table pins it to exactly that"
      (is (= #{:ne} (qkb/possible dir/cardinal kb C A D)))
      (is (= :ne (qkb/definite dir/cardinal kb C A D))))
    (testing "so a direction the network excludes is not answered"
      (is (not (v/ask? kb (list 'southwestOf A D) C)))
      (is (not (v/ask? kb (list 'northOf A D) C)))
      (is (not (v/ask? kb (list 'sameLocationAs A D) C))))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "#{:ne} sits inside every denotation that contains it"
      (is (v/ask? kb (list 'northwardOf A D) C) "northwardOf ⊇ #{:n :ne :nw}")
      (is (v/ask? kb (list 'eastwardOf A D) C)  "eastwardOf  ⊇ #{:e :ne :se}"))
    (testing "and outside the two denotations that do not"
      (is (not (v/ask? kb (list 'southwardOf A D) C)))
      (is (not (v/ask? kb (list 'westwardOf A D) C))))
    (testing "the converse derived predicates hold the other way round"
      (is (v/ask? kb (list 'southwardOf D A) C))
      (is (v/ask? kb (list 'westwardOf D A) C)))))

(tu/deftest-kb the-converse-is-derived-with-the-fact
  (tu/with-terms [A B]
    (v/assert kb (list 'northOf A B) C)
    (testing "one asserted direction constrains the pair both ways round"
      (is (v/ask? kb (list 'northOf A B) C))
      (is (v/ask? kb (list 'southOf B A) C)))
    (testing "and rules the opposite readings out"
      (is (not (v/ask? kb (list 'southOf A B) C)))
      (is (not (v/ask? kb (list 'northOf B A) C)))
      (is (not (v/ask? kb (list 'eastwardOf A B) C))
          "due north is level on the east-west axis, so no easterly component"))))

(tu/deftest-kb an-axis-the-chain-disagrees-on-leaves-the-pair-open
  (tu/with-terms [A B D]
    (v/assert kb (list 'northOf A B) C)
    (v/assert kb (list 'southOf B D) C)
    (testing "north then south says only that A and D share a meridian"
      (is (= #{:n :eq :s} (qkb/possible dir/cardinal kb C A D)))
      (is (= :unknown (qkb/definite dir/cardinal kb C A D))))
    (testing "so no direction predicate is entailed — not even a derived one"
      (is (not (v/ask? kb (list 'northOf A D) C)))
      (is (not (v/ask? kb (list 'northwardOf A D) C)))
      (is (not (v/ask? kb (list 'sameLocationAs A D) C))))))

(tu/deftest-kb coincidence-carries-a-direction-across
  (tu/with-terms [A B D]
    (v/assert kb (list 'sameLocationAs A B) C)
    (v/assert kb (list 'northOf B D) C)
    (testing "eq is the identity, so A stands where B does"
      (is (= #{:n} (qkb/possible dir/cardinal kb C A D)))
      (is (v/ask? kb (list 'northOf A D) C)))))

(tu/deftest-kb an-open-argument-enumerates-the-entailed-places
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "(northeastOf A ?y) — every place A is entailed to be northeast of"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'northeastOf A '?y) C)))]
        (is (= #{B D} ys) "B by assertion and D by composition; not A itself")))
    (testing "(northwardOf ?x D) — every place entailed to lie north of D"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'northwardOf '?x D) C)))]
        (is (= #{A B} xs))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'eastwardOf '?x '?y) C)))]
        (is (= #{[A B] [A D] [B D]} pairs))))))
