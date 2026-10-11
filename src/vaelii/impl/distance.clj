;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.distance
  "Qualitative distance: seven classes tiling `[0, ∞)`, three derived ranges, composition
  computed from the class bounds by the triangle inequality, and the calculus and prover
  over `vaelii.impl.qcn-kb`. See docs/space.md."
  (:require [vaelii.impl.qcn-kb :as qkb]))

(def class-order
  "The seven classes, nearest first: the order `classify` and `compose` walk."
  [:co :very-close :close :near :moderate :far :very-far])

(def class-bounds
  "Each class as the bounds `[lo hi]` of the half-open interval `(lo, hi]` of distances it
  covers. The intervals tile the non-negative reals in `class-order`, and `:co` runs from
  -∞ so that it denotes exactly zero. Scaling every finite bound by one factor leaves
  `compose` unchanged."
  {:co         [##-Inf 0]
   :very-close [0 1]
   :close      [1 10]
   :near       [10 100]
   :moderate   [100 1000]
   :far        [1000 10000]
   :very-far   [10000 ##Inf]})

(def all-classes
  "The seven classes: the universe of the algebra."
  (set class-order))

(defn classify
  "The single class a numeric distance `d` falls in.  The classes tile `[0, ∞)`, so this is
  total over real distances — and nil for a negative number, which is no distance at all
  and which `:co`'s unbounded lower end would otherwise swallow."
  [d]
  (when-not (neg? d)
    (first (filter (fn [c]
                     (let [[lo hi] (class-bounds c)]
                       (and (< lo d) (<= d hi))))
                   class-order))))

(defn- triangle-range
  "The half-open range `(L, H]` of distances possible between A and C when d(A,B) lies in
  `(l1, h1]` and d(B,C) in `(l2, h2]`: the triangle inequality read on the bounds. L is
  exclusive because d1 > l1 and d2 <= h2 give d1 - d2 > l1 - h2."
  [[l1 h1] [l2 h2]]
  [(max (- l1 h2) (- l2 h1)) (+ h1 h2)])

(defn- meets?
  "Do the half-open ranges `(lo, hi]` and `(l, h]` share a distance?"
  [[lo hi] [l h]]
  (and (< lo h) (< l hi)))

(defn compose
  "The composition of two class sets: every class whose interval meets the triangle range
  of some pair of members."
  [s1 s2]
  (into #{}
        (for [c1 s1 c2 s2
              :let [r (triangle-range (class-bounds c1) (class-bounds c2))]
              c   class-order
              :when (meets? (class-bounds c) r)]
          c)))

(defn converse-set
  "The converse of a class set: itself, since d(a,b) = d(b,a)."
  [classes]
  classes)

(def distance-algebra
  "Qualitative distance as a `vaelii.impl.qcn` relation algebra."
  {:universe all-classes
   :identity #{:co}
   :compose  compose
   :converse converse-set})

(def base-class-predicate
  "Distance class keyword → the binary predicate a fact about it is stored under."
  '{:co         coLocatedWith
    :very-close veryCloseTo
    :close      closeTo
    :near       nearTo
    :moderate   moderatelyFarFrom
    :far        farFrom
    :very-far   veryFarFrom})

(def distance-denotation
  "Every distance predicate, the seven base and the three derived ranges, mapped to the set
  of classes it denotes."
  (merge
   (into {} (map (fn [[cls pred]] [pred #{cls}])) base-class-predicate)
   {'withinNearDistanceOf  #{:co :very-close :close :near}
    'beyondFarDistanceFrom #{:far :very-far}
    'atSomeDistanceFrom    (disj all-classes :co)}))

(def qualitative-distance
  "Qualitative distance as a `vaelii.impl.qcn-kb` calculus."
  (qkb/calculus :distance distance-algebra distance-denotation))

(defn distance-prover
  "The qualitative-distance entailment prover, which `vaelii.core/add-reasoner` registers
  as `:distance`."
  []
  (qkb/prover qualitative-distance))
