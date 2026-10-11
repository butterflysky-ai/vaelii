;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.orientation
  "Cardinal direction: nine base directions, each an `[east-west north-south]` pair of
  point relations, four derived predicates, and the calculus and prover over
  `vaelii.impl.qcn-kb`. `vaelii.impl.projection` computes composition and converse from
  the projection table. See docs/space.md."
  (:require [vaelii.impl.projection :as proj]
            [vaelii.impl.qcn-kb :as qkb]))

(def direction->xy
  "Each base direction as its `[x y]` projection: x the east-west relation of the target,
  y the north-south one."
  {:n  [:eq :gt], :ne [:gt :gt], :e [:gt :eq], :se [:gt :lt]
   :s  [:eq :lt], :sw [:lt :lt], :w [:lt :eq], :nw [:lt :gt]
   :eq [:eq :eq]})

(def direction-algebra
  "The cardinal directions as a `vaelii.impl.qcn` relation algebra."
  (proj/algebra direction->xy))

(def all-directions
  "The nine base directions: the universe of the algebra."
  (:universe direction-algebra))

(def compose
  "The composition of two direction sets, computed axis-wise."
  (:compose direction-algebra))

(def converse-set
  "The converse of a direction set: both axes flipped."
  (:converse direction-algebra))

(def base-direction-predicate
  "Base direction keyword → the binary predicate a fact about it is stored under."
  '{:n  northOf,     :ne northeastOf, :e eastOf, :se southeastOf
    :s  southOf,     :sw southwestOf, :w westOf, :nw northwestOf
    :eq sameLocationAs})

(def direction-denotation
  "Every direction predicate, the nine base and the four derived, mapped to the set of
  base directions it denotes."
  (merge
   (into {} (map (fn [[dir pred]] [pred #{dir}])) base-direction-predicate)
   '{northwardOf #{:n :ne :nw}
     southwardOf #{:s :se :sw}
     eastwardOf  #{:e :ne :se}
     westwardOf  #{:w :nw :sw}}))

(def cardinal
  "The cardinal directions as a `vaelii.impl.qcn-kb` calculus."
  (qkb/calculus :cardinal direction-algebra direction-denotation))

(defn orientation-prover
  "The cardinal-direction entailment prover, which `vaelii.core/add-reasoner` registers as
  `:cardinal`."
  []
  (qkb/prover cardinal))
