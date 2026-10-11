;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.relative
  "Relative direction: nine base relations, each a `[left-right front-back]` pair of point
  relations in the frame of reference a context states, four derived predicates, and the
  calculus and prover over `vaelii.impl.qcn-kb`. The context is the viewpoint, so the
  calculus is binary. `vaelii.impl.projection` computes composition and converse from the
  projection table. See docs/space.md."
  (:require [vaelii.impl.projection :as proj]
            [vaelii.impl.qcn-kb :as qkb]))

(def relation->axes
  "Each base relation as its `[left-right front-back]` projection. The coordinates grow
  rightwards and frontwards, so `:lt` on the first axis is to the left and `:gt` on the
  second is in front."
  {:left  [:lt :eq], :front-left  [:lt :gt], :behind-left  [:lt :lt]
   :right [:gt :eq], :front-right [:gt :gt], :behind-right [:gt :lt]
   :front [:eq :gt], :behind      [:eq :lt], :eq           [:eq :eq]})

(def relative-algebra
  "The relative frame as a `vaelii.impl.qcn` relation algebra."
  (proj/algebra relation->axes))

(def all-relations
  "The nine base relations: the universe of the algebra."
  (:universe relative-algebra))

(def compose
  "The composition of two relation sets, computed axis-wise."
  (:compose relative-algebra))

(def converse-set
  "The converse of a relation set: both axes flipped."
  (:converse relative-algebra))

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under."
  '{:left         leftOf
    :right        rightOf
    :front        inFrontOf
    :behind       behind
    :front-left   frontLeftOf
    :front-right  frontRightOf
    :behind-left  behindLeftOf
    :behind-right behindRightOf
    :eq           sameRelativePositionAs})

(def relative-denotation
  "Every relative-direction predicate, the nine base and the four derived, mapped to the
  set of base relations it denotes."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{leftwardOf  #{:left :front-left :behind-left}
     rightwardOf #{:right :front-right :behind-right}
     frontwardOf #{:front :front-left :front-right}
     rearwardOf  #{:behind :behind-left :behind-right}}))

(def relative
  "Relative direction as a `vaelii.impl.qcn-kb` calculus."
  (qkb/calculus :relative relative-algebra relative-denotation))

(defn relative-prover
  "The relative-direction entailment prover, which `vaelii.core/add-reasoner` registers as
  `:relative`."
  []
  (qkb/prover relative))
