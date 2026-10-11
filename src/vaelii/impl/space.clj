;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.space
  "RCC-8 topology: the eight base region relations, the six derived predicates, the
  transcribed composition table, and the calculus and prover over `vaelii.impl.qcn-kb`.
  See docs/space.md."
  (:require [vaelii.impl.qcn-kb :as qkb]))

(def all-relations
  "The eight RCC-8 base relations: the universe of the algebra."
  #{:dc :ec :po :eq :tpp :ntpp :tppi :ntppi})

(def rcc8-converse
  "Each base relation's converse."
  {:dc :dc, :ec :ec, :po :po, :eq :eq,
   :tpp :tppi, :ntpp :ntppi, :tppi :tpp, :ntppi :ntpp})

(defn converse-set
  "The converse of a relation set: the constraint on `(b a)` that one on `(a b)` gives."
  [rels]
  (into #{} (map rcc8-converse) rels))

(def rcc8-composition
  "The Randell–Cui–Cohn composition table: `(get-in rcc8-composition [r1 r2])` is the set
  of base relations possible between x and z given `r1`(x,y) and `r2`(y,z).
  `qcn_algebra_test` holds the relation-algebra laws over it (docs/qcn.md)."
  {:dc    {:dc    all-relations
           :ec    #{:dc :ec :po :tpp :ntpp}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:dc :ec :po :tpp :ntpp}
           :ntpp  #{:dc :ec :po :tpp :ntpp}
           :tppi  #{:dc}
           :ntppi #{:dc}
           :eq    #{:dc}}
   :ec    {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:dc :ec :po :tpp :tppi :eq}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:ec :po :tpp :ntpp}
           :ntpp  #{:po :tpp :ntpp}
           :tppi  #{:dc :ec}
           :ntppi #{:dc}
           :eq    #{:ec}}
   :po    {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:dc :ec :po :tppi :ntppi}
           :po    all-relations
           :tpp   #{:po :tpp :ntpp}
           :ntpp  #{:po :tpp :ntpp}
           :tppi  #{:dc :ec :po :tppi :ntppi}
           :ntppi #{:dc :ec :po :tppi :ntppi}
           :eq    #{:po}}
   :tpp   {:dc    #{:dc}
           :ec    #{:dc :ec}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:tpp :ntpp}
           :ntpp  #{:ntpp}
           :tppi  #{:dc :ec :po :tpp :tppi :eq}
           :ntppi #{:dc :ec :po :tppi :ntppi}
           :eq    #{:tpp}}
   :ntpp  {:dc    #{:dc}
           :ec    #{:dc}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:ntpp}
           :ntpp  #{:ntpp}
           :tppi  #{:dc :ec :po :tpp :ntpp}
           :ntppi all-relations
           :eq    #{:ntpp}}
   :tppi  {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:ec :po :tppi :ntppi}
           :po    #{:po :tppi :ntppi}
           :tpp   #{:po :eq :tpp :tppi}
           :ntpp  #{:po :tpp :ntpp}
           :tppi  #{:tppi :ntppi}
           :ntppi #{:ntppi}
           :eq    #{:tppi}}
   :ntppi {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:po :tppi :ntppi}
           :po    #{:po :tppi :ntppi}
           :tpp   #{:po :tppi :ntppi}
           :ntpp  #{:po :tpp :ntpp :tppi :ntppi :eq}
           :tppi  #{:ntppi}
           :ntppi #{:ntppi}
           :eq    #{:ntppi}}
   :eq    {:dc #{:dc} :ec #{:ec} :po #{:po} :tpp #{:tpp}
           :ntpp #{:ntpp} :tppi #{:tppi} :ntppi #{:ntppi} :eq #{:eq}}})

(defn compose
  "The composition of two relation sets: the union of the table entries over every pair of
  members."
  [s1 s2]
  (into #{}
        (mapcat (fn [a] (mapcat (fn [b] (get-in rcc8-composition [a b])) s2)))
        s1))

(def rcc8-algebra
  "RCC-8 as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:eq}
   :compose  compose
   :converse converse-set})

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under."
  '{:dc    spatiallyDisconnected
    :ec    externallyConnected
    :po    partiallyOverlapping
    :eq    spatiallyEqual
    :tpp   tangentialProperPart
    :ntpp  nonTangentialProperPart
    :tppi  tangentialProperPartInverse
    :ntppi nonTangentialProperPartInverse})

(def spatial-denotation
  "Every RCC-8 predicate, the eight base and the six derived, mapped to the set of base
  relations it denotes."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{regionConnectedTo  #{:ec :po :eq :tpp :ntpp :tppi :ntppi}
     partOfRegion       #{:tpp :ntpp :eq}
     properPartOfRegion #{:tpp :ntpp}
     hasRegionPart      #{:tppi :ntppi :eq}
     regionOverlaps     #{:po :tpp :ntpp :tppi :ntppi :eq}
     regionDiscreteFrom #{:dc :ec}}))

(def spatial-predicates
  "The predicates the RCC-8 prover claims: the keys of `spatial-denotation`."
  (set (keys spatial-denotation)))

(def rcc8
  "RCC-8 as a `vaelii.impl.qcn-kb` calculus."
  (qkb/calculus :rcc8 rcc8-algebra spatial-denotation))

(defn spatial-prover
  "The RCC-8 entailment prover, which `vaelii.core/add-reasoner` registers as `:rcc8`."
  []
  (qkb/prover rcc8))
