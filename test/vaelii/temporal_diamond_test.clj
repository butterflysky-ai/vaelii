;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.temporal-diamond-test
  "The Nixon diamond over time.  A quaker is a pacifist by default and a republican is not
  a pacifist by default.  Dick1 is a quaker for his whole life and a republican for one
  stretch of it.

  A claim that holds over part of a life belongs in a context bounded to that time (the
  `empty` comment in CxCore).  So the life is one context, and each stretch of it is a
  context below the life: the youth, the term and the retirement.  The life states the
  order of the three stretches with Allen relations, and the interval algebra composes
  them.

  Outside the term only the quaker default applies, so Dick1 is a pacifist at `:default`
  and no reader there reads a dilemma.  Inside the term the two defaults collide.  The engine
  represents the collision as a dilemma and does not decide it: both sides stay believed
  at `:default`, `contradictions` reports the pair, and the cautious reading
  (`docs/labeling.md`) concludes neither side.  A second individual who is a quaker and a
  republican for his whole life holds the dilemma in every stretch."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxTime "upper"]])
                        (v/add-prover (iv/allen-prover))
                        (v/add-reasoner :brave-cautious))))

(defn- default-rule [ante conseq]
  (list 'set/defaultRule (list 'set/forwardRule (list 'implies ante conseq))))

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(defn- holds?     [s ctx] (boolean (v/ask? tu/*kb* s ctx)))
(defn- cautious?  [s ctx] (boolean (v/ask? tu/*kb* (list 'cautiously s) ctx)))
(defn- dilemma-at?
  "Does reader `ctx` see the pair of stored handles `hs` as a dilemma?"
  [hs ctx]
  (boolean (some #(= hs (:nogood %)) (v/contradictions tu/*kb* ctx))))

(tu/deftest-kb diamonds-are-forever
  (tu/with-terms [quaker republican pacifist Dick1 Dick2 Youth Term Retirement
                  CxLife CxYouth CxTerm CxRetirement]
    (v/assert kb (list 'genlCx CxLife 'CxUniverse) 'CxUniverse)
    (doseq [c [CxYouth CxTerm CxRetirement]]
      (v/assert kb (list 'genlCx c CxLife) 'CxUniverse))
    (v/assert kb (default-rule (list quaker '?x) (list pacifist '?x)) CxLife)
    (v/assert kb (default-rule (list republican '?x) (list 'not (list pacifist '?x))) CxLife)
    (v/assert kb (list 'meets Youth Term) CxLife)
    (v/assert kb (list 'meets Term Retirement) CxLife)
    ;; Dick1: a quaker for the whole life, a republican for the term alone.
    (v/assert kb (list quaker Dick1) CxLife)
    (v/assert kb (list republican Dick1) CxTerm)
    (let [pos (list pacifist Dick1)
          neg (list 'not (list pacifist Dick1))
          hs  #{(v/handle-of kb pos CxLife) (v/handle-of kb neg CxTerm)}]
      (testing "the life orders its three stretches"
        (is (holds? (list 'before Youth Retirement) CxLife)
            "youth meets the term and the term meets retirement, so youth is before retirement"))
      (testing "outside the term, only the quaker default applies"
        (doseq [c [CxLife CxYouth CxRetirement]]
          (is (holds? pos c) (str "pacifist in " c))
          (is (not (holds? neg c)) (str "no denial in " c))
          (is (not (dilemma-at? hs c)) (str "no dilemma read in " c)))
        (is (= :default (v/defeat-class kb (v/handle-of kb pos CxLife)))))
      (testing "inside the term, the two defaults form a dilemma the engine does not decide"
        (is (holds? pos CxTerm))
        (is (holds? neg CxTerm))
        (is (= :default (v/defeat-class kb (v/handle-of kb neg CxTerm))))
        (is (dilemma-at? hs CxTerm) "contradictions reports the pair to the term's reader")
        (is (empty? (v/conflicts kb)) "a dilemma is not a hard clash")
        (is (not (cautious? pos CxTerm)) "no cautious pacifism in the term")
        (is (not (cautious? neg CxTerm)) "and no cautious denial either")))
    ;; Dick2: a quaker and a republican for the whole life, the republican side stated first.
    (v/assert kb (list republican Dick2) CxLife)
    (v/assert kb (list quaker Dick2) CxLife)
    (let [pos (list pacifist Dick2)
          neg (list 'not (list pacifist Dick2))
          hs  #{(v/handle-of kb pos CxLife) (v/handle-of kb neg CxLife)}]
      (testing "the diamond held for the whole life holds in every stretch"
        (doseq [c [CxLife CxYouth CxTerm CxRetirement]]
          (is (dilemma-at? hs c) (str "the dilemma is read in " c))
          (is (holds? pos c) (str "the pacifist side stands in " c))
          (is (holds? neg c) (str "the denial stands in " c))
          (is (not (cautious? pos c)) (str "no cautious pacifism in " c))
          (is (not (cautious? neg c)) (str "no cautious denial in " c)))
        (is (empty? (v/conflicts kb)))))))
