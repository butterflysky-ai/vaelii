;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.engine-vocabulary-test
  "The terms the engine reads by name are declared in CxUniverse, so a KB can query what the
  engine answers and the vocabulary audit classifies each one.  Each row pins one
  declaration against the engine behaviour it describes."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private U 'CxUniverse)

;; ---- different -------------------------------------------------------------

(tu/deftest-kb different-is-declared-at-the-arity-its-prover-answers
  (testing "the declaration loads and the vocabulary audit classifies the term"
    (is (:enforced (v/interpreted 'different)))
    (is (true? (v/ask? kb '(variable_arity_predicate different) U)))
    (is (true? (v/ask? kb '(arityMin different 2) U)))
    (is (empty? (v/sentexes-matching kb '(args different ?t) '?ctx)))
    (is (true? (v/ask? kb '(commutative different) U))))
  (testing "two distinct names are different in either order"
    (tu/with-terms [Alpha Beta]
      (is (true? (v/ask? kb (list 'different Alpha Beta) U)))
      (is (true? (v/ask? kb (list 'different Beta Alpha) U)))
      (is (false? (v/ask? kb (list 'different Alpha Alpha) U))))))

;; ---- the equality relations and the rule and strength wrappers -------------

(tu/deftest-kb the-equality-relations-are-declared-binary-with-untyped-positions
  (doseq [r '[sameAs equals]]
    (is (:enforced (v/interpreted r)) (str r " is classified enforced"))
    (is (true? (v/ask? kb (list 'binary_predicate r) U)) (str r " is a binary_predicate"))
    (is (empty? (v/sentexes-matching kb (list 'arg r '?n '?t) '?ctx))
        (str r " declares no type: either side is a term of any kind")))
  (testing "a merge under either relation still answers from the closure"
    (tu/with-terms [Alpha Beta Gamma Delta]
      (v/assert kb (list 'sameAs Alpha Beta) U)
      (v/assert kb (list 'equals Gamma Delta) U)
      (is (true? (v/ask? kb (list 'sameAs Beta Alpha) U)))
      (is (true? (v/ask? kb (list 'equals Delta Gamma) U)))
      (is (false? (v/ask? kb (list 'different Alpha Beta) U))))))

(tu/deftest-kb every-wrapper-the-engine-peels-is-commented-and-classified
  (doseq [w '[set/forwardRule set/backwardRule set/defaultRule set/inertRule
              set/forwardOnlyRule set/solveRule set/assumptionRule
              set/hardConstraint set/softConstraint set/monotonic set/inert]]
    (is (:enforced (v/interpreted w)) (str w " is classified enforced"))))

;; ---- the signed integer types ----------------------------------------------

(tu/deftest-kb integer-is-partitioned-by-sign-twice
  (testing "each part is below integer through its partition"
    (doseq [t '[positive_integer non_positive_integer negative_integer non_negative_integer]]
      (is (true? (v/ask? kb (list 'genl t 'integer) U)) (str t " is below integer"))))
  (testing "the parts of one partition are disjoint, and the two partitions cross"
    (is (true? (v/ask? kb '(disjoint positive_integer non_positive_integer) U)))
    (is (true? (v/ask? kb '(disjoint negative_integer non_negative_integer) U)))
    (is (not (true? (v/ask? kb '(disjoint non_negative_integer non_positive_integer) U)))
        "zero is in both non_ types"))
  (testing "a literal is admitted by the sign types it has"
    (is (true? (v/ask? kb '(non_negative_integer 0) U)))
    (is (true? (v/ask? kb '(non_positive_integer 0) U)))
    (is (true? (v/ask? kb '(negative_integer -3) U)))
    (is (true? (v/ask? kb '(non_positive_integer -3) U)))
    (is (false? (v/ask? kb '(non_negative_integer -3) U)))))

;; ---- argN --------------------------------------------------------------------

(tu/deftest-kb argN-is-declared-with-position-0-admitted
  (is (:inert (v/interpreted 'argN)) "nothing in the engine derives or reads argN")
  (is (true? (v/ask? kb '(ternary_predicate argN) U)))
  (is (empty? (v/sentexes-matching kb '(arg argN 1 ?t) '?ctx)) "the term found declares no type")
  (is (true? (v/ask? kb '(arg argN 2 non_negative_integer) U))
      "position 0, the relation or operator, is in the type")
  (is (true? (v/ask? kb '(non_negative_integer 0) U)))
  (is (true? (v/ask? kb '(quotedArg argN 3 formula) U))))

(tu/deftest-kb an-argN-fact-at-position-0-is-admitted
  (tu/with-terms [likes Fred Mary]
    (v/assert kb (list 'argN likes 0 (list likes Fred Mary)) U)
    (v/assert kb (list 'argN Mary 2 (list likes Fred Mary)) U)
    (is (true? (v/ask? kb (list 'argN likes 0 (list likes Fred Mary)) U)))
    (is (true? (v/ask? kb (list 'argN Mary 2 (list likes Fred Mary)) U)))))
