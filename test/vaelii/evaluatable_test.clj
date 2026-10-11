;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.evaluatable-test
  "`add-evaluatable` — wrapping a plain Clojure fn as an evaluatable prover: the check
  shape (a computed truth) and the result-binding shape (a computed value), their
  registration through a KB, arity dispatch, and how a computed conjunct joins and reads
  as a leaf of a node-engine derivation."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the check shape: a computed truth ----------------------------------

(tu/deftest-kb a-check-predicate-holds-when-the-fn-returns-truthy
  (tu/with-terms [big_enough]
    (v/add-evaluatable kb big_enough (fn [n] (>= n 60)))
    (testing "the fn's truthy result is the predicate holding, its falsey result its failing"
      (is (v/ask? kb (list big_enough 75)))
      (is (v/ask? kb (list big_enough 60)))        ; the fn's own boundary: 60 >= 60
      (is (not (v/ask? kb (list big_enough 50)))))
    (testing "nothing is stored — the answer is computed, so no sentex is minted"
      (is (empty? (v/find-sentexes kb big_enough))))))

;; ---- the result-binding shape: a computed value -------------------------

(tu/deftest-kb a-result-binding-function-binds-the-output-slot
  (tu/with-terms [sumOf]
    (v/add-evaluatable kb sumOf + {:result :first})
    (testing "a variable output slot is bound to the fn's value"
      (is (= [{'?r 5}] (v/ask kb (list sumOf '?r 2 3)))))
    (testing "a ground output slot is checked against the value, not bound"
      (is (v/ask? kb (list sumOf 5 2 3)))
      (is (not (v/ask? kb (list sumOf 9 2 3)))))))

(tu/deftest-kb the-output-slot-can-sit-last-or-at-an-index
  (tu/with-terms [sumLast sumMid]
    (v/add-evaluatable kb sumLast + {:result :last})
    (v/add-evaluatable kb sumMid + {:result 1})
    (testing ":last names the final slot"
      (is (= [{'?r 5}] (v/ask kb (list sumLast 2 3 '?r)))))
    (testing "an integer index names an interior slot, the rest being the inputs"
      (is (= [{'?r 5}] (v/ask kb (list sumMid 2 '?r 3)))))
    (testing "an input still unbound computes nothing"
      (is (= [] (v/ask kb (list sumLast '?a 3 '?r)))))))

;; ---- registration composes through the KB's atom ------------------------

(tu/deftest-kb add-evaluatable-registers-through-the-provers-atom
  (tu/with-terms [triple]
    (let [before (count (provers/registry kb))
          ret    (v/add-evaluatable kb triple (fn [n] (* 3 n)) {:result :first})]
      (testing "it returns the kb and grows the live registry by one prover"
        (is (identical? kb ret))
        (is (= (inc before) (count (provers/registry kb)))))
      (testing "the added prover is the wrapper for this predicate"
        (is (some #(= triple (:pred %)) (provers/registry kb)))))))

;; ---- arity dispatch: only the form the fn can take ---------------------

(tu/deftest-kb arity-dispatch-leaves-other-shapes-to-other-provers
  (tu/with-terms [between]
    (v/add-evaluatable kb between (fn [lo x hi] (<= lo x hi)))   ; a 3-ary check
    (testing "a goal of the fn's arity is answered"
      (is (v/ask? kb (list between 1 2 3)))
      (is (not (v/ask? kb (list between 1 5 3)))))
    (testing "a goal of the wrong arity is not this prover's, so nothing answers it"
      (is (not (v/ask? kb (list between 1 2))))
      (is (not (v/ask? kb (list between 1 2 3 4)))))
    (testing "an explicit :arity lets a variadic fn declare the shapes it takes"
      (tu/with-terms [chainMax]
        (v/add-evaluatable kb chainMax (fn [& xs] (apply max xs)) {:result :first :arity #{2 3}})
        (is (= [{'?m 9}] (v/ask kb (list chainMax '?m 4 9))))
        (is (= [{'?m 9}] (v/ask kb (list chainMax '?m 4 9 2))))))))

;; ---- a thrown fn is no solution, never a crashed query ------------------

(tu/deftest-kb a-thrown-fn-yields-no-solution
  (tu/with-terms [quotient]
    (v/add-evaluatable kb quotient / {:result :first})
    (testing "an ordinary computation binds"
      (is (= [{'?q 3}] (v/ask kb (list quotient '?q 6 2)))))
    (testing "a division by zero throws inside the fn and reads as no solution"
      (is (= [] (v/ask kb (list quotient '?q 1 0))))
      (is (not (v/ask? kb (list quotient '?q 1 0)))))))

;; ---- a computed conjunct joins in the node engine -----------------------

(tu/deftest-kb an-evaluatable-check-joins-after-the-generator-that-binds-it
  (tu/with-terms [big_enough hasScore Alice Bob]
    (v/add-evaluatable kb big_enough (fn [n] (>= n 60)))
    (v/assert kb (list hasScore Alice 75) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list hasScore Bob 40)   'CxUniverse {:strength :monotonic})
    (testing "the join binds ?n from the fact and then computes the check — either order"
      (is (= #{Alice}
             (set (map #(get % '?x)
                       (v/query kb [(list hasScore '?x '?n) (list big_enough '?n)]
                                'CxUniverse {:max-depth 1})))))
      (is (= #{Alice}
             (set (map #(get % '?x)
                       (v/query kb [(list big_enough '?n) (list hasScore '?x '?n)]
                                'CxUniverse {:max-depth 1}))))))
    (testing "a result-binding function likewise consumes a bound input and produces a value"
      (tu/with-terms [doubled]
        (v/add-evaluatable kb doubled (fn [n] (* 2 n)) {:result :first})
        (is (= #{[Alice 150] [Bob 80]}
               (set (map (juxt #(get % '?x) #(get % '?d))
                         (v/query kb [(list hasScore '?x '?n) (list doubled '?d '?n)]
                                  'CxUniverse {:max-depth 1})))))))))

;; ---- an evaluatable is a leaf of a derivation, and it follows belief ----

(tu/deftest-kb an-evaluatable-reads-as-a-leaf-of-a-rule-derivation
  (tu/with-terms [passing hasScore hasPassed Alice Bob]
    (v/add-evaluatable kb passing (fn [n] (>= n 60)))
    (v/assert kb (list hasScore Alice 75) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list hasScore Bob 40)   'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies
                       (list 'and (list hasScore '?x '?n) (list passing '?n))
                       (list hasPassed '?x))
              'CxUniverse {:direction :forward})
    (testing "the rule derives only the individual whose bound score computes true"
      (is (= #{Alice}
             (set (map #(get % '?x)
                       (v/query kb (list hasPassed '?x) 'CxUniverse {:max-depth 2}))))))
    ;; Forward chaining materializes the conclusion (an evaluatable antecedent is computed
    ;; in the join, not looked up and dropped), so a `query {:proof? true}` reads the
    ;; *believed* `(hasPassed Alice)` off the engine's leaf solver directly and expands no
    ;; rule: the search proof stops there — `:via :leaf`, no `:because`.  Provenance lives
    ;; in the stored justification instead, which `why` reads.  That is `proof-tree`'s
    ;; contract: the search proof is for what the KB *derives*, `why` for what it *holds*,
    ;; and a materialized conclusion is held.
    (testing "the materialized conclusion appears as a stored leaf of the query proof"
      (let [proof (:proof (tu/sole-answer (v/query kb (list hasPassed Alice) 'CxUniverse
                                                   {:max-depth 2 :proof? true})))]
        (is (= [:leaf] (mapv :via proof)))
        (is (empty? (mapcat :because proof)))))
    (testing "the computed antecedent is traceable through the stored justification (why)"
      (let [h            (v/handle-of kb (list hasPassed Alice) 'CxUniverse)
            w            (v/why kb h)
            support      (:support w)
            rule-syms    (into #{} (mapcat (comp flatten :rule)) support)
            because-syms (into #{} (comp (mapcat :because) (mapcat (comp flatten :sentence)))
                               support)]
        (testing "the belief is held, drawn by the rule whose antecedent is the evaluatable"
          (is (:believed? w))
          (is (contains? rule-syms passing))       ; the computed check is in the firing rule
          (is (contains? rule-syms hasScore)))
        (testing "and it rests on the handle-bearing antecedent — the score fact"
          ;; the computed antecedent contributes no handle, by design, so `:because`
          ;; carries the fact that gives the belief something to be withdrawn with
          (is (contains? because-syms hasScore))
          (is (contains? because-syms Alice)))))
    (testing "the derivation follows belief: retract the supporting fact and it is gone"
      (let [h (v/handle-of kb (list hasScore Alice 75) 'CxUniverse)]
        (v/retract! kb h)
        (is (empty? (v/query kb (list hasPassed '?x) 'CxUniverse {:max-depth 2})))))))

;; ---- forward chaining computes an evaluatable antecedent, so ask? = query ----
;; Forward chaining computes an evaluatable antecedent through the registry rather than
;; looking it up as a stored fact, so it materializes the firing and `ask?` — which
;; reads what forward chaining materialized — agrees with `query`, whose leaf is the
;; registry.  Assert the same rule with a stored-fact leaf for the evaluatable and the
;; firing would be dropped, splitting the two; they must agree.

(tu/deftest-kb ask-and-query-agree-on-a-forward-rule-with-an-evaluatable-antecedent
  (tu/with-terms [big_enough score topScorer Alice Carol]
    (v/add-evaluatable kb big_enough (fn [n] (> n 60)))
    ;; rule asserted *before* the facts — the join runs as each fact arrives
    (v/assert kb (list 'implies
                       (list 'and (list score '?x '?s) (list big_enough '?s))
                       (list topScorer '?x))
              'CxUniverse {:direction :forward :strength :monotonic})
    (v/assert kb (list score Alice 90) 'CxUniverse {:strength :monotonic})   ; 90 > 60 holds
    (v/assert kb (list score Carol 40) 'CxUniverse {:strength :monotonic})   ; 40 > 60 fails
    (testing "the computed antecedent holds — ask? materializes the conclusion query derives"
      (is (v/ask? kb (list topScorer Alice)))
      (is (seq (v/query kb (list topScorer Alice) 'CxUniverse {:max-depth 5})))
      (is (= (v/ask? kb (list topScorer Alice))
             (boolean (seq (v/query kb (list topScorer Alice) 'CxUniverse {:max-depth 5}))))))
    (testing "the computed antecedent fails — both agree the conclusion is not drawn"
      (is (not (v/ask? kb (list topScorer Carol))))
      (is (empty? (v/query kb (list topScorer Carol) 'CxUniverse {:max-depth 5})))
      (is (= (v/ask? kb (list topScorer Carol))
             (boolean (seq (v/query kb (list topScorer Carol) 'CxUniverse {:max-depth 5}))))))))

;; ---- and the firing is order-independent, facts before the rule --------------
;; `planned-join` pins the evaluatable after its binder by cost, not by the static
;; canonical antecedent order (which a per-KB evaluatable is not in), so which of the
;; fact and the rule arrives first cannot change what is derived.

(tu/deftest-kb an-evaluatable-antecedent-fires-with-the-facts-asserted-before-the-rule
  (tu/with-terms [big_enough score topScorer Dave Erin]
    (v/add-evaluatable kb big_enough (fn [n] (> n 60)))
    (v/assert kb (list score Dave 90) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list score Erin 40) 'CxUniverse {:strength :monotonic})
    ;; the rule is added last — `fire-rule` runs the full join over the existing facts,
    ;; and the evaluatable must still land after `score` binds its input
    (v/assert kb (list 'implies
                       (list 'and (list score '?x '?s) (list big_enough '?s))
                       (list topScorer '?x))
              'CxUniverse {:direction :forward :strength :monotonic})
    (testing "the full join over stored facts computes the check for each"
      (is (v/ask? kb (list topScorer Dave)))
      (is (not (v/ask? kb (list topScorer Erin))))
      (is (= #{Dave}
             (set (map #(get % '?x)
                       (v/query kb (list topScorer '?x) 'CxUniverse {:max-depth 5}))))))))

;; ---- the sole-prover guard applies to the wrapper too -------------------

(tu/deftest-kb a-rule-concluding-the-predicate-stops-the-evaluatable-running-alone
  (tu/with-terms [flag someType Thing1]
    (v/add-evaluatable kb flag (fn [n] (pos? n)))
    (testing "with nothing else reaching the predicate, the wrapper is the sole prover"
      (is (empty? (provers/shadowing-channels kb (list flag 3) 'CxUniverse)))
      (let [appl (provers/applicable-provers kb (provers/registry kb) (list flag 3) 'CxUniverse)]
        (is (= flag (:pred (provers/sole-prover kb appl (list flag 3) 'CxUniverse))))))
    (testing "a rule that could also conclude the predicate opens the :rules channel,"
      (v/assert kb (list 'genl someType 'thing) 'CxUniverse)
      (v/assert kb (list 'implies (list someType '?x) (list flag 1)) 'CxUniverse
                {:direction :backward})
      (is (contains? (provers/shadowing-channels kb (list flag 3) 'CxUniverse) :rules))
      (testing "so the wrapper no longer runs alone — the union includes the rule"
        (let [appl (provers/applicable-provers kb (provers/registry kb) (list flag 3) 'CxUniverse)]
          (is (nil? (provers/sole-prover kb appl (list flag 3) 'CxUniverse))))))))
