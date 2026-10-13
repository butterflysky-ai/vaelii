;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.matches-pattern-test
  "`matchesPattern` — the computed string-shape check that lets a `defn` over a string
  subtype resolve **by evaluation**, the way `integer` lets the sign-refined integer
  collections resolve (docs/defns.md).  `(matchesPattern ?string ?pattern)` holds when the
  whole of `?string` matches the regular expression `?pattern`, both ground strings; the
  match runs through a step-limited view, and a pattern that does not compile is refused at
  the assert entry point."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private ipv4-pattern
  "A dotted-quad shape, loose on the digit count — enough to separate an address-shaped
  string from one that is not, which is what these tests need."
  "\\d+\\.\\d+\\.\\d+\\.\\d+")

;; ---- 1. the primitive: matchesPattern is computed from two ground strings ----

(tu/deftest-kb matchesPattern-is-a-computed-string-shape-check
  (testing "the whole string matches, or it does not"
    (is (v/ask? kb (list 'matchesPattern "192.168.1.1" ipv4-pattern) 'CxUniverse)
        "an address-shaped string matches")
    (is (not (v/ask? kb (list 'matchesPattern "not-an-ip" ipv4-pattern) 'CxUniverse))
        "a non-address does not"))
  (testing "the match is anchored to the whole string, not a substring"
    (is (not (v/ask? kb (list 'matchesPattern "192.168.1.1 and more" ipv4-pattern) 'CxUniverse))
        "a trailing tail fails a whole-string match"))
  (testing "a non-string subject is a sound no, the way integer is for a non-integer"
    (is (not (v/ask? kb (list 'matchesPattern 5 ipv4-pattern) 'CxUniverse))
        "5 is not a string")))

;; ---- 2. a string subtype defined over matchesPattern admits by evaluation ----

(tu/deftest-kb a-string-subtype-admits-by-evaluation
  ;; matchesPattern already answers false for a non-string subject, so the shape check
  ;; alone defines the subtype — no separate (string ?x) conjunct, which is not evaluable.
  (tu/with-terms [dotted_quad]
    (v/assert kb (list 'genl dotted_quad 'string) 'CxUniverse)
    (v/assert kb (list 'defnSufficient dotted_quad (list 'matchesPattern '?x ipv4-pattern)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dotted_quad (list 'matchesPattern '?x ipv4-pattern)) 'CxUniverse)
    (testing "a member is admitted from a bare string, at zero sentex cost"
      (is (v/ask? kb (list dotted_quad "192.168.1.1") 'CxUniverse) "an address-shaped string")
      (is (v/ask? kb (list dotted_quad "10.0.0.1") 'CxUniverse)    "another"))
    (testing "and a non-member is not"
      (is (not (v/ask? kb (list dotted_quad "not-an-ip") 'CxUniverse))    "wrong shape")
      (is (not (v/ask? kb (list dotted_quad "192.168.1.1x") 'CxUniverse)) "a trailing character"))))

;; ---- 3. non-membership is provable via a failing necessary ----

(tu/deftest-kb a-string-subtype-disproves-via-a-failing-necessary
  (tu/with-terms [dotted_quad]
    (v/assert kb (list 'genl dotted_quad 'string) 'CxUniverse)
    (v/assert kb (list 'defnNecessary dotted_quad (list 'matchesPattern '?x ipv4-pattern)) 'CxUniverse)
    (is (v/ask? kb (list 'not (list dotted_quad "not-an-ip")) 'CxUniverse)
        "a wrong-shape string fails the necessary, so ¬membership is provable")
    (is (v/ask? kb (list 'not (list dotted_quad 5)) 'CxUniverse)
        "a non-string fails matchesPattern too")
    (testing "but a genuine member is NOT disproved"
      (is (not (v/ask? kb (list 'not (list dotted_quad "192.168.1.1")) 'CxUniverse))
          "an address-shaped string IS a member, so its negation must not be provable"))))

;; ---- 4. an uncompilable pattern is refused at the assert entry point ----

(tu/deftest-kb an-uncompilable-pattern-is-refused-at-the-assert-entry-point
  (testing "a pattern that does not compile is a :bad-pattern refusal"
    (let [problems (v/check kb (list 'matchesPattern "x" "(") 'CxUniverse)]
      (is (= :bad-pattern (:type (first problems)))
          "the unclosed group is reported, not left to fail silently at query time")))
  (testing "a compilable pattern raises no problem"
    (is (empty? (v/check kb (list 'matchesPattern "x" ipv4-pattern) 'CxUniverse))
        "a valid pattern is admitted")))

;; ---- 5. a rule antecedent on matchesPattern or integer is computed ----

(tu/deftest-kb a-rule-antecedent-on-matchesPattern-or-integer-fires
  ;; Written with the computed literal first: canonical order moves it after the
  ;; generator that binds its input, so the join reaches it with that input ground.
  (tu/with-terms [hasLabel hasCount flagged_thing counted_thing named_thing ItemOne ItemTwo]
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list 'matchesPattern '?s "a+b")
                                            (list hasLabel '?x '?s))
                             (list flagged_thing '?x)))
              'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list 'integer '?n) (list hasCount '?x '?n))
                             (list counted_thing '?x)))
              'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list 'matchesPattern '?s "b+c?")
                                      (list hasLabel '?x '?s))
                       (list named_thing '?x))
              'CxUniverse)
    (v/assert kb (list hasLabel ItemOne "aab") 'CxUniverse)
    (v/assert kb (list hasLabel ItemTwo "bbc") 'CxUniverse)
    (v/assert kb (list hasCount ItemOne 3) 'CxUniverse)
    (v/assert kb (list hasCount ItemTwo 3.5) 'CxUniverse)
    (testing "a forward rule concludes only of the string that matches"
      (is (v/ask? kb (list flagged_thing ItemOne) 'CxUniverse))
      (is (not (v/ask? kb (list flagged_thing ItemTwo) 'CxUniverse))))
    (testing "a forward rule concludes only of the integer"
      (is (v/ask? kb (list counted_thing ItemOne) 'CxUniverse))
      (is (not (v/ask? kb (list counted_thing ItemTwo) 'CxUniverse))))
    (testing "a backward rule answers the same way, under prove and the node engine"
      (is (= [{'?x ItemTwo}] (v/prove kb (list named_thing '?x) 'CxUniverse)))
      (is (= [{'?x ItemTwo}] (v/query kb (list named_thing '?x) 'CxUniverse {:max-depth 1}))))
    (testing "either written order stores one rule"
      (is (= (v/assert kb (list 'set/forwardRule
                                (list 'implies (list 'and (list hasLabel '?x '?s)
                                                     (list 'matchesPattern '?s "a+b"))
                                      (list flagged_thing '?x)))
                       'CxUniverse)
             (v/handle-of kb (list 'set/forwardRule
                                   (list 'implies (list 'and (list 'matchesPattern '?s "a+b")
                                                        (list hasLabel '?x '?s))
                                         (list flagged_thing '?x)))
                          'CxUniverse))))))
