;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kind-antecedent-forward-test
  "Forward rules whose only antecedent is a `string`, `number`, `boolean` or `sentence`
  literal.

  These tests pin what forward chaining does with such a rule.  A rule whose only
  antecedent is `(k ?x)` has no stored fact to trigger it: a prover answers each kind,
  and no datum carries the kind's functor.  An arriving fact that holds a value of the
  kind does not fire the rule."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

;; The fixture loads the upper layer, whose reflection.txt holds the expression lattice
;; `sentence` answers in.
(use-fixtures :once (tu/loaded #(doto % (core-context/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private Quote
  "The engine's `Quote`, the quoting function a `sentence` antecedent reads."
  sx/quote-functor)

(def ^:private cases
  "Each kind beside a value of that kind, as `[kind value]`."
  [['string "rex"]
   ['number 2.5]
   ['boolean true]
   ['sentence (list Quote (list 'not (list 'dog 'Muffet)))]])

(defn- setup!
  "State what a `sentence` value needs: `Quote` as a function and `dog` as a predicate."
  [kb]
  (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
  (v/assert kb (list 'unary_predicate 'dog) 'CxUniverse))

(tu/deftest-kb a-rule-whose-only-antecedent-is-a-kind-does-not-fire
  (setup! kb)
  (doseq [[kind value] cases]
    (tu/with-terms [valueOf kinded Ann]
      (v/assert kb (list 'implies (list kind '?x) (list kinded '?x))
                'CxUniverse {:direction :forward})
      (v/assert kb (list valueOf Ann value) 'CxUniverse)
      (testing (str "(" kind " ?x) alone, over a fact holding " (pr-str value))
        (is (empty? (v/sentexes-matching kb (list kinded value) 'CxUniverse)))))))
