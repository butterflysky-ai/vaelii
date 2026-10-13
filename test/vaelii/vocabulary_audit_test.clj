;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vocabulary-audit-test
  "Declared and enforced, against declared and ignored.

  Nothing about a declaration's *shape* says whether anything reads it.
  `(maxCardinality parentOf 2)` is a well-formed ternary fact, storable, believed, and
  read by nobody — so a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented.  `vaelii.impl.vocabulary` answers the
  question for the engine's own grammar, and these tests are what keep the answer true:
  a term core.txt declares that the roster says nothing about fails here, and so does a
  roster entry naming a term the grammar has retired.

  An upper-layer baseline holds the whole population, which is why this is its own
  namespace — the constraint tests beside it (`constraint-vocabulary-test`) need a cleared
  KB."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.vocabulary :as vocab]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(tu/deftest-kb every-term-the-grammar-declares-is-classified
  ;; The durable half.  A functor added to core.txt without anybody deciding whether
  ;; the engine reads it lands in `:unclassified`, and this fails — which is the whole
  ;; point: `interArg` sat in the design notes as a plausible declaration for as long
  ;; as nothing was checking.
  (let [a (v/vocabulary-audit kb)]
    (is (empty? (:unclassified a))
        "a term core.txt declares that vocabulary/roster says nothing about")
    (is (empty? (:retired a))
        "a roster entry naming a term core.txt no longer declares")
    (is (empty? (:contradicted a))
        "a term the special-predicate table gives an arm to and the roster calls inert")
    (is (seq (:enforced a)))
    (is (seq (:inert a)) "and the inert set is not empty — the roster classifies some terms inert")))

(tu/deftest-kb a-new-grammar-declaration-nobody-classified-is-reported
  ;; The test above only fails if this mechanism works, so drive it: a term added to the
  ;; grammar shows up unclassified rather than passing quietly.
  ;; core.txt names the population, so the term is added to the file's terms as well as
  ;; declared in CxUniverse.
  (tu/with-terms [maxCardinality]
    (v/assert kb (list 'comment maxCardinality "a plausible-looking declaration")
              'CxUniverse)
    (let [terms (conj @@#'vocab/file-terms maxCardinality)]
      (with-redefs [vocab/file-terms (delay terms)]
        (is (= [maxCardinality] (:unclassified (v/vocabulary-audit kb))))))))

;; `the-special-predicate-table-and-the-roster-agree` stood here and is gone.  It walked
;; `special/entries` asserting no functor with an arm was classified inert — which is
;; `audit`'s `:contradicted` restated, and the test above already asserts that empty.  The
;; half of it that was about two hand-written lists agreeing went with the roster: the
;; prose now sits on the term's own declaration and the class is read off that entry's
;; facets, so there is no second list for the table to disagree with.

(tu/deftest-kb the-two-new-constraints-are-on-the-enforced-side
  ;; Ties the implementations in `constraint-vocabulary-test` to the roster, so removing
  ;; one and leaving the claim is a failing test rather than a stale sentence.
  (is (:enforced (v/interpreted 'interArg)))
  (is (:enforced (v/interpreted 'arity)))
  (is (nil? (v/interpreted 'maxCardinality))
      "a term the grammar does not declare is out of scope, not answered")
  (is (:inert (v/interpreted 'typeToInstancePred))
      "and a declared term nothing reads says so rather than reading as enforced"))

(deftest the-roster-answers-in-exactly-one-of-the-two-classes
  (doseq [[term entry] vocab/roster]
    (is (= 1 (count (select-keys entry [:enforced :inert])))
        (str term " must be enforced or inert, and say which"))
    (is (seq (or (:enforced entry) (:inert entry)))
        (str term " carries no reason"))))
