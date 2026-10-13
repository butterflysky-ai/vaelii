;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argpreserving-meta-test
  "The argument-type meta-predicates answer along the `genl` closure on the query
  surface, so `ask` agrees with the generalization `check` already walks internally.
  Read literally instead, a stored `(arg petMammal 1 mammal)` is the only thing
  `(ask (arg petMammal 1 animal))` could return — nothing — even though
  `(genl mammal animal)` holds and `check` accepts an animal there, and the two entry points
  disagree about one declaration.

  The engine answers it in `provers/MetaConstraintProver`, a bounded closure walk, and
  NOT by declaring the meta-predicates `transitiveInArg` — that would tax every one of
  the KB's very many `arg`/`genlArg` lookups (see `resources/kb/CxUniverse.txt`).  The
  predicate position (1) reaches DOWN `genl` (a constraint on a super binds its
  specializations); an unconditional type reaches UP (a stored subtype answers its
  supertypes — `arg`/`genlArg` position 3, `interArg`'s target position 5); and
  `interArg`'s trigger position 3, being an antecedent, is contravariant and reaches
  DOWN.

  The KB here is the upper layer alone, so what these tests read is the *shipped* vocabulary
  and not one they stated."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private C 'CxUniverse)

;; ---- arg, both directions --------------------------------------------

(tu/deftest-kb arg-answers-up-the-genl-chain-via-transitiveInArg
  ;; position 3 is a TYPE: a stored constraint on mammal answers up to animal
  (tu/with-terms [petMammal mammal animal dog]
    (v/assert kb (list 'genl animal 'thing) C)
    (v/assert kb (list 'genl mammal animal) C)
    (v/assert kb (list 'genl dog mammal) C)
    (v/assert kb (list 'arg petMammal 1 mammal) C)
    (testing "the literally stored declaration is answerable, and it is stored"
      (is (v/ask? kb (list 'arg petMammal 1 mammal) C))
      (is (seq (v/sentexes-matching kb (list 'arg petMammal 1 mammal) '?ctx))))
    (testing "the supertype answers even though nobody stored it — the gap this closes"
      (is (v/ask? kb (list 'arg petMammal 1 animal) C))
      (is (empty? (v/sentexes-matching kb (list 'arg petMammal 1 animal) '?ctx))
          "answered on demand, never materialized"))
    (testing "and the default context read (unscoped) finds it too"
      (is (v/ask? kb (list 'arg petMammal 1 animal))))
    (testing "but the constraint does not descend at position 3 — inverse is up only"
      (is (not (v/ask? kb (list 'arg petMammal 1 dog) C))))))

(tu/deftest-kb arg-inherits-down-the-predicate-via-transitiveInArgInverse
  ;; position 1 is the PREDICATE: a constraint on a general predicate reaches its
  ;; genl-specializations, and not the other way
  (tu/with-terms [mySuper mySub myOver myType]
    (v/assert kb (list 'genl myType 'thing) C)
    (v/assert kb (list 'genl mySub mySuper) C)
    (v/assert kb (list 'genl mySuper myOver) C)
    (v/assert kb (list 'arg mySuper 1 myType) C)
    (testing "a specialization of the constrained predicate inherits the constraint"
      (is (v/ask? kb (list 'arg mySub 1 myType) C))
      (is (empty? (v/sentexes-matching kb (list 'arg mySub 1 myType) '?ctx))))
    (testing "but a generalization does not — transitiveInArgInverse reaches down, not up"
      (is (not (v/ask? kb (list 'arg myOver 1 myType) C))))))

;; ---- genlArg, interArg, arity: the same shape, smoke-tested ----------

(tu/deftest-kb genlArg-answers-up-the-genl-chain-at-position-3
  (tu/with-terms [typeRel mammal animal]
    (v/assert kb (list 'genl animal 'thing) C)
    (v/assert kb (list 'genl mammal animal) C)
    (v/assert kb (list 'genlArg typeRel 1 mammal) C)
    (testing "the stored subtype constraint answers up to the supertype"
      (is (v/ask? kb (list 'genlArg typeRel 1 animal) C))
      (is (empty? (v/sentexes-matching kb (list 'genlArg typeRel 1 animal) '?ctx))))))

(tu/deftest-kb quotedArg-answers-along-the-closure-like-its-three-siblings
  ;; The mention twin was the one member of the family this table had no row for, so
  ;; `ask` disagreed with the entry point about one declaration: `checks/declaration-reader`
  ;; reads `quotedArg` through `res/constraining-predicates` exactly as it reads the
  ;; other three, and refuses a sub-predicate's tuple under a super's declaration —
  ;; while the query surface answered only what was literally stored.
  ;;
  ;; The types here are the *syntactic* lattice CxUniverse ships, not a stated one: a
  ;; `quotedArg` types the term written in a position, so `positive_integer` below
  ;; `integer` is the refinement the covariance is read over.
  (tu/with-terms [pAge pInfantAge]
    (v/assert kb (list 'genl pInfantAge pAge) C)
    (v/assert kb (list 'quotedArg pAge 1 'positive_integer) C)
    (testing "the stored declaration answers, and it is stored"
      (is (v/ask? kb (list 'quotedArg pAge 1 'positive_integer) C))
      (is (seq (v/sentexes-matching kb (list 'quotedArg pAge 1 'positive_integer) '?ctx))))
    (testing "position 3 widens UP — the narrower kind answers the broader query"
      (is (v/ask? kb (list 'quotedArg pAge 1 'integer) C))
      (is (empty? (v/sentexes-matching kb (list 'quotedArg pAge 1 'integer) '?ctx))
          "answered on demand, never materialized — nothing is minted from a quotedArg"))
    (testing "and does not narrow down: a broader declaration is not the narrower one"
      (is (not (v/ask? kb (list 'quotedArg pAge 1 'string) C))))
    (testing "position 1 reaches DOWN the predicate — a super's declaration binds the sub,
              which is the reading the entry point already had"
      (is (v/ask? kb (list 'quotedArg pInfantAge 1 'positive_integer) C))
      (is (v/ask? kb (list 'quotedArg pInfantAge 1 'integer) C)
          "both variances at once, as arg does"))
    (testing "position 2 is fixed — a declaration on one position answers for no other"
      (is (not (v/ask? kb (list 'quotedArg pAge 2 'positive_integer) C))))))

(tu/deftest-kb quotedArg-answers-what-the-entry-point-already-refuses-on
  ;; The two entry points, on one declaration.  `checks/args-quoted-problem` reads a super's
  ;; declaration against a sub's tuple through `res/constraining-predicates`, so the
  ;; refusal descends; the query surface has to descend with it or the same declaration
  ;; means one thing to `assert` and another to `ask`.  Binary, because a quoted position
  ;; needs a tuple to sit in and a unary functor is snake_case by the naming rule.
  (tu/with-terms [pAgeOf pInfantAgeOf]
    (v/assert kb (list 'genl pInfantAgeOf pAgeOf) C)
    (v/assert kb (list 'quotedArg pAgeOf 2 'string) C)
    (testing "the entry point refuses the sub's tuple under the super's declaration"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list pInfantAgeOf 'Bob 5) C)))
      (is (v/assert kb (list pInfantAgeOf 'Bob "two") C)
          "and admits one whose written term is the declared kind"))
    (testing "and `ask` says the declaration binding it is there to be read"
      (is (v/ask? kb (list 'quotedArg pInfantAgeOf 2 'string) C))
      (is (empty? (v/sentexes-matching kb (list 'quotedArg pInfantAgeOf 2 'string) '?ctx))
          "answered, not stored — the entry point reads the same closure without materializing it"))))

(tu/deftest-kb interArg-trigger-narrows-down-target-widens-up
  ;; The conditional constraint's two types have OPPOSITE variance.  The trigger
  ;; (position 3) is the antecedent: `(interArg myRel 1 carnivore 2 meat)` convicts
  ;; every carnivore, so it convicts every lion (a lion is a carnivore) and answers the
  ;; *subtype* trigger — but it says nothing about predators at large, so it does not
  ;; answer the *supertype* trigger.  The target (position 5) is the consequent, an
  ;; ordinary unconditional type: `meat` answers up to `food`.  Widening the trigger up
  ;; (the old, wrong direction) would convict the non-carnivore predators `check` never
  ;; touches — unsound; not answering the narrower lion trigger — incomplete.
  (tu/with-terms [myRel lion carnivore predator meat food]
    (v/assert kb (list 'genl predator 'thing) C)
    (v/assert kb (list 'genl carnivore predator) C)
    (v/assert kb (list 'genl lion carnivore) C)
    (v/assert kb (list 'genl food 'thing) C)
    (v/assert kb (list 'genl meat food) C)
    (v/assert kb (list 'interArg myRel 1 carnivore 2 meat) C)
    (testing "the trigger narrows DOWN — a subtype trigger is answered"
      (is (v/ask? kb (list 'interArg myRel 1 lion 2 meat) C)))
    (testing "the trigger does NOT widen up — a supertype trigger convicts non-carnivores"
      (is (not (v/ask? kb (list 'interArg myRel 1 predator 2 meat) C))))
    (testing "the target widens UP its type"
      (is (v/ask? kb (list 'interArg myRel 1 carnivore 2 food) C)))
    (testing "trigger narrowed and target widened together"
      (is (v/ask? kb (list 'interArg myRel 1 lion 2 food) C)))
    (testing "nothing is materialized"
      (is (empty? (v/sentexes-matching kb (list 'interArg myRel 1 lion 2 meat) '?ctx))))))

(tu/deftest-kb arity-does-not-generalize-down-the-predicate
  ;; arity is deliberately NOT among the generalized meta-predicates.  Unlike a type
  ;; constraint, a sub-predicate may carry a signature of its own — a ternary
  ;; specialization of a binary — so its arity is not answered down `genl` as a fact,
  ;; and answering it would in any case need the forward `(arity ?p 2) ⊢
  ;; (binary_predicate ?p)` cycle a backward prover cannot fire.  `arity/relation-length`
  ;; still holds a sub-predicate that declares NOTHING of its own to its supers at assert
  ;; time — a refusal, not an answerable `(arity sub n)`.
  (tu/with-terms [mySuper mySub]
    (v/assert kb (list 'genl mySub mySuper) C)
    (v/assert kb (list 'arity mySuper 2) C)
    (testing "the specialization does not inherit the arity as an answerable fact"
      (is (not (v/ask? kb (list 'arity mySub 2) C))))
    (testing "so the derive cycle concludes no predicate type for it either"
      (is (not (v/ask? kb (list 'binary_predicate mySub) C))))))
