;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.temporal-functional-in-arg-test
  "A **computed** `genlCx` edge widens which merges a context can see exactly as much as a
  stated one does — vaelii#56, reported by Lain against the calendar dimension.

  `context-nat` materializes `(genlCx <january> <year>)` off a `contextArgSubrelation`
  declaration with nobody asserting it (docs/context-nat.md).  Until this closed, that
  edge reached the taxonomy and the exception re-checks and stopped there: the three
  equality reconcilers a `genlCx` edge owes were written out by hand in the assert path
  and in the rule-conclusion path, and the producer — the third entry point — called none of
  them.  So two fillers of one functional slot, made jointly visible for the first time
  by a computed month→year edge, stayed unmerged, uncontradicted and unreported, while
  the same two facts under a *stated* edge merged.  Whether they merged came down to
  whether the year's fact was written before January existed.

  The reconcilers run from one place, the settle's `special/drain-context-moves!`,
  whichever of the three entry points stored the edge.  What the tests here pin is the *equivalence*: a computed edge and a
  stated one reach the same beliefs, in every order the ingredients can arrive in.

  The mark is stated **in the year context** throughout rather than in CxUniverse.  A
  reified `cx/` context is not wired under CxUniverse by anything — its ancestor set is what the
  declarations compute — so a mark left in CxUniverse is invisible from the calendar and
  the scenario would be testing the wrong absence."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; One fixed context function: every test gets a cleared KB of its own, so there is
;; nothing for a second test's calendar to collide with.
(def ^:private year  '(CxCalFn CxMonad (DatetimeFn "2000")))
(def ^:private month '(CxCalFn CxMonad (DatetimeFn "2000-01")))
(def ^:private U 'CxUniverse)

(defn- dimension!
  "Declare the reify kinds a calendar context needs — but not the ordering, which is the
  arrival every test below places for itself."
  [kb]
  (v/assert kb '(result CxCalFn context) U)
  (v/assert kb '(unreifiable_function DatetimeFn) U))

(defn- order-by-subinterval! [kb]
  (v/assert kb '(contextArgSubrelation CxCalFn 2 subintervalOf) U))

(defn- fillers
  "The `the_best` fillers a reader in `ctx` sees, sorted so the reading is order-blind."
  [kb ctx]
  (sort (map (comp str '?x) (v/ask kb '(the_best ?x) ctx))))

;; ---- the functional merge a computed edge newly licenses -----------------

(tu/deftest-kb a-computed-edge-merges-the-functional-slot-it-newly-exposes
  ;; The issue's own sequence: the year's filler is written before January exists, so
  ;; the edge that makes the two jointly visible is materialized by January's own mint —
  ;; after both the mark and the first filler are already stored.
  (dimension! kb)
  (order-by-subinterval! kb)
  (v/assert kb '(functionalInArg the_best 1) year)
  (v/assert kb '(the_best LaMulanaTwo) year {:strength :monotonic})
  (v/assert kb '(the_best Silksong) month {:strength :monotonic})
  (testing "January sees one filler, not two — the computed edge ran the merge"
    (is (= ["LaMulanaTwo"] (fillers kb month)))
    (is (v/same-class? kb 'LaMulanaTwo 'Silksong)
        "and the two names are one thing, which is what a functional slot means here"))
  (testing "and the merge is knowledge rather than an error"
    (is (empty? (v/violations kb)))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb the-filler-arrival-order-does-not-decide-the-computed-merge
  ;; The other half of the reported order-dependence: January's filler first, the year's
  ;; second.  A second route reaches the pair in this ordering — the year's own assert
  ;; runs `derive-functional-equalities`, which sweeps every reader below the context it
  ;; is handed — so the edge's sweep is not the only thing that could merge here.  That
  ;; is what makes the year-first ordering above a *divergence* rather than a flat
  ;; absence: one arrival order has a second route and the other has none, so the same
  ;; four sentences answer two ways.
  (dimension! kb)
  (order-by-subinterval! kb)
  (v/assert kb '(functionalInArg the_best 1) year)
  (v/assert kb '(the_best Silksong) month {:strength :monotonic})
  (v/assert kb '(the_best LaMulanaTwo) year {:strength :monotonic})
  (is (= ["LaMulanaTwo"] (fillers kb month)))
  (is (v/same-class? kb 'LaMulanaTwo 'Silksong)))

(tu/deftest-kb a-subrelation-declaration-arriving-last-merges-what-its-edges-expose
  ;; The edge-arrives-last shape, which a computed edge can only reach this way: both
  ;; contexts and both fillers are stored while the dimension is unordered, and the
  ;; `contextArgSubrelation` declaration is what materializes the edge.
  (dimension! kb)
  (v/assert kb '(functionalInArg the_best 1) year)
  (v/assert kb '(the_best LaMulanaTwo) year {:strength :monotonic})
  (v/assert kb '(the_best Silksong) month {:strength :monotonic})
  (testing "unordered, the two contexts are blind to each other and nothing merges"
    (is (= ["Silksong"] (fillers kb month)) "January reads only its own")
    (is (not (v/same-class? kb 'LaMulanaTwo 'Silksong))))
  (order-by-subinterval! kb)
  (testing "the declaration computes the edge, and the edge runs the merge it owes"
    (is (= ["LaMulanaTwo"] (fillers kb month)))
    (is (v/same-class? kb 'LaMulanaTwo 'Silksong))))

(tu/deftest-kb a-stated-edge-over-the-same-shape-reaches-the-same-belief
  ;; The reporter's repair receipt, kept as the equivalence it was always measuring.  It
  ;; localized the defect by asserting one otherwise-irrelevant *stated* edge and
  ;; watching the owed merge appear; what it pins now is that there is nothing left for
  ;; a stated edge to repair — the computed edge already reached the belief the stated
  ;; one reaches, and asserting one afterwards changes nothing.
  (dimension! kb)
  (order-by-subinterval! kb)
  (v/assert kb '(functionalInArg the_best 1) year)
  (v/assert kb '(the_best LaMulanaTwo) year {:strength :monotonic})
  (v/assert kb '(the_best Silksong) month {:strength :monotonic})
  (let [before (fillers kb month)
        ky     (:context (tu/sentex-matching kb '(the_best LaMulanaTwo) year))]
    (v/assert kb (list 'genlCx ky U) U)
    (is (= before (fillers kb month)) "the stated edge finds nothing owed")
    (is (= ["LaMulanaTwo"] (fillers kb month)))))

;; ---- the migration half: the same trigger, the other closure ------------

(tu/deftest-kb a-fact-inherited-through-a-computed-edge-is-restated-under-its-elected-spelling
  ;; The issue's "analogous gap", and the one that loses knowledge outright rather than
  ;; declining to add any.  The merge is stated in January and the fact lives in the
  ;; year, so when the computed edge makes the year visible from January the record is
  ;; spelled the way a context that could not see the merge stored it: January's reader
  ;; asks after the representative and misses, and the displaced spelling is no longer
  ;; believed from there either — the fact reads back under *neither* name.
  (dimension! kb)
  (v/assert kb '(petalCount Rose 5) year)
  (v/assert kb '(equals Rose Rosa) month)
  (testing "unordered, January sees nothing of the year — no edge, no inheritance"
    (is (empty? (v/sentexes-matching kb '(petalCount ?x ?n) month))))
  (order-by-subinterval! kb)
  (let [rep (v/representative kb 'Rose)]
    (testing "the computed edge restates the inherited fact under the elected spelling"
      (is (= [(list 'petalCount rep 5)]
             (map :sentence (v/sentexes-matching kb '(petalCount ?x ?n) month)))))
    (testing "so January answers under both names, as a merged pair must"
      (is (= [{'?n 5}] (v/ask kb '(petalCount Rose ?n) month)))
      (is (= [{'?n 5}] (v/ask kb '(petalCount Rosa ?n) month))))
    (testing "and the year, which cannot see the merge, keeps the spelling it stored"
      (is (= ['(petalCount Rose 5)]
             (map :sentence (v/sentexes-matching kb '(petalCount ?x ?n) year)))))))

;; ---- the antisymmetric arm, wired identically --------------------------

(tu/deftest-kb a-computed-edge-merges-an-antisymmetric-pair-it-newly-exposes
  ;; `antisym-equate-under-context-edge` shares `equate-under-context-edge`'s body and
  ;; shared its silence; a converse pair split across the two calendar contexts is the
  ;; same event through the other mark.
  (dimension! kb)
  (order-by-subinterval! kb)
  (v/assert kb '(anti_symmetric asHeavyAs) year)
  (v/assert kb '(asHeavyAs Lead Plumbum) year {:strength :monotonic})
  (v/assert kb '(asHeavyAs Plumbum Lead) month {:strength :monotonic})
  (is (v/same-class? kb 'Lead 'Plumbum)
      "a converse pair under an anti_symmetric mark is two names for one thing"))
