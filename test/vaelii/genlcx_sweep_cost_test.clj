;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.genlcx-sweep-cost-test
  "What a `(genlCx sub super)` edge's merge sweep costs, as counted derivations, and the
  two things about that count which are properties of the algorithm rather than of the
  fixture.

  `equate-under-context-edge-via` hands `context-down(sub)` — the contexts whose ancestor
  set this edge changed — to both twins' `derive`, which sweep that set instead of the
  whole reader fan of each candidate's own storage context.

  ## The two claims

  **Flat in readers the edge does not reach.**  Contexts wired under the *candidates'*
  branch and not under `sub` see exactly what they saw before the edge, so the count is
  asserted equal across 0, 4, 8 and 16 of them.  Before the reader set was narrowed this
  count was 25, 49, 73, 121 — one extra derivation per candidate per bystander.  That
  growth is why a `genlCx` edge cost more as a KB gained contexts at all, and why
  `starter/load-into` went from 0.87 s to 2.50 s while the shipped files grew 1,668 ->
  3,200+ sentexes.

  **Linear, at one derivation per candidate, in readers it does reach.**  The same
  contexts wired under `sub` instead do gain visibility, and each one must be swept.  The
  count rises by exactly the candidate count per reader — which is the claim that says the
  narrowing reaches the right set rather than simply doing less: a sweep narrowed to
  nothing would pass the first claim and fail this one.

  ## Why a count, and why a slope rather than a number

  `assert_cost_test`'s reason for the count: the quantity is an integer the engine
  computes, so it is identical across runs and machines and needs no warm-up or
  tolerance.  Its preference for an exact number does not carry here, and the reason is
  measurable — the same fixture at the same size answers 13 in one namespace's KB and 25
  in another's, because a sweep's absolute total also carries what the settle beneath it
  probes, which is a function of the KB the fixture happened to build.  A slope is not:
  one derivation per candidate per swept reader is what the code does, and it reads the
  same whatever the fixture holds.  So the pins here are `=` across bystanders and an
  exact slope across widened readers, and neither can be satisfied by a fixture drifting
  under them.

  `genlcx_sweep_test` holds the other half — the merges the narrowing must still derive,
  and the readers it must not visit."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.special :as special]
            [vaelii.test-util :as tu]))

(def ^:private pairs
  "Clashing pairs across the two branches.  Six, so the slope below is 12 — two digits,
  which reads against a two-digit count without costing a second."
  6)

(def ^:private candidates
  "Facts the sweep enumerates: both halves of every pair.  The slope the second claim
  asserts, since each candidate is re-derived once per reader swept."
  (* 2 pairs))

(defn- sweep-derivations
  "`derive-functional-equalities-in` calls made while `f` runs — one per candidate per
  reader swept, so the call is the measurement of the reader fan.  Redefined rather than
  read off a counter, for `settle_region_cost_test`'s reason: the engine carries none."
  [f]
  (let [calls (atom 0)
        orig  @#'special/derive-functional-equalities-in]
    (with-redefs [special/derive-functional-equalities-in
                  (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(defn- joining-edge-derivations
  "Two mutually blind branches holding `pairs` clashing pairs, plus `extra` reader
  contexts wired either under `sub` (`under-sub?`, so the joining edge widens them) or
  under the candidates' own branch (so it does not).  Answers what the joining edge
  costs."
  [kb extra under-sub?]
  (tu/with-terms [parentOf CxLeft CxRight CxSub]
    (v/assert kb (list 'functional parentOf) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSub CxLeft) 'CxUniverse)
    (dotimes [_ extra]
      (v/assert kb (list 'genlCx (tu/fresh-term :context "CxR") (if under-sub? CxSub CxLeft))
                'CxUniverse))
    (dotimes [_ pairs]
      (let [k (tu/fresh-term :individual "Kid")]
        (v/assert kb (list parentOf k (tu/fresh-term :individual "MumA")) CxLeft)
        (v/assert kb (list parentOf k (tu/fresh-term :individual "MumB")) CxRight)))
    (sweep-derivations #(v/assert kb (list 'genlCx CxSub CxRight) 'CxUniverse))))

(def ^:private sizes [0 4 8 16])

(deftest a-joining-edge-costs-nothing-for-readers-it-does-not-reach
  (let [counts (into {} (for [n sizes]
                          [n (tu/with-neutral-kb [kb tu/fresh]
                               (joining-edge-derivations kb n false))]))]
    (is (apply = (vals counts))
        (str "derivations by bystander count: " (sort-by key counts)
             " — a count that rises with contexts the edge left alone is the whole reader"
             " fan being swept again"))))

(deftest a-joining-edge-costs-one-derivation-per-candidate-per-reader-it-does-reach
  (let [counts (into {} (for [n sizes]
                          [n (tu/with-neutral-kb [kb tu/fresh]
                               (joining-edge-derivations kb n true))]))
        base   (counts 0)]
    (testing "every widened reader is swept, at one derivation per candidate"
      (is (= (into {} (for [n sizes] [n (+ base (* n candidates))])) counts)
          (str "derivations by widened-reader count: " (sort-by key counts)
               " — the slope is the candidate count, " candidates)))))
