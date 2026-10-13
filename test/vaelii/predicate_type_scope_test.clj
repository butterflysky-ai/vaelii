;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicate-type-scope-test
  "A property mark like `(transitive P)` is the queryable classification itself — there is
  no derived `…Predicate` twin and no prover reading a global roster.  So asking
  `(transitive P)` is ordinary context-scoped retrieval, and it agrees with the
  `has-prop?`, `isa?` and stored-sentex reads beside it from every vantage.  A permuting
  mark's property is the exception: it decides the key a sentex is stored under in every
  context, so `has-prop?` reads it where the store does (docs/contexts.md).

  The shipped ontology **masks** the scoping: `symmetric`/`transitive`/`reflexive`/
  `functional` are `decontextualized_predicate`s (core.txt), so a real KB lifts every such
  mark into CxUniverse and every context sees it — global and scoped agree.  So this pins
  the scoping on a **bare** KB, where the mark stays in the context it was declared in and
  a sibling cannot see it; `meta_test` is the companion that pins the lifted, shipped
  behaviour.

  Each test builds its own KB on the **isolated** database pair: it rebuilds in a loop,
  which would clear the shared pair out from under another namespace's `:once` fixture."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(deftest a-predicate-type-mark-is-answered-from-the-asking-vantage
  (testing "a transitive mark declared in one context does not answer a sibling's query"
    ;; No upper layer here, so `transitive` is not a decontextualized_predicate and the mark
    ;; stays in CxPtsA rather than lifting to CxUniverse.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitive ptrans) 'CxPtsA)
      (testing "the declaring context sees it, every reader agreeing"
        (is (v/ask? kb '(transitive ptrans) 'CxPtsA)
            "the stored mark answers the ground goal")
        (is (contains? (set (map #(get % '?p) (v/ask kb '(transitive ?p) 'CxPtsA)))
                       'ptrans)
            "and the open enumeration includes it"))
      (testing "a context that cannot see the declaration does not"
        (is (not (v/ask? kb '(transitive ptrans) 'CxPtsB))
            "the ground prove is scoped to the vantage, not read off a global roster")
        (is (not (contains? (set (map #(get % '?p)
                                      (v/ask kb '(transitive ?p) 'CxPtsB)))
                            'ptrans))
            "and so is the open enumeration"))
      (testing "the mark agrees with the reads that were always scoped"
        (is (empty? (v/sentexes-matching kb '(transitive ptrans) 'CxPtsB))
            "the stored-sentex match answers nothing from the sibling")
        (is (not (v/has-prop? kb :transitive 'ptrans 'CxPtsB))
            "and has-prop? answers false there")
        (v/assert kb '(symmetric psym) 'CxPtsA)
        (is (v/has-prop? kb :symmetric 'psym 'CxPtsB)
            (str "except for a permuting mark, whose property decides the key a sentex is "
                 "stored under in every context, so it is read where the store reads it")))
      (testing "an unscoped `?ctx` query still spans the whole KB"
        (is (v/ask? kb '(transitive ptrans) '?ctx)
            "the any-context read is unchanged — a nil/?ctx context is no filter")))))
