;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.equality-test
  "Equality — `rewriteOf` / `sameAs` / `equals`, and the `different` that survives
  them.  Every test here holds against the shipped feature: one belief-following
  partition behind the three relations, recomputed on edge change like the `genl`
  and `genlCx` closures beside it.

  Each test pins one decision from [docs/equality.md](../../docs/equality.md) and
  carries a comment naming it.  The shape under test is three assertable relations
  feeding **one equivalence closure**

    (rewriteOf Preferred Deprecated)   directional: the second argument is retired
    (sameAs A B)                       OWL, individuals, neither deprecated
    (equals A B)                       sameAs without the individuals restriction

  and one *unassertable* one, `(different A B ...)`, which is negation as failure
  over that closure — the unique-name assumption OWL drops and vaelii keeps.

  The five claims the shape makes are: a merge **migrates** every sentex mentioning
  the loser and **blocks** (never deletes) the stale spelling; congruence is a side
  effect of the term index, so a nested occurrence is rewritten too; the
  representative is **content-keyed**, so it cannot depend on arrival order;
  `functional` **derives** an equality rather than throwing; and a **rule** may
  conclude one of the three, which merges where the conclusion is placed.

  House rules apply as everywhere else: gensym'd temporaries via `tu/with-terms`,
  engine vocabulary (`rewriteOf`, `sameAs`, `equals`, `different`, `functional`,
  `genl`, `disjoint`, `symmetric`, contexts) literal, and the neutral fixture
  asserts the KB is restored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private merge-cost-ctx
  "The context section 10's cost tests work in.  Literal rather than gensym'd, because
  those tests build their own KB on the isolated pair and wipe it, which is what
  `tu/with-cleared-kb` is for."
  'CxMergeCost)

;; ---- helpers -------------------------------------------------------------

(defn- believed?
  "Is `sentence` stored in `context` **and** currently believed?

  Deliberately not `query`: a merge **rewrites goals**, so `query` on the retired
  spelling answers with the representative's sentex.  That is the right behaviour and
  the wrong instrument for asking which spelling the KB actually believes, which is
  what most of these tests are about."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (boolean (and h (v/in? kb h)))))

(defn- stored-not-believed?
  "The signature of a **blocked** spelling: the sentex is still there (handles callers
  hold stay valid) and the JTMS holds it OUT."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (and (some? h) (some? (v/sentex kb h)) (not (v/in? kb h)))))

(defn- why-sentences
  "Every sentence mentioned anywhere in a `why` proof tree — the antecedents, the
  rules, and the informants' own sentences.  Flattened, because the doc requires that
  `why` *names* the functional declaration and both facts without saying which slot
  each lands in."
  [node]
  (when (map? node)
    (concat (when-let [s (:sentence node)] [s])
            (when-let [r (:rule node)] [r])
            (mapcat (fn [sup] (cons (:rule sup) (mapcat why-sentences (:because sup))))
                    (:support node)))))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;; ---- 1. the three relations and one closure ------------------------------
;; DECISION (Three assertable relations, one closure): "`rewriteOf` names the
;; representative and marks the loser deprecated."  Direction is the whole content of
;; the relation, so the preferred term must win *regardless* of how it sorts — this
;; test deliberately gives the preferred term the lexicographically **larger** name,
;; which is the tie-break `sameAs` would otherwise use.

(tu/deftest-kb rewrite-of-deprecates-its-second-argument-whatever-the-spelling
  (tu/with-terms [bornIn Chicago CxName]
    (let [[lo hi] (sort [(tu/tmp-ind "Obama") (tu/tmp-ind "Obama")])]
      ;; the preferred term is `hi`, so lexicographic order cannot explain the outcome
      (v/assert kb (list bornIn lo Chicago) CxName)
      (v/assert kb (list 'rewriteOf hi lo) CxName)
      (testing "the fact is migrated to the preferred term"
        (is (believed? kb (list bornIn hi Chicago) CxName)))
      (testing "and the deprecated spelling is blocked, not deleted"
        (is (stored-not-believed? kb (list bornIn lo Chicago) CxName))))))

;; DECISION (Three assertable relations, one closure): "`sameAs` ... Both names stay
;; first-class; neither is deprecated; the representative is an internal detail" —
;; and the representative is then chosen by decision 2, the **lexicographically
;; smallest symbol**.  So the observable difference between `rewriteOf` and
;; `sameAs`/`equals` is exactly this: with the same two symbols and the same argument
;; order, `rewriteOf` elects its first argument and `sameAs` elects the smaller one.

(tu/deftest-kb same-as-states-no-preference-so-the-smaller-symbol-represents
  (tu/with-terms [bornIn Chicago CxName]
    (let [[lo hi] (sort [(tu/tmp-ind "Obama") (tu/tmp-ind "Obama")])]
      (v/assert kb (list bornIn hi Chicago) CxName)
      ;; written larger-first, so an implementation that trusted argument order would
      ;; elect `hi` and this test would catch it
      (v/assert kb (list 'sameAs hi lo) CxName)
      (testing "the lexicographically smaller symbol represents the class"
        (is (believed? kb (list bornIn lo Chicago) CxName)))
      (testing "so the fact written under the larger one is the blocked spelling"
        (is (stored-not-believed? kb (list bornIn hi Chicago) CxName))))))

;; DECISION (Three assertable relations, one closure): "All three feed **one
;; equivalence closure**.  They differ in what they say *about* the members, not in
;; the classes they produce."  Each of the three, alone, must migrate.

(tu/deftest-kb all-three-relations-merge
  (doseq [rel ['rewriteOf 'sameAs 'equals]]
    (testing (str rel " merges its arguments")
      (tu/with-terms [bornIn Chicago CxName]
        (let [[lo hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])]
          ;; `lo` is both the preferred term of the rewrite and the lexicographic
          ;; winner, so all three relations must agree on it
          (v/assert kb (list bornIn hi Chicago) CxName)
          (v/assert kb (list rel lo hi) CxName)
          (is (believed? kb (list bornIn lo Chicago) CxName)
              (str rel " did not migrate the fact to the representative"))
          (is (stored-not-believed? kb (list bornIn hi Chicago) CxName)
              (str rel " did not block the non-representative spelling")))))))

;; DECISION (Choosing the representative): "Chains compose: `rewriteOf A B` and
;; `rewriteOf B C` make `A` the representative of all three."  The middle term is a
;; representative when the first edge is read alone, so a one-hop implementation
;; passes the A/B half and fails here.

(tu/deftest-kb a-rewrite-chain-composes-into-one-class-with-one-representative
  (tu/with-terms [bornIn Chicago Berlin CxName]
    (tu/with-terms [A B C]
      (v/assert kb (list bornIn B Chicago) CxName)
      (v/assert kb (list bornIn C Berlin)  CxName)
      (v/assert kb (list 'rewriteOf A B) CxName)
      (v/assert kb (list 'rewriteOf B C) CxName)
      (testing "A represents all three, so both facts read under A"
        (is (believed? kb (list bornIn A Chicago) CxName))
        (is (believed? kb (list bornIn A Berlin)  CxName)))
      (testing "and neither of the two retired spellings is believed"
        (is (stored-not-believed? kb (list bornIn B Chicago) CxName))
        (is (stored-not-believed? kb (list bornIn C Berlin)  CxName)))
      (testing "B is deprecated too, so it does not represent C"
        (is (not (believed? kb (list bornIn B Berlin) CxName)))))))

;; DECISION (Choosing the representative): "Order independence is non-negotiable
;; ..., so the choice can never depend on handle ids or arrival order — handles are
;; allocated in assertion order, and that was a real bug in the Nixon diamond."
;; Every ordering of the merge and the facts must produce the identical reading.  The
;; permutation harness is `order_independence_test`'s, on the isolated database pair
;; so the loop's clears cannot pull the scratch space out from under this namespace.

(deftest the-representative-does-not-depend-on-assertion-order
  (tu/with-terms [bornIn worksAt Chicago Acme CxName]
    (let [[lo hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])
          ops     [#(v/assert % (list 'sameAs hi lo) CxName)
                   #(v/assert % (list bornIn  hi Chicago) CxName)
                   #(v/assert % (list worksAt lo Acme) CxName)
                   #(v/assert % (list bornIn  lo Chicago) CxName)]
          observe (fn [kb]
                    ;; the *reading*, never a handle: handles are allocated in
                    ;; assertion order, so one in the map would make every ordering
                    ;; differ for a reason that is not about belief
                    {:born-under-lo  (believed? kb (list bornIn  lo Chicago) CxName)
                     :born-under-hi  (believed? kb (list bornIn  hi Chicago) CxName)
                     :works-under-lo (believed? kb (list worksAt lo Acme)    CxName)
                     :works-under-hi (believed? kb (list worksAt hi Acme)    CxName)
                     :different      (v/ask? kb (list 'different lo hi) CxName)})
          results (into #{} (map (fn [ordering]
                                   (let [k (tu/isolated-fresh)]
                                     (doseq [op ordering] (op k))
                                     (observe k))))
                        (permutations ops))]
      (is (= 1 (count results))
          (str "the representative moved with assertion order — "
               (count results) " distinct outcomes across 24 orderings: "
               (pr-str results)))
      (testing "and the one outcome elects the lexicographically smaller symbol"
        (let [r (first results)]
          (is (true?  (:born-under-lo  r)))
          (is (false? (:born-under-hi  r)))
          (is (true?  (:works-under-lo r)))
          (is (false? (:works-under-hi r)))
          (is (false? (:different r)) "merged terms are not different")))
      (tu/clear-kb! (tu/isolated-test-kb)))))

;; ---- 2. migration --------------------------------------------------------
;; DECISION (What a merge does — Migrate): "Each gets a rewritten twin under the
;; representative, **derived and justified** by `[the original sentex, the equality
;; sentex]`."  Derived, not re-asserted: the twin is not a premise, and its
;; justification names both parents.

(tu/deftest-kb the-migrated-twin-is-derived-and-justified-by-the-fact-and-the-equality
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (let [fact (v/assert kb (list bornIn Dep Chicago) CxName)
            eq   (v/assert kb (list 'rewriteOf Pref Dep) CxName)
            twin (v/handle-of kb (list bornIn Pref Chicago) CxName)]
        (testing "the twin exists and is believed"
          (is (some? twin))
          (is (true? (v/in? kb twin))))
        (testing "it is derived, not asserted"
          (is (false? (v/premise? kb twin)))
          (is (seq (v/supporting-justifications kb twin))))
        (testing "and its justification names the original fact and the equality"
          (let [antes (set (mapcat :antecedents (v/supporting-justifications kb twin)))]
            (is (contains? antes fact) "the original sentex is not an antecedent")
            (is (contains? antes eq)   "the equality sentex is not an antecedent")))))))

;; DECISION (What a merge does — Block the original): "The stale spelling stays
;; stored but is not believed and does not match ...  Handles that callers already
;; hold stay valid."  Blocking, not sweeping: `exceptWhen` deletes an unsupported
;; conclusion, and this must **not**, because the premise is still the caller's.

(tu/deftest-kb the-stale-spelling-is-blocked-and-its-handle-stays-valid
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (let [h (v/assert kb (list bornIn Dep Chicago) CxName)]
        (v/assert kb (list 'rewriteOf Pref Dep) CxName)
        (testing "the handle the caller holds still resolves to its sentex"
          (is (some? (v/sentex kb h)))
          (is (= (list bornIn Dep Chicago) (:sentence (v/sentex kb h))))
          (is (= h (v/handle-of kb (list bornIn Dep Chicago) CxName))))
        (testing "but it is not believed"
          (is (false? (v/in? kb h)))
          (is (false? (:believed? (v/why-not kb h)))))
        (testing "and it does not match — a raw level-2 lookup sees no believed hit"
          (is (empty? (v/lookup kb 2 (list bornIn Dep Chicago) CxName))))))))

;; DECISION (What a merge does — Rewrite goals): "A query naming a non-representative
;; is rewritten before lookup, since its own sentexes are no longer believed."  So the
;; retired spelling is still a usable *question* even though it is not a usable
;; *answer* — which is what makes migration invisible to a caller who has not heard
;; about the merge.

(tu/deftest-kb a-goal-naming-the-deprecated-term-is-rewritten-and-still-answers
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (v/assert kb (list bornIn Dep Chicago) CxName)
      (v/assert kb (list 'rewriteOf Pref Dep) CxName)
      (testing "the closed goal answers under either spelling"
        (is (seq (v/sentexes-matching kb (list bornIn Pref Chicago) CxName)))
        (is (seq (v/sentexes-matching kb (list bornIn Dep  Chicago) CxName))
            "the goal was not rewritten to the representative before lookup")
        (is (true? (v/ask? kb (list bornIn Dep Chicago) CxName))))
      (testing "and an open goal binds to the representative, not the retired name"
        (is (= #{Pref} (set (map #(get % '?who)
                                 (v/ask kb (list bornIn '?who Chicago) CxName)))))))))

;; A merge retires a spelling for the contexts below it, and a rule naming that spelling
;; is not read there, as a fact naming it is not.
(tu/deftest-kb a-rule-naming-a-retired-spelling-is-hidden-below-the-merge
  (tu/with-terms [bornIn knows CxUpper CxLower]
    (tu/with-terms [Pref Dep]
      (v/assert kb (list 'genlCx CxLower CxUpper) 'CxUniverse)
      (let [rule (list 'implies (list bornIn '?x Dep) (list knows '?x Dep))]
        (v/assert kb rule CxUpper)
        (v/assert kb (list 'rewriteOf Pref Dep) CxLower)
        (testing "the context that states the rule, above the merge, reads it"
          (is (= 1 (count (v/sentexes-matching kb rule CxUpper)))))
        (testing "a context below the merge has retired Dep, and does not read the rule"
          (is (empty? (v/sentexes-matching kb rule CxLower))))))))

;; DECISION (What a merge does — Migrate): "Dedup falls out: when the rewritten form
;; already exists, find-or-create returns that handle and it simply gains a second
;; justification."  One handle with two supports, never two handles — this is the
;; claim that makes a merge idempotent against content the KB already had.

(tu/deftest-kb merging-two-spellings-of-one-fact-yields-one-handle-with-two-supports
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (let [pref-h (v/assert kb (list bornIn Pref Chicago) CxName)
            _      (v/assert kb (list bornIn Dep  Chicago) CxName)
            before (count (v/supporting-justifications kb pref-h))]
        (v/assert kb (list 'rewriteOf Pref Dep) CxName)
        (testing "the representative's handle is unchanged"
          (is (= pref-h (v/handle-of kb (list bornIn Pref Chicago) CxName))))
        (testing "it is still the premise the caller asserted"
          (is (true? (v/premise? kb pref-h)))
          (is (true? (v/in? kb pref-h))))
        (testing "and it gained a justification rather than spawning a second sentex"
          (is (> (count (v/supporting-justifications kb pref-h)) before)))
        (testing "exactly one believed sentex carries the predicate"
          (is (= 1 (count (v/sentexes-with-functor kb bornIn {:believed? true})))))))))

(defn- climbed-reading
  "Whether CxName believes `(alive Rex)` once `ops` run in order: `:ground` `(dog Rex)` and
  the forward rule `(animal ?x) => (alive ?x)`, `:e1` `(genl dog mammal)`, `:e2`
  `(genl <upper> animal)`, `:merge` `(rewriteOf mammalia mammal)`, and `:except` /
  `:unexcept` an `except` of the merge stored / retracted."
  [upper ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog mammal mammalia animal alive Rex CxName]
      (let [hs (volatile! {})]
        (doseq [op ops]
          (case op
            :ground   (do (v/assert kb (list dog Rex) CxName)
                          (v/assert kb (list 'implies (list animal '?x) (list alive '?x)) CxName
                                    {:direction :forward}))
            :e1       (v/assert kb (list 'genl dog mammal) CxName)
            :e2       (v/assert kb (list 'genl ({:mammal mammal :mammalia mammalia} upper) animal)
                                CxName)
            :merge    (vswap! hs assoc :merge (v/assert kb (list 'rewriteOf mammalia mammal) CxName
                                                        {:strength :monotonic}))
            :except   (v/assert kb (list 'except (list 'sentexHandle (:merge @hs))) CxName
                                {:strength :monotonic})
            :unexcept (v/retract! kb (v/handle-of kb (list 'except (list 'sentexHandle (:merge @hs)))
                                                  CxName))))
        (boolean (some->> (v/handle-of kb (list alive Rex) CxName) (#(v/believed? kb % CxName))))))))

;; A merge restates a `genl` edge as a twin, and a twin edge brings the facts under it to
;; the rules above it as an asserted edge does.  A firing that climbed the retired edge
;; is withdrawn at the merge and drawn again over the twin, so `(alive Rex)` is believed
;; in every order: the merge last, an edge after the merge, and the merge's twins made
;; when an `except` of it leaves.
(deftest a-firing-that-climbed-a-merged-type-s-edge-holds-in-every-arrival-order
  (doseq [upper [:mammal :mammalia]]
    (is (= #{true} (into #{} (map #(climbed-reading upper %))
                         (permutations [:ground :e1 :e2 :merge])))
        (str upper)))
  (is (= #{true} (into #{} (map #(climbed-reading :mammalia (concat [:merge :except] % [:unexcept])))
                       (permutations [:ground :e1 :e2])))
      "the except leaves"))

;; ---- 3. congruence -------------------------------------------------------
;; DECISION (Congruence comes free): "The inverted term index locates a term at **any
;; nesting depth**, and migration rewrites it there, so merging performs congruence
;; closure eagerly over all ground content."  The doc claims this falls out; nothing
;; else in the suite would notice if it did not, because every other test puts the
;; merged term in top-level argument position.

(tu/deftest-kb a-merged-term-nested-inside-a-compound-is-rewritten-too
  (tu/with-terms [reportedThat livesIn Ann Bob CxStory]
    (tu/with-terms [Pref Dep]
      ;; Dep occurs only at depth 2 — never as an argument of the stored literal
      (v/assert kb (list reportedThat Ann (list livesIn Bob Dep)) CxStory)
      (v/assert kb (list 'rewriteOf Pref Dep) CxStory)
      (testing "the nested occurrence is rewritten, so the congruent twin exists"
        (is (believed? kb (list reportedThat Ann (list livesIn Bob Pref)) CxStory)))
      (testing "and the nested stale spelling is blocked like a flat one"
        (is (stored-not-believed? kb (list reportedThat Ann (list livesIn Bob Dep))
                                  CxStory))))))

;; DECISION (Interactions — Symmetric predicates): "Argument sorting for a symmetric
;; predicate is done at canonicalization time against the *stored* symbols.  A later
;; merge changes what the sorted order should be, so migration must re-canonicalize
;; rather than substitute textually."  A textual substitution leaves the twin's stored
;; sentence out of canonical order, which `handle-of` would hide (it probes both
;; orders), so the *stored sentence* is read directly.

(tu/deftest-kb migration-re-canonicalizes-a-symmetric-literal-rather-than-substituting
  (tu/with-terms [siblingOf CxKin]
    (let [[lo mid hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])]
      (v/assert kb (list 'symmetric siblingOf) CxKin)
      ;; stored canonically as (siblingOf lo mid)
      (v/assert kb (list siblingOf mid lo) CxKin)
      ;; retire `lo` in favour of `hi`, which sorts *after* mid
      (v/assert kb (list 'rewriteOf hi lo) CxKin)
      (let [twin (v/handle-of kb (list siblingOf mid hi) CxKin)]
        (testing "the twin exists"
          (is (some? twin)))
        (testing "and its stored sentence is re-canonicalized, not textually rewritten"
          (is (= (list siblingOf mid hi) (:sentence (v/sentex kb twin)))
              "the merge substituted textually and left (siblingOf hi mid) stored"))))))

;; ---- 4. retraction -------------------------------------------------------
;; DECISION (What a merge does): "Retraction needs no new code.  Dropping the equality
;; invalidates the derivations, the dependency-directed sweep collects the twins, and
;; unblocking revives the originals."  Both halves matter: a sweep that left the twin
;; stored would make the term count wrong, and an unblock that did not happen would
;; lose the caller's own premise.

(tu/deftest-kb retracting-the-equality-sweeps-the-twins-and-revives-the-originals
  (tu/with-terms [bornIn worksAt Chicago Acme CxName]
    (tu/with-terms [Pref Dep]
      (let [f1 (v/assert kb (list bornIn  Dep Chicago) CxName)
            f2 (v/assert kb (list worksAt Dep Acme)    CxName)
            eq (v/assert kb (list 'rewriteOf Pref Dep) CxName)]
        (testing "both twins exist while the equality holds"
          (is (believed? kb (list bornIn  Pref Chicago) CxName))
          (is (believed? kb (list worksAt Pref Acme)    CxName)))
        (v/retract! kb eq)
        (testing "the twins are swept — collected, not merely disbelieved"
          (is (nil? (v/handle-of kb (list bornIn  Pref Chicago) CxName)))
          (is (nil? (v/handle-of kb (list worksAt Pref Acme)    CxName))))
        (testing "and the originals are unblocked"
          (is (true? (v/in? kb f1)))
          (is (true? (v/in? kb f2)))
          (is (seq (v/sentexes-matching kb (list bornIn Dep Chicago) CxName))))
        (testing "so the two symbols are different again"
          (is (true? (v/ask? kb (list 'different Pref Dep) CxName))))))))

;; ---- 5. `different` ------------------------------------------------------
;; DECISION (The unique-name assumption survives): "`(different X Y)` is **provable
;; exactly when the arguments lie in no shared equivalence class** — so distinct
;; symbols denote distinct individuals until an equality sentex says otherwise."
;; All three phases in one test, because the interesting claim is the transition and
;; not any single reading.

(tu/deftest-kb different-tracks-the-closure-in-both-directions
  (tu/with-terms [CxName]
    (tu/with-terms [Pref Dep]
      (testing "two unmerged symbols are different by the unique-name assumption"
        (is (true? (v/ask? kb (list 'different Pref Dep) CxName))))
      (let [eq (v/assert kb (list 'sameAs Pref Dep) CxName)]
        (testing "once merged they are not"
          (is (false? (v/ask? kb (list 'different Pref Dep) CxName))))
        (v/retract! kb eq)
        (testing "and retracting the merge restores the difference — the closure split"
          (is (true? (v/ask? kb (list 'different Pref Dep) CxName))))))))

;; DECISION (The unique-name assumption survives): "**Variable arity.**  `(different
;; A B C)` asserts the arguments are pairwise distinct."  Pairwise, so merging *any*
;; one pair must take the whole literal down — a check that only tested the first pair
;; would pass on a two-argument test and fail here.

(tu/deftest-kb different-is-variable-arity-and-pairwise
  (tu/with-terms [CxName]
    (tu/with-terms [A B C]
      (testing "three pairwise-distinct symbols"
        (is (true? (v/ask? kb (list 'different A B C) CxName))))
      ;; merge the pair that is *not* first, so a first-pair-only check is caught
      (v/assert kb (list 'sameAs B C) CxName)
      (testing "merging any one pair falsifies the whole literal"
        (is (false? (v/ask? kb (list 'different A B C) CxName))))
      (testing "while the untouched pair is still different"
        (is (true? (v/ask? kb (list 'different A B) CxName)))))))

;; DECISION (The unique-name assumption survives): "**Not assertible.**  It is
;; answered by a prover and never stored.  Asserting it is rejected.  (An assertible
;; `different` would be OWL's `differentFrom` — a positive commitment that makes a
;; later `sameAs` contradictory.  Deliberately not built.)"

(tu/deftest-kb different-is-not-assertible
  (tu/with-terms [CxName]
    (tu/with-terms [A B]
      (testing "asserting it is rejected"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'different A B) CxName))))
      (testing "and the refusal stores nothing"
        (is (nil? (v/handle-of kb (list 'different A B) CxName)))
        (is (zero? (v/count-with-functor kb 'different)))
        (is (empty? (v/find-sentexes kb 'different)))))))

;; DECISION (The unique-name assumption survives): "**Ground only.**  The prover is
;; inapplicable unless every argument is bound.  `(different ?x Y)` would enumerate
;; every term in the KB that is not `Y`, so it is refused rather than answered
;; explosively."
;;
;; SPEC NOTE — "refused" is not pinned to a mechanism by the doc.  Since `different`
;; is a **prover**, and a prover declares `applicable?`, the reading taken here is
;; that an open goal makes it inapplicable, so `ask` yields nothing and the goal drops
;; out of `query-plan` (which lists applicable provers only).  The alternative reading
;; — throwing on an open `different` — would fail this test, which is the point: the
;; doc should say which.  The claim both readings share, and the one that actually
;; matters, is that nothing enumerates.

(tu/deftest-kb an-open-different-is-refused-rather-than-enumerated
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [A B C]
      (doseq [x [A B C]] (v/assert kb (list bornIn x Chicago) CxName))
      (testing "the ground goal is claimed by some prover — the control"
        (is (seq (v/query-plan kb (list 'different A B) CxName))))
      (testing "an unbound argument makes that prover inapplicable"
        ;; named by count rather than by class, since the doc names no prover
        (is (< (count (v/query-plan kb (list 'different '?x B) CxName))
               (count (v/query-plan kb (list 'different A   B) CxName)))
            "a prover claimed an open `different` goal"))
      (testing "and nothing enumerated the KB looking for non-B terms"
        (is (empty? (v/ask kb (list 'different '?x B)  CxName)))
        (is (empty? (v/ask kb (list 'different '?x '?y) CxName)))))))

;; DECISION (The unique-name assumption survives): "**Not canonicalized.**  No chain
;; merging ...  `lessThan` merges chains because it is **transitive** ... `different`
;; is **not** transitive — `A≠B` and `B≠C` say nothing about `A` and `C` — so
;; chain-merging it would manufacture a claim nobody made."
;;
;; `different` is never stored, so the only place a chain merge could happen is a rule
;; antecedent, where the literal *is* stored as part of the rule sentex.  That is what
;; is read back here: two `different` literals sharing a variable must survive
;; canonicalization as two literals, not collapse the way `(lessThan ?a ?b)` +
;; `(lessThan ?b ?c)` does.

(tu/deftest-kb a-different-chain-in-a-rule-antecedent-is-not-merged
  (tu/with-terms [triple item CxStory]
    (let [rh (v/assert-rule kb [(list item '?a) (list item '?b) (list item '?c)
                                (list 'different '?a '?b)
                                (list 'different '?b '?c)]
                            (list triple '?a '?b '?c)
                            CxStory {:direction :forward})
          antes (:antecedent (v/sentex kb rh))
          diffs (filter #(= 'different (first %)) antes)]
      (testing "both literals survive — no chain merge"
        (is (= 2 (count diffs))
            (str "the two `different` literals were merged into "
                 (pr-str diffs) " — `different` is not transitive")))
      (testing "and neither grew an argument"
        (is (every? #(= 3 (count %)) diffs)))
      (testing "the rule fires for a binding the merged form would have rejected"
        ;; a=c is allowed: the rule constrains a≠b and b≠c and says nothing about a,c
        (tu/with-terms [X Y]
          (v/assert kb (list item X) CxStory)
          (v/assert kb (list item Y) CxStory)
          (is (seq (v/sentexes-matching kb (list triple X Y X) CxStory))
              "a merged (different ?a ?b ?c) would have blocked a = c")))
      (testing "and a rule assert does not store a `different` fact"
        (is (zero? (v/count-with-functor kb 'different)))))))

;; DECISION (Interactions — Stratification): "`different` in a rule antecedent is a
;; **negative dependency**, so it joins the rule dependency graph beside `exceptWhen`.
;; A rule concluding an equality from a `different` antecedent is a cycle through
;; negation and is rejected — otherwise belief would depend on arrival order."

(tu/deftest-kb a-rule-concluding-an-equality-from-a-different-antecedent-is-rejected
  (tu/with-terms [candidate CxMerge]
    (tu/with-terms [Anchor]
      (testing "the one-rule cycle through negation is refused at assert time"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert-rule kb [(list candidate '?x)
                                        (list 'different '?x Anchor)]
                                    (list 'sameAs '?x Anchor)
                                    CxMerge {:direction :forward}))))
      (testing "and the refusal leaves no rule behind"
        (is (empty? (v/sentexes-in-context kb CxMerge)))))))

;; ---- 6. `functional` -----------------------------------------------------
;; DECISION (`functional` infers equality instead of throwing): "`(functional P)` plus
;; two different values for the same first argument currently throws.  It will instead
;; **derive** an equality between the values."  Not throwing is half the claim; the
;; merge actually happening is the other half.
;;
;; SPEC NOTE — the doc says "an equality" without naming which of the three relations
;; is derived.  `equals` is this suite's choice (the values of a functional role are
;; any terms, not necessarily individuals, which is exactly `equals`'s remit).  The
;; assertions about *merging* are spelling-independent and stand whichever is chosen;
;; only the `derived-equality-exists` assertion below depends on it.
;;
;; Until this lands, the second `(motherOf Tom ...)` assert **throws** — that is the
;; behaviour under specification, so these three tests report as ERROR rather than
;; FAIL, and the two below never reach their assertions at all.

(tu/deftest-kb functional-derives-an-equality-instead-of-throwing
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (testing "the second value does not throw"
        (is (some? (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic}))))
      (testing "the two values are merged, so they are no longer different"
        (is (false? (v/ask? kb (list 'different lo hi) CxFam))))
      (testing "and a fact about either reads under the representative"
        (v/assert kb (list caresFor hi Tom) CxFam)
        (is (believed? kb (list caresFor lo Tom) CxFam)))
      (testing "the derived equality is itself a sentex"
        (is (some? (v/handle-of kb (list 'equals lo hi) CxFam)))))))

(tu/deftest-kb a-merge-rests-on-every-functional-declaration-not-on-one-of-them
  ;; Nothing refuses `(functional P)` in two contexts, which is two sentexes and two
  ;; handles.  Resting the derived equality on one of them puts an assertion-ordered
  ;; handle into the justification's antecedents: retracting *that* declaration would
  ;; withdraw a merge the other one still licenses, and which of the two it was would
  ;; depend on the order they arrived in.  One justification per declaration is what
  ;; makes the merge a function of the knowledge.
  ;;
  ;; **Both directions, on independent predicates**, because a single arm cannot tell
  ;; this apart from luck: resting the merge on one arbitrary handle passes whenever the
  ;; retracted declaration happens not to be the chosen one.  Retiring the first in one
  ;; predicate and the second in another, no single choice survives both.
  (tu/with-terms [Tom CxFam CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxFam 'CxUniverse) 'CxUniverse)
    (doseq [retire [:first :second]]
      (let [motherOf (tu/fresh-term :predicate "motherOf")
            [lo hi]  (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
            h1       (v/assert kb (list 'functional motherOf) CxFam)
            h2       (v/assert kb (list 'functional motherOf) CxStory)]
        (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
        (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
        (is (v/same-class? kb lo hi)
            "the merge is derived while both declarations stand")
        (testing (str "retiring the " (name retire) " declaration leaves the merge")
          (v/retract! kb (if (= retire :first) h1 h2))
          (is (v/same-class? kb lo hi)
              (str "the surviving declaration licenses the same equality, so the merge "
                   "stands — it never rested on one arbitrary handle")))))))

;; DECISION (`functional` infers equality instead of throwing): "Making it a real
;; justification rather than a side effect is what makes it safe ... the merge is
;; justified, `why` names exactly which declaration and which two facts caused it."
;; A silent merge would be the dangerous version of this feature, so the *inspectable*
;; half is pinned separately from the *reversible* half below.

(tu/deftest-kb why-on-a-functional-merge-names-the-declaration-and-both-facts
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (let [eq (v/handle-of kb (list 'equals lo hi) CxFam)]
        (is (some? eq) "no derived equality to explain")
        (let [tree (v/why kb eq)
              said (set (why-sentences tree))]
          (testing "it is derived, not a premise"
            (is (true?  (:believed? tree)))
            (is (false? (:premise?  tree)))
            (is (seq (:support tree))))
          (testing "and the argument names the declaration and both facts"
            (is (contains? said (list 'functional motherOf))
                "why does not name the functional declaration that caused the merge")
            (is (contains? said (list motherOf Tom lo)))
            (is (contains? said (list motherOf Tom hi)))))))))

;; DECISION (`functional` infers equality instead of throwing): "retracting any one of
;; them runs the existing sweep and un-merges.  An opaque merge would be dangerous; an
;; inspectable, reversible one is knowledge."

(tu/deftest-kb retracting-either-functional-fact-un-merges-the-values
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (let [second-fact (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})]
        (v/assert kb (list caresFor hi Tom) CxFam)
        (testing "merged while both facts stand"
          (is (false? (v/ask? kb (list 'different lo hi) CxFam)))
          (is (believed? kb (list caresFor lo Tom) CxFam)))
        (v/retract! kb second-fact)
        (testing "retracting one of them un-merges"
          (is (true? (v/ask? kb (list 'different lo hi) CxFam)))
          (is (nil?  (v/handle-of kb (list 'equals lo hi) CxFam))))
        (testing "and the migrated twin is swept while the original revives"
          (is (nil? (v/handle-of kb (list caresFor lo Tom) CxFam)))
          (is (true? (believed? kb (list caresFor hi Tom) CxFam))))))))

(tu/deftest-kb a-collision-merges-only-when-both-facts-are-monotonic
  ;; DECISION (docs/reference.md, decisions 6 and 13): a merge is never defeated and is
  ;; undone only by retracting a premise it rests on, so it rests on `:monotonic`
  ;; evidence alone.  A `functional` or `anti_symmetric` collision with a `:default` fact
  ;; is a nogood: the unique `:default` fact is OUT and two `:default` facts are a
  ;; dilemma, whichever fact arrives first.
  (doseq [mark    ['functional 'anti_symmetric]
          [sa sb] [[:monotonic :default] [:monotonic :monotonic] [:default :default]]
          flip?   [false true]]
    (tu/with-terms [rel Kid Ann Bea CxFam]
      (let [[fa fb] (if (= 'functional mark)
                      [(list rel Kid Ann) (list rel Kid Bea)]
                      [(list rel Ann Bea) (list rel Bea Ann)])
            both?   (= :monotonic sa sb)
            ;; read at the context: an `anti_symmetric` loser is decided by its reader
            held?   #(boolean (v/believed? kb (v/handle-of kb % CxFam) CxFam))
            dilemma (fn [] (some #(= #{fa fb} (into #{} (map :sentence) (:sides %)))
                                 (v/contradictions kb)))]
        (v/assert kb (list mark rel) CxFam)
        (doseq [[f st] (cond-> [[fa sa] [fb sb]] flip? reverse)]
          (v/assert kb f CxFam {:strength st}))
        (testing (str mark " " sa " beside " sb (when flip? ", the second first"))
          (is (= both? (v/same-class? kb Ann Bea)))
          (is (= both? (some? (v/handle-of kb (list 'equals Ann Bea) CxFam))))
          (when-not both?
            (is (held? fa))
            (is (= (= :default sa) (held? fb)))
            (is (= (= :default sa) (boolean (dilemma))))))))))

;; A member's class also moves under an unchanged label, through a justification of it
;; arriving or leaving, and the merge follows the class as it follows a write.
(defn- collision-with-route
  "Write in a fresh context a `mark` over a fresh `rel`, a `:monotonic` forward rule
  `(route ?x ?y) => (rel ?x ?y)`, the `:monotonic` tuple `fa`, the `:default` tuple `fb`,
  and the `:monotonic` `route` twin of `fb`, which makes `fb` `:monotonic`: the route
  first when `route-first?`, else last."
  [kb mark route-first?]
  (tu/with-terms [rel route Kid Ann Bea CxFam]
    (let [[fa fb] (if (= 'functional mark)
                    [(list rel Kid Ann) (list rel Kid Bea)]
                    [(list rel Ann Bea) (list rel Bea Ann)])
          r       (cons route (rest fb))]
      (v/assert kb (list mark rel) CxFam)
      (v/assert kb (list 'set/forwardRule (list 'implies (list route '?x '?y) (list rel '?x '?y)))
                CxFam {:strength :monotonic})
      (when route-first? (v/assert kb r CxFam {:strength :monotonic}))
      (v/assert kb fa CxFam {:strength :monotonic})
      (v/assert kb fb CxFam {:strength :default})
      (when-not route-first? (v/assert kb r CxFam {:strength :monotonic}))
      {:fa fa :fb fb :route r :a Ann :b Bea :cx CxFam})))

(defn- held-at?
  "Is `s` stored at `cx` and believed there?  An `anti_symmetric` loser is decided by its
  reader."
  [kb s cx]
  (boolean (some->> (v/handle-of kb s cx) (#(v/believed? kb % cx)))))

(tu/deftest-kb a-merge-follows-its-members-classes-when-a-route-moves
  (doseq [mark '[functional anti_symmetric]]
    (testing (str mark ", the route retracted after the merge: fb is the unique :default member")
      (let [{:keys [fa fb route a b cx]} (collision-with-route kb mark true)]
        (is (true? (v/same-class? kb a b)))
        (v/retract! kb (v/handle-of kb route cx))
        (is (false? (v/same-class? kb a b)))
        (is (true? (held-at? kb fa cx)))
        (is (false? (held-at? kb fb cx)))))
    (testing (str mark ", the route arriving after fb merges as it does arriving first")
      (let [{:keys [a b]} (collision-with-route kb mark false)]
        (is (true? (v/same-class? kb a b)))))))

(tu/deftest-kb a-reader-re-decides-a-merging-converse-pair-when-a-member-s-class-drops
  ;; the reader decides the pair while it merges, so its answer watches both members;
  ;; the functional sequence first leaves the reader's answer cached before the drop
  (let [{f-route :route f-cx :cx} (collision-with-route kb 'functional false)]
    (v/retract! kb (v/handle-of kb f-route f-cx)))
  (let [{:keys [fa fb route cx]} (collision-with-route kb 'anti_symmetric false)]
    (v/retract! kb (v/handle-of kb route cx))
    (is (true? (held-at? kb fa cx)))
    (is (false? (held-at? kb fb cx)))))

;; DECISION (`functional` infers equality instead of throwing) meeting order
;; independence: a declaration has to reach the facts already stored exactly as it
;; reaches the facts that follow — the both-directions rule `entail-existing` states
;; for the argument constraints, and the same rule here.  The three tests above all
;; write the declaration first, which is the direction that was never the question:
;; the values a functional slot already holds are co-referent whether the KB is told
;; the predicate is functional before it is told the facts or after, and if it is not,
;; then whether two names denote one woman depends on which line of a file arrived
;; first.

(tu/deftest-kb a-functional-declaration-arriving-after-the-facts-merges-them-too
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (testing "before the declaration the two values are simply two values"
        (is (true? (v/ask? kb (list 'different lo hi) CxFam))))
      (v/assert kb (list 'functional motherOf) CxFam)
      (testing "the declaration merges what it now says was always one thing"
        (is (false? (v/ask? kb (list 'different lo hi) CxFam))))
      (testing "the derived equality is a sentex here too"
        (is (some? (v/handle-of kb (list 'equals lo hi) CxFam))))
      (testing "and a fact about either reads under the representative"
        (v/assert kb (list caresFor hi Tom) CxFam)
        (is (believed? kb (list caresFor lo Tom) CxFam))))))

(tu/deftest-kb the-functional-declaration-reaches-the-same-belief-from-either-end
  ;; the oracle for the test above: the same three sentences in the two orders that
  ;; matter, compared on what the KB *believes* rather than on what it stored
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
          decl (list 'functional motherOf)
          f1   (list motherOf Tom lo)
          f2   (list motherOf Tom hi)
          reading (fn [] [(v/ask? kb (list 'different lo hi) CxFam)
                          (v/representative kb lo)
                          (v/representative kb hi)
                          (some? (v/handle-of kb (list 'equals lo hi) CxFam))])]
      (doseq [s [decl f1 f2]] (v/assert kb s CxFam))
      (let [declaration-first (reading)]
        (doseq [s [decl f1 f2]]
          (when-let [h (v/handle-of kb s CxFam)] (v/retract! kb h)))
        (doseq [s [f2 f1 decl]] (v/assert kb s CxFam))
        (is (= declaration-first (reading))
            "the same three sentences believe different things in the two orders")))))

(tu/deftest-kb a-retroactive-functional-merge-carries-the-same-argument
  ;; the merge is knowledge only if it is inspectable, and a retroactive one names the
  ;; same three sentexes a forward one does — otherwise `why` would explain one arrival
  ;; order and shrug at the other
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (v/assert kb (list 'functional motherOf) CxFam)
      (let [eq (v/handle-of kb (list 'equals lo hi) CxFam)]
        (is (some? eq) "no derived equality to explain")
        (let [said (set (why-sentences (v/why kb eq)))]
          (is (contains? said (list 'functional motherOf)))
          (is (contains? said (list motherOf Tom lo)))
          (is (contains? said (list motherOf Tom hi))))))))

(tu/deftest-kb retracting-a-retroactive-functional-declaration-un-merges
  ;; reversibility is the other half of "inspectable, reversible", and the declaration
  ;; is one of the three antecedents whichever order it arrived in
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list caresFor hi Tom) CxFam)
      (testing "merged while the declaration stands"
        (is (false? (v/ask? kb (list 'different lo hi) CxFam)))
        (is (believed? kb (list caresFor lo Tom) CxFam)))
      (v/retract! kb (v/handle-of kb (list 'functional motherOf) CxFam))
      (testing "retracting the declaration un-merges the values it merged"
        (is (true? (v/ask? kb (list 'different lo hi) CxFam)))
        (is (nil?  (v/handle-of kb (list 'equals lo hi) CxFam))))
      (testing "and the migrated twin goes with it"
        (is (nil? (v/handle-of kb (list caresFor lo Tom) CxFam)))
        (is (true? (believed? kb (list caresFor hi Tom) CxFam)))))))

(tu/deftest-kb a-retroactive-declaration-collapses-a-whole-slot-not-one-pair
  ;; three spellings of one mother: the sweep is over the predicate's extent, so every
  ;; value in the slot lands in one class rather than the first pair it happens to meet
  (tu/with-terms [motherOf Tom CxFam]
    (let [[a b c] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (doseq [m [a b c]] (v/assert kb (list motherOf Tom m) CxFam {:strength :monotonic}))
      (v/assert kb (list 'functional motherOf) CxFam)
      (testing "all three collapse to one representative"
        (is (= 1 (count (distinct (map #(v/representative kb %) [a b c]))))
            (str "three values did not reach one class: "
                 (pr-str (mapv #(v/representative kb %) [a b c]))))))))

(tu/deftest-kb a-functional-merge-a-rule-triggered-displaces-the-spelling-too
  ;; The second value arrives as a rule's conclusion, so the merge happens from inside
  ;; the chaining run rather than from the assert that started it.  The migration is the
  ;; same either way, and so is what it owes: the twin is stored *and* the spelling it
  ;; restates stops being believed.  Leaving the supersession to whatever runs next
  ;; leaves both spellings believed — which is the state `recover` would not come back
  ;; in, since the rebuild reads the twin off the store and displaces the original.
  (tu/with-terms [motherOf parentOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list caresFor hi Tom) CxFam)
      (v/assert-rule kb [(list parentOf '?x '?y)] (list motherOf '?x '?y) CxFam {:direction :forward})
      (v/assert kb (list parentOf Tom hi) CxFam {:strength :monotonic})
      (testing "the derived second value merges"
        (is (v/same-class? kb lo hi)))
      (testing "and the fact under the retired spelling is restated, not doubled"
        (is (believed? kb (list caresFor lo Tom) CxFam))
        (is (stored-not-believed? kb (list caresFor hi Tom) CxFam))))))

;; ---- 7. an equality a rule concluded -------------------------------------
;; DECISION (Interactions — A rule concluding one of the three relations merges): "a
;; rule-concluded `(sameAs A B)` reaches `special/integrate-equality-sentex` — the same
;; arm the table runs for an asserted one — so the closure learns the edge, migration
;; restates every sentex it displaces, the retired spelling stops being believed, and a
;; migration the integrity checks refuse is filed as a violation."  The live/rebuilt
;; half of the same claim is
;; `recovery-test/recover-agrees-about-a-rule-concluded-equality`.
;;
;; All three relations, because the derivation path dispatches on the functor: the two
;; symmetric ones elect the smaller spelling and `rewriteOf` elects its first argument,
;; so a fact written `(alias lo hi)` retires `hi` under every one of them.

(defn- rule-concluded-merge!
  "Assert a rule concluding `(rel ?x ?y)` from a fact of `aliasOf`, plus one fact naming
  the spelling the merge retires, and fire it.  `aliasOf` is declared on the
  forced-monotonic roster where the rule is stated, since a firing concludes an equality
  only from roster antecedents.  Returns `[lo hi]` — the elected representative and the retired
  spelling."
  [kb rel aliasOf caresFor Tom context]
  (let [[lo hi] (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])]
    (v/assert kb (list 'forced_monotonic_predicate aliasOf) context)
    (v/assert-rule kb [(list aliasOf '?x '?y)] (list rel '?x '?y) context {:direction :forward})
    (v/assert kb (list caresFor hi Tom) context)
    (v/assert kb (list aliasOf lo hi) context)
    [lo hi]))

(tu/deftest-kb a-rule-concluding-an-equality-merges-like-an-asserted-one
  (doseq [rel '[rewriteOf sameAs equals]]
    (testing (str "a rule concluding " rel)
      (tu/with-terms [aliasOf caresFor CxAlias]
        (tu/with-terms [Tom]
          (let [[lo hi] (rule-concluded-merge! kb rel aliasOf caresFor Tom CxAlias)]
            (testing "the conclusion is stored and believed"
              (is (believed? kb (list rel lo hi) CxAlias)))
            (testing "and the closure holds the edge it states"
              (is (v/same-class? kb lo hi)
                  (str "the equality closure never learned the rule's conclusion "
                       (pr-str (list rel lo hi))))
              (is (= lo (v/representative kb hi))))
            (testing "the retired spelling is blocked and its restatement believed"
              (is (stored-not-believed? kb (list caresFor hi Tom) CxAlias))
              (is (believed? kb (list caresFor lo Tom) CxAlias)))
            (testing "and the only violation is the one the merge itself creates"
              ;; `rewriteOf` files one, and it is the merge rather than the derivation
              ;; that files it: the antecedent fact names both terms, so migration
              ;; restates it as `(alias lo lo)`, the rule fires again on the
              ;; restatement, and a self-edge is what `wff` refuses.  `(sameAs A A)` is
              ;; accepted, so the two symmetric relations file nothing.
              (is (= (if (= rel 'rewriteOf) #{:not-well-formed} #{})
                     (set (map :violation (v/violations kb))))
                  (str "unexpected violations: " (pr-str (v/violations kb)))))
            (v/clear-violations! kb)))))))

(tu/deftest-kb a-twin-a-derived-merge-created-fires-the-rules-that-match-it
  ;; The twin is new content the run has not seen, so it goes back on the agenda exactly
  ;; as the twin of an asserted merge does — and it has to, because the spelling it
  ;; restates stops matching the moment the merge lands: a rule that had not yet reached
  ;; the original would otherwise fire on neither.
  ;;
  ;; The second antecedent is what makes the twin the only route to the conclusion.  It
  ;; holds of the representative and not of the retired spelling, so the join cannot
  ;; succeed before the merge — and the conclusion cannot be a migrated twin of an
  ;; earlier firing either, there having been none to migrate.
  (tu/with-terms [aliasOf caresFor lives devotedTo Tom CxAlias]
    (v/assert-rule kb [(list caresFor '?x '?y) (list lives '?x)]
                   (list devotedTo '?x '?y) CxAlias {:direction :forward})
    (let [[lo hi] (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])]
      (v/assert kb (list lives lo) CxAlias)
      ;; a firing concludes an equality only from roster antecedents
      (v/assert kb (list 'forced_monotonic_predicate aliasOf) CxAlias)
      (v/assert-rule kb [(list aliasOf '?x '?y)] (list 'sameAs '?x '?y) CxAlias {:direction :forward})
      (v/assert kb (list caresFor hi Tom) CxAlias)
      (is (nil? (v/handle-of kb (list devotedTo hi Tom) CxAlias))
          "the join must not succeed before the merge, or the twin proves nothing")
      (v/assert kb (list aliasOf lo hi) CxAlias)
      (is (v/same-class? kb lo hi))
      (is (believed? kb (list devotedTo lo Tom) CxAlias)
          "the twin never reached the agenda: nothing fired off the restated fact"))))

(defn- stated-and-derived-merge-reading
  "The sentences CxAlias believes once `ops` run in order, with `lo` and `hi` read back as
  `Lo` and `Hi`: `:fact` `(aliasOf lo hi)`, `:rule` `(aliasOf ?x ?y) => (sameAs ?x ?y)`,
  `:merge` the premise `(sameAs lo hi)`, `:unmerge` its retraction, all `:monotonic`."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [aliasOf CxAlias]
      (let [[lo hi] (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])
            m       {:strength :monotonic}]
        (v/assert kb (list 'forced_monotonic_predicate aliasOf) CxAlias)
        (doseq [op ops]
          (case op
            :fact    (v/assert kb (list aliasOf lo hi) CxAlias m)
            :rule    (v/assert-rule kb [(list aliasOf '?x '?y)] (list 'sameAs '?x '?y) CxAlias
                                    (assoc m :direction :forward))
            :merge   (v/assert kb (list 'sameAs lo hi) CxAlias m)
            :unmerge (v/retract! kb (v/handle-of kb (list 'sameAs lo hi) CxAlias))))
        (into #{} (comp (filter #(believed? kb % CxAlias))
                        (map #(replace {lo 'Lo hi 'Hi aliasOf 'aliasOf} %)))
              (for [r [aliasOf 'sameAs], [a b] [[lo lo] [lo hi] [hi hi]]] (list r a b)))))))

(deftest a-merge-stated-and-derived-reads-alike-in-every-arrival-order
  ;; With the premise last, the firing over `(aliasOf Lo Hi)` is stored as a second
  ;; justification of the merge, which the withdrawal at the merge keeps
  ;; (`settle/merge-support`); with the premise first, the spelling is superseded on
  ;; arrival and that firing is made only once the premise leaves.  Belief agrees.
  (doseq [tail [[] [:unmerge]]]
    (is (= #{#{'(aliasOf Lo Lo) '(sameAs Lo Hi) '(sameAs Lo Lo)}}
           (into #{} (map #(stated-and-derived-merge-reading (concat % tail)))
                 (permutations [:fact :rule :merge])))
        (pr-str tail))))

;; ---- 8. disjointness -----------------------------------------------------
;; DECISION (Interactions — Disjointness): a merge can *create* a clash, `(dog Rex)` +
;; `(cat Fluffy)` + merge makes one individual both.  The twin is stored, supersedes its
;; original, and the clash is decided and reported like any stored clash; dropping the
;; twin would leave the member restated second under its old spelling.

(tu/deftest-kb a-merge-that-creates-a-disjointness-clash-stores-the-twin-and-reports-it
  (tu/with-terms [dog cat CxPet]
    (tu/with-terms [Rex Fluffy]
      (v/assert kb (list 'disjoint dog cat) CxPet {:strength :monotonic})
      (v/assert kb (list dog Rex)    CxPet)
      (v/assert kb (list cat Fluffy) CxPet)
      (v/assert kb (list 'sameAs Rex Fluffy) CxPet)
      (let [[rep other] (sort [Rex Fluffy])
            [t-rep t-other] (if (= rep Rex) [dog cat] [cat dog])]
        (testing "both memberships are restated under the representative and believed"
          (is (believed? kb (list t-rep rep) CxPet))
          (is (believed? kb (list t-other rep) CxPet))
          (is (stored-not-believed? kb (list t-other other) CxPet)))
        (testing "the clash is a reported dilemma, and nothing is filed in violations"
          (is (some #(and (= :disjoint (:kind %))
                          (= #{(list dog rep) (list cat rep)} (set (map :sentence (:sides %)))))
                    (v/contradictions kb)))
          (is (not-any? #(= :disjoint (:violation %)) (v/violations kb))))))))

(tu/deftest-kb a-clash-member-out-at-the-merge-takes-the-representative-when-its-defeater-goes
  ;; `(dog Bea)` is OUT when the merge arrives, defeated by the :monotonic `(cat Bea)`;
  ;; its twin is stored OUT beside it, so retracting `(cat Bea)` leaves the KB a KB
  ;; built without `(cat Bea)` would be: `(dog Ann)` believed, `(dog Bea)` superseded
  (tu/with-terms [dog cat CxZoo]
    (tu/with-terms [Ann Bea]
      (let [[rep other] (sort [Ann Bea])]
        (v/assert kb (list 'disjoint dog cat) CxZoo {:strength :monotonic})
        (v/assert kb (list cat other) CxZoo {:strength :monotonic})
        (v/assert kb (list dog other) CxZoo)
        (v/assert kb (list 'equals rep other) CxZoo {:strength :monotonic})
        (is (believed? kb (list cat rep) CxZoo))
        (is (stored-not-believed? kb (list dog rep) CxZoo))
        (v/retract! kb (v/handle-of kb (list cat other) CxZoo))
        (is (believed? kb (list dog rep) CxZoo))
        (is (stored-not-believed? kb (list dog other) CxZoo))))))

;; ---- 9. well-formedness --------------------------------------------------
;; DECISION (Choosing the representative): "A `rewriteOf` cycle has no representative
;; and is rejected by `wff`, like a `genl` cycle."  Both the two-edge cycle and the
;; longer one, because a check that only compared the two arguments of the edge being
;; asserted would pass the first and miss the second.

(tu/deftest-kb a-rewrite-of-cycle-is-rejected
  (tu/with-terms [CxName]
    (tu/with-terms [A B C]
      (testing "the two-edge cycle"
        (v/assert kb (list 'rewriteOf A B) CxName)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf B A) CxName))))
      (testing "the three-edge cycle, which a pairwise check would miss"
        (v/assert kb (list 'rewriteOf B C) CxName)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf C A) CxName))))
      (testing "and a refused edge leaves nothing stored"
        (is (nil? (v/handle-of kb (list 'rewriteOf B A) CxName)))
        (is (nil? (v/handle-of kb (list 'rewriteOf C A) CxName)))))))

;; DECISION (Choosing the representative): a self-edge is the degenerate cycle, and it
;; is the one an import pipeline actually produces (the same term aligned to itself).

(tu/deftest-kb a-rewrite-of-self-edge-is-rejected
  (tu/with-terms [CxName]
    (tu/with-terms [A]
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'rewriteOf A A) CxName)))
      (is (nil? (v/handle-of kb (list 'rewriteOf A A) CxName))))))

;; ---- 10. what the supersession reconcile costs ---------------------------
;;
;; The blocked spelling of section 3 is *derived state*: `special/refresh-supersessions`
;; recomputes it every settle so that a supersession cannot outlive the merge behind it.
;; What a standing merge set costs that reconcile is a shape question rather than a
;; feature one, and it is the reason these tests count instead of asserting: a KB's
;; merges are not a small fixed population — `owl:sameAs` is what an RDF import emits in
;; quantity, and re-examining every displaced spelling on every settle makes loading n
;; merges quadratic in n.
;;
;; So the reconcile is narrowed to the region the settle moved plus what migration just
;; handed it, and the narrowing is a claim about what cannot have changed.  A wrong
;; claim is a stale supersession — a spelling left hidden after the merge that hid it is
;; gone, which is the caller's own premise withheld — so the cost gate is followed by
;; the three cases it must never trade.  The unit counted is `kb/rewrite-term*`, one
;; call per displaced spelling re-examined.

(defn- counting-rewrites
  "Run `f`, returning the number of `kb/rewrite-term*` calls it caused."
  [f]
  (let [n    (atom 0)
        orig kb/rewrite-term*]
    (with-redefs [kb/rewrite-term* (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(defn- merges!
  "n `(sameAs …)` merges, each displacing exactly one stored fact: the fact is written
  under the larger spelling and the smaller one wins the content-keyed election."
  [kb n]
  (dotimes [i n]
    (v/assert kb (list 'eqcBorn (symbol (str "EqcHi" i)) 'EqcPlace) merge-cost-ctx)
    (v/assert kb (list 'sameAs (symbol (str "EqcAa" i)) (symbol (str "EqcHi" i)))
              merge-cost-ctx)))

(deftest one-unrelated-retraction-does-not-re-examine-every-standing-merge
  (testing "a retraction naming no merged term costs the reconcile nothing, at any
            standing merge count"
    ;; The region this settle moved is the one plain fact and what rested on it.  No
    ;; equality edge moved, no rewrite rule moved and no context edge moved, so no
    ;; standing entry can have stopped holding — and none is re-examined.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (merges! kb n)
                   (let [h (v/assert kb '(eqc_plain EqcTarget) merge-cost-ctx)]
                     (counting-rewrites #(v/retract! kb h)))))
          few  (cost 10)
          many (cost 40)]
      (is (= 0 few many)
          (str "an unrelated retraction re-examined the standing merges: " few
               " (10 merges) / " many " (40 merges) rewrites")))))

(deftest loading-merges-does-not-re-examine-the-merges-already-standing
  (testing "asserting one more merge re-examines what it displaced, not the whole set"
    ;; The other half of the same claim, and the one that makes a corpus load linear.
    ;; Migration walks the class the new edge moved and hands the reconcile its own
    ;; output; every other entry belongs to a class this edge did not touch.
    (let [cost (fn [standing]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (merges! kb standing)
                   (v/assert kb '(eqcBorn EqcHiZ EqcPlace) merge-cost-ctx)
                   (counting-rewrites
                    #(v/assert kb '(sameAs EqcAaZ EqcHiZ) merge-cost-ctx))))
          few  (cost 10)
          many (cost 40)]
      (is (= few many)
          (str "one more merge cost more on a KB with more standing merges: " few
               " (10 standing) / " many " (40 standing) rewrites")))))

;; The three cases the narrowing must not miss.  Each moves something the region alone
;; does not describe, and each leaves a spelling hidden that should have come back.

(deftest un-merging-one-pair-revives-it-with-other-merges-standing
  (testing "retracting one sameAs among many revives exactly its own spelling"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merges! kb 20)
      (let [eq (v/handle-of kb '(sameAs EqcAa7 EqcHi7) merge-cost-ctx)
            f7 (v/handle-of kb '(eqcBorn EqcHi7 EqcPlace) merge-cost-ctx)
            f8 (v/handle-of kb '(eqcBorn EqcHi8 EqcPlace) merge-cost-ctx)]
        (is (false? (v/in? kb f7)) "displaced while the merge stands")
        (v/retract! kb eq)
        (is (true? (v/in? kb f7))
            "the un-merged spelling is believed again: the entry was re-examined")
        (is (false? (v/in? kb f8))
            "and the pair beside it, whose merge still stands, is still displaced")))))

(deftest un-merging-a-derived-equality-revives-its-spelling-too
  (testing "a merge nobody asserted, withdrawn by a retraction that never names it"
    ;; The retracted handle is a `motherOf` fact; the equality it supported is derived
    ;; (`functional`), so the thing that stopped displacing the spelling is not in the
    ;; region under its own name.  The closure moving is the whole of what says so.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merges! kb 20)
      (v/assert kb '(functional eqcMotherOf) merge-cost-ctx)
      (v/assert kb '(eqcMotherOf EqcTom EqcMaryA) merge-cost-ctx {:strength :monotonic})
      (let [second-fact (v/assert kb '(eqcMotherOf EqcTom EqcMaryB) merge-cost-ctx {:strength :monotonic})]
        (v/assert kb '(eqcCaresFor EqcMaryB EqcTom) merge-cost-ctx)
        (let [orig (v/handle-of kb '(eqcCaresFor EqcMaryB EqcTom) merge-cost-ctx)]
          (is (false? (v/in? kb orig))
              "displaced by the derived merge, which elected the smaller spelling")
          (v/retract! kb second-fact)
          (is (true? (v/in? kb orig))
              "and believed again once the derived merge goes, twenty merges standing"))))))

(deftest dropping-a-schematic-rewrite-revives-what-it-normalized
  (testing "an equation leaving re-normalizes the sentences it reached"
    ;; The channel a class comparison cannot see: a schematic rewrite displaces a
    ;; spelling by normalizing its *terms*, so the entry it produced names no merged
    ;; symbol at all.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merges! kb 20)
      (v/assert kb '(eqcKnows EqcRoot (eqc_dad_of (eqc_dad_of EqcRoot))) merge-cost-ctx)
      (let [orig (v/handle-of kb '(eqcKnows EqcRoot (eqc_dad_of (eqc_dad_of EqcRoot)))
                              merge-cost-ctx)
            rule (v/assert kb '(equals (eqc_dad_of (eqc_dad_of ?x)) (eqc_grandad_of ?x))
                           merge-cost-ctx)]
        (is (false? (v/in? kb orig)) "normalized away while the equation stands")
        (v/retract! kb rule)
        (is (true? (v/in? kb orig))
            "and believed again once nothing normalizes it")))))

;; DECISION (regression): the equality relations relate NAMES — their arguments are
;; mentions, like a quoting_function's — so a merge must not rewrite a denial OF the merge
;; into the vacuous `(not (sameAs A A))`.  Without that, a monotonic denial of a default
;; merge was silently superseded and the merge stood (docs/equality.md, the flagged case).

(tu/deftest-kb a-denial-of-an-equality-leaves-a-default-merge-standing-in-either-order
  ;; the equality relations are on the engine's baseline roster, so on this bare KB too
  ;; the merge is never a loser and a denial of it is held OUT (decision 13); the merge
  ;; keeps the strength it was written at
  (doseq [denial-first? [false true]]
    (tu/with-terms [A B]
      (let [deny  #(v/assert kb (list 'not (list 'sameAs A B)) 'CxUniverse {:strength :monotonic})
            _     (when denial-first? (deny))
            merge (v/assert kb (list 'sameAs A B) 'CxUniverse)
            d     (if denial-first? (v/handle-of kb (list 'not (list 'sameAs A B)) 'CxUniverse) (deny))]
        (is (v/same-class? kb A B) (str "denial first: " denial-first?))
        (is (= :default (v/defeat-class kb merge)))
        (is (not (v/in? kb d)) "the denial is held OUT")))))

(deftest the-mention-set-mirrors-the-canonical-equality-predicate-set
  ;; `res/equality-mention-heads` is `rewrite/equality-relations`, a copy of
  ;; `kb/equality-predicates` — `kb` requires `resolution`, so the canonical set cannot be
  ;; required back into it.  Keep the two equal, or a relation added to one and not the
  ;; other rewrites the mentions of the relation it forgot.
  (is (= kb/equality-predicates @#'res/equality-mention-heads)))

;; ---- a stated equation is answered ----------------------------------------

;; DECISION (Answering an equation): a believed `(sameAs A B)` is answered by every read.
;; The stored equation is never restated, so no read may call it retired; `ask` reads the
;; closure for the symmetric, reflexive and transitive forms and enumerates a bound
;; symbol's class.  The stated sentence reaching none of `ask?`, `prove` and
;; `sentexes-matching` is the failure this pins, and each column below is one of them.

(defn- equation-reads
  "Every read of `pred` over `a` / `b` / `c`, where `(pred a b)` and `(sameAs b c)` are
  stated in `ctx`."
  [kb pred a b c ctx]
  {:stated    (v/ask? kb (list pred a b) ctx)
   :symmetric (v/ask? kb (list pred b a) ctx)
   :reflexive (v/ask? kb (list pred a a) ctx)
   :chain     (v/ask? kb (list pred a c) ctx)
   :open      (set (map #(get % '?y) (v/ask kb (list pred a '?y) ctx)))
   :prove     (count (v/prove kb (list pred a b) ctx))
   :matching  (count (v/sentexes-matching kb (list pred a b) ctx))})

(tu/deftest-kb a-stated-equation-is-answered-by-every-read
  (doseq [pred ['sameAs 'equals]]
    (testing (str pred " is reflexive, symmetric and transitive through the closure")
      (tu/with-terms [CxEq]
        (let [[a b c] (sort [(tu/tmp-ind "Eq") (tu/tmp-ind "Eq") (tu/tmp-ind "Eq")])]
          (v/assert kb (list pred a b) CxEq {:strength :monotonic})
          (v/assert kb (list 'sameAs b c) CxEq {:strength :monotonic})
          (is (= {:stated true :symmetric true :reflexive true :chain true
                  :open #{a b c} :prove 1 :matching 1}
                 (equation-reads kb pred a b c CxEq))))))))

(tu/deftest-kb a-stated-rewrite-of-is-answered-as-a-directed-edge
  ;; `rewriteOf` is directional: the stated edge answers every read, and neither its
  ;; converse nor a self-edge (which `wff` refuses) is answered.  The goal is asked as
  ;; spelled, since the spelling rename it states would otherwise rewrite the goal into
  ;; `(rewriteOf a a)`.
  (tu/with-terms [CxEq]
    (let [[a b c] (sort [(tu/tmp-ind "Rw") (tu/tmp-ind "Rw") (tu/tmp-ind "Rw")])]
      (v/assert kb (list 'rewriteOf a b) CxEq {:strength :monotonic})
      (v/assert kb (list 'sameAs b c) CxEq {:strength :monotonic})
      (is (= {:stated true :symmetric false :reflexive false :chain false
              :open #{b} :prove 1 :matching 1}
             (equation-reads kb 'rewriteOf a b c CxEq))))))

(tu/deftest-kb an-equation-is-answered-only-where-it-is-visible
  ;; The closure read is scoped like `same-class?`: a context outside the equation's
  ;; ancestor set was told nothing, so the unique-name assumption still holds there.
  (tu/with-terms [CxEq CxElsewhere]
    (let [[a b] (sort [(tu/tmp-ind "Vis") (tu/tmp-ind "Vis")])]
      (v/assert kb (list 'sameAs a b) CxEq {:strength :monotonic})
      (testing "visible where stated"
        (is (true? (v/ask? kb (list 'sameAs b a) CxEq))))
      (testing "not visible from a context that does not inherit it"
        (is (false? (v/ask? kb (list 'sameAs b a) CxElsewhere)))
        (is (= #{a} (set (map #(get % '?y) (v/ask kb (list 'sameAs a '?y) CxElsewhere)))))
        (is (true? (v/ask? kb (list 'different a b) CxElsewhere)))))))

(tu/deftest-kb a-ground-instance-of-a-schematic-equation-is-answered
  ;; Each side of a ground `equals` is a term, normalized at its own root: the instance
  ;; of `(equals (fatherOf (fatherOf ?x)) (grandfather_of ?x))` at `Bob` reaches one
  ;; normal form, and an instance of nothing does not.
  (tu/with-terms [fatherOf grandfather_of Bob Ann CxEq]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
              CxEq)
    (is (true? (v/ask? kb (list 'equals (list fatherOf (list fatherOf Bob))
                                (list grandfather_of Bob))
                       CxEq)))
    (is (false? (v/ask? kb (list 'equals (list fatherOf (list fatherOf Bob))
                                 (list grandfather_of Ann))
                        CxEq)))))

;; ---- a `different` guard is order-independent ----------------------------

(deftest a-different-guarded-firing-is-withdrawn-by-a-fact-that-arrives-after-it
  ;; `different` is negation as failure over the equality closure and over the
  ;; `indeterminate_term` category, so a fact arriving on either **withdraws** it.  It is
  ;; not assertible and holds by the absence of a merge, so it names no handle a
  ;; justification could carry and no `SupportingProver` support can reach it: the rule is
  ;; registered in the re-check index (`rules/different-flip-predicates`) and the firing is
  ;; re-decided in `chain/different-blocks?`.
  ;;
  ;; Both arrival orders are run against each flip source.  The same three sentences must
  ;; settle to the same belief whichever way round they arrive, which is the order
  ;; independence README.md lists as a property no code may break.
  (doseq [[label flip!]
          [["sameAs — a merge puts the two names in one class"
            (fn [kb a b] (v/assert kb (list 'sameAs a b) 'CxUniverse))]
           ["indeterminate_term — a member is exempt from the unique-name assumption"
            (fn [kb a _] (v/assert kb (list 'indeterminate_term a) 'CxUniverse))]
           ["a declared subkind of it — reached through the genls fan, not by name"
            (fn [kb a _]
              (tu/with-terms [vague_kind]
                (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
                (v/assert kb (list vague_kind a) 'CxUniverse)))]]]
    (testing label
      (let [believed (doall
                      (for [order [:guard-then-fact :fact-then-guard]]
                        (tu/with-kb [kb]
                          (tu/with-terms [pRel qRel Aa Bb]
                            (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
                            (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
                            (when (= order :fact-then-guard) (flip! kb Aa Bb))
                            (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                              (list 'different '?x '?y))
                                               (list qRel '?x '?y))
                                      'CxUniverse {:direction :forward})
                            (v/assert kb (list pRel Aa Bb) 'CxUniverse)
                            (when (= order :guard-then-fact) (flip! kb Aa Bb))
                            [(v/ask? kb (list 'different Aa Bb) 'CxUniverse)
                             (v/ask? kb (list qRel Aa Bb) 'CxUniverse)]))))]
        (is (apply = believed)
            (str "the same knowledge in either order yields the same beliefs; got "
                 (pr-str (vec believed))))
        (is (= [false false] (first believed))
            "and the answer is the one the guard licenses: no difference, no conclusion")))))

(tu/deftest-kb a-different-guarded-firing-comes-back-when-the-withdrawing-fact-leaves
  ;; The release direction, which the block alone does not give: retracting the fact that
  ;; suspended the unique-name assumption restores the difference, and the firing it
  ;; guarded is re-derived rather than left withdrawn.
  (tu/with-terms [pRel qRel Aa Bb]
    (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
    (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list pRel '?x '?y) (list 'different '?x '?y))
                       (list qRel '?x '?y))
              'CxUniverse {:direction :forward})
    (v/assert kb (list 'indeterminate_term Aa) 'CxUniverse)
    (v/assert kb (list pRel Aa Bb) 'CxUniverse)
    (is (not (v/ask? kb (list qRel Aa Bb) 'CxUniverse))
        "exempt from the UNA, so the guard does not hold and nothing is concluded")
    (v/retract! kb (v/handle-of kb (list 'indeterminate_term Aa) 'CxUniverse))
    (is (v/ask? kb (list qRel Aa Bb) 'CxUniverse)
        "and the conclusion arrives once the exemption goes, with no re-assertion")))

(deftest a-different-guarded-firing-comes-back-through-the-subkind-channel-too
  ;; The release direction through the channel the flip set reaches by fan-out rather than
  ;; by name.  A kind declared `(genl K indeterminate_term)` makes its members exempt from
  ;; the unique-name assumption, and the exemption rests on **two** sentences — the edge
  ;; and the membership — so withdrawing either restores the difference and owes the
  ;; firing back.  `different-flip-predicates` names `genl` outright and reaches the
  ;; membership through `special/recheck-on-predicate`'s `genls-global` fan, and neither
  ;; route has a blocked justification to move: the guard is evaluated in the join, so the
  ;; suppressed firing never existed.
  (doseq [[label lift!]
          [["the membership retracted — reached through the genls fan"
            (fn [kb k a] (v/retract! kb (v/handle-of kb (list k a) 'CxUniverse)))]
           ["the genl edge retracted — the edge is what made the kind indeterminate"
            (fn [kb k _] (v/retract! kb (v/handle-of kb (list 'genl k 'indeterminate_term)
                                                     'CxUniverse)))]]]
    (testing label
      (tu/with-cleared-kb [kb tu/fresh]
        (tu/with-terms [pRel qRel Aa Bb vague_kind]
          (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
          (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
          (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                            (list 'different '?x '?y))
                             (list qRel '?x '?y))
                    'CxUniverse {:direction :forward})
          (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
          (v/assert kb (list vague_kind Aa) 'CxUniverse)
          (v/assert kb (list pRel Aa Bb) 'CxUniverse)
          (is (not (v/ask? kb (list qRel Aa Bb) 'CxUniverse))
              "exempt from the UNA, so the guard does not hold and nothing is concluded")
          (lift! kb vague_kind Aa)
          (is (v/ask? kb (list 'different Aa Bb) 'CxUniverse)
              "the exemption is gone, so the two are provably different again")
          (is (v/ask? kb (list qRel Aa Bb) 'CxUniverse)
              "and the firing the guard licensed arrives, with no re-assertion"))))))
