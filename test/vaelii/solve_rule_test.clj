;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.solve-rule-test
  "`set/solveRule` — a normal rule (`h :- b`) inside a solve, beside the choices
  `set/assumptionRule` offers.  A choice says what a solve may pick; a solve rule says what
  follows in the answer set from what was picked, and a constraint may then name that.

  The problems here need both:

    * **set cover** — pick sets (a choice), derive which elements are covered (a solve
      rule), and require every element covered (a hard constraint over the derived atom);
    * **reachability** — pick edges (a choice), derive what the root reaches (a recursive
      solve rule), and require every node reached.  A cycle of picked edges the root
      cannot reach supports none of its own atoms: the solver's unfounded-set reading,
      which a completion-only encoding lacks;
    * **a rule true in base too** — a bare `set/solveRule` answers backward goals over
      what `Base` believes and derives the same head inside each answer set.

  The record and wrapper tests need no backend; the solves are guarded on `asp?`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solve-context :as sc]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

(defn- truths
  "The positive sentences a labeling holds, as a set."
  [labeling]
  (set (:true labeling)))

(defn- picked-sets
  "The sets a labeling picks, as a set."
  [pick labeling]
  (set (keep #(when (= pick (first %)) (second %)) (:true labeling))))

(defn- refusal-type
  "The `:type` a refusal thrown by `f` carries, or nil when `f` returns."
  [f]
  (:type (ex-data (try (f) nil (catch clojure.lang.ExceptionInfo e e)))))

;; ---- 1. the wrapper and the record ---------------------------------------

(deftest a-solve-rule-adds-the-solve-engine
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q r s]
      (let [bare  (v/assert kb (list 'set/solveRule (list 'implies (list p '?x) (list q '?x)))
                            'CxUniverse)
            fwd   (v/assert kb (list 'set/forwardRule
                                     (list 'set/solveRule (list 'implies (list r '?x) (list s '?x))))
                            'CxUniverse)
            inert (v/assert kb (list 'set/inertRule
                                     (list 'set/solveRule (list 'implies (list q '?x) (list r '?x))))
                            'CxUniverse)]
        (testing "bare, the rule runs backward in base and in a solve"
          (is (= [:derive #{:backward :solve}] ((juxt :effect :engines) (sentex-of kb bare)))))
        (testing "a direction wrapper beside it says how it runs in base"
          (is (= #{:forward :backward :solve} (:engines (sentex-of kb fwd)))))
        (testing "set/inertRule leaves it to a solve alone"
          (is (= #{:solve} (:engines (sentex-of kb inert))))
          (is (not (rules/chains? (sentex-of kb inert)))))
        (testing "the wrappers come back in the order a re-assert reads"
          (is (= (list 'set/solveRule (list 'implies (list p '?x) (list q '?x)))
                 (rules/rewrap-sentex (v/readable-sentence (sentex-of kb bare)) (sentex-of kb bare))))
          (is (= (list 'set/solveRule (list 'set/inertRule (list 'implies (list q '?x) (list r '?x))))
                 (rules/rewrap-sentex (v/readable-sentence (sentex-of kb inert))
                                      (sentex-of kb inert)))))
        (testing "a solve rule and the same rule without it are one sentex, joined by union"
          (let [plain (v/assert kb (list 'set/forwardRule (list 'implies (list p '?x) (list q '?x)))
                                'CxUniverse)]
            (is (= bare plain))
            (is (= #{:forward :backward :solve} (:engines (sentex-of kb bare))))))))))

(deftest a-solve-spelling-joined-onto-a-stored-rule-enters-the-solve-extent
  ;; the solve extent is the rule-extent node `[:solve]`; its count is read off the
  ;; family method, since no reader returns the counter itself
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q CxSolve]
      (let [idx      (:index kb)
            solve    (fn [] (reads/as-stored-rules-in idx :solve #{CxSolve}))
            counter  (fn [] (p/family-count idx :rule-extent [:solve] p/every-context))
            before   (counter)
            r        (list 'implies (list p '?x) (list q '?x))
            h        (v/assert kb r CxSolve)
            h'       (v/assert kb (list 'set/solveRule r) CxSolve)]
        (is (= h h'))
        (is (contains? (:engines (sentex-of kb h)) :solve))
        (is (= #{h} (solve)) "the joined rule is in the solve extent")
        (v/retract! kb h)
        (is (= #{} (solve)))
        (is (= before (counter)) "the retraction takes out exactly what the join posted")))))

(deftest a-solve-rule-combination-with-no-reading-is-refused
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q]
      (let [r (list 'implies (list p '?x) (list q '?x))]
        (doseq [[label s] [["a choice is in a solve already" (list 'set/solveRule (list 'set/assumptionRule r))]
                           ["so is a constraint" (list 'set/hardConstraint (list 'set/solveRule r))]
                           ["one answer set has no defeat" (list 'set/solveRule (list 'set/defaultRule r))]]]
          (testing label
            (is (= :not-well-formed
                   (:type (ex-data (try (v/assert kb s 'CxUniverse) nil
                                        (catch clojure.lang.ExceptionInfo e e))))))
            (is (seq (v/check kb s 'CxUniverse)))))))))

;; ---- 2. set cover: a choice, a derived atom, a constraint over it ---------

(defn- cover-rule
  "`covered` derived from the picks: a solve rule a solve alone runs."
  [{:keys [pick member covered]}]
  (list 'set/inertRule
        (list 'set/solveRule
              (list 'implies (list 'and (list pick '?s) (list member '?x '?s))
                    (list covered '?x)))))

(defn- cover-statements
  "Sets S1 {a b}, S2 {b c}, S3 {c}, S4 {a c} over the elements `elements`, a choice of any
  set and at most two picked — everything but the solve rule and the requirement."
  [{:keys [cand pick member element]} elements]
  (concat (for [[set* xs] {'S1 '[Ea Eb] 'S2 '[Eb Ec] 'S3 '[Ec] 'S4 '[Ea Ec]}
                s         (cons (list cand set*) (for [x xs] (list member x set*)))]
            s)
          (for [x elements] (list element x))
          [(list 'set/assumptionRule (list 'implies (list cand '?s) (list pick '?s)))
           (list 'asp/atMost 2 '?s (list pick '?s))]))

(defn- require-covered
  "Every element required covered, as a hard constraint over the derived atom."
  [{:keys [element covered uncovered]}]
  (list 'set/hardConstraint
        (list 'implies (list 'and (list element '?x) (list 'not (list covered '?x)))
              (list uncovered '?x))))

(defn- install-cover!
  "The set-cover problem over `elements`: the sets and the choice, `covered` derived from
  the picks, and every element required covered."
  [kb ctx terms elements]
  (doseq [s (concat (cover-statements terms elements) [(cover-rule terms) (require-covered terms)])]
    (v/assert kb s ctx)))

(deftest set-cover-needs-a-choice-a-solve-rule-and-a-constraint-over-it
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick member element covered uncovered CxCover]
        (let [terms {:cand cand :pick pick :member member :element element
                     :covered covered :uncovered uncovered}]
          (v/assert kb (list 'genlCx CxCover 'CxUniverse) 'CxUniverse)
          (install-cover! kb CxCover terms '[Ea Eb Ec])
          (let [r      (v/assert kb (list 'do/label CxCover (tu/tmp-ctx "Cover")) CxCover)
                picked (fn [l] (set (keep #(when (= pick (first %)) (second %)) (:true l))))]
            (testing "every optimum is a pair of sets covering all three elements"
              (is (= #{#{'S1 'S2} #{'S1 'S3} #{'S1 'S4} #{'S2 'S4}}
                     (set (map picked (:labelings r))))))
            (testing "the covered atoms are derived, not chosen, and each world records them"
              (is (= (set (map #(list covered %) '[Ea Eb Ec])) (set (:derived r))))
              (is (every? #(every? (truths %) (map (fn [x] (list covered x)) '[Ea Eb Ec]))
                          (:labelings r))))
            (testing "nothing was derived in base: the rule runs in a solve alone"
              (is (empty? (v/sentexes-matching kb (list covered '?x) CxCover))))))))))

(deftest an-element-no-set-covers-leaves-no-world
  ;; `(not (covered Ed))` names an atom no rule can derive, so it holds in every model and
  ;; the hard constraint excludes them all — a requirement nothing can meet is not vacuous
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick member element covered uncovered CxCover]
        (v/assert kb (list 'genlCx CxCover 'CxUniverse) 'CxUniverse)
        (install-cover! kb CxCover {:cand cand :pick pick :member member :element element
                                    :covered covered :uncovered uncovered}
                        '[Ea Eb Ec Ed])
        (let [r (v/assert kb (list 'do/label CxCover (tu/tmp-ctx "Cover") :one) CxCover)]
          (is (= :unsatisfiable (:reason r)))
          (is (zero? (:count r))))))))

;; ---- 3. reachability: a recursive solve rule over chosen edges ------------

(deftest reachability-over-chosen-edges-is-founded-in-the-root
  ;; Candidate edges A→B, B→C, C→B, at most one into each node, every node reached from
  ;; the root.  Keeping as many edges as it may leaves two candidates: {A→B, B→C}, and
  ;; {C→B, B→C}, where B and C are each other's only support — a loop the root never
  ;; enters, which an answer set gives no atom.  So {A→B, B→C} is the one answer.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cedge edge node root reach unreached A B C CxReach]
        (v/assert kb (list 'genlCx CxReach 'CxUniverse) 'CxUniverse)
        (doseq [n [A B C]] (v/assert kb (list node n) CxReach))
        (v/assert kb (list root A) CxReach)
        (doseq [[x y] [[A B] [B C] [C B]]] (v/assert kb (list cedge x y) CxReach))
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list cedge '?x '?y) (list edge '?x '?y)))
                  CxReach)
        (v/assert kb (list 'asp/atMost 1 '?x (list edge '?x '?y)) CxReach)
        (v/assert kb (list 'set/inertRule
                           (list 'set/solveRule (list 'implies (list root '?x) (list reach '?x))))
                  CxReach)
        (v/assert kb (list 'set/inertRule
                           (list 'set/solveRule
                                 (list 'implies (list 'and (list reach '?x) (list edge '?x '?y))
                                       (list reach '?y))))
                  CxReach)
        (testing "without the reach requirement, both edge sets are optimal"
          (is (= 2 (:count (v/assert kb (list 'do/label CxReach (tu/tmp-ctx "Free")) CxReach)))))
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'and (list node '?n) (list 'not (list reach '?n)))
                                 (list unreached '?n)))
                  CxReach)
        (let [r      (v/assert kb (list 'do/label CxReach (tu/tmp-ctx "Reach")) CxReach)
              edges  (fn [l] (set (filter #(= edge (first %)) (:true l))))]
          (is (= 1 (:count r)))
          (is (= #{(list edge A B) (list edge B C)} (edges (first (:labelings r)))))
          (is (every? (truths (first (:labelings r))) [(list reach A) (list reach B) (list reach C)])))))))

;; ---- 4. a rule true in base, and in each answer set ----------------------

(deftest a-bare-solve-rule-answers-in-base-and-derives-in-each-world
  ;; `atCapital` holds of whoever is assigned a capital.  Ann's assignment is a base fact,
  ;; so base answers `(atCapital Ann)` backward; Bob's is a choice, so each world derives
  ;; `(atCapital Bob)` or not by what it picked.  The base instance is true in both.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [assign capital city cand atCapital Ann Bob Paris Lyon CxTrip]
        (v/assert kb (list 'genlCx CxTrip 'CxUniverse) 'CxUniverse)
        (v/assert kb (list capital Paris) CxTrip)
        (doseq [c [Paris Lyon]] (v/assert kb (list city c) CxTrip))
        (v/assert kb (list assign Ann Paris) CxTrip)
        (v/assert kb (list cand Bob) CxTrip)
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list 'and (list cand '?p) (list city '?c))
                                 (list assign '?p '?c)))
                  CxTrip)
        (v/assert kb (list 'functional assign) CxTrip)
        (v/assert kb (list 'set/solveRule
                           (list 'implies (list 'and (list assign '?p '?c) (list capital '?c))
                                 (list atCapital '?p)))
                  CxTrip)
        (testing "base answers the rule backward over what it believes"
          (is (v/provable? kb (list atCapital Ann) CxTrip))
          (is (not (v/provable? kb (list atCapital Bob) CxTrip))))
        (let [trips  (tu/tmp-ctx "Trip")
              r      (v/assert kb (list 'do/label CxTrip trips) CxTrip)
              worlds (into {} (map (fn [l] [(some #(when (= [assign Bob] (take 2 %)) (nth % 2)) (:true l))
                                            (truths l)]))
                           (:labelings r))]
          (is (= #{Paris Lyon} (set (keys worlds))) "two worlds, one per city")
          (testing "a world that sends Bob to the capital derives it, and the other does not"
            (is (contains? (worlds Paris) (list atCapital Bob)))
            (is (not (contains? (worlds Lyon) (list atCapital Bob)))))
          (testing "Ann's base instance is true in both"
            (is (every? #(contains? % (list atCapital Ann)) (vals worlds))))
          (testing "do/classify reads a derived atom as it reads a choice"
            (let [c (v/assert kb (list 'do/classify trips) CxTrip)]
              (is (some #{(list atCapital Ann)} (:forced c)))
              (is (some #{(list atCapital Bob)} (:supportable c))))))))))

(deftest default-negation-reads-the-answer-set
  ;; `idle` holds of a worker no task in the answer set is assigned to: default negation
  ;; over a derived atom, which a soft constraint then penalizes.  Two tasks, two workers,
  ;; each task to one worker: the optimum spreads them, leaving no one idle.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [task worker does busy idle idleWorker T1 T2 W1 W2 CxWork]
        (v/assert kb (list 'genlCx CxWork 'CxUniverse) 'CxUniverse)
        (doseq [t [T1 T2]] (v/assert kb (list task t) CxWork))
        (doseq [w [W1 W2]] (v/assert kb (list worker w) CxWork))
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list 'and (list task '?t) (list worker '?w))
                                 (list does '?w '?t)))
                  CxWork)
        (v/assert kb (list 'asp/atMost 1 '?w (list does '?w '?t)) CxWork)
        (v/assert kb (list 'asp/atLeast 1 '?w (list does '?w '?t)) CxWork)
        (v/assert kb (list 'set/inertRule
                           (list 'set/solveRule (list 'implies (list does '?w '?t) (list busy '?w))))
                  CxWork)
        (v/assert kb (list 'set/inertRule
                           (list 'set/solveRule
                                 (list 'implies (list 'and (list worker '?w) (list 'not (list busy '?w)))
                                       (list idle '?w))))
                  CxWork)
        (v/assert kb (list 'set/softConstraint (list 'implies (list idle '?w) (list idleWorker '?w)))
                  CxWork)
        (let [r (v/assert kb (list 'do/label CxWork (tu/tmp-ctx "Work")) CxWork)]
          (is (pos? (:count r)))
          (doseq [l (:labelings r)]
            (let [t (truths l)]
              (is (= #{W1 W2} (set (keep #(when (= does (first %)) (second %)) t)))
                  "each worker takes a task")
              (is (not-any? #(= idle (first %)) t) "and so no one is idle"))))))))

(deftest a-required-choice-nothing-offers-leaves-no-world
  ;; The choice-literal twin of the uncovered element: task T2 has no candidate worker, so
  ;; `(does W1 T2)` is no atom, `(not (does ?w T2))` bound by the background holds in every
  ;; model, and the hard requirement admits none
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [task cand does unassigned T1 T2 W1 CxJobs]
        (v/assert kb (list 'genlCx CxJobs 'CxUniverse) 'CxUniverse)
        (doseq [t [T1 T2]] (v/assert kb (list task t) CxJobs))
        (v/assert kb (list cand W1 T1) CxJobs)
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list cand '?w '?t) (list does '?w '?t)))
                  CxJobs)
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'and (list task '?t) (list 'not (list does W1 '?t)))
                                 (list unassigned '?t)))
                  CxJobs)
        (is (= :unsatisfiable
               (:reason (v/assert kb (list 'do/label CxJobs (tu/tmp-ctx "Jobs") :one) CxJobs))))))))

;; ---- 5. what else reads a derived atom ------------------------------------

(deftest a-cardinality-bound-counts-derived-atoms
  ;; `asp/atLeast 3` over `covered` in place of the hard constraint: a bound is ground over
  ;; the derived atoms as it is over the choices, so the optima are the same four pairs
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick member element covered CxCover]
        (let [terms {:cand cand :pick pick :member member :element element :covered covered}]
          (v/assert kb (list 'genlCx CxCover 'CxUniverse) 'CxUniverse)
          (doseq [s (concat (cover-statements terms '[Ea Eb Ec])
                            [(cover-rule terms) (list 'asp/atLeast 3 '?x (list covered '?x))])]
            (v/assert kb s CxCover))
          (let [r (v/assert kb (list 'do/label CxCover (tu/tmp-ctx "Cover")) CxCover)]
            (is (= #{#{'S1 'S2} #{'S1 'S3} #{'S1 'S4} #{'S2 'S4}}
                   (set (map #(picked-sets pick %) (:labelings r)))))))))))

(deftest an-exception-on-a-solve-rule-blocks-its-binding
  ;; S1 is blocked, so picking it covers nothing, and the one pair covering a, b and c
  ;; without it is S2 with S4.  The exception is evaluated in `Base`, per binding.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick member element covered uncovered blocked CxCover]
        (let [terms {:cand cand :pick pick :member member :element element
                     :covered covered :uncovered uncovered}]
          (v/assert kb (list 'genlCx CxCover 'CxUniverse) 'CxUniverse)
          (doseq [s (concat (cover-statements terms '[Ea Eb Ec])
                            [(list 'exceptWhen (list blocked '?s) (cover-rule terms))
                             (require-covered terms)
                             (list blocked 'S1)])]
            (v/assert kb s CxCover))
          (let [r (v/assert kb (list 'do/label CxCover (tu/tmp-ctx "Cover")) CxCover)]
            (is (= #{#{'S2 'S4}} (set (map #(picked-sets pick %) (:labelings r)))))))))))

;; ---- 6. which solve rules run ---------------------------------------------

(deftest only-a-believed-solve-rule-the-base-sees-runs
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick member element covered uncovered CxCover CxElsewhere]
        (let [terms  {:cand cand :pick pick :member member :element element
                      :covered covered :uncovered uncovered}
              label! #(v/assert kb (list 'do/label CxCover (tu/tmp-ctx "Cover") :one) CxCover)]
          (doseq [c [CxCover CxElsewhere]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
          (doseq [s (concat (cover-statements terms '[Ea Eb Ec]) [(require-covered terms)])]
            (v/assert kb s CxCover))
          (testing "a solve rule in a context the base does not see derives nothing"
            ;; and with no solve rule concluding it, `covered` is no program predicate:
            ;; the requirement's `(not (covered ?x))` is a background literal, which
            ;; nothing believed satisfies, so it forbids nothing
            (v/assert kb (cover-rule terms) CxElsewhere)
            (let [r (label!)]
              (is (empty? (:derived r)))
              (is (= 1 (:count r)))))
          (let [h (v/assert kb (cover-rule terms) CxCover)]
            (testing "one the base sees derives what the picks cover"
              (let [r (label!)]
                (is (= (set (map #(list covered %) '[Ea Eb Ec])) (set (:derived r))))
                (is (= 1 (:count r)))))
            (testing "and once retracted, derives nothing"
              (v/retract! kb h)
              (is (empty? (:derived (label!)))))))))))

(deftest the-same-program-in-either-order-labels-the-same
  ;; derived atoms take their ids in content order after the choices', so the order the
  ;; program was asserted in reaches neither the worlds nor the one `:one` commits to
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick member element covered uncovered CxOne CxTwo]
        (let [terms (fn [] {:cand cand :pick pick :member member :element element
                            :covered covered :uncovered uncovered})
              stmts (concat (cover-statements (terms) '[Ea Eb Ec])
                            [(cover-rule (terms)) (require-covered (terms))])
              run   (fn [ctx mode] (v/assert kb (list 'do/label ctx (tu/tmp-ctx "Order") mode) ctx))]
          (doseq [c [CxOne CxTwo]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
          (doseq [s stmts] (v/assert kb s CxOne))
          (doseq [s (reverse stmts)] (v/assert kb s CxTwo))
          (let [[a b] (map #(run % :all) [CxOne CxTwo])]
            (is (= 4 (:count a)))
            (is (= (set (map truths (:labelings a))) (set (map truths (:labelings b)))))
            (is (= (:derived a) (:derived b))))
          (is (= (truths (first (:labelings (run CxOne :one))))
                 (truths (first (:labelings (run CxTwo :one)))))))))))

;; ---- 7. what grounding refuses ---------------------------------------------

(deftest a-solve-rule-the-solve-cannot-ground-is-refused
  ;; each refusal comes from grounding, before a solver is asked, so none needs a backend
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [cand pick member element covered odd]
      (let [terms {:cand cand :pick pick :member member :element element :covered covered}
            label (fn [extra]
                    (let [ctx (tu/tmp-ctx "Bad")]
                      (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
                      (doseq [s (concat (cover-statements terms '[Ea Eb Ec]) [(cover-rule terms)] extra)]
                        (v/assert kb s ctx))
                      #(v/assert kb (list 'do/label ctx (tu/tmp-ctx "Bad") :one) ctx)))]
        (testing "a negated head, which a labeling could not record"
          (is (= :not-well-formed
                 (refusal-type (label [(list 'set/inertRule
                                             (list 'set/solveRule
                                                   (list 'implies (list pick '?s)
                                                         (list 'not (list odd '?s)))))])))))
        (testing "a negated literal the positive ones leave open"
          (is (= :not-well-formed
                 (refusal-type (label [(list 'set/inertRule
                                             (list 'set/solveRule
                                                   (list 'implies (list 'and (list pick '?s)
                                                                        (list 'not (list covered '?x)))
                                                         (list odd '?s))))])))))
        (testing "more derived atoms than the cap"
          ;; four choice heads, then three covered atoms: past a cap of five
          (with-redefs [sc/max-derived-atoms 5]
            (is (= :not-well-formed (refusal-type (label []))))))))))
