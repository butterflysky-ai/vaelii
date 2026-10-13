;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-solve-test
  "Constraint rules (`set/hardConstraint` / `set/softConstraint`) and the single-labeling
  `do/label … :one` mode — the grounding-rule → integrity-constraint path that lets a
  solve express a nogood over two *different* individuals (graph adjacency), which the
  direct-clash detectors (always one shared individual) cannot.

  The worked example is graph 3-coloring: a choice of colour per node
  (`assumptionRule`), at-most-one-colour (`functional`), and no-monochrome-edge (a hard
  constraint whose body joins the edge facts against the colour choices).  A single
  `:label` solve keeps a colour for every node (the keep-belief objective) capped at one
  (functional) with no adjacent clash (the hard constraint) — a valid proper colouring.

  Enumeration/solving needs an ASP backend, so the end-to-end tests are guarded on
  `asp?`; the wrapper/record unit tests are not."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

;; ---- 1. the constraint wrapper marks the record, and never chains --------

(deftest a-constraint-rule-is-marked-and-inference-inert
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [colored benchEdge]
      (let [body (list 'implies
                       (list 'and (list benchEdge '?x '?y)
                             (list colored '?x '?k) (list colored '?y '?k))
                       (list 'monochrome '?x '?y))
            hard (v/assert kb (list 'set/hardConstraint body) 'CxUniverse)
            soft (v/assert kb (list 'set/softConstraint body) 'CxUniverse)
            bare (v/assert kb body 'CxUniverse)]
        (testing "the wrapper is part of identity: hard, soft, and bare are three sentexes"
          (is (not= hard soft))
          (is (not= hard bare))
          (is (not= soft bare)))
        (testing "constraint-of reads the class off the record"
          (is (= :hard (rules/constraint-of (sentex-of kb hard))))
          (is (= :soft (rules/constraint-of (sentex-of kb soft))))
          (is (nil? (rules/constraint-of (sentex-of kb bare)))))
        (testing "a constraint rule forward- and backward-chains for nobody"
          (is (not (rules/forward-sentex? (sentex-of kb hard))))
          (is (not (rules/backward-sentex? (sentex-of kb hard))))
          (is (rules/backward-sentex? (sentex-of kb bare))
              "while a bare rule chains — backward, the default"))
        (testing "and re-asserting the same hard constraint is idempotent"
          (is (= hard (v/assert kb (list 'set/hardConstraint body) 'CxUniverse))))))))

(deftest a-constraint-rule-derives-no-marker
  ;; The defining behaviour: the head is a contradiction *marker*, not a truth — the
  ;; rule never fires, so no `(monochrome …)` is ever derived, even with facts present.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [colored benchEdge A B]
      (v/assert kb (list 'set/hardConstraint
                         (list 'implies
                               (list 'and (list benchEdge '?x '?y)
                                     (list colored '?x '?k) (list colored '?y '?k))
                               (list 'monochrome '?x '?y)))
                'CxUniverse)
      ;; even given a monochrome edge as plain facts, nothing derives the marker
      (v/assert kb (list benchEdge A B) 'CxUniverse)
      (v/assert kb (list colored A 'red) 'CxUniverse)
      (v/assert kb (list colored B 'red) 'CxUniverse)
      (is (empty? (v/sentexes-matching kb (list 'monochrome A B) 'CxUniverse))))))

;; ---- 2. hard 3-coloring end to end via do/label … :one -------------------

(defn- install-3coloring!
  "The choice + functional + hard-adjacency program over `nodes` and `edges` in `ctx`."
  [kb ctx colored nodes edges]
  (doseq [k '[k1 k2 k3]]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list 'bench_node '?x) (list colored '?x k)))
              ctx))
  (v/assert kb (list 'functional colored) ctx {:strength :monotonic})
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'benchEdge '?x '?y)
                                 (list colored '?x '?k) (list colored '?y '?k))
                           (list 'monochrome '?x '?y)))
            ctx)
  (doseq [n nodes] (v/assert kb (list 'bench_node n) ctx {:strength :monotonic}))
  (doseq [[a b] edges] (v/assert kb (list 'benchEdge a b) ctx {:strength :monotonic})))

(defn- coloring-of
  "node -> colour, read from a `:one` labeling's chosen-true `(colored node k)` heads."
  [labeling]
  (into {} (map (fn [s] [(nth s 1) (nth s 2)])) (:true labeling)))

(deftest hard-constraint-3-colors-a-triangle
  ;; A triangle is 3-colorable and needs all three colours: the tightest small witness
  ;; that the adjacency constraint over *different* nodes is honored.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxTri colored
                            '[N1 N2 N3] '[[N1 N2] [N2 N3] [N1 N3]])
        (let [r        (v/assert kb (list 'do/label 'CxTri 'CxTriPlan :one) 'CxTri)
              labeling (first (:labelings r))
              coloring (coloring-of labeling)]
          (testing "one labeling, computed and returned but not persisted"
            (is (= 1 (:count r)))
            (is (nil? (:context labeling)))
            (is (not (contains? (set (v/contexts kb)) 'CxTriPlan1))))
          (testing "every node gets exactly one colour"
            (is (= #{'N1 'N2 'N3} (set (keys coloring))))
            (is (= 3 (count (:true labeling))) "one chosen colour per node")
            (is (= 6 (count (:false labeling)))
                "the other two colours per node are chosen-false (3 nodes × 2)"))
          (testing "no edge is monochrome — a proper colouring"
            (doseq [[a b] '[[N1 N2] [N2 N3] [N1 N3]]]
              (is (not= (coloring a) (coloring b)) (str a "-" b))))
          (testing "a triangle exhausts all three colours"
            (is (= 3 (count (set (vals coloring))))))
          (testing "base belief is untouched — no colour is believed, nothing contradicts"
            (is (empty? (v/sentexes-matching kb (list colored 'N1 'k1) 'CxTri)))
            (is (zero? (count (v/contradictions kb))))))))))

(deftest hard-constraint-3-colors-a-path
  ;; A 4-node path, 3-colorable with a colour to spare — checks the join grounds the
  ;; right per-edge nogoods when nodes share endpoints.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxPath colored
                            '[P1 P2 P3 P4] '[[P1 P2] [P2 P3] [P3 P4]])
        (let [r        (v/assert kb (list 'do/label 'CxPath 'CxPathPlan :one) 'CxPath)
              coloring (coloring-of (first (:labelings r)))]
          (is (= 1 (:count r)))
          (is (= #{'P1 'P2 'P3 'P4} (set (keys coloring))) "all four nodes coloured")
          (doseq [[a b] '[[P1 P2] [P2 P3] [P3 P4]]]
            (is (not= (coloring a) (coloring b)) (str a "-" b))))))))

(deftest a-clique-of-four-is-not-3-colorable
  ;; K4: four mutually-adjacent nodes cannot be 3-colored.  The hard constraints make
  ;; the program UNSAT, so no valid total colouring exists — the solve leaves at least
  ;; one node uncoloured rather than manufacturing a monochrome edge.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxK4 colored
                            '[Q1 Q2 Q3 Q4]
                            '[[Q1 Q2] [Q1 Q3] [Q1 Q4] [Q2 Q3] [Q2 Q4] [Q3 Q4]])
        (let [r        (v/assert kb (list 'do/label 'CxK4 'CxK4Plan :one) 'CxK4)
              coloring (coloring-of (first (:labelings r)))]
          (testing "no proper total 3-colouring: some node is left uncoloured"
            (is (< (count coloring) 4)))
          (testing "and whatever it did colour has no monochrome edge among the coloured"
            (doseq [[a b] '[[Q1 Q2] [Q1 Q3] [Q1 Q4] [Q2 Q3] [Q2 Q4] [Q3 Q4]]]
              (when (and (coloring a) (coloring b))
                (is (not= (coloring a) (coloring b)) (str a "-" b))))))))))

(deftest three-colors-the-australia-map
  ;; The textbook CSP: the six states of mainland Australia + Tasmania.  Its triangles
  ;; (Wa-Nt-Sa, Sa-Nsw-V, …) force all three colours, and Tasmania has no land border —
  ;; the keep-belief `:one` objective colours it anyway, since a coloured node keeps a
  ;; choice while an uncoloured one defeats all three.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (let [regions '[Wa Nt Sa Q Nsw V T]
              borders '[[Wa Nt] [Wa Sa] [Nt Sa] [Nt Q] [Sa Q]
                        [Sa Nsw] [Sa V] [Q Nsw] [Nsw V]]]
          (install-3coloring! kb 'CxAustralia colored regions borders)
          (let [r        (v/assert kb (list 'do/label 'CxAustralia 'CxAustraliaPlan :one) 'CxAustralia)
                coloring (coloring-of (first (:labelings r)))]
            (testing "all seven regions coloured, Tasmania included"
              (is (= (set regions) (set (keys coloring))))
              (is (contains? coloring 'T) "an isolated region is still coloured"))
            (testing "no shared border is monochrome — a proper colouring"
              (doseq [[a b] borders]
                (is (not= (coloring a) (coloring b)) (str a "-" b))))
            (testing "the map needs all three colours"
              (is (= 3 (count (set (vals coloring))))))))))))

;; ---- 2b. all-hard 3-coloring (at-least-one via negated choice literals) ---

(defn- install-allhard-3coloring!
  "The bench's all-hard recipe: colour choice per node, hard at-most-one, hard
  at-least-one (a negated-choice constraint), hard no-monochrome-edge."
  [kb ctx colored nodes edges]
  (doseq [k '[k1 k2 k3]]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list 'bench_node '?x) (list colored '?x k)))
              ctx))
  (doseq [[ka kc] '[[k1 k2] [k1 k3] [k2 k3]]]
    (v/assert kb (list 'set/hardConstraint
                       (list 'implies (list 'and (list colored '?x ka) (list colored '?x kc))
                             (list 'double_colored '?x)))
              ctx))
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'bench_node '?x)
                                 (list 'not (list colored '?x 'k1))
                                 (list 'not (list colored '?x 'k2))
                                 (list 'not (list colored '?x 'k3)))
                           (list 'uncolored '?x)))
            ctx)
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'benchEdge '?x '?y)
                                 (list colored '?x '?k) (list colored '?y '?k))
                           (list 'monochrome '?x '?y)))
            ctx)
  (doseq [n nodes] (v/assert kb (list 'bench_node n) ctx {:strength :monotonic}))
  (doseq [[a b] edges] (v/assert kb (list 'benchEdge a b) ctx {:strength :monotonic})))

(deftest all-hard-colors-every-node-including-isolated
  ;; The exact bench encoding at unit scale, solved in **:sat** mode: the hard
  ;; at-least-one (a negated-choice `:- not colored(x,k1..k3)` constraint) forces a colour
  ;; on EVERY node — even one with no edges — so the solve is plain satisfaction with no
  ;; keep-belief objective, and still every node is coloured exactly once.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        ;; a triangle plus a totally isolated node Iso (no edges)
        (install-allhard-3coloring! kb 'CxAllHard colored
                                    '[N1 N2 N3 Iso] '[[N1 N2] [N2 N3] [N1 N3]])
        (let [r        (v/assert kb (list 'do/label 'CxAllHard 'CxAllHardPlan :sat) 'CxAllHard)
              coloring (coloring-of (first (:labelings r)))]
          (testing ":sat returns one labeling, persists nothing"
            (is (= 1 (:count r)))
            (is (nil? (:context (first (:labelings r))))))
          (testing "every node coloured exactly once, isolated node included"
            (is (= #{'N1 'N2 'N3 'Iso} (set (keys coloring)))))
          (testing "the triangle is properly coloured"
            (doseq [[a b] '[[N1 N2] [N2 N3] [N1 N3]]]
              (is (not= (coloring a) (coloring b)) (str a "-" b)))
            (is (= 3 (count (set (map coloring '[N1 N2 N3])))))))))))

(deftest a-negated-choice-literal-binds-its-own-variables
  ;; The at-least-one idiom with nothing else in the body: `?k` is bound by the negated
  ;; choice literal and by nothing else.  Negated literals come out of the body before
  ;; the positive join, so nothing else can bind them — a bare substitution would find
  ;; no head for an unbound `?k`, drop the binding, and leave the constraint
  ;; contributing no nogood at all, which is a solve returning worlds it forbids.  The
  ;; join is what grounds `?k` over every colour and forbids each one's absence.
  ;;
  ;; `functional` makes the two colours a *soft* clash, so both-true is a legal model
  ;; that merely costs — which is what makes the hard constraint's effect visible:
  ;; without it there are two optima (one colour each), with it exactly one (both).
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored cand Item]
        (doseq [k '[k1 k2]]
          (v/assert kb (list 'set/assumptionRule
                             (list 'implies (list cand '?c) (list colored '?c k)))
                    'CxNegJoin))
        (v/assert kb (list 'functional colored) 'CxNegJoin)
        (v/assert kb (list cand Item) 'CxNegJoin {:strength :monotonic})
        (testing "without the at-least-one: two optima, one colour apiece"
          (is (= 2 (:count (v/assert kb (list 'do/label 'CxNegJoin 'CxNegJoinPlan :all)
                                     'CxNegJoin)))))
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'not (list colored '?x '?k))
                                 (list 'mustColor '?x '?k)))
                  'CxNegJoin)
        (testing "with it: no colour may be absent, so the one legal world keeps both"
          (let [r (v/assert kb (list 'do/label 'CxNegJoin 'CxNegJoinPlan :all) 'CxNegJoin)]
            (is (= 1 (:count r)))
            (is (empty? (:false (first (:labelings r)))))
            (is (= 2 (count (:true (first (:labelings r))))))))
        (testing "and :sat, with no keep-belief objective pushing the atoms true, agrees"
          (let [l (first (:labelings (v/assert kb (list 'do/label 'CxNegJoin 'CxNegJoinPlan :sat)
                                               'CxNegJoin)))]
            (is (empty? (:false l)) "the first model found still satisfies the constraint")))))))

(deftest an-unsatisfiable-program-reports-no-labeling-rather-than-an-empty-one
  ;; K4 under the all-hard encoding admits no model: at-least-one plus at-most-one
  ;; plus no-monochrome-edge over four mutually adjacent nodes needs a fourth colour.
  ;;
  ;; `:one` / `:sat` read a single answer set, and an infeasible program keeps nothing
  ;; — which has the same shape as the one perfectly ordinary world in which every
  ;; choice happened to be false.  For *this* program that world violates both hard
  ;; constraints it was built from, so reporting it as the labeling is reporting a
  ;; world the solve just proved impossible.  `:all` gets this right by enumerating
  ;; nothing, and the three modes have to agree.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-allhard-3coloring! kb 'CxUnsat colored
                                    '[Q1 Q2 Q3 Q4]
                                    '[[Q1 Q2] [Q1 Q3] [Q1 Q4] [Q2 Q3] [Q2 Q4] [Q3 Q4]])
        (doseq [mode [:one :sat]]
          (let [r (v/assert kb (list 'do/label 'CxUnsat 'CxUnsatPlan mode) 'CxUnsat)]
            (testing (str mode " reports no world, and says why")
              (is (zero? (:count r)))
              (is (= :unsatisfiable (:reason r)))
              (is (empty? (:labelings r))))))
        (testing ":all agrees, having enumerated nothing"
          (is (zero? (:count (v/assert kb (list 'do/label 'CxUnsat 'CxUnsatPlan :all) 'CxUnsat)))))
        (testing "and the menu of choices is still reported — grounding did happen"
          (is (= 12 (count (:choices (v/assert kb (list 'do/label 'CxUnsat 'CxUnsatPlan :one)
                                               'CxUnsat))))
              "4 nodes × 3 colours"))))))

;; ---- 3. phase timings ride the :one result -------------------------------

(deftest one-mode-carries-phase-timings
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [colored]
        (install-3coloring! kb 'CxUniverse colored '[T1 T2] '[[T1 T2]])
        (let [r (v/assert kb (list 'do/label 'CxUniverse 'CxTimePlan :one) 'CxUniverse)]
          (is (every? number? [(:ground-ms r) (:translate-ms r) (:solve-ms r)])
              "grounding / translate / solve are timed separately for a profiling caller"))))))
