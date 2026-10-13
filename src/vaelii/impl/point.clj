;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.point
  "The point algebra over time **instants** — a relation algebra over the generic
  constraint network in `vaelii.impl.qcn`, and the smallest one there is.  Three base
  relations, jointly exhaustive and pairwise disjoint, so exactly one holds of any two
  instants:

    :before   t(a) < t(b)
    :equal    t(a) = t(b)
    :after    t(a) > t(b)

  `vaelii.impl.interval` is about stretches of time, which have extent and can therefore
  meet, overlap and nest; this is about the moments themselves, where the only question is
  which came first.  The two meet at `vaelii.impl.stp`, which relates an interval to its
  two endpoint instants and puts numbers on the gaps between them.

  **The same algebra appears twice in this tree.**  `vaelii.impl.projection` builds a
  nine-relation algebra out of two independent one-dimensional projections — the cardinal
  directions of `vaelii.impl.orientation` and the relative frame of `vaelii.impl.relative`
  are both that shape — and each projection is exactly these three relations under the
  spellings `:lt` / `:eq` / `:gt`.  The table is duplicated rather than shared: there the
  three relations are a position on an axis and an implementation detail of the algebras
  built over them, here they are an order in time with their own vocabulary, and neither
  namespace should have to read the other's keywords to say what it means.  Nine identical
  entries are cheaper than that coupling, and either copy is checkable against the
  definitions on its own.

  Instants are **stored as ordinary sentexes** — the three named binary predicates
  (`instantBefore`, `instantAfter`, `instantEqual`) plus three derived ones
  (`instantNotBefore`, `instantNotAfter`, `instantNotEqual`) that each name a *disjunction*
  of them.  An instant named by a symbol is an ordinary individual.

  The calculus reads every asserted instant relation visible from a context into a
  qualitative constraint network — `{[i j] → #{possible base relations}}`, an unrecorded
  pair meaning \"unknown\", i.e. all three — and `qcn/path-consistent` tightens it to a
  fixpoint.  The prover then answers a goal `(P i j)` by **entailment**: it holds iff every
  relation still possible between i and j satisfies P, `possible ⊆ denotation(P)`.  So
  `(instantBefore A B)` and `(instantBefore B C)` entail `(instantBefore A C)`, and the
  weaker `(instantNotAfter A C)` with it.

  For three relations path consistency is not merely sound but **complete**: the point
  algebra's full disjunctive form is tractable, and a network of it that survives the pass
  has a model.  So an emptied constraint here means genuine unsatisfiability, which is what
  makes a cycle of strict `instantBefore` facts a reportable contradiction rather than a
  suspicion.

  **A node is an instant or a point of a thing.**  Besides instants named by a symbol,
  the network takes the six point terms of `vaelii.impl.timepoint` — `(StartFn X)`,
  `(EarliestEndFn X)` … — and calendar moments, and reads the order those terms fix
  among themselves as a second reader: one thing's start before its end, its bounds
  around them, calendar moments by their fields.  So a story's own order, a period's
  uncertain boundaries and a dated claim are one network, and a cycle through any of them
  is the same reported inconsistency as a cycle of stated facts.  `IncludesInstantProver`
  reads a thing against a moment off it: yes, no, or unknown where the moment falls
  inside a range a bound leaves open.

  The vocabulary ships in `kb/upper/time.txt` beside the interval relations.  The
  prover is **opt-in** on top of it: register it with `vaelii.core/add-prover`, and until
  then a KB stores and retrieves instant relations as ordinary facts without paying for the
  network."
  (:require [clojure.set :as set]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.timepoint :as tp]
            [vaelii.impl.types.prover :as prover-types]))

;; ---- the algebra --------------------------------------------------------

(def all-relations
  "The three jointly-exhaustive, pairwise-disjoint instant relations — the universe of the
  algebra, and so the constraint on a pair nothing is known about."
  #{:before :equal :after})

(def point-converse
  "Each base relation's converse — reading the claim backwards.  One pair and one
  self-converse, since `:equal` is the identity."
  {:before :after, :equal :equal, :after :before})

(defn converse-set
  "The converse of a relation set — how an asserted `(P a b)` constraint is read backwards
  as the constraint on `(b a)`."
  [rels]
  (into #{} (map point-converse) rels))

(def point-composition
  "`(get-in point-composition [r1 r2])` is the set of base relations possible between a and
  c given `r1`(a,b) and `r2`(b,c).  `:equal` is the identity element on both sides.

  Only two entries lose information, and they are the same shape twice: a before b with b
  after c puts both a and c on the far side of b, in either order, so nothing at all
  follows.  Everything else is a singleton — which is why a chain of strict orderings
  composes to a strict ordering however long it is."
  {:before {:before #{:before} :equal #{:before} :after all-relations}
   :equal  {:before #{:before} :equal #{:equal}  :after #{:after}}
   :after  {:before all-relations :equal #{:after} :after #{:after}}})

(defn compose
  "The composition of two relation SETS: every base relation possible between a and c when
  r(a,b) ∈ `s1` and r(b,c) ∈ `s2` — the union of the table entries, since a disjunction on
  either side admits every combination."
  [s1 s2]
  (into #{}
        (mapcat (fn [a] (mapcat (fn [b] (get-in point-composition [a b])) s2)))
        s1))

(def point-algebra
  "The point algebra as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:equal}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under.  Every
  name carries the `instant` prefix: `before` and `after` are already Allen's *interval*
  relations, and a moment ordered against a moment is a different claim from a stretch
  ordered against a stretch.  `:equal` is `instantEqual` for the reason `intervalEqual` is
  not `equals` — two instants coinciding is a claim about time, not about the identity of
  two terms."
  '{:before instantBefore
    :equal  instantEqual
    :after  instantAfter})

(def instant-denotation
  "Every instant predicate — the three base ones and the three derived ones — mapped to the
  set of base relations it denotes.  A goal `(P a b)` is entailed exactly when the relations
  still possible between a and b are a *subset* of P's denotation, so a derived predicate is
  entailed by more networks than a base one, and the base predicates are the singletons.

  The three derived predicates are each the complement of one base relation, and over a
  jointly-exhaustive triple a complement *is* a negation — so the names are literal.
  `instantNotAfter` is ≤ and `instantNotBefore` is ≥, which is what a temporal ordering
  usually wants; `instantNotEqual` is ≠.  With them the vocabulary names every disjunction
  the algebra can express bar the universe, which is the absence of a claim and needs no
  name."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{instantNotAfter  #{:before :equal}
     instantNotBefore #{:after :equal}
     instantNotEqual  #{:before :after}}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def instants
  "The point algebra as a `vaelii.impl.qcn-kb` calculus — the algebra, the vocabulary, and
  the two caches.  Everything below delegates to the shared glue, which is the same code
  RCC-8, the cardinal directions and Allen's intervals run."
  (qkb/calculus :point point-algebra instant-denotation
                {:over-nodes tp/constraints-over
                 :node?      tp/node-term?}))

(defn possible-point-relations
  "The base relations still possible between instants `i1` and `i2` given everything
  believed in `context` — `#{}` when the network is inconsistent.

  This is the algebra read directly rather than through a goal, so a caller that needs to
  know *how much* is pinned down — rather than whether one named relation is entailed —
  asks here."
  [kb context i1 i2]
  (qkb/possible instants kb context i1 i2))

(defn point-prover
  "The point-algebra entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover instants))

;; ---- a thing against a moment -------------------------------------------

(defn- endpoint-relations
  "`[st te]`: the relations still possible between `thing`'s start and `t`, and between `t`
  and `thing`'s end."
  [kb context thing t]
  [(possible-point-relations kb context (tp/point :start thing) t)
   (possible-point-relations kb context t (tp/point :end thing))])

(defn- inclusion-verdict
  "Does a thing include the moment `t`, given `endpoint-relations`' `[st te]` — at or after
  its start and before its end, the calendar terms' half-open convention?  `:true`,
  `:false` when `t` falls before the start or at or after the end, `:unknown` when the
  network leaves either side open, `:inconsistent` when the network contradicts itself."
  [[st te]]
  (cond
    (or (empty? st) (empty? te))                                  :inconsistent
    (and (set/subset? st #{:before :equal}) (= te #{:before}))    :true
    (or (= st #{:after}) (set/subset? te #{:after :equal}))       :false
    :else                                                         :unknown))

(defn- inclusion-literal
  "`[neg? thing t]` for a goal `(includesInstant thing t)` or its negation, each argument a
  variable or, for `t`, a node term; else nil."
  [goal]
  (let [neg? (and (sequential? goal) (= 2 (count goal)) (= sx/not-functor (first goal)))
        lit  (if neg? (second goal) goal)]
    (when (and (sequential? lit) (= 3 (count lit)) (= 'includesInstant (first lit)))
      (let [[_ x t] lit]
        (when (or (sx/variable? t) (tp/node-term? t)) [neg? x t])))))

(defn- inclusion-contexts [kb context]
  (if (sx/variable? context) (qkb/reader-contexts kb instants) [context]))

(defn- deciding-pairs
  "The endpoint pairs a verdict of `v` rests on: both for `:true`, and for `:false` the one
  or two that put `t` outside."
  [thing t [st te] v]
  (let [s [(tp/point :start thing) t]
        e [t (tp/point :end thing)]]
    (if (= v :true)
      [s e]
      (cond-> []
        (= st #{:after})                  (conj s)
        (set/subset? te #{:after :equal}) (conj e)))))

(defn- entailed-inclusions
  "The network's answers to `goal` as `[bindings support]`, one per reader context that
  answers.  An open thing ranges over the things with a point in that context's network,
  and an open moment over its nodes."
  [kb goal context support?]
  (let [[neg? x t] (inclusion-literal goal)
        want  (if neg? :false :true)
        open? sx/variable?]
    (for [c    (inclusion-contexts kb context)
          :let [ns (when (or (open? x) (open? t)) (qkb/nodes (qkb/network kb instants c)))]
          xv   (if (open? x) (into #{} (keep tp/thing-of) ns) [x])
          tv   (if (open? t) ns [t])
          :when (or (not= x t) (= xv tv))
          :let [rels (endpoint-relations kb c xv tv)]
          :when (= want (inclusion-verdict rels))]
      [(cond-> {} (open? x) (assoc x xv) (open? t) (assoc t tv))
       (when support?
         (into #{} (mapcat (fn [[a b]] (qkb/support instants kb c a b)))
               (deciding-pairs xv tv rels want)))])))

(defn- solve-inclusion
  "`goal`'s solutions as `[bindings support]` pairs, the one reader behind both prover
  methods.  `support?` false leaves the support nil and reads no support pass.

  The network answers first, its support unioning the reader contexts that answer and
  empty when the terms alone decide.  A stored `includesInstant` fact the network does not
  entail answers after it, supported by its own handles.  An answer both give carries the
  network's support alone, since the forward join matches the stored fact on its own."
  [kb goal context support?]
  (let [found    (entailed-inclusions kb goal context support?)
        sups     (reduce (fn [m [b s]] (update m b (fnil into #{}) s)) {} found)
        entailed (map (fn [b] [b (when support? (sups b))]) (distinct (map first found)))
        stored   (reduce (fn [m [h b]] (if (sups b) m (update m b (fnil conj #{}) h)))
                         {} (res/matches-visible kb goal context))]
    (concat entailed (map (fn [[b hs]] [b (when support? hs)]) stored))))

(defrecord IncludesInstantProver []
  prover-types/Prover
  ;; both polarities, as the calculus provers answer theirs: `(not (includesInstant X t))`
  ;; holds when the network puts `t` outside X, which is what makes an `argue` over the
  ;; goal answer :unknown for a moment inside an uncertain bound rather than :false.
  ;; Completeness 100 holds because `solve-inclusion` reads the stored literal as well.
  (applicable? [_ _ goal _] (some? (inclusion-literal goal)))
  ;; An open argument enumerates only the things and moments the network names, while a
  ;; calendar moment no fact names can fall inside a thing, so the planner is told to bind
  ;; the argument first.
  (est-bindings [_ _ goal _]
    (let [[_ x t] (inclusion-literal goal)]
      (if (or (sx/variable? x) (sx/variable? t)) provers/deferred-est 1)))
  (cost [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (map first (solve-inclusion kb goal context false)))
  prover-types/SupportingProver
  (support-functors [_] #{'includesInstant})
  (support-sources [_] (set (keys instant-denotation)))
  (solve-with-support [_ kb goal context] (solve-inclusion kb goal context true)))

(defn includes-instant-prover
  "The prover answering `includesInstant` off the point network, to register with
  `vaelii.core/add-prover`."
  []
  (->IncludesInstantProver))
