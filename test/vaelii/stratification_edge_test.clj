;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stratification-edge-test
  "Stratification when a **taxonomy edge** is what closes the cycle, rather than a
  rule.  See the Stratification section of
  [docs/exceptions.md](../../docs/exceptions.md).

  Both kinds of edge in the rule dependency graph fan out over the genl **spec**
  closure, so a cycle through negation can exist purely because of a `genl` edge: an
  exception on `flightless` is reached by a stored `(penguin Opus)` the moment
  `(genl penguin flightless)` holds.  `stratification_test` covers the case where the
  edge is already there and a rule arrives last; this namespace covers the other
  order, where both rules are stored and the **edge** arrives last.

  Three things to pin, and they are the same three the rule path pins:

  * the edge that closes a cycle is **refused**, and leaves nothing behind — neither
    a sentex nor a taxonomy closure that learned it;
  * an edge that closes nothing is accepted, so the refusal above is attributable to
    the cycle and not to the mere presence of an excepted rule;
  * the walk is **skipped entirely** when no stored rule carries a negative edge, which
    is every rule in the bundled starter and therefore every ordinary `genl` assert.
    Asserted by counting `wff/genl-negation-cycle` calls, not by a clock.

  Plus the derivation path, where the answer is different by necessity: forward
  chaining cannot throw, so a derived edge that would close a cycle is dropped and
  reported in `(v/violations kb)` alongside the definitional constraints.

  House rules as everywhere: gensym'd temporaries via `tu/with-terms`, engine
  vocabulary (`genl`, `genlCx`, `set/defaultRule`, `exceptWhen`) literal, and the
  neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wff :as wff]
            [vaelii.ref.gen :as gen]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- except-rule
  "The shape docs/exceptions.md writes: an exception query wrapping a defeasible rule."
  [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq)))))

(defn- refusal
  "Assert, and return the `ex-data` of the refusal — nil if the assert went through.
  Reading the data rather than catching bare `ExceptionInfo` is what distinguishes a
  stratification refusal from a well-formedness or naming one, which would pass a
  `thrown?` test for the wrong reason."
  [kb sentence context]
  (try (v/assert kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- walks
  "Run `f`, returning how many times an edge check walked the rule dependency graph.
  Counting the search calls measures the fast path exactly; a timing test would measure
  the machine."
  [f]
  (let [n    (atom 0)
        orig wff/genl-negation-cycle]
    (with-redefs [wff/genl-negation-cycle (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(defn- cycle-shaped-rules!
  "The two rules of the cycle, with the `genl` edge that closes it **not** asserted:

    R1  excepts-on `flightless`, concludes `p`
    R2  depends-on `p`,          concludes `penguin`

  Stratified as it stands — nothing concludes `flightless`.  Adding
  `(genl penguin flightless)` puts `penguin` in `specs(flightless)`, so R1's negative
  edge reaches R2 and R2's positive edge reaches back: a cycle through negation."
  [kb {:keys [base p flightless penguin ctx]}]
  (v/assert kb (except-rule (list flightless '?x) [(list base '?x)] (list p '?x)) ctx)
  (v/assert kb (vr/rule-sentence [(list p '?x)] (list penguin '?x)) ctx {:direction :forward}))

;; ---- the edge that closes the cycle is refused ---------------------------
;; DECISION: the `genl` assert is the operation at fault, so the **edge** is what is
;; refused — the same answer `wff` already gives an edge that would make the taxonomy
;; cyclic, and the one that keeps stored state stratified at all times.

(tu/deftest-kb a-genl-edge-that-closes-a-cycle-between-stored-rules-is-refused
  (tu/with-terms [base p flightless penguin CxEdge]
    (let [terms {:base base :p p :flightless flightless :penguin penguin :ctx CxEdge}]
      (cycle-shaped-rules! kb terms)
      (let [data (refusal kb (list 'genl penguin flightless) CxEdge)]
        (testing "the edge is refused, and says why"
          (is (= :not-stratified (:type data))))
        (testing "the refusal names the cycle it would have created"
          (is (seq (:cycle data))))))))

(tu/deftest-kb a-genl-edge-that-closes-nothing-is-accepted
  ;; The control for the test above.  Same two rules, same excepted rule in the KB,
  ;; a `genl` edge that simply does not put anything in the exception's spec closure
  ;; — so the refusal above is attributable to the **cycle** and not to "there is an
  ;; exception around, refuse edges".
  (tu/with-terms [base p flightless penguin unrelated CxEdge]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (is (v/assert kb (list 'genl penguin unrelated) CxEdge)
        "penguin under an unrelated supertype crosses no negative edge")
    (is (tax/genl?-global (reasoning/taxonomy kb) penguin unrelated)
        "and the accepted edge did reach the closures")))

(tu/deftest-kb the-same-edge-is-accepted-when-the-rule-carries-no-exception
  ;; The second control, one step further out: identical rule *shapes*, identical
  ;; edge, but R1 states no exception — so the graph has no negative edge at all and
  ;; the cycle it would close is ordinary positive recursion, which is a supported
  ;; feature rather than a violation.
  (tu/with-terms [base p flightless penguin CxPlain]
    (is (v/assert kb (vr/rule-sentence [(list base '?x)] (list p '?x)) CxPlain {:direction :forward}))
    (is (v/assert kb (vr/rule-sentence [(list p '?x)] (list penguin '?x)) CxPlain {:direction :forward}))
    (is (v/assert kb (list 'genl penguin flightless) CxPlain))))

;; ---- a genlCx edge is not walked ----------------------------------------
;; The dependency graph is over *predicates* and its edges read the `genl` closure
;; alone, so a `genlCx` edge adds no graph edge and a walk could only find a cycle
;; already stored.

(tu/deftest-kb a-genlCx-edge-walks-nothing-and-is-accepted
  (tu/with-terms [base p flightless penguin CxEdge CxSub]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (is (zero? (walks #(v/assert kb (list 'genlCx CxSub CxEdge) CxSub))))
    (is (tax/sees? (reasoning/taxonomy kb) CxSub CxEdge))))

;; ---- a refused edge leaves nothing behind --------------------------------

(tu/deftest-kb a-refused-edge-leaves-neither-a-sentex-nor-a-closure
  ;; The check runs before the sentex is created *and* before the taxonomy is
  ;; touched: it adds the edge to a detached copy of the taxonomy to ask the
  ;; question.  A half-applied refusal would leave the closures claiming an edge no
  ;; sentex supports, which `recover` would then disagree with.
  (tu/with-terms [base p flightless penguin CxEdge]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (let [before-sx    (tu/sentex-ids kb)
          before-dd    (tu/justification-ids kb)
          before-edges (tax/genl-edges (reasoning/taxonomy kb))
          data         (refusal kb (list 'genl penguin flightless) CxEdge)]
      (is (= :not-stratified (:type data)))
      (is (= before-sx (tu/sentex-ids kb))    "no sentex was stored")
      (is (= before-dd (tu/justification-ids kb)) "no justification was stored")
      (testing "and the cached closures never learned the edge"
        (is (= before-edges (tax/genl-edges (reasoning/taxonomy kb))))
        (is (not (tax/genl?-global (reasoning/taxonomy kb) penguin flightless)))
        (is (not (contains? (tax/specs-global (reasoning/taxonomy kb) flightless) penguin)))))))

;; ---- the fast path ------------------------------------------------------
;; Every rule in the bundled starter is unexcepted, so a regression here would slow
;; every ordinary `genl` assert in the ontology.

(tu/deftest-kb an-edge-change-walks-nothing-when-no-rule-carries-an-exception
  (tu/with-terms [base p CxFast]
    (v/assert kb (vr/rule-sentence [(list base '?x)] (list p '?x)) CxFast {:direction :forward})
    (testing "no exception anywhere: the edge assert does not walk the graph at all"
      (tu/with-terms [sub super]
        (is (zero? (walks #(v/assert kb (list 'genl sub super) CxFast))))))
    (testing "control: one excepted rule in the KB and the same operation does walk"
      (tu/with-terms [exc otherBase other sub super]
        (v/assert kb (except-rule (list exc '?x) [(list otherBase '?x)] (list other '?x))
                  CxFast)
        (is (pos? (walks #(v/assert kb (list 'genl sub super) CxFast))))))))

;; ---- the walk's cost -----------------------------------------------------
;; A walk reaches a rule once per edge into it, and the graph is dense wherever many
;; rules read one type.  A stored rule's node is read from the store (the record, and the
;; rule's exceptWhen meta-sentexes off the index), so an edge check builds each one once,
;; however many edges reach it.

(defn- node-builds
  "Run `f`, returning how many stored-rule nodes the stratification checks built."
  [f]
  (let [n    (atom 0)
        orig @#'checks/stored-rule-node]
    (with-redefs-fn {#'checks/stored-rule-node
                     (fn [kb h] (swap! n inc) (orig kb h))}
      f)
    @n))

(tu/deftest-kb an-edge-check-builds-each-stored-rule-node-once
  (tu/with-terms [hub exc p sub CxDense]
    (let [spokes (vec (repeatedly 6 #(tu/tmp-type "spoke")))]
      (doseq [t spokes] (v/assert kb (list 'genl t hub) CxDense))
      ;; an excepted rule reading `hub`
      (v/assert kb (except-rule (list exc '?x) [(list hub '?x)] (list p '?x)) CxDense)
      ;; one rule concluding each spoke, each reading `hub` as well: every spoke's rule is
      ;; read by all seven rules, seven edges into each
      (doseq [t spokes]
        (v/assert kb (vr/rule-sentence [(list hub '?x)] (list t '?x)) CxDense
                  {:direction :forward}))
      ;; the edge's walk starts at the seven rules reading `hub`
      (let [n (node-builds #(v/assert kb (list 'genl sub hub) CxDense))]
        (testing "the edge is accepted: nothing concludes a spec of the fresh subtype"
          (is (tax/genl?-global (reasoning/taxonomy kb) sub hub)))
        (testing "seven stored rules, seven nodes, against 42 edges into them"
          (is (= 7 n)))))))

(tu/deftest-kb a-genl-edge-check-builds-no-excepted-rule-the-edge-does-not-reach
  ;; Four rules read `top` and conclude predicates nothing reads; the excepted rules read
  ;; `hub`, under which the spoke rules conclude.  An edge under `top` reaches the four
  ;; readers of `top` and none of the excepted rules, so its check builds the same four
  ;; nodes with two excepted rules stored and with six.
  (tu/with-terms [hub top CxWide]
    (let [except! (fn [] (v/assert kb (except-rule (list (tu/tmp-type "exc") '?x)
                                                   [(list hub '?x)]
                                                   (list (tu/tmp-type "seen") '?x))
                                   CxWide))]
      (dotimes [_ 4]
        (let [t (tu/tmp-type "spoke")]
          (v/assert kb (list 'genl t hub) CxWide)
          (v/assert kb (vr/rule-sentence [(list hub '?x)] (list t '?x)) CxWide
                    {:direction :forward}))
        (v/assert kb (vr/rule-sentence [(list top '?x)] (list (tu/tmp-type "out") '?x)) CxWide
                  {:direction :forward}))
      (dotimes [_ 2] (except!))
      (let [at-two (node-builds #(v/assert kb (list 'genl (tu/tmp-type "sub") top) CxWide))]
        (dotimes [_ 4] (except!))
        (let [at-six (node-builds #(v/assert kb (list 'genl (tu/tmp-type "sub") top) CxWide))]
          (is (= 4 at-two at-six)))))))

(defn- rule-index-reads
  "Run `f`, returning how many reads of the rule index's antecedent, consequent and
  re-check postings it made."
  [f]
  (let [n    (atom 0)
        wrap (fn [orig] (fn [& args] (swap! n inc) (apply orig args)))]
    (with-redefs [reads/as-stored-rules-by-antecedent-global (wrap reads/as-stored-rules-by-antecedent-global)
                  reads/as-stored-rules-by-consequent-global (wrap reads/as-stored-rules-by-consequent-global)
                  reads/watched-rules-on              (wrap reads/watched-rules-on)]
      (f))
    @n))

(defn- chain-edge-reads
  "Rule-index reads of the check on `(genl p6 p0)` over a chain of six rules, rule i
  reading `p<i>` and concluding `p<i+1>`, with `width` spec types under every `p<i>`.  The
  edge closes a positive cycle through all six rules, so the check walks the whole chain
  and accepts it."
  [kb width ctx]
  (let [ps (vec (repeatedly 7 #(tu/tmp-type "link")))]
    (doseq [p ps, _ (range width)] (v/assert kb (list 'genl (tu/tmp-type "kind") p) ctx))
    (doseq [[p q] (partition 2 1 ps)]
      (v/assert kb (vr/rule-sentence [(list p '?x)] (list q '?x)) ctx {:direction :forward}))
    (let [cycle (atom ::unread)
          n     (rule-index-reads
                 #(reset! cycle (@#'checks/edge-negation-cycle kb (list 'genl (ps 6) (ps 0)))))]
      [n @cycle])))

(tu/deftest-kb a-genl-edge-check-reads-the-rule-index-flat-in-the-spec-closure-width
  (tu/with-terms [base exc seen CxChain]
    ;; one excepted rule elsewhere, so the check walks at all
    (v/assert kb (except-rule (list exc '?x) [(list base '?x)] (list seen '?x)) CxChain)
    (let [[narrow narrow-cycle] (chain-edge-reads kb 2 CxChain)
          [wide wide-cycle]     (chain-edge-reads kb 12 CxChain)]
      (is (= [nil nil] [narrow-cycle wide-cycle]) "a positive cycle is accepted")
      (is (= narrow wide)))))

;; ---- the walk from the edge against the whole graph ------------------------
;; The check walks once, against the edges, from the rules reading a predicate at or
;; above the edge's supertype.  The oracle builds the probe's whole graph forwards, each
;; reader's spec closures to the rules concluding into them, and looks for a negative
;; edge whose head reaches its tail.  The store is stratified, so a cycle in the probe's
;; graph runs through the edge, and the two give the same verdict for every candidate
;; edge; the walk's cycle runs through the edge, and is the same content in either
;; arrival order.

(defn- graph-cycle?
  "Does the probe's graph, built forwards over `specs-global`, hold a cycle through
  negation?"
  [kb a b]
  (let [probe  (tax/detached-copy (reasoning/taxonomy kb))
        _      (tax/add-genl probe a b ::oracle)
        rules  ((@#'checks/stratification-readers kb))
        under? (fn [r p] (or (:concludes-any? r)
                             (contains? (tax/specs-global probe p) (:consequent-pred r))))
        edges  (for [r rules
                     [kind preds] [[:pos (:antecedent-preds r)] [:neg (:exception-preds r)]]
                     p preds, r' rules :when (under? r' p)]
                 [kind (:id r) (:id r')])
        succ   (reduce (fn [m [_ u v]] (update m u (fnil conj #{}) v)) {} edges)
        reach? (fn [from to]
                 (loop [todo [from] seen #{}]
                   (when-let [x (peek todo)]
                     (or (= x to)
                         (recur (into (pop todo) (remove seen (succ x))) (conj seen x))))))]
    (boolean (some (fn [[kind u v]] (and (= :neg kind) (reach? v u))) edges))))

(defn- label-content
  "A cycle with each `rule#<handle>` label read as the rule's sentence and context."
  [kb cycle]
  (mapv #(if-let [[_ h] (re-matches #"rule#(\d+)" %)]
           (let [sx (p/get-sentex (:records kb) (parse-long h))]
             [(sx/sentence-of sx) (:context sx)])
           %)
        cycle))

(defn- through-edge?
  "Does `cycle`'s last step run from a rule reading a predicate at or above `b` to a
  rule concluding a spec of `a`?"
  [kb cycle a b]
  (let [tx      (reasoning/taxonomy kb)
        [_ h]   (re-matches #"rule#(\d+)" (nth cycle (- (count cycle) 3)))
        node    (@#'checks/stored-rule-node kb (parse-long h))
        spec    (second (re-matches #"\S+ (.+)" (nth cycle (- (count cycle) 2))))
        above   (set (map str (tax/genls-global tx b)))]
    (and (contains? (set (map str (tax/specs-global tx a))) spec)
         (boolean (some #(above (str %)) (concat (:antecedent-preds node)
                                                 (:exception-preds node)))))))

(defn- world-types [world]
  (->> (:writes world) (map :sentence) (tree-seq coll? seq)
       (filter #(and (symbol? %) (re-matches #"tmpty[a-z]\d+" (name %))))
       distinct sort vec))

(defn- oracle-seed
  [seed]
  (let [world (gen/gen-world seed {:rules [2 6] :writes [8 14] :types [4 7]})
        types (world-types world)
        pairs (for [a types, b types :when (not= a b)] [a b])
        load  (fn [order] (gen/load-world! world order {}))
        one   (load (vec (:writes world)))
        two   (load (vec (rseq (vec (:writes world)))))]
    (try
      (let [same-store? (= (set (map :refused (:refused one))) (set (map :refused (:refused two))))]
        (vec (for [[a b] pairs
                   :let [kb     (:kb one)
                         sent   (list 'genl a b)
                         old    (graph-cycle? kb a b)
                         new    (@#'checks/edge-negation-cycle kb sent)
                         new-2  (@#'checks/edge-negation-cycle (:kb two) sent)]]
               {:seed seed :edge sent :refused? (some? new)
                :problem (cond
                           (not= old (some? new)) [:verdict old new]
                           (and new (not (through-edge? kb new a b))) [:not-through-edge new]
                           (and same-store? (not= (some? new) (some? new-2))) [:order-verdict new new-2]
                           (and same-store? new
                                (not= (label-content kb new) (label-content (:kb two) new-2)))
                           [:order-cycle new new-2])})))
      (finally (gen/close-kb! one) (gen/close-kb! two)))))

(deftest a-genl-edge-check-agrees-with-the-whole-graph-on-random-worlds
  (let [rows (into [] (mapcat oracle-seed) (range 1 21))]
    (is (empty? (filter :problem rows)) (pr-str (take 3 (filter :problem rows))))
    (testing "the candidate edges hold refusals and acceptances both"
      (is (pos? (count (filter :refused? rows))))
      (is (pos? (count (remove :refused? rows)))))))

;; ---- the derivation path -------------------------------------------------
;; DECISION: a *derived* edge is **dropped and reported**, not thrown.  Forward
;; chaining is a fixpoint and an exception escaping one rule firing would make the
;; resulting belief set depend on which rule fired first — the same reasoning that
;; puts the definitional constraints in `violations` rather than in a throw.  Dropping
;; rather than merely reporting is what keeps the invariant: an unstratified edge that
;; was only *reported* would still be in the taxonomy.

(tu/deftest-kb a-derived-edge-that-would-close-a-cycle-is-dropped-and-reported
  (tu/with-terms [base p flightless penguin subtypeMarker noted CxDerive]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxDerive})
    ;; a rule that *concludes* a genl edge, plus an innocuous one firing on the same
    ;; fact — chaining must finish the run, not abort at the bad conclusion
    (v/assert kb (vr/rule-sentence [(list subtypeMarker '?t)] (list 'genl '?t flightless))
              CxDerive {:direction :forward})
    (v/assert kb (vr/rule-sentence [(list subtypeMarker '?t)] (list noted '?t))
              CxDerive {:direction :forward})
    (v/assert kb (list subtypeMarker penguin) CxDerive)
    (let [vs (v/violations kb)]
      (testing "the conclusion is reported as inadmissible, with the cycle"
        (is (= [:not-stratified] (mapv :violation vs)))
        (is (seq (:cycle (:detail (first vs))))))
      (testing "and dropped: no sentex, and the closures never learned it"
        (is (empty? (v/sentexes-matching kb (list 'genl penguin flightless) '?ctx)))
        (is (not (tax/genl?-global (reasoning/taxonomy kb) penguin flightless))))
      (testing "chaining still ran to a fixpoint rather than aborting"
        (is (seq (v/sentexes-matching kb (list noted penguin) '?ctx)))))))

;; ---- the probe's memo is its own -----------------------------------------
;; The stratification probe asks its question of a detached copy of the taxonomy, and
;; the read memo is a **side atom** inside that value — so a copy that kept the
;; reference would let the probe write closures computed over the refused edge into
;; the live memo, stamped one gen ahead of the live relation.  Those entries answer
;; real reads the moment the live gen catches up.  The sequence below arranges exactly
;; that catch-up: a retraction bumps the gen without an intervening closure read (an
;; assert's own checks would recompute-and-clear on the way in; a retraction runs no
;; checks), so a shared memo would serve the refused edge as a real subtype.

(tu/deftest-kb a-refused-edge-does-not-poison-the-closure-memo-through-the-probe
  (tu/with-terms [base p flightless penguin sub super CxEdge]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (let [h    (v/assert kb (list 'genl sub super) CxEdge)
          data (refusal kb (list 'genl penguin flightless) CxEdge)]
      (is (= :not-stratified (:type data)) "the probe ran and the edge was refused")
      (v/retract! kb h)
      (testing "the closure read after the gen catch-up never sees the refused edge"
        (is (not (contains? (tax/specs-global (reasoning/taxonomy kb) flightless) penguin)))
        (is (not (contains? (tax/genls-global (reasoning/taxonomy kb) penguin) flightless)))))))

(tu/deftest-kb a-derived-edge-that-closes-no-cycle-is-placed-normally
  ;; The control for the drop above: same derivation, same excepted rule in the KB,
  ;; an edge that crosses no negative edge — so it lands and reaches the closures.
  (tu/with-terms [base p flightless penguin unrelated subtypeMarker CxDerive]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxDerive})
    (v/assert kb (vr/rule-sentence [(list subtypeMarker '?t)] (list 'genl '?t unrelated))
              CxDerive {:direction :forward})
    (v/assert kb (list subtypeMarker penguin) CxDerive)
    (is (empty? (v/violations kb)))
    (is (seq (v/sentexes-matching kb (list 'genl penguin unrelated) '?ctx)))
    (is (tax/genl?-global (reasoning/taxonomy kb) penguin unrelated)
        "a derived edge reaches the taxonomy through integrate-transitive")))

;; ---- the consequent-var-pred rule and negation ---------------------------
;;
;; A rule concluding `(?p ?x)` could conclude *any*
;; predicate once `?p` binds, so the stratification check treats it as a concluder of the
;; predicate its NAF antecedent depends on — `rules/direct-concluders` folds in the
;; `p/var-consequent-key` catch-all.  Without that a one-rule negation cycle slips the entry point.

(tu/deftest-kb a-variable-consequent-rule-that-could-conclude-its-own-naf-is-refused
  (tu/with-terms [bar foo]
    (let [rule (vr/rule-sentence [(list bar '?p '?x) (list 'unknown (list foo '?x))]
                                 '(?p ?x))
          data (refusal kb rule 'CxNaturalWorld)]
      (is (= :not-stratified (:type data))
          "it could conclude foo while depending on foo's absence — an unstratified rule"))))

(tu/deftest-kb a-variable-consequent-rule-with-no-naf-is-accepted
  ;; the control: the refusal above is the cycle, not the mere presence of a variable
  ;; consequent — a var-consequent rule with a monotonic antecedent asserts cleanly.
  (tu/with-terms [holds]
    (let [h (v/assert kb (vr/rule-sentence [(list holds '?p '?x '?y)] '(?p ?x ?y))
                      'CxNaturalWorld {:direction :forward})]
      (is (some? h))
      (v/retract! kb h))))

;; The other two negative-antecedent forms fold into the same cycle: `check-stratified`
;; treats the exception's predicates and the aggregate bodies' predicates as negative
;; edges exactly as it does `unknown`, and a variable consequent concludes any of them.

(tu/deftest-kb a-variable-consequent-rule-excepted-on-its-own-conclusion-is-refused
  ;; the `exceptWhen` branch: the rule's exception reads `foo`, and its variable consequent
  ;; `(?p ?x)` could conclude `foo` — a one-rule negation cycle through the exception.
  (tu/with-terms [bar foo]
    (let [rule (list 'exceptWhen (list foo '?x)
                     (vr/rule-sentence [(list bar '?p '?x)] '(?p ?x)))
          data (refusal kb rule 'CxNaturalWorld)]
      (is (= :not-stratified (:type data))
          "it could conclude foo while excepted when foo holds — an unstratified rule"))))

(tu/deftest-kb a-variable-consequent-rule-aggregating-its-own-conclusion-is-refused
  ;; the aggregate branch: the rule counts over `foo`, and its variable consequent `(?p ?x)`
  ;; could conclude `foo` — the count has no settled answer, so the rule is refused.
  (tu/with-terms [bar foo]
    (let [rule (vr/rule-sentence [(list bar '?p '?x)
                                  (list 'agg/count '?n '?v (list foo '?v))]
                                 '(?p ?x))
          data (refusal kb rule 'CxNaturalWorld)]
      (is (= :not-stratified (:type data))
          "it could conclude foo while counting foo's extent — an unstratified rule"))))
