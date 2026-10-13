;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.jtms
  "A non-monotonic truth-maintenance system.

  Each TMS *node* corresponds to a datum (a sentex handle) and records: its label
  (IN/OUT), whether it is a premise (and at what assumption *strength*), its
  derivation depth, the justifications that conclude it (:supports), and the
  justifications that use it as an antecedent or name it as their rule (:consequences).

  A node holds **no reference to the sentex it labels** — only its handle.  The record
  store is where a sentex lives, so a copy here would be a second one to keep in step;
  and because this graph is always resident, a strong reference from it would hold every
  record in RAM, which on a paging backend defeats the paging entirely (measured: the
  nodes reached 50% of the record store).  A caller that needs the sentence fetches it
  by handle.

  Belief is a least fixpoint: a node is IN when it is a premise or has a valid
  justification (all antecedents IN).  Because labels are computed from the current
  justification set rather than accumulated as events arrive, belief is
  order-independent.  A contradiction takes nothing OUT here: the settle places it as a
  `contradicts` and a `defeat`, and the read walk hides the loser at the readers where the
  defeat is in force (`vaelii.impl.except`), so the network holds support labels only.

  ## Two invariants

  **Order independence.** The same knowledge, given in any order, yields the same
  beliefs.  Every operation here recomputes labels from current state, so nothing
  depends on arrival order.  (The one place this can leak is a *tie-break* between
  two equally-strong beliefs: keying it on handle id would smuggle assertion order
  back in, so the contradiction layer keys it on content — see
  `vaelii.impl.solve/content-key`.)

  **Locality.** No operation recomputes the whole graph.  A change can only affect
  nodes downstream of it, so every relabel is scoped to the *affected region* — the
  forward consequence closure of whatever changed — with the rest of the graph held
  fixed as the boundary.  Cost is proportional to the region, not to the size of the
  KB, which is what lets belief maintenance scale.

  These two pull against each other, and the reconciliation is the whole design:
  a local fixpoint over the region, with boundary labels fixed, has a *unique*
  solution, and it is the same one a global fixpoint would produce.  See
  `relabel-region*`.

    * strength — every premise carries a strength (:monotonic / :default); every
      justification carries a *strength* too (:monotonic for a bare rule, :default for
      a defeasible one), capping the class it confers.  From these, `relabel` derives
      each IN node's *defeat-class* (monotonic > default, see
      vaelii.impl.strength).  Strength **propagates**: a justification confers no more
      than the weakest of its antecedents' classes, so a conclusion is never stronger
      than what it rests on.  That makes the class equation recursive, and
      `region-classes` solves it as a least fixpoint inside the region relabel.
      The class decides who loses a soft contradiction at a reader
      (`vaelii.impl.decide`); the network records no defeat, and nothing forces a datum
      OUT.

    * superseded — a *map* `datum -> reason` of datums displaced by an equality
      merge: the stale spelling of a fact whose terms have been rewritten to their
      class representative (docs/equality.md).  Three things make it its own state
      rather than a reuse of `blocked`:

      - `blocked` names *justifications*, and a directly asserted `(bornIn Dep
        Chicago)` is a **premise with no justification at all** — `region-fixpoint`
        seeds every premise IN unconditionally, so there is nothing for a block to
        invalidate.  Superseding has to act on the datum.
      - A superseded spelling lost no argument; it was restated, and `why-not` must be
        able to say so — hence the map carries the displacing representative rather than
        being a bare set.
      - It is **not** a forced OUT inside the fixpoint.  A superseded datum stays in
        `:in` for the purposes of `valid?`, because its rewritten twin is justified
        *by it*: forcing it OUT structurally would invalidate the twin's own
        justification and the merge would believe neither spelling.  What
        supersession removes is *reported* belief — `in?` and `in-datums` subtract
        it — so the stale spelling stops matching and stops answering queries, while
        everything derived from it stands.  The nogood families detect over the IN
        label (`network-in?`), so a nogood with a superseded member keeps its
        placement, and the clash reports leave it out (docs/nmtms.md).

      Retention is the point: the spelling is the **caller's premise**, so unlike an
      excepted conclusion it is never swept, and dropping the equality gives it back.
      Like `blocked` the map is *derived* — core recomputes it each
      settle from the equality closure — so belief stays order independent.

    * forced — three sets the forced-monotonic roster writes (docs/nmtms.md, \"The
      forced-monotonic roster\"): `:mono`, premises whose class is `:monotonic` whatever
      strength they carry; `:out`, datums the fixpoint never adds, a premise included;
      and `:void`, justifications that support nothing and confer no class.  Each is an
      **attribute** of the element it names, written by the caller with the element and
      rewritten when the roster moves (`set-forced`), so the stored content keeps the
      strength it was written at and every record a forced set governs stays stored.

    * blocked — a set of *justification* ids whose rule's exception currently holds
      (`exceptWhen`, see docs/exceptions.md).  A blocked justification is simply
      **invalid**, so it supports nothing and confers no defeat-class — which is what
      lets the ordinary dependency-directed sweep garbage-collect an excepted
      conclusion.  This module is pure and has no
      KB, so it cannot run the exception query itself: the caller evaluates the
      exception and hands the answer in with `set-blocked`, which relabels only the
      region the change reaches.  The set is *derived* — computed
      from current state each settle, never accumulated — so belief stays order
      independent.

  Retraction is dependency-directed: drop the premise, relabel, then SWEEP the
  affected closure — datums that end up OUT with no valid support are solely supported
  by the retraction, so they (and their non-premise justifications) are returned for the
  caller to delete from the stores.

  This module owns the in-memory graph; the caller owns physical deletion, since
  only it holds the stores."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.jtms-protocol :refer [Tms
                                               -believed? -believed -node? -datums
                                               -any-node? -any-belief? -depth -premise?
                                               -premise-strength -defeat-class
                                               -blocked -superseded -touched -touched-in
                                               -touched-new -touched-out -reset-touched
                                               -touch-mark -touched-since
                                               -supports
                                               -dependents -justification -justifications
                                               -ensure-node -add-premise -suspend-premise
                                               -add-justification -restrength-informant
                                               -forced? -forced-members -set-forced
                                               -relabel -set-blocked
                                               -supersede -retract -sweep
                                               -drop-justification -snapshot
                                               -hold -release -held]]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.tms :as tms-types])
  (:import [java.util PriorityQueue]
           [java.util.concurrent.atomic AtomicReference]))

(defmacro ^:private moving
  "Run `body`, a mutation of the network, between two moves of the change clock
  (`observe/note-change`), and answer what `body` answers.

  Every mutating entry point in this namespace wraps its mutation in this, rather than
  the two `Tms` implementations bumping the clock: the entry points are the whole of how
  the engine reaches the network, so one wrap apiece is exhaustive by construction and
  neither representation can forget one.  A call that turns out to move no label bumps
  anyway, which costs a re-derivation and never a wrong answer.

  The clock moves on both sides of the mutation.  A cache stamps an entry with the clock
  it read before computing, and installs the entry only when the clock still reads that
  value afterwards (`literal-cache/lookup`, `provers/cached-reach`).  The move before the
  mutation keeps a read made inside it from being served an entry computed before it.
  The move after retires every entry computed while the mutation ran: a reader thread
  that reads the clock between the first move and the mutation computes from the network
  before the mutation, and without the second move its entry would be served at the
  clock the mutation leaves, to the writer's own next read as well
  (`kb_concurrency_test`)."
  [& body]
  `(do (observe/note-change)
       (let [r# (do ~@body)]
         (observe/note-change)
         r#)))

(defn- without-informant
  "`antecedents` as a vector, with a rule-handle `informant` taken out of it.  A firing
  hands over its handle list with the rule in it (`chain/derive-conclusion`), and so does
  a seven-field frame on disk (`codec/decode-justification`); both store the rule once."
  [informant antecedents]
  (if (and (integer? informant)
           (reduce (fn [_ h] (if (= informant h) (reduced true) false)) false antecedents))
    (into [] (remove #(= informant %)) antecedents)
    (vec antecedents)))

(defn rests-on
  "Every handle justification `j` needs believed to be valid: its antecedents, plus its
  informant when that is a rule handle.  The sweep preview, `why-not`'s missing list, the
  visibility check and recovery's storedness check read this."
  [j]
  (let [inf (:informant j)]
    (cond-> (vec (:antecedents j)) (integer? inf) (conj inf))))

(defn- reduce-rests-on
  "`(reduce f init (rests-on j))` without the vector: the adjacency writes run once per
  justification added or swept, and the add is the hottest write path there is."
  [f init j]
  (let [acc (reduce f init (:antecedents j))
        inf (:informant j)]
    (if (integer? inf) (f acc inf) acc)))

(def respell-informant
  "The informant of a justification storing a spelling a reader reads of a fact, from the
  row holding the fact as written and the marks that sort it (`chain/respell-rows!`).  Its
  first antecedent is the row and the rest are the marks: every one must be IN for the
  justification to be valid, and only the row caps the class it confers
  (`class-antecedents`), so a spelling holds at the class of the fact it spells."
  'respell)

(defn class-antecedents
  "The antecedents of justification `j` whose classes cap the class it confers: all of
  them, except under `respell-informant`, where only the first does."
  [j]
  (let [as (:antecedents j)]
    (if (and (= respell-informant (:informant j)) (next as))
      [(first as)]
      as)))

(defn ->just
  "Construct a Justification, defaulting `strength` to :monotonic — a bare monotone
  justification adds no defeasibility of its own, so `conferred-class` caps it at its
  weakest antecedent.  A rule-handle informant is taken out of `antecedents`
  (`without-informant`).  `subsumptions` is a rule firing's set of `[sub super]` pairs,
  stored under `:subsumptions` when it is not empty."
  ([id informant antecedents consequence bindings]
   (->just id informant antecedents consequence bindings :monotonic nil))
  ([id informant antecedents consequence bindings strength]
   (->just id informant antecedents consequence bindings strength nil))
  ([id informant antecedents consequence bindings strength subsumptions]
   (cond-> (tms-types/->Justification id informant (without-informant informant antecedents)
                                      consequence bindings (or strength :monotonic))
     (seq subsumptions) (assoc :subsumptions subsumptions))))

(defn graph-just
  "The part of a justification the **network** is made of — everything except the
  firing's `:bindings`.

  Belief never reads the bindings: `valid?` needs the antecedents, `conferred-class`
  the strength and the informant, and the region walks the consequence.  The bindings
  are the variable map of the firing that produced it, and only two readers want them
  — re-evaluating an `exceptWhen` query and a NAF antecedent per firing — both of
  which hold the KB and take the **record** from the store, where it is durable.  So
  the network keeps the graph and the store keeps the record, and the JTMS stops
  holding a second copy of every justification.  Measured (`lein bench-jtms`, a
  rules-heavy corpus at 3.6 justifications per node): 80 of 277 B each.

  It also **normalizes** — antecedents to a vector without the informant, strength
  defaulted — so that however a caller spells a justification, the two
  representations store a value equal to each other's.  `:bindings` is nil rather
  than dropped, keeping the record shape fixed for every reader.  `:subsumptions` stays,
  for the dedup key (`just-key`)."
  [j]
  (->just (:id j) (:informant j) (:antecedents j) (:consequence j) nil (:strength j)
          (:subsumptions j)))

;; ---- derivation depth ---------------------------------------------------
;;
;; The two walks below keep every stored depth at the least solution of the depth
;; equation (docs/nmtms.md, "Derivation depth").  Each reads the network through accessor
;; fns, so the dense network runs the same code over its columns.

(defn- depth-queue
  "An empty min-queue of `[depth datum]` entries."
  ^PriorityQueue []
  (PriorityQueue. 16 (fn [a b] (Long/compare (long (nth a 0)) (long (nth b 0))))))

(defn- one-deeper
  "One more than the deepest of `antes`, each read through `depth-of`."
  ^long [antes depth-of]
  (inc (long (reduce (fn [^long m a] (max m (long (depth-of a)))) 0 antes))))

(defn- cites?
  "Does `antes` name `d`?  A justification lists its rule under the rule's node too, and
  the rule is no antecedent of it."
  [antes d]
  (boolean (some #(= d %) antes)))

(defn lowered-depths
  "`{node depth}` for `datum` at `depth` and for every node downstream of it whose
  shallowest justification reads shallower once it is, walked shallowest first.  Writes
  nothing.  `dependents` names the justification ids citing a node, `antecedents` and
  `consequence` read one justification (nil for an id no longer stored), and `depth-of`
  is the stored depth."
  [datum depth dependents antecedents consequence depth-of]
  (let [q (depth-queue)]
    (.add q [depth datum])
    (loop [low {datum depth}]
      (if-let [[v d] (.poll q)]
        (if (> (long v) (long (get low d)))
          (recur low)
          (recur (reduce (fn [low jid]
                           (let [antes (antecedents jid)
                                 c     (consequence jid)]
                             (if (or (nil? c) (not (cites? antes d)))
                               low
                               (let [cur  #(get low % (depth-of %))
                                     cand (one-deeper antes cur)]
                                 (if (< cand (long (cur c)))
                                   (do (.add q [cand c]) (assoc low c cand))
                                   low)))))
                         low (dependents d))))
        low))))

(defn region-depths
  "`{node depth}` for each node of `region` whose depth moves when the region is solved
  afresh, every node outside it held at its stored depth.  `region` is closed under
  consequence (an affected region), so no node outside it reads one inside.  Writes
  nothing; the accessors are `lowered-depths`', plus `premise?` and `supports`.

  Knuth's generalization of Dijkstra's algorithm: a justification is queued once its
  last antecedent inside the region is final, and the queue pops shallowest first.  A
  region node that no justification reaches from outside the region keeps its stored
  depth."
  [region premise? supports dependents antecedents consequence depth-of]
  (let [inside (set region)
        q      (depth-queue)
        ;; jid -> [its antecedents inside the region not yet final, the deepest final one]
        wait   (volatile! {})]
    (doseq [d inside]
      (if (premise? d)
        (.add q [0 d])
        (doseq [jid (supports d)]
          (let [antes (antecedents jid)
                n     (count (into #{} (filter inside) antes))
                hi    (reduce (fn [^long m a] (if (contains? inside a) m (max m (long (depth-of a)))))
                              0 antes)]
            (if (zero? n) (.add q [(inc hi) d]) (vswap! wait assoc jid [n hi]))))))
    (loop [final {}]
      (if-let [[v d] (.poll q)]
        (if (contains? final d)
          (recur final)
          (do (doseq [jid (dependents d)
                      :let [[n hi] (get @wait jid)]
                      :when (and n (cites? (antecedents jid) d))]
                (let [hi (max (long hi) (long v))]
                  (if (== 1 (long n))
                    (do (vswap! wait dissoc jid) (.add q [(inc hi) (consequence jid)]))
                    (vswap! wait assoc jid [(dec (long n)) hi]))))
              (recur (assoc final d v))))
        (into {} (remove (fn [[d v]] (== (long v) (long (depth-of d))))) final)))))

;; ---- labelling ----------------------------------------------------------

(defn- lower-depth*
  "`state` with `datum` lowered to `depth` and the fall pushed down its consequences."
  [state datum depth]
  (let [nodes (:nodes state)
        justs (:justs state)]
    (reduce-kv (fn [s d v] (assoc-in s [:nodes d :depth] v))
               state
               (lowered-depths datum depth
                               #(get-in nodes [% :consequences])
                               #(get-in justs [% :antecedents])
                               #(get-in justs [% :consequence])
                               #(get-in nodes [% :depth] 0)))))

(defn- ensure* [state datum depth]
  (if-let [n (get-in state [:nodes datum])]
    (if (< (long depth) (long (:depth n 0)))
      (lower-depth* state datum depth)
      state)
    ;; A node the window **created** is noted as it is created, and that is the only
    ;; place the distinction exists: by the time the relabel that follows reads the
    ;; graph, a brand-new node and a stored one that has been OUT for a hundred settles
    ;; look identical — neither is believed, and both are about to be.  `touched-new` is
    ;; what separates them (see `revived`).
    (-> state
        (assoc-in [:nodes datum] {:datum datum :premise? false
                                  :depth depth :supports #{} :consequences #{}})
        (update :touched-new (fnil conj #{}) datum))))

(defn- valid?
  "Is justification `j` currently satisfied under the IN set `in`, the blocked set
  `blocked` and the `:void` forced set `void`?

  Four independent conditions: every antecedent believed, the rule believed when the
  informant is a rule handle, the justification not blocked by its rule's exception, and
  not void."
  [j in blocked void]
  (let [inf (:informant j)]
    (and (every? #(contains? in %) (:antecedents j))
         (or (not (integer? inf)) (contains? in inf))
         (not (contains? blocked (:id j)))
         (not (contains? void (:id j))))))

(defn- forced-set
  "`state`'s forced set `kind`."
  [state kind]
  (get-in state [:forced kind] #{}))

(defn- conferred-class
  "The defeat-class a valid justification confers on its consequence: its own
  strength, capped by the *weakest* of its antecedents' classes.

  A conclusion can be no stronger than the weakest thing it rests on — a bare rule
  over a merely-default premise concludes a default, and the same rule over
  known-true facts concludes a monotonic, which is correct: it *is* monotonically
  entailed.

  The **informant is not in the cap**.  A rule-handle informant is a condition of
  `valid?`, which is what makes retracting or defeating the rule withdraw everything it
  licensed — a *validity* role, not a ground, and `antecedents` never lists it.
  Capping on it as well would fold the rule's assumption strength into every
  conclusion — and a rule takes `:default` unless its own assertion says otherwise,
  exactly as a fact does, so that alone would put every datum an ordinary rule
  licensed at `:default`.  The strength a rule contributes
  is already carried by `:strength` on the justification (`provers/firing-strength`:
  `:default` for a `set/defaultRule` and for a guarded rule)."
  [j classes]
  (reduce (fn [c a] (strength/min c (get classes a :default)))
          (or (:strength j) :monotonic)
          (class-antecedents j)))

(defn- node-class
  "The defeat-class of an IN datum: the strongest support it has — its premise
  strength, and the class each currently-valid justification *confers* on it.

  A blocked justification is not valid, so it confers nothing: its strength is never
  read, exactly as if it were missing an antecedent."
  [state d in classes]
  (let [n       (get-in state [:nodes d])
        blocked (:blocked state #{})
        void    (forced-set state :void)
        prem  (when (:premise? n)
                (if (contains? (forced-set state :mono) d)
                  :monotonic
                  (:premise-strength n :default)))
        strs  (for [jid (:supports n)
                    :let [j (get-in state [:justs jid])]
                    :when (and j (valid? j in blocked void))]
                (conferred-class j classes))]
    (reduce strength/max :default (remove nil? (cons prem strs)))))

;; ---- region-local relabelling -------------------------------------------

(defn- affected-region
  "Every node whose label could change when `seeds` change: the forward closure over
  consequence justifications, seeds included.

  This is the claim locality rests on — a node's label is a function of its
  justifications' antecedents, so a node whose label can move is, by construction,
  reachable from whatever moved.  Everything outside the region is boundary: fixed,
  and never even looked at."
  [state seeds]
  (loop [seen #{}, stack (vec seeds)]
    (if (empty? stack)
      seen
      (let [d (peek stack), stack (pop stack)]
        (if (seen d)
          (recur seen stack)
          (recur (conj seen d)
                 (into stack (->> (get-in state [:nodes d :consequences])
                                  (map #(get-in state [:justs % :consequence]))
                                  (remove nil?)))))))))

(defn- region-fixpoint
  "Least fixpoint of IN over `region`, with `base` — the boundary's believed nodes —
  held fixed.

  Blocking invalidates a justification rather than a datum, so it is read through
  `valid?`: an excepted conclusion has lost a derivation, so the retraction sweep
  collects it (docs/exceptions.md, \"Garbage collection, not defeat\").

  Starting from *nothing believed inside the region* and only ever adding is what
  keeps support well-founded: a cycle within the region that has no ground outside
  it never enters, exactly as in a global least fixpoint.  And a least fixpoint is
  unique, so the result cannot depend on the order nodes are visited — which is why
  going local costs no order independence."
  [state region cands base]
  (let [blocked (:blocked state #{})
        void    (forced-set state :void)
        out     (forced-set state :out)
        justs   (:justs state)
        nodes   (:nodes state)
        seeded  (into base (filter #(and (get-in state [:nodes % :premise?])
                                         (not (contains? out %))))
                      region)]
    ;; Semi-naive worklist.  `valid?` is monotone in `in` (blocked is fixed and the
    ;; reserved `:out` slot is empty), so a justification only needs re-testing when one
    ;; of its antecedents newly enters `in` — reached through `:consequences`, the stored
    ;; inverse of the antecedent edge.  Each justification is retried once per antecedent
    ;; that fires, not once per round: O(region edges), not O(region depth × cands).  The
    ;; result is the same unique least fixpoint, so locality and order independence hold.
    (loop [in    seeded
           stack (vec cands)]
      (if (empty? stack)
        in
        (let [j (peek stack), stack (pop stack), c (:consequence j)]
          (if (and (contains? region c)
                   (not (contains? in c))
                   (not (contains? out c))
                   (valid? j in blocked void))
            (recur (conj in c)
                   (into stack (keep justs) (get-in nodes [c :consequences])))
            (recur in stack)))))))

(defn- region-classes
  "Defeat-classes for `region` under the IN set `in`, as a **least fixpoint**.

  The class equation is recursive: a justification confers no more than the weakest
  of its antecedents' classes, so a node's class depends on its antecedents'.  A
  single pass over the region would therefore be wrong, and wrong in a way that looks
  fine — visited in one order it reads a not-yet-computed antecedent as bottom and
  under-rates the conclusion; visited in another it reads a stale, too-high value and
  over-rates it.  Either way the answer would depend on the traversal order, which is
  exactly what order independence forbids.

  So: every in-region IN node starts at `:default`, the bottom of the lattice, and
  the equation is iterated to stability.  The operator is monotone in the class
  lattice (`strength/max` and `strength/min` both are, and raising an antecedent's
  class can only raise what a justification confers), and the iteration starts at
  bottom, so it converges to the *least* fixpoint.  A least fixpoint is unique —
  hence independent of visit order, and of the order the knowledge arrived in.

  Nodes outside the region are boundary: their stored class is read and held fixed,
  just as their labels are.  A boundary node whose class could move would have an
  antecedent in the region and would therefore be in the region itself, so holding
  them fixed loses nothing."
  [state region in]
  (let [nodes   (:nodes state)
        justs   (:justs state)
        base    (reduce (fn [m d] (if (contains? in d) m (dissoc m d)))
                        (:classes state {}) region)
        members (filterv #(contains? in %) region)
        init    (reduce (fn [m d] (assoc m d :default)) base members)]
    ;; Worklist over the same monotone operator.  A node's class rises only when an
    ;; antecedent's rises, so a member is recomputed only when a node it derives from
    ;; moves — reached through `:consequences`.  Starting every member at :default
    ;; (bottom), this converges to the same unique least fixpoint a round-robin sweep
    ;; would, in O(region edges) rather than O(region depth × members); the class lattice
    ;; has height one, so each member's class changes at most once.  Uniqueness of the
    ;; least fixpoint is what keeps the answer independent of the order nodes are visited.
    (loop [classes init
           stack   (vec members)]
      (if (empty? stack)
        ;; drop the :default entries **of this region**.  Every read of this map already
        ;; defaults an absent datum to :default (it is the lattice's bottom), so storing
        ;; them says nothing — and on a KB whose content is mostly :default, which a
        ;; common-sense KB's is, they are nearly the whole map.  `defeat-class` is the one
        ;; reader that did not default, and it decides OUT-vs-absent from `:in` instead,
        ;; which is what it was really using the entry's presence to mean.
        ;;
        ;; Only the members are filtered, because only they were seeded at :default here:
        ;; every entry outside the region came from an earlier relabel that applied this
        ;; same filter, so the map already holds no :default anywhere else.  Rebuilding
        ;; the whole map instead would make a region relabel O(classes) — proportional to
        ;; the KB rather than to the region, which is the one thing locality forbids, and
        ;; it is invisible until a KB carries enough non-:default content for the map to
        ;; be large (an import of Cyc's monotonic assertions is exactly that).
        (reduce (fn [m d] (if (= :default (get m d)) (dissoc m d) m)) classes members)
        (let [d   (peek stack)
              stk (pop stack)
              cls (node-class state d in classes)]
          (if (= cls (get classes d))
            (recur classes stk)
            (recur (assoc classes d cls)
                   (into stk (comp (keep justs)
                                   (map :consequence)
                                   (filter #(contains? in %)))
                         (get-in nodes [d :consequences])))))))))

(defn- note-epoch
  "`state` with `hs` recorded in the window's open epoch, the one the last `-touch-mark`
  opened: what `-touched-since` reads.  No epoch is open before the first mark of a
  window, so a window nobody marks records nothing twice."
  [state hs]
  (let [es (:epochs (:marks state))]
    (if (seq es)
      (update-in state [:marks :epochs (dec (count es))] into hs)
      state)))

(defn- relabel-region*
  "Recompute `:in` and the defeat-classes for `region`, holding every
  node outside it fixed.  Equivalent to a global relabel whenever the region is the
  affected closure of what changed, and proportional to the region rather than to
  the graph.

  Boundary classes need no recomputation either: a node's class depends on which of
  its justifications are valid and on those justifications' antecedents' classes, so
  a boundary node whose class could move would have an antecedent in the region — and
  would therefore be in the region itself."
  [state region]
  (let [old-in   (:in state #{})
        ;; the region members this window has not relabelled yet — their label right now
        ;; is their label before anything in the window moved, and that is the reading
        ;; `touched-in` wants.  A member relabelled earlier already contributed its own,
        ;; and the earlier one is the one that predates the window.
        fresh    (into #{} (remove (:touched state #{})) region)
        ;; only the justifications that can conclude something in the region matter
        cands    (into [] (comp (mapcat #(get-in state [:nodes % :supports] #{}))
                                (distinct)
                                (keep #(get-in state [:justs %])))
                       region)
        in       (region-fixpoint state region cands (set/difference old-in region))
        state    (assoc state :in in)]
    ;; Record the region as *touched*: a supporter's belief can flip only inside a
    ;; relabelled region, so the accumulated touched set is a superset of every handle
    ;; whose belief moved this settle — what `tax/refresh-beliefs` uses to skip a cache
    ;; no moved supporter touches.  Alongside
    ;; it, `touched-in` records which of them were **believed before** — so the two
    ;; together say which way each one moved, which the superset alone cannot.
    (-> state
        (assoc :classes (region-classes state region in))
        (update :touched (fnil into #{}) region)
        (note-epoch region)
        (update :touched-in (fnil into #{}) (filter old-in fresh)))))

(defn- resettle
  "Relabel the region affected by `seeds`."
  [state seeds]
  (relabel-region* state (affected-region state seeds)))

(defn- relabel-all*
  "Relabel every node.  No engine path calls it — the assert / retract / settle path
  relabels regions and a rebuild composes the region relabels its own adds run
  (`recovery/rebuild-tms`) — so this is the differential oracle's whole-graph operation, which
  is why both representations carry it (`relabel`).

  The blocked set is **reset to empty first**, and the supersession map with it.  Neither
  is stored — blocking is derived from the exception queries and supersession from the
  equality closure — so a whole-graph relabel can read neither back, and one that merged
  into whatever was there could only ever *add*: a block standing for a justification
  whose exception no longer holds, or a spelling held OUT for an equality nothing
  asserts.  That is the bug docs/taxonomy.md records for the transitive closures.  So
  this lands unblocked and unsuperseded, and a caller that wants either states the whole
  answer again (`set-blocked` and `supersede` both replace)."
  [state]
  (let [state (assoc state :blocked #{} :superseded {})]
    (relabel-region* state (set (keys (:nodes state))))))

(defn- premise* [state datum strength-kw]
  (-> (ensure* state datum 0)
      (assoc-in [:nodes datum :premise?] true)
      (assoc-in [:nodes datum :premise-strength] (or strength-kw :default))
      (resettle [datum])))

(defn- add-just* [state j]
  (let [{:keys [id consequence] :as just} (graph-just j)
        state (-> state
                  (assoc-in [:justs id] just)
                  (update-in [:nodes consequence :supports] conj id)
                  (as-> s (reduce-rests-on (fn [st a] (update-in st [:nodes a :consequences] conj id))
                                           s just)))
        in    (:in state #{})]
    ;; Fast path — a *redundant* justification changes nothing, so skip the region relabel.
    ;; If `consequence` is already believed and this justification confers no stronger a
    ;; defeat-class than it already holds (or is not even valid), then belief, groundability
    ;; and every downstream class are unmoved: an already-IN node feeds its consequences
    ;; identically whether it rests on one witness or two.  This is what collapses a
    ;; recursive/cyclic forward load from O(derived²) to O(derived).  The `affected-region`
    ;; walk that dominated it happened *per re-derivation* — every alternate path to an
    ;; existing fact relabelled the fact's whole growing forward closure.  Now the closure is
    ;; walked once, when the fact is *first* derived (a brand-new node has no consequences
    ;; yet, so its region is a singleton and the relabel is O(log n)); every later
    ;; re-derivation via another path is a no-op.  Any *real* change still takes the full
    ;; resettle — a newly-IN consequence, a class that actually rises, a blocked one
    ;; (all of which move belief or class and so must reconcile the region) — so belief is
    ;; identical to the per-conclusion relabel, only cheaper.
    ;;
    ;; The consequence still enters `touched`, and that is not a hedge against the fast
    ;; path being wrong about belief.  A caller reading the window asks a slightly larger
    ;; question — *is what I published about this datum still current* — and a second
    ;; witness moves the answer to that while moving no label: a reader of the window
    ;; that kept an answer about the datum keeps one that reads fewer reasons than the KB
    ;; holds.  Noting one handle is O(1) where
    ;; polling every standing pair for its support count is O(standing) per settle — which
    ;; `lein perf`'s `negation-arbitration` measures as a 19% worse growth ratio at 800
    ;; standing dilemmas, against no measurable change for this.  `touched-in` takes it too,
    ;; or the window would read as "newly believed" — but only when this window has not
    ;; relabelled it already, since an earlier relabel's answer is the one that predates
    ;; the window (`relabel-region*`'s `fresh`).
    (if (and (contains? in consequence)
             (or (not (valid? just in (:blocked state #{}) (forced-set state :void)))
                 (let [cls (get (:classes state) consequence :default)]
                   (= cls (strength/max cls (conferred-class just (:classes state)))))))
      (cond-> (-> state
                  (update :touched (fnil conj #{}) consequence)
                  (note-epoch [consequence]))
        (not (contains? (:touched state #{}) consequence))
        (update :touched-in (fnil conj #{}) consequence))
      (resettle state [consequence]))))

(defn- restrength-informant* [state informant strength]
  ;; The adjacency lists every justification a rule informs under the rule's node
  ;; (`reduce-rests-on` in `add-just*` — the link that makes retracting the rule withdraw
  ;; its conclusions), so the node's `:consequences` is the candidate set and nothing
  ;; scans the whole `:justs` map.  The informant filter keeps out a justification that
  ;; merely *uses* the rule's handle as an ordinary antecedent.
  (let [jids  (into []
                    (filter #(= informant (get-in state [:justs % :informant])))
                    (get-in state [:nodes informant :consequences] #{}))
        stale (into [] (remove #(= strength (get-in state [:justs % :strength]))) jids)]
    (if (empty? stale)
      state
      (-> (reduce (fn [s jid] (assoc-in s [:justs jid :strength] strength)) state stale)
          (resettle (mapv #(get-in state [:justs % :consequence]) stale))))))

;; ---- retraction ---------------------------------------------------------

(defn dissoc-all
  "`(apply dissoc m ks)` in one transient pass.  `apply dissoc` walks the map once per
  key with a full HAMT path copy each time, and `ks` here is the whole swept region of
  a retraction — which is a routine path rather than a rare one, since an `exceptWhen`
  block runs the sweep on ordinary fact arrival.

  Public because the dense network sweeps the same region out of the same shape: its
  `superseded` is the one persistent map it keeps (docs/density.md), so
  `vaelii.impl.dense-jtms` drops a swept region from it through this rather than
  through a second copy of the reasoning."
  [m ks]
  (if (seq ks) (persistent! (reduce dissoc! (transient (or m {})) ks)) (or m {})))

(defn- disj-all
  "`(apply disj s ks)` in one transient pass, for the same reason as `dissoc-all`."
  [st ks]
  (if (seq ks) (persistent! (reduce disj! (transient (or st #{})) ks)) (or st #{})))

(defn- unlink-just
  "`state` without justification `jid`: out of `:justs`, off its consequence's
  `:supports` and off every `:consequences` it was listed under.  No relabel."
  [state jid]
  (let [{:keys [consequence] :as j} (get-in state [:justs jid])]
    (-> state
        (update :justs dissoc jid)
        (update-in [:nodes consequence :supports] #(disj (or % #{}) jid))
        (as-> s (reduce-rests-on (fn [s2 a]
                                   (update-in s2 [:nodes a :consequences]
                                              #(disj (or % #{}) jid)))
                                 s j)))))

(defn- redepth*
  "`state` with the depths re-solved over the consequence closure of those `seeds` still
  in the graph: the nodes that lost a premise mark or a justification, whose depth can
  rise.  No seed left, no walk."
  [state seeds]
  (let [nodes (:nodes state)
        live  (filterv #(contains? nodes %) seeds)]
    (if (empty? live)
      state
      (let [justs (:justs state)]
        (reduce-kv (fn [s d v] (assoc-in s [:nodes d :depth] v))
                   state
                   (region-depths (affected-region state live)
                                  #(get-in nodes [% :premise?])
                                  #(get-in nodes [% :supports])
                                  #(get-in nodes [% :consequences])
                                  #(get-in justs [% :antecedents])
                                  #(get-in justs [% :consequence])
                                  #(get-in nodes [% :depth] 0)))))))

(defn- sweep*
  "SWEEP: collect the datums in `suspects` that are no longer derivable (OUT) and are
  not premises, delete them and every
  justification touching them, and return
  [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]
  :removed-supports [[consequence informant]...]}], the last read before the unlink and
  absent when nothing was removed.
  A survivor that lost a justification, and each of `raised`, has its depth re-solved
  (`redepth*`).

  Nothing forces a datum OUT, so OUT is having no valid derivation.  Blocking
  suppresses a derivation (see `region-fixpoint`), which is what makes this the garbage
  collector for an excepted conclusion as well as for a retracted one —
  docs/exceptions.md, \"Garbage collection, not defeat\".

  The caller must have relabelled `suspects` already: this reads `:in`, it does not
  compute it.

  Like every other operation here it is **region-local**: the justifications to tear
  down are read off the dead nodes' own `:supports` / `:consequences`, never found by
  scanning `:justs`.  That matters because `exceptWhen` blocks a justification on
  ordinary fact arrival, so sweeping is routine rather than a retraction-only path,
  and a sweep that scanned the whole graph would make a run of them quadratic."
  [state suspects raised]
  (let [in       (:in state #{})
        dead     (filter (fn [d]
                           (and (not (get-in state [:nodes d :premise?]))
                                (not (contains? in d))))
                         suspects)
        ;; The justifications that touch a dead datum are exactly the ones its node
        ;; already names: `:supports` (it is their consequence) and `:consequences`
        ;; (it is one of their antecedents, or their rule).  Reading the two
        ;; adjacency sets keeps this proportional to the swept region — scanning
        ;; `:justs` instead would make every sweep cost the whole graph, which is the
        ;; locality invariant this module is built on (docs/nmtms.md).
        dead-jids (into #{}
                        (comp (mapcat (fn [d] (concat (get-in state [:nodes d :supports] #{})
                                                      (get-in state [:nodes d :consequences] #{}))))
                              ;; an adjacency set names a justification; only a live one
                              ;; is ours to remove or to report
                              (filter #(contains? (:justs state) %)))
                        dead)
        removed-justifications (remove #(= :premise (get-in state [:justs % :informant])) dead-jids)
        removed-supports (mapv #(let [j (get-in state [:justs %])] [(:consequence j) (:informant j)])
                               removed-justifications)
        ;; the swept datums, as handles.  The caller fetches each one's record from the
        ;; store before deleting it — the store is where a sentex lives, and a copy kept
        ;; here would be a second one to keep in step (and, on a paging backend, would
        ;; hold every record resident).
        removed-sentexes   (vec dead)
        ;; the survivors among these lost a justification
        lost  (keep #(get-in state [:justs % :consequence]) dead-jids)
        ;; 5. apply removals to the graph
        state (reduce unlink-just state dead-jids)
        state (update state :nodes dissoc-all dead)
        state (update state :classes dissoc-all dead)
        ;; a block names a justification, so a swept justification must lose its
        ;; block too — an id left behind would be a stale block waiting to be
        ;; reapplied to whatever reuses it
        state (update state :blocked disj-all dead-jids)
        ;; ...and a forced membership names a justification or a datum, for the same reason
        state (-> state
                  (update-in [:forced :void] disj-all dead-jids)
                  (update-in [:forced :mono] disj-all dead)
                  (update-in [:forced :out] disj-all dead))
        ;; a supersession names a datum, so a swept datum must lose it too — an entry
        ;; left behind would hold a future handle OUT for a merge that is long gone
        state (update state :superseded dissoc-all dead)
        ;; the swept nodes were OUT, so dropping them cannot move any survivor's label —
        ;; only the bookkeeping set needs the removal
        state (update state :in disj-all dead)
        state (redepth* state (into (vec raised) lost))]
    [state (cond-> {:removed-sentexes removed-sentexes
                    :removed-justifications removed-justifications}
             (seq removed-supports) (assoc :removed-supports removed-supports))]))

(defn- retract-known*
  [state datum]
  (let [;; 1. drop premise support for datum
        state    (-> state
                     (assoc-in [:nodes datum :premise?] false)
                     (update-in [:nodes datum] dissoc :premise-strength))
        ;; 2. MARK: the affected closure — also exactly the region to relabel, so
        ;;    marking and relabelling walk the graph once between them
        suspects (affected-region state [datum])
        ;; 3. relabel that region with datum no longer a premise (SAVE happens
        ;;    implicitly: a suspect with a surviving valid justification stays IN)
        state    (relabel-region* state suspects)]
    ;; 4-5. sweep what the retraction solely supported, and apply the removals
    (sweep* state suspects [datum])))

(defn- drop-just*
  "Return [new-state removals] with justification `jid` gone: unlinked, unblocked, its
  consequence's region relabelled and then swept, so a conclusion it alone grounded
  leaves with it.  `jid` itself is not among the reported removals — the caller asked
  for it by name, and is listed only in `:removed-supports`.  An unknown `jid` is a no-op."
  [state jid]
  (if-let [c (get-in state [:justs jid :consequence])]
    (let [inf      (get-in state [:justs jid :informant])
          state    (-> state
                       (unlink-just jid)
                       (update :blocked disj-all [jid])
                       (update-in [:forced :void] disj-all [jid]))
          suspects (affected-region state [c])
          [state r] (sweep* (relabel-region* state suspects) suspects [c])]
      [state (update r :removed-supports (fnil conj []) [c inf])])
    [state {:removed-sentexes [] :removed-justifications []}]))

(defn- suspend-premise*
  [state datum]
  (if-not (get-in state [:nodes datum])
    state
    (let [state (-> state
                    (assoc-in [:nodes datum :premise?] false)
                    (update-in [:nodes datum] dissoc :premise-strength))]
      (-> (relabel-region* state (affected-region state [datum]))
          (redepth* [datum])))))

(defn- retract*
  "Return [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]}].

  An unknown datum is a no-op: retraction is idempotent, and the test is what keeps it
  so.  Reaching `retract-known*` regardless would have `assoc-in` *create* the node it
  was asked to retract; the sweep then collects the phantom (not a premise, not
  IN) and the result claims a removal that never happened."
  [state datum]
  (if-not (get-in state [:nodes datum])
    [state {:removed-sentexes [] :removed-justifications []}]
    (retract-known* state datum)))

(defn- set-blocked*
  [state jids]
  (let [jids    (set jids)
        was     (:blocked state #{})
        ;; only the justifications whose blocked status actually MOVED can change a
        ;; label, so they alone seed the region — the ones blocked in both sets are
        ;; already accounted for in the current labels
        changed (set/union (set/difference jids was) (set/difference was jids))]
    (if (empty? changed)
      state
      (-> state
          (assoc :blocked jids)
          (resettle (keep #(get-in state [:justs % :consequence]) changed))))))

(defn- set-forced*
  "`state` with each of `xs` added to forced set `kind` (`on?`) or taken out of it, and
  the region of the members that moved relabelled: the datums with a node for `:mono`
  and `:out`, the consequences of the stored justifications for `:void`."
  [state kind xs on?]
  (let [cur   (forced-set state kind)
        moved (into [] (comp (distinct) (filter #(not= (boolean on?) (contains? cur %)))) xs)]
    (if (empty? moved)
      state
      (let [region (affected-region state (if (= :void kind)
                                            (keep #(get-in state [:justs % :consequence]) moved)
                                            (filter #(get-in state [:nodes %]) moved)))
            was    (filterv #(contains? (:in state #{}) %) region)
            state  (-> state
                       (assoc-in [:forced kind] (if on? (into cur moved) (disj-all cur moved)))
                       (relabel-region* region))]
        ;; what the change took OUT, for `revived` to re-seed if it comes back this window
        (update state :touched-out (fnil into #{}) (remove #(contains? (:in state) %)) was)))))

(defn- swap-with-result!
  "Atomically apply `f` — a pure `state -> [state' result]` fn — to atom `a`,
  retrying on contention exactly as `swap!` does, and return the result.

  Do not reach for deref-then-`reset!` here.  It silently *discards* any concurrent
  `swap!` landing between the two, and under incidental concurrency (a REPL thread
  beside the web handler) what that loses is premises and justifications, not
  staleness.  Atomicity here makes concurrent operations compose; it does not make
  interleaved KB operations semantically serializable — the engine's contract is still
  one writer (docs/storage.md)."
  [a f]
  (loop []
    (let [old @a
          [new result] (f old)]
      (if (compare-and-set! a old new)
        result
        (recur)))))

;; ---- the representation protocol --------------------------------------------
;; The `Tms` protocol lives in `vaelii.impl.jtms-protocol` — both this reference
;; network and `vaelii.impl.dense-jtms` sit behind it, and it is too large to
;; instrument (scripts/coverage.sh).  Its methods are `:refer`red above; the
;; public façade over them is at the foot of this file.

;; ---- the reference implementation: one atom, one persistent map ---------

(defn- ref-view
  "The state map a `RefTms` read answers from, given its `hold` and `state` fields: the map
  the open hold took when it opened, for a thread other than its owner that
  `observe/reads-held-in?` says reads it, and otherwise the live map.

  A live read takes the registry before and after the map, and reads again when a hold
  opened or closed in between: a settle mutates the network only while its hold is open,
  so a map read with no hold open on either side is one no settle was deciding."
  [^AtomicReference hold ^clojure.lang.Atom state]
  (let [st (.get hold)]
    (if (and st (identical? (:owner (:hold st)) (Thread/currentThread)))
      @state
      (loop []
        (let [m  (observe/registry)
              st (.get hold)]
          (if (and st (observe/reads-held-in? m (:hold st)))
            (:state st)
            (let [s @state]
              (if (identical? m (observe/registry)) s (recur)))))))))

(deftype RefTms [^clojure.lang.Atom state ^AtomicReference hold]
  ;; `@tms` yields the state map, which is what the JTMS tests and the RAM benches
  ;; read.  It is the live map, not a copy — this implementation *is* the canonical
  ;; shape, so there is nothing to materialize.
  ;;
  ;; `hold` is nil, or `{:hold h :state s}` while hold `h` is open: `s` is the state map
  ;; when it opened, and every read below answers from `s` to a thread that reads `h`'s
  ;; belief.  The map is persistent, so keeping it copies nothing.
  clojure.lang.IDeref
  (deref [_] @state)
  Tms
  (-believed? [_ datum]
    (let [s (ref-view hold state)]
      (and (contains? (:in s #{}) datum)
           (not (contains? (:superseded s {}) datum)))))
  (-believed [_] (let [s (ref-view hold state)] (seq (remove (:superseded s {}) (:in s #{})))))
  (-any-node?   [_] (boolean (seq (:nodes (ref-view hold state)))))
  (-any-belief? [_] (let [s (ref-view hold state)]
                      (boolean (first (remove (:superseded s {}) (:in s #{}))))))
  (-node? [_ datum] (contains? (:nodes (ref-view hold state)) datum))
  (-datums [_] (keys (:nodes (ref-view hold state))))
  (-depth [_ datum] (get-in (ref-view hold state) [:nodes datum :depth] 0))
  (-premise? [_ datum] (boolean (get-in (ref-view hold state) [:nodes datum :premise?])))
  (-premise-strength [_ datum] (get-in (ref-view hold state) [:nodes datum :premise-strength]))
  (-defeat-class [_ datum]
    (let [s (ref-view hold state)]
      (when (contains? (:in s) datum) (get (:classes s) datum :default))))
  (-blocked [_] (:blocked (ref-view hold state) #{}))
  (-superseded [_] (:superseded (ref-view hold state) {}))
  (-touched [_] (:touched @state #{}))
  (-touched-in [_] (:touched-in @state #{}))
  (-touched-new [_] (:touched-new @state #{}))
  (-touched-out [_] (:touched-out @state #{}))
  (-reset-touched [_]
    (swap! state #(-> %
                      (assoc :touched #{} :touched-in #{} :touched-new #{} :touched-out #{})
                      (update :marks (fn [m] {:gen (inc (:gen m 0)) :epochs []}))))
    nil)
  (-touch-mark [_]
    ;; an empty open epoch is shared, as the dense network shares it
    (let [m (:marks (swap! state update :marks
                           (fn [m] (let [m (or m {:gen 0 :epochs []})
                                         e (peek (:epochs m))]
                                     (if (and e (empty? e)) m (update m :epochs conj #{}))))))]
      [(:gen m) (dec (count (:epochs m)))]))
  (-touched-since [_ mark]
    (let [st @state
          {:keys [gen epochs]} (:marks st)
          [g i] mark]
      (if (and mark (= g gen) (< i (count epochs)))
        (into #{} cat (subvec epochs i))
        (:touched st #{}))))
  (-supports [_ datum] (get-in (ref-view hold state) [:nodes datum :supports] #{}))
  (-dependents [_ datum] (get-in (ref-view hold state) [:nodes datum :consequences] #{}))
  (-justification [_ jid] (get-in (ref-view hold state) [:justs jid]))
  (-justifications [_] (vals (:justs (ref-view hold state))))
  (-ensure-node [_ datum depth]
    ;; skip the swap when it would write back a value-identical map — a node already
    ;; present at a depth no higher than `depth` is exactly what `ensure*` leaves
    ;; (`min` keeps the stored depth); this runs once per placement, so most calls
    ;; are that no-op.  Sound under the single-writer contract: nothing moves the
    ;; node between the read and the skipped write.
    (let [n (when observe/*chain-fast-paths* (get (:nodes @state) datum))]
      (when (or (nil? n) (< (long depth) (long (:depth n 0))))
        (swap! state ensure* datum depth)))
    nil)
  (-add-premise [_ datum strength] (swap! state premise* datum strength) nil)
  (-suspend-premise [_ datum] (swap! state suspend-premise* datum) nil)
  (-add-justification [_ just] (swap! state add-just* just) nil)
  (-restrength-informant [_ informant strength]
    (swap! state restrength-informant* informant strength) nil)
  (-forced? [_ kind x] (contains? (forced-set (ref-view hold state) kind) x))
  (-forced-members [_ kind] (forced-set (ref-view hold state) kind))
  (-set-forced [_ kind xs on?] (swap! state set-forced* kind xs on?) nil)
  (-relabel [_] (swap! state relabel-all*) nil)
  (-set-blocked [_ jids] (swap! state set-blocked* jids) nil)
  (-supersede [_ m] (swap! state assoc :superseded (if (map? m) m (into {} m))) nil)
  (-retract [_ datum] (swap-with-result! state #(retract* % datum)))
  (-sweep [_ seeds] (swap-with-result! state (fn [s] (sweep* s (affected-region s seeds) nil))))
  (-drop-justification [_ jid] (swap-with-result! state #(drop-just* % jid)))
  (-snapshot [_] (dissoc @state :marks))
  (-hold [_ h]
    ;; the writer is the one thread that swaps `state`, so the map read here is the one
    ;; every relabel after this call starts from
    (.compareAndSet hold nil {:hold h :state @state}))
  (-release [_ h]
    (let [st (.get hold)]
      (when (identical? h (:hold st)) (.compareAndSet hold st nil)))
    nil)
  (-held [_] (:hold (.get hold))))

(defn create-tms
  "A fresh, empty truth-maintenance network — the reference implementation.

  `:in` is the believed set and the authority on belief — nodes carry no label of
  their own, so there is no second copy to drift.  It is maintained region-locally.

  `:blocked` is the set of justification ids currently blocked by their rule's
  exception; it starts empty and only a caller that has evaluated the exceptions can
  fill it.

  (Rules live in the stores as sentexes, not here.)"
  []
  (->RefTms (atom {:nodes {} :justs {} :blocked #{} :superseded {}
                   :forced {:mono #{} :out #{} :void #{}}
                   :classes {} :in #{}
                   :touched #{} :touched-in #{} :touched-new #{} :touched-out #{}})
            (AtomicReference. nil)))

;; ---- public API ---------------------------------------------------------
;;
;; Thin dispatch onto the protocol.  Every engine path calls these, never a protocol
;; method directly, so the representation a KB was opened with is invisible above
;; this line.

(defn in?
  "Is `datum` believed?  Structural support minus supersession: a datum the equality
  layer has displaced keeps its place in the fixpoint (its twin is justified by it)
  but is not believed, so it stops matching and stops answering queries."
  [tms datum] (-believed? tms datum))

(defn network-in?
  "Is `datum` IN in the network, a superseded spelling included?  The families
  `chain/place-nogoods!` places detect their nogoods over this label, so a nogood with a
  superseded member keeps its placement (docs/nmtms.md)."
  [tms datum] (some? (-defeat-class tms datum)))

(defn depth  [tms datum] (-depth tms datum))
(defn known-datum?
  "Does the TMS hold a node for `datum`?  False for an **inert** sentex
  (`core/assert-inert`) — stored and indexed but never a TMS datum — which is how
  `retract!` tells a belief-bearing retraction from a direct teardown."
  [tms datum] (-node? tms datum))
(defn in-datums [tms] (-believed tms))
(defn any-node?   [tms] (-any-node? tms))
(defn any-belief? [tms] (-any-belief? tms))
(defn premise? [tms datum] (-premise? tms datum))
(defn premise-strength [tms datum] (-premise-strength tms datum))
(defn datums [tms] (-datums tms))

(defn defeat-class
  "The current defeat-class of an IN datum (monotonic / default), or nil
  when the datum is OUT.  Valid after `relabel`.

  `:classes` holds only the datums *above* the lattice's bottom, so IN-ness is what
  separates \"OUT, hence no class\" from \"IN at the default class\".  An entry's mere
  presence cannot carry both, since only one of them is information."
  [tms datum] (-defeat-class tms datum))

(defn touched
  "The datums whose region has been relabelled since the last `reset-touched!` — a
  superset of every datum whose belief could have flipped in that window.  `settle`
  reads it to tell `tax/refresh-beliefs` which handles moved, so a cache no moved
  supporter touches is skipped.

  Plus the datums a **redundant** justification landed on, which is the one entry here
  whose belief provably did *not* move: the window is read as \"what I published about
  this datum may be out of date\", and a second witness for an already-believed
  conclusion moves that without moving a label (`add-just*` says why the alternative is
  worse).  Every consumer reads a superset, so an extra handle costs a re-derivation and
  never an answer."
  [tms] (-touched tms))

(defn touched-in
  "The subset of `touched` whose label was **IN** when this window first relabelled it.
  With `touched` and current belief this set gives the label delta: a datum in `touched`
  and IN now but not here came *in*, and one here that is OUT now went *out*.  The
  superset alone cannot say which, since most of a relabelled region does not move.  A
  superseded spelling keeps an IN label and is not believed (`in?`), so `settle-finish`
  drops the spellings superseded when the window opened before it reports belief.

  \"When first relabelled\" is what makes it a reading from before the window rather
  than from part-way through it: a datum relabelled twice keeps the earlier answer."
  [tms] (-touched-in tms))

(defn touched-new
  "The datums whose **node this window created** — the ones that had no label to move
  because they had no node.  `touched-in` cannot say this: a brand-new datum and a
  stored one that has been OUT since the settle before both read as \"not believed when
  the window opened\", and they are the two halves `revived` has to keep apart."
  [tms] (-touched-new tms))

(defn revived
  "The datums this window brought **back**: relabelled, believed now, not believed when
  the window opened, and already in the graph before it opened.

  A revival is the one belief move nothing downstream of it has seen.  A datum arriving
  is chained from as it arrives; a datum losing belief withdraws its conclusions through
  the justifications that name it.  A datum that goes OUT and comes back has neither —
  no arrival to chain from, no justification to withdraw — and while it was OUT the
  belief-filtered matcher hid it, so a partner that arrived meanwhile joined against
  nothing.  `settle` re-seeds these onto the agenda for exactly that reason.

  The three window sets between them are the whole belief delta, and this is the corner
  of it that costs work rather than a report: `touched` minus `touched-in` is what
  gained belief, and minus `touched-new` is the part of *that* which is not a datum the
  writer has already chained from.  A datum a forced-set change took OUT inside the
  window (`-touched-out`) is one too when it is believed again by the window's end,
  whether or not it was believed when the window opened: a partner arriving while it
  was OUT joined against nothing.

  The two-arity takes `touched` as the caller already read it — `settle` reads the
  region once per pass and hands the value to everything in the pass that wants it,
  since the dense network materializes a fresh set on every read."
  ([tms] (revived tms (touched tms)))
  ([tms t]
   (if (empty? t)
     #{}
     (let [was-in (touched-in tms)
           born   (touched-new tms)]
       (-> #{}
           (into (comp (remove was-in) (remove born) (filter #(in? tms %))) t)
           (into (filter #(in? tms %)) (-touched-out tms)))))))

(defn reset-touched!
  "Clear the accumulated touched sets (see `touched` / `touched-in` / `touched-new`).
  `settle` clears them once it has read them, at the *end* — so the window a caller sees
  spans everything since the last settle finished, which for `edit` is the whole
  deferred batch and its one settle rather than the settle alone."
  [tms] (-reset-touched tms) tms)

(defn touch-mark
  "A mark of this point in the touched window, for a reader that asks the window more
  than once in it: `touched-since` answers what was recorded after it.  Each reader keeps
  its own mark."
  [tms] (-touch-mark tms))

(defn touched-since
  "The datums `touched` recorded after `mark` (`touch-mark`): a datum relabelled again
  since the mark is in it although `touched` held it already, which a set difference over
  `touched` would drop.  A superset of what moved since the mark, as `touched` is of what
  moved in the window.  The whole of `touched` for a mark the window outdated
  (`reset-touched!`) or a nil one."
  [tms mark] (-touched-since tms mark))

(defn superseded
  "The `datum -> reason` map of spellings an equality merge has displaced."
  [tms] (-superseded tms))

(defn superseded? [tms datum] (contains? (-superseded tms) datum))

(defn supersession
  "Why `datum` is superseded — the representative that displaced it — or nil."
  [tms datum] (get (-superseded tms) datum))

(defn supersede
  "**Replace** the superseded map with `m` (`{datum reason}`).

  Replace, not accumulate, for the same reason `set-blocked` replaces: the caller
  recomputes the whole answer from the current equality closure each settle, so a
  supersession cannot outlive the merge that caused it and belief cannot depend on
  the order the merges arrived in.

  No relabel: supersession does not enter the fixpoint (see the namespace docstring),
  it only subtracts from what `in?` reports, so there is no region to recompute."
  [tms m] (moving (-supersede tms m)) tms)

(defn supports
  "Justification ids that conclude `datum` (its supporting justifications)."
  [tms datum] (-supports tms datum))

(defn dependents
  "Justification ids that use `datum` as an antecedent (or a defeater)."
  [tms datum] (-dependents tms datum))

(defn justification [tms jid] (-justification tms jid))
(defn justifications [tms] (-justifications tms))

(defn- indexed
  "`coll` as something `nth` reaches in constant time — itself when it already is one
  (an antecedent list is stored as a vector), a vector otherwise."
  ^clojure.lang.Indexed [coll]
  (if (instance? clojure.lang.Indexed coll) coll (vec coll)))

(defn- covered?
  "Is every one of `a`'s `na` elements among `b`'s `nb`? — the subset half, by index
  rather than by seq, so nothing is allocated to answer it."
  [^clojure.lang.Indexed a ^long na ^clojure.lang.Indexed b ^long nb]
  (loop [i 0]
    (if (>= i na)
      true
      (let [x (.nth a i)]
        (if (loop [j 0]
              (cond (>= j nb)          false
                    (= x (.nth b j))   true
                    :else              (recur (inc j))))
          (recur (inc i))
          false)))))

(defn- same-antecedents?
  "Do `a` and `b` name the same antecedents *as sets* — same members, order and
  duplicates immaterial?  Mutual containment, which is that definition read directly,
  and it allocates nothing where `(= (set a) (set b))` allocated two hash sets.

  The allocation matters because of **where this is asked**.  A conclusion re-derived
  by k witnesses is checked once per witness against every justification it holds so
  far, so the comparison runs Θ(k²) times per conclusion across a run.  Measured on the
  W4 join pyramid (10k, 65k derived facts): 7.7M comparisons for 429k justifications
  stored, and building those sets was the single largest line in the profile.

  An antecedent list is two to five handles, so a scan beats hashing one of them, and
  a mismatch — the common case, since a fresh witness is a fresh justification — ends
  at the first member `b` does not hold."
  [a b]
  (let [av (indexed a) na (count a)
        bv (indexed b) nb (count b)]
    (and (covered? av na bv nb)
         (covered? bv nb av na))))

(def ^:dynamic *dedup-cache*
  "`{:tms tms :m mutable-HashMap-of-consequence→HashSet-of-just-keys}`, or nil — the
  default, and `has-justification?` scans `-supports` as always.

  A **run-scoped index over the dedup question**.  A conclusion re-derived by k
  witnesses is asked about once per witness, and each ask scans every justification it
  already holds — Θ(k²) `same-antecedents?` comparisons per conclusion across a forward
  run, with a `-justification` fetch apiece (the W4 join pyramid at 1k: ~430k firings
  over ~66k conclusions, and the scan is the largest line in the profile).  Bound by
  `chain/chain` for the length of a run, the first ask per conclusion builds its key
  set from `-supports` once and every later ask is one hash probe.

  The binding carries the TMS it was built beside, and `dedup-cache-for` hands the
  map out only to that TMS: a nested run over a *second* KB (legal from a
  `:on-progress` callback) reaches these fns with the first KB's binding still in
  force, and handle spaces overlap, so an unscoped reuse would answer one KB's dedup
  question from the other's supports.  Anything but the owning TMS bypasses to the
  reference scan.

  Justification *existence* is structural, not belief: a label flip adds and removes
  nothing here, so no entry goes stale by belief moving — only by a justification
  being **removed**, which reaches the graph on exactly two paths (`retract!`,
  `sweep!`), and both clear the cache wholesale.  `add-justification` extends the
  entry it passes through, so a bound cache never disagrees with the graph it mirrors.
  The keys are handle-content — no canonicalization — so there is no canon stamp to
  carry (`observe/*handle-cache*`, which has one, says what that kind of stamp is
  for; the `:tms` slot here is identity, not currency)."
  nil)

(defn- dedup-cache-for
  "The bound dedup index's map when it mirrors `tms`, else nil (see `*dedup-cache*`)."
  ^java.util.HashMap [tms]
  (let [c *dedup-cache*]
    (when (and c (identical? (:tms c) tms)) (:m c))))

(defmacro with-dedup-cache
  "Run `body` with the justification dedup index engaged for `tms`; an outer cache
  over the *same* TMS is reused rather than shadowed — the composition
  `observe/with-handle-cache` makes — and one over another TMS is shadowed by a
  fresh map.  A no-op when `observe/*chain-fast-paths*` is bound false — the
  reference lever `chain_fast_paths_test` pulls."
  [tms & body]
  `(let [tms# ~tms]
     (binding [*dedup-cache* (or (let [c# *dedup-cache*]
                                   (when (and c# (identical? (:tms c#) tms#)) c#))
                                 (when observe/*chain-fast-paths*
                                   {:tms tms# :m (java.util.HashMap.)}))]
       ~@body)))

;; Both key shapes normalize fixnum boxing to Long: the HashMap/HashSet compare with
;; Java equals, where Integer 7 ≠ Long 7, and the reference scan compares with `=`,
;; where they are equal — every handle producer allocates Longs today, but the cache
;; is where a future Integer would silently split a key, so the coercion lives here
;; rather than as a convention.
(defn- unbox ^Object [x] (if (int? x) (long x) x))

(defn- just-key
  "The content `has-justification?` deduplicates on — the informant, the antecedents
  **as a set**, `same-antecedents?`'s judgement (order and duplicates immaterial) frozen
  into one hashable value, and the subsumptions.  A rule-handle informant is dropped
  from the set: a stored record never lists it there, and a firing's handle list does.
  Two firings that pair the same facts with different literals can rest on one
  antecedent set, and the subsumptions keep them two (`late_route_test`)."
  [informant antecedents subsumptions]
  (let [inf (unbox informant)
        s   (set antecedents)]
    [inf (if (integer? inf) (disj s inf) s) (not-empty subsumptions)]))

(defn- dedup-keys
  "The cached key set for `consequence`, built from its supports on the first ask."
  ^java.util.HashSet [tms ^java.util.Map cache consequence]
  (let [ck (unbox consequence)]
    (or (.get cache ck)
        (let [s (java.util.HashSet.)]
          (doseq [jid (-supports tms consequence)]
            (when-let [j (-justification tms jid)]
              (.add s (just-key (:informant j) (:antecedents j) (:subsumptions j)))))
          (.put cache ck s)
          s))))

(defn justification-key
  "The dedup key of a justification from `informant` over `antecedents` with
  `subsumptions`, a set or nil — `just-key`, for a caller that asks
  `has-justification?` and then adds the justification, and so would otherwise build the
  same set twice."
  ([informant antecedents] (just-key informant antecedents nil))
  ([informant antecedents subsumptions] (just-key informant antecedents subsumptions)))

(defn has-justification?
  "Is there already a support for `consequence` from `informant` over exactly these
  antecedents (as a set), with the same subsumptions?  Guards against duplicate
  justifications.  Answered from the dedup index when one is bound for this TMS — the
  same judgement, one hash probe — and by the supports scan otherwise.  `k`, when given,
  is `justification-key` of the same informant and antecedents, and carries the
  subsumptions; without it the question is about a justification with none."
  ([tms informant antecedents consequence]
   (has-justification? tms informant antecedents consequence nil))
  ([tms informant antecedents consequence k]
   (if-let [^java.util.Map cache (dedup-cache-for tms)]
     (.contains (dedup-keys tms cache consequence) (or k (just-key informant antecedents nil)))
     (let [antes (without-informant informant antecedents)
           subs  (when k (nth k 2))]
       (boolean
        (some (fn [jid]
                (let [j (-justification tms jid)]
                  (and (= informant (:informant j))
                       (= subs (:subsumptions j))
                       (same-antecedents? antes (:antecedents j)))))
              (-supports tms consequence)))))))

;; Every mutating entry point below wraps its mutation in `moving`, which moves the
;; change clock a cache derived from *belief* stamps itself with before and after it.

(defn ensure-node [tms datum depth] (moving (-ensure-node tms datum depth)) datum)

(defn add-premise
  "Add `datum` as a premise at `strength` (default :default)."
  ([tms datum] (add-premise tms datum :default))
  ([tms datum strength-kw]
   (moving (-add-premise tms datum (or strength-kw :default)))
   datum))

(defn suspend-premise
  "Drop `datum`'s premise mark and relabel its region without sweeping: a retraction's
  effect on belief, undone by `add-premise` at the same strength.  Unknown datums no-op.
  Bare, not `!`: the node and its justifications stay.  `core/preview` is the caller
  (docs/nmtms.md)."
  [tms datum] (moving (-suspend-premise tms datum)) datum)

(defn add-justification
  "Add `just` to the network.  `k`, when given, is its `justification-key`, already built
  for the `has-justification?` that guarded the add."
  ([tms just] (add-justification tms just nil))
  ([tms just k]
   (moving (-add-justification tms just))
   ;; keep a bound dedup index in step: extend the one entry this justification lands
   ;; in, when that entry has been built (an absent entry rebuilds from `-supports`,
   ;; which now includes this justification, so absence needs nothing)
   (when-let [^java.util.Map cache (dedup-cache-for tms)]
     (when-let [^java.util.HashSet ks (.get cache (unbox (:consequence just)))]
       (.add ks (or k (just-key (:informant just) (:antecedents just) (:subsumptions just))))))
   just))

(defn restrength-informant
  "Set `strength` as the rule-contribution slot of every justification whose informant
  is `informant`, and relabel the region their consequences span.

  A justification's `:strength` is the *rule's* contribution, read off the record at
  fire time (`chain/rule-view-of`) — a cache of `provers/firing-strength`.  When that
  moves (a re-asserted rule's defeasibility resolves strict, or an `exceptWhen` arrives
  or leaves: `special/restrength-firings!`),
  the cache must move with it, or belief keeps the arrival order the slot resolution
  exists to remove: the same rule stated defeasible-then-strict and strict-then-defeasible
  would confer two different classes on conclusions already derived.  The antecedent half
  of `conferred-class` is already read live at labelling time, so this one scalar is the
  only stored copy — updated here, then relabelled through the full affected region,
  since a class that rises can flip defeat decisions anywhere in the consumer ancestor set."
  [tms informant strength]
  (moving (-restrength-informant tms informant strength))
  tms)

(defn forced?
  "Is `x` a member of forced set `kind`?"
  [tms kind x] (-forced? tms kind x))

(defn forced-members
  "Every member of forced set `kind`, as a set."
  [tms kind] (-forced-members tms kind))

(defn set-forced
  "Add each of `xs` to forced set `kind` (`on?` true) or take it out, and relabel the
  region the members that moved reach.  `:mono` names premises whose class is
  `:monotonic` whatever strength they carry, `:out` datums never IN, and `:void`
  justifications that support nothing.  A member may be written before its node or its
  justification exists, so the element never holds a label the set rules out."
  [tms kind xs on?]
  (when (seq xs) (moving (-set-forced tms kind xs on?)))
  tms)

(defn premise-class
  "The class `datum`'s premise mark confers: `:monotonic` for a `:mono` member, its
  premise strength otherwise, nil for a datum that is no premise."
  [tms datum]
  (when-let [s (premise-strength tms datum)]
    (if (forced? tms :mono datum) :monotonic s)))

(defn relabel
  "Recompute *every* node's label and defeat-class, and clear the blocked and superseded
  sets — the whole-graph counterpart to the region relabels the assert / retract / settle
  path runs, for a caller that holds no smaller region.  Nothing on the live paths calls it:
  the assert / retract / settle path relabels regions, and `recover` composes the region
  relabels its own rebuild runs (`recovery/rebuild-tms`), its settle re-deriving blocking
  wholesale.  It is the
  differential oracle's whole-graph operation (`strength_test`, `jtms_dense_oracle_test`,
  `jtms_blocked_test`), which is why both representations implement it.

  It **clears blocked and superseded** because both are derived from queries that are never
  stored — a whole-graph relabel cannot recover either and must not inherit a stale one."
  [tms] (moving (-relabel tms)) tms)

(defn blocked
  "The justification ids currently blocked by their rule's exception."
  [tms] (-blocked tms))

(defn set-blocked
  "Replace the blocked set with `jids` — the justifications whose exception the caller
  has just found to hold — and relabel the region the change reaches.

  The set is *replaced*, not accumulated: the caller re-evaluates every exception it
  cares about and states the whole answer.  Nothing here remembers that a justification was blocked a round ago,
  so belief cannot depend on the order the exceptions were discovered in.

  The region is seeded from the **consequences of the justifications whose blocked
  status changed** — blocking or unblocking j can only move j's conclusion and what
  follows from it — so cost is proportional to that region, not to the graph, and a
  call that changes nothing does no work at all.  `#{}` unblocks everything."
  [tms jids] (moving (-set-blocked tms jids)) tms)

(defn hold!
  "Open hold `h` (`observe/new-hold`) on `tms`, and answer whether it opened: false when a
  hold is open on it already.  Until `release!`, every relabel records the labels it moves
  as they were before the hold's first move, and once `observe/open-hold!` registers `h`, a
  thread other than its owner reads belief, the blocked and superseded sets, and
  on the reference every read, from those.  A settle holds its network this way, so a
  reader beside it reads the belief the settle began from until the settle publishes what
  it decided (`vaelii.impl.settle/settle`)."
  [tms h] (-hold tms h))

(defn release!
  "Close hold `h` on `tms`.  A no-op for a hold that is not the one open."
  [tms h] (-release tms h) nil)

(defn held
  "The hold open on `tms`, or nil."
  [tms] (-held tms))

(defn consequence-closure
  "The forward consequence closure of `seeds`, seeds included: every datum a justification
  resting on one of them concludes, transitively.  The region `grounded-in-region` labels,
  for a caller that needs the datums a forced-OUT set can move and not their labels."
  [tms seeds]
  (loop [seen #{}, stack (vec seeds)]
    (if (empty? stack)
      seen
      (let [d (peek stack), stack (pop stack)]
        (if (contains? seen d)
          (recur seen stack)
          (recur (conj seen d)
                 (into stack (comp (keep #(justification tms %)) (map :consequence))
                       (dependents tms d))))))))

(defn region-in
  "The datums of `scope`, a part of `region` closed forward within it, that stay believed
  with `extra` forced OUT and `invalid` (justification ids) read as invalid, every datum of
  `region` outside `scope` read at its label in `base` and every datum outside `region`
  at its live one, added to `base`: `grounded-in-region*`'s fixpoint over `scope`."
  [tms region scope base extra belief-only invalid]
  (let [out?        #(or (contains? extra %) (forced? tms :out %))
        blocked-set (blocked tms)
        just-of     #(justification tms %)
        ;; raw belief for a boundary datum: reported belief plus the superseded spellings
        ;; the fixpoint keeps IN (their twin is justified by them).
        raw-in?     (fn [d] (or (in? tms d) (superseded? tms d)))
        ;; an antecedent in the region reads the recomputed set; outside it, live belief
        believed?*  (fn [in d] (if (contains? region d) (contains? in d) (raw-in? d)))
        valid-here? (fn [in j] (and (if-let [b (and belief-only (belief-only j))]
                                      (let [label? (if (set? b) b #{b})]
                                        (every? #(if (label? %) (raw-in? %) (believed?* in %))
                                                (:antecedents j)))
                                      (every? #(believed?* in %) (:antecedents j)))
                                    (let [inf (:informant j)]
                                      (or (not (integer? inf)) (believed?* in inf)))
                                    (not (contains? blocked-set (:id j)))
                                    (not (contains? invalid (:id j)))
                                    (not (forced? tms :void (:id j)))))
        ;; scope premises seed the fixpoint unless forced out
        seed        (into base (filter #(and (premise? tms %) (not (out? %)))) scope)
        ;; the justifications that can conclude something in the scope
        cands       (into [] (comp (mapcat #(supports tms %)) (distinct) (keep just-of)) scope)]
    (loop [in seed, stack cands]
      (if (empty? stack)
        in
        (let [j (peek stack), stack (pop stack), c (:consequence j)]
          (if (and (contains? scope c)
                   (not (contains? in c))
                   (not (out? c))
                   (valid-here? in j))
            (recur (conj in c)
                   (into stack (keep just-of) (dependents tms c)))
            (recur in stack)))))))

(defn- invalid-seeds
  "The conclusions of the justifications `invalid` names."
  [tms invalid]
  (into #{} (keep #(:consequence (justification tms %))) invalid))

(defn- grounded-in-region*
  [tms extra belief-only invalid]
  (let [extra   (set extra)
        invalid (set invalid)
        ;; the only datums a forced-out member or an invalid justification can move
        region  (consequence-closure tms (into extra (invalid-seeds tms invalid)))]
    {:region region :in (region-in tms region region #{} extra belief-only invalid)}))

(defn grounded-in-region
  "For `extra` — datums to force OUT — the forward consequence closure of `extra`
  (`:region`) and, within it, the datums that stay believed once `extra` is disbelieved
  (`:in`), the rest of the graph held at its current label.

  Read **region-local**: belief for a datum outside the region is taken per-datum from
  `in?`, never materialized, so cost is proportional to the region and not to the KB — the
  property that keeps `classify-local` linear in the number of dilemmas rather than
  quadratic (`grounded_in_region_test`).  The walk mirrors `affected-region` over the
  closure and the fixpoint mirrors `region-fixpoint` over it, both restricted to the
  region.  Built on the protocol reads (`in?`, `dependents`, `supports`, `justification`,
  `premise?`, `blocked`, `superseded?`), so both network representations answer
  it identically without either implementing a method — the derived-read footing `revived`
  has.

  The read behind the solve-free skeptical/credulous bracket
  (`vaelii.impl.asp.label/classify-local`, docs/labeling.md).

  `belief-only`, when given, maps a justification to the antecedent, or the set of
  antecedents, it reads at its current label rather than the recomputed one, or nil:
  `exc/belief-only-antecedent`, for a reader's copy that rests on an equality hidden
  wherever the copy is read.  `invalid` is a set of justification ids read as invalid,
  as a blocked one is: a guarded firing a reader re-asks and finds blocked."
  ([tms extra] (grounded-in-region* tms extra nil nil))
  ([tms extra belief-only] (grounded-in-region* tms extra belief-only nil))
  ([tms extra belief-only invalid] (grounded-in-region* tms extra belief-only invalid)))

(defn classes-in-region
  "The defeat-classes of the datums `in` holds inside `region`, where `region` and `in`
  are a `grounded-in-region` answer: the classes belief carries with that answer's `extra`
  forced OUT, the rest of the graph held at its current classes.

  The least fixpoint `region-classes` computes during a relabel, over the same equation —
  a datum's class is the strongest of its premise strength and what each valid
  justification confers, and a justification confers the weakest of its own strength and
  its antecedents' classes.  Every member starts at `:default`, the bottom, and the
  operator is monotone, so iterating to stability reaches the least fixpoint whatever the
  visit order.  Built on the protocol reads, like `grounded-in-region`, so both network
  representations answer it without implementing a method.

  The settle's reader of it is a nogood weighed at a vantage that withdraws part of what
  supports a member (docs/nmtms.md, \"A defeat is scoped to its vantage\")."
  [tms region in]
  (let [blocked-set (blocked tms)
        members     (filterv #(contains? in %) region)
        believed?*  (fn [d] (if (contains? region d)
                              (contains? in d)
                              (or (in? tms d) (superseded? tms d))))
        class-of    (fn [classes d] (if (contains? region d)
                                      (get classes d :default)
                                      (or (defeat-class tms d) :default)))
        node-class  (fn [classes d]
                      (let [prem (when (premise? tms d) (or (premise-class tms d) :default))
                            strs (for [jid  (supports tms d)
                                       :let [j (justification tms jid)]
                                       :when (and j
                                                  (every? believed?* (:antecedents j))
                                                  (let [inf (:informant j)]
                                                    (or (not (integer? inf)) (believed?* inf)))
                                                  (not (contains? blocked-set (:id j)))
                                                  (not (forced? tms :void (:id j))))]
                                   (reduce (fn [c a] (strength/min c (class-of classes a)))
                                           (or (:strength j) :monotonic)
                                           (class-antecedents j)))]
                        (reduce strength/max :default (remove nil? (cons prem strs)))))]
    (loop [classes (zipmap members (repeat :default))]
      (let [next (reduce (fn [m d] (assoc m d (node-class classes d))) classes members)]
        (if (= next classes) classes (recur next))))))

(defn retract!
  "Dependency-directed retraction (drop premise / relabel / sweep).  Returns
  {:removed-sentexes [datum...] :removed-justifications [jid...]
  :removed-supports [[consequence informant]...]}, the last absent when no justification
  went; a caller deletes the records and the justifications, and reads the supports
  without a justification fetch.  Unknown datums no-op (empty result): retraction is
  idempotent."
  [tms datum]
  ;; the one path besides `sweep!` that removes justifications — a bound dedup index
  ;; over this TMS is cleared wholesale rather than edited (see `*dedup-cache*`)
  (moving (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
          (-retract tms datum)))

(defn sweep!
  "Garbage-collect the consequence closure of `seeds`: every datum in it that is not
  a premise and is OUT is deleted, along with the justifications
  touching it.  Returns the same shape as `retract!`, for the caller to apply to its
  own stores.

  This is `retract!`'s sweep without the retraction.  It exists because `exceptWhen`
  removes a conclusion by invalidating its justification rather than by withdrawing a
  premise: blocking suppresses a derivation (`region-fixpoint`), so the conclusion is OUT
  and this collects it exactly as a retraction would — the trade
  docs/exceptions.md records under \"Garbage collection, not defeat\".

  Labels must already be current — `set-blocked` relabels the same region — so this
  only reads `:in`."
  [tms seeds]
  ;; removes justifications, so a bound dedup index over this TMS is cleared (see
  ;; `*dedup-cache*`)
  (moving (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
          (-sweep tms seeds)))

(defn drop-justification!
  "Remove the one justification `jid` from the network, relabel the region it
  supported, and sweep what that leaves OUT.  Returns `retract!`'s shape, for
  the caller to apply to its own stores; `jid`'s own record is the caller's to delete,
  and is listed only in `:removed-supports`.

  The one removal that names a justification rather than a datum.  Every other one
  reaches a justification through a datum leaving — its consequence swept, or an
  antecedent or rule retracted — which is right whenever a justification is wrong
  because something it rests on went.  A permuting mark leaving is the case where a
  justification is wrong about *where* it points: the firing still holds, but at a
  spelling the store stopped folding into its row (`chain/reconcile-spellings!`)."
  [tms jid]
  ;; removes a justification, so a bound dedup index over this TMS is cleared (see
  ;; `*dedup-cache*`)
  (moving (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
          (-drop-justification tms jid)))

(defn snapshot
  "The network as one canonical persistent map (see `-snapshot`).  A testing and
  debugging surface — the differential oracle compares two implementations with it."
  [tms] (-snapshot tms))

;; ---- what the network holds beside itself, declared ---------------------

(caches/register-cache
 {:cache    :justification-dedup
  :label    "Justification dedup"
  :scope    :process
  :unit     "conclusions"
  :limit    nil
  :counters nil
  :note     (str "Which justifications a conclusion already holds, so a conclusion "
                 "reached by k witnesses is not scanned k times. Bound for the length "
                 "of one chaining run and dropped when it returns, so there is nothing "
                 "to count between runs.")
  :read     (fn [_] {:entries (some-> ^java.util.HashMap (:m *dedup-cache*) .size)})})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(defn- tms-of [kb] (:tms @(:reasoning kb)))

(caches/register-derived
 {:id :M1 :label "Labels" :kind :index :keyed-by :handle :reads [:justifications]
  :holds-content? false
  :retired-by {:relabelled :K :roster :K :recover :R :image-install :R}
  :computed :write :imaged? :network :at [[:tms]]
  :value (fn [kb] (let [s (snapshot (tms-of kb))]
                    (assoc (select-keys s [:in :blocked :classes :forced :superseded])
                           :premises (into #{} (keep (fn [[d n]] (when (:premise? n) d)))
                                           (:nodes s)))))
  :note "IN, blocked, monotonic class, forced and superseded per handle; a mutation relabels its region inside `moving`"})

(caches/register-derived
 {:id :M2 :label "Touched window" :kind :journal :keyed-by :handle :reads [:M1]
  :holds-content? false
  :retired-by {:relabelled :K :roster :K :settle-exit :W :recover :W}
  :computed :write :imaged? false :at [[:tms]]
  :value (fn [kb] (select-keys (snapshot (tms-of kb))
                               [:touched :touched-in :touched-new :touched-out]))
  :note "the handles relabelled since the last settle exit, with the reader marks into it; `reset-touched!` at the settle exit empties it and moves the mark generation"})

(caches/register-derived
 {:id :M3 :label "Belief hold" :kind :index :keyed-by :global :reads [:M1]
  :holds-content? false
  :retired-by {:held :K}
  :computed :settle :imaged? false :at [[:tms]]
  :value (fn [kb] (held (tms-of kb)))
  :note "the labels as they stood before a settle's first relabel, which other threads read until the settle publishes"})

(caches/register-derived
 {:id :M4 :label "Justification dedup" :cache :justification-dedup :kind :pass
  :holds-content? false
  :keyed-by :handle :reads [:justifications]
  :retired-by {:relabelled :W} :computed :pass :imaged? false :var #'*dedup-cache*
  :note "the justification keys each conclusion holds, bound for one chaining run; `retract!`, `sweep!` and `drop-justification!` clear it"})
