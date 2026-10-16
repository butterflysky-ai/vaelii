;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.except
  "The visibility `except` roster: which handles a believed `except` hides from a
  reading context, with the meta-except cascade; and the read walk that applies the
  placed `defeat`s at a reader.  See docs/exceptions.md and docs/nmtms.md."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- except-of
  "The handle the `except` stored at `eh` hides, or nil when `eh` holds no `(except
  (sentexHandle H))`."
  [recs eh]
  (let [s (:sentence (p/get-sentex recs eh))]
    (when (and (seq? s) (= sx/except-functor (first s)) (= 2 (count s)))
      (sx/handle-id (second s)))))

(defn visible-exception-index
  "The excepts stated in a context of `view-context`'s ancestor set, as `{target-handle ->
  #{except-handle ...}}`, or nil when none is stated there or `view-context` is a
  variable: the `except` extent in that set, one record read per except.  Both the hot
  boolean reads and diagnostic exception forest use this one index so they cannot
  disagree about scope.

  The ancestor set is the unscoped one (`tax/context-up-global`): the except filter
  cannot be scoped by the filter it derives."
  [kb view-context]
  (let [idx (:index kb)]
    (when-not (or (sx/variable? view-context) (not (reads/stores-any? idx sx/except-functor)))
      (let [up   (tax/context-up-global (reasoning/taxonomy kb) view-context)
            recs (:records kb)]
        (not-empty
         (reduce (fn [m eh] (if-let [t (except-of recs eh)] (update m t (fnil conj #{}) eh) m))
                 {} (reads/as-stored-with-functor-in idx sx/except-functor up)))))))

(defn- exception-states
  "`{handle {:in? bool :in-force? bool}}` for every except reachable from `roots`, each
  evaluated once, so a chain of n excepts costs n reads: an except is in force when it is
  believed and no except of it is (the meta-except cascade, docs/contexts.md).  An except
  met a second time on one walk reads as not in force.  `ehs-of` is `(fn [handle])`, the
  excepts naming a handle that the reader sees."
  [tms ehs-of roots]
  (let [states (atom {})]
    (letfn [(active? [eh seen]
              (if (contains? seen eh)
                false
                (if-some [state (get @states eh)]
                  (:in-force? state)
                  (let [in? (boolean (jtms/in? tms eh))
                        ;; Eagerly evaluate every child: `not-any?` directly over the
                        ;; recursive calls would short-circuit after one active child,
                        ;; leaving its siblings absent from the diagnostic state map.
                        child-active (mapv #(active? % (conj seen eh)) (ehs-of eh))
                        active (boolean (and in? (not-any? true? child-active)))]
                    (swap! states assoc eh {:in? in? :in-force? active})
                    active))))]
      (doseq [eh roots] (active? eh #{}))
      @states)))

(defn- exception-node
  "One node of `exception-status`' forest, its children in content order.  A node met a
  second time on one walk is `:cycle? true`."
  [records states ehs-of eh seen]
  (if (contains? seen eh)
    {:handle eh :in? (get-in states [eh :in?] false) :in-force? false
     :cycle? true :excepted-by []}
    (let [seen' (conj seen eh)
          {:keys [in? in-force?]} (get states eh)]
      {:handle eh
       :in? in?
       :in-force? in-force?
       :excepted-by (mapv #(exception-node records states ehs-of % seen')
                          (nm/sort-by-content-key
                           (fn [h]
                             (let [s (p/get-sentex records h)]
                               [(:context s) (:sentence s)]))
                           (ehs-of eh)))})))

(defn- excepts-seen
  "`(fn [handle])`, the excepts naming a handle stated in a context of `view-context`'s
  ancestor set (`reads/as-stored-naming`), or nil when no except is stored or
  `view-context` is a variable, since an except hides its target below its own context
  and not above it.  The ancestor set is the unscoped one (`tax/context-up-global`): the
  scoped `context-up` is itself filtered by what the excepts hide."
  [kb view-context]
  (let [idx (:index kb)]
    (when-not (or (sx/variable? view-context) (not (reads/stores-any? idx sx/except-functor)))
      (let [up (tax/context-up-global (reasoning/taxonomy kb) view-context)]
        #(reads/as-stored-naming idx sx/except-functor % up)))))

(defn exception-status
  "Diagnostic exception forest for `handle` from `view-context`.

  Returns `{:exceptions [...] :excepted? bool}`.  Roots are every visible exception
  directly targeting `handle`, ordered by assertion context and content; nested
  meta-exceptions live under `:excepted-by`.  Reads the excepts naming `handle` and,
  through the cascade, those naming them, and no others."
  [kb handle view-context]
  (if-let [ehs-of (excepts-seen kb view-context)]
    (let [records (:records kb)
          ordered-roots (nm/sort-by-content-key
                         (fn [h]
                           (let [s (p/get-sentex records h)]
                             [(:context s) (:sentence s)]))
                         (ehs-of handle))
          states (exception-states (reasoning/tms kb) ehs-of ordered-roots)
          roots (mapv #(exception-node records states ehs-of % #{}) ordered-roots)]
      {:exceptions roots
       :excepted? (boolean (some :in-force? roots))})
    {:exceptions [] :excepted? false}))

(defn in-force-targets
  "The targets of `target->ehs` (`visible-exception-index`'s answer) that an except in
  force hides, as a set: `excepted-handles` over a roster its caller already read."
  [kb target->ehs]
  (if (empty? target->ehs)
    #{}
    (let [states    (exception-states (reasoning/tms kb) #(get target->ehs %)
                                      (into [] cat (vals target->ehs)))
          in-force? #(get-in states [% :in-force?])]
      (persistent!
       (reduce-kv (fn [acc target ehs]
                    (if (some in-force? ehs)
                      (conj! acc target)
                      acc))
                  (transient #{})
                  target->ehs)))))

(defn excepted-handles
  "The handles a believed `except` in force hides from `view-context`, read off the
  `except` extent over its ancestor set (docs/contexts.md, \"except\").  Empty when
  nothing is excepted, and for a variable `view-context`, since an except hides its
  target below its own context and not above it.  A caller asking about particular
  handles asks `except-hidden-fn` or `excepted?` instead."
  [kb view-context]
  (in-force-targets kb (visible-exception-index kb view-context)))

(defn except-hidden-fn
  "A predicate `(fn [handle]) -> boolean` answering, for one `view-context`, what
  `excepted-handles` answers as a set, or **nil** when no context of its ancestor set
  states an except.  The nil is a storage gate, not a belief one: excepts that are all
  defeated still give a predicate, which answers false.  The gate reads the `except`
  extent, which holds both polarities, so a stored `(not (except …))` in a context of the
  set gives a predicate too.  This is the excepts alone, which a derivation asks
  (`chain/antecedent-hidden?`); a read asks `exc/hidden-fn`.  The predicate reads the
  excepts naming the asked handle, and the cascade over the excepts naming those.

  The ancestor set is the unscoped one, for `visible-exception-index`'s reason."
  [kb view-context]
  (let [idx (:index kb)]
    (when-not (or (sx/variable? view-context) (not (reads/stores-any? idx sx/except-functor)))
      (let [up (tax/context-up-global (reasoning/taxonomy kb) view-context)]
        (when (reads/stores-in? idx sx/except-functor up)
          (let [ehs-of #(reads/as-stored-naming idx sx/except-functor % up)
                tms    (reasoning/tms kb)]
            (fn [handle]
              (boolean
               (when-let [ehs (ehs-of handle)]
                 (let [states (exception-states tms ehs-of ehs)]
                   (some #(get-in states [% :in-force?]) ehs)))))))))))

;; ---- the read walk: the placed defeats applied at read time ---------------------
;;
;; A placed nogood stores `(defeat (sentexHandle L))` (`chain/place-nogood!`), and a
;; reader at or below its placement does not believe `L`, nor what rests only on `L`.
;; Nothing records which reader reads what: each read walks the asked handle's support
;; at the reader and forces OUT the targets hidden there, with a memo that lives as long
;; as the predicate one read builds.  See docs/nmtms.md, "A nogood placed as a
;; conclusion".

(def nogood-informant
  "The informant of every justification a placed nogood stores (`chain/place-nogood!`)."
  'nogood)

(def guard-informant
  "The informant of every justification a guard defeat stores
  (`chain/place-guard-defeats!`): a firing's `exceptWhen` or `unknown` that holds below its
  placement."
  'guard)

(defn belief-only-antecedent
  "The antecedent justification `j` rests on for belief and not for visibility, or nil.
  A reader's copy has one: `[original equality except]` under informant `except`
  (`special/migrate-sentex`) is stored in a context that reads the except, so the equality
  is hidden wherever the copy is read, and that hiding is the copy's reason rather than a
  withdrawal of it.  The read walk adds the placed nogood's own loser
  (`placed-belief-only`)."
  [j]
  (when (= 'except (:informant j))
    (nth (:antecedents j) 1 nil)))

(defn- defeat-target*
  "The handle a `(defeat (sentexHandle H))` sentence names, or nil."
  [s]
  (when (and (seq? s) (= sx/defeat-functor (first s)) (= 2 (count s)))
    (sx/handle-id (second s))))

(defn support
  "`h` and its justification ancestors: every handle a justification of one of them rests
  on, transitively, not descending past a premise unless `past-premises?`, and leaving
  out each handle `stop?` names, which the read takes at its label.  A premise's other
  justifications decide its class, not its belief, so only a class read descends past
  it."
  ([tms h stop?] (support tms h stop? false))
  ([tms h stop? past-premises?]
   (loop [seen #{}, stack [h]]
     (if (empty? stack)
       seen
       (let [d (peek stack) stack (pop stack)]
         (if (or (contains? seen d) (stop? d))
           (recur seen stack)
           (recur (conj seen d)
                  (if (and (not past-premises?) (jtms/premise? tms d))
                    stack
                    (into stack (comp (keep #(jtms/justification tms %)) (mapcat jtms/rests-on))
                          (jtms/supports tms d))))))))))

;; ---- a defeat met again on one read: the cycle, broken in content order ------------
;;
;; A defeat's force reads the belief of its support, and that belief reads the force of
;; the defeats naming a handle in it, so a defeat can rest on itself through other
;; defeats.  The read keeps each defeat it is reading open under the index it opened at
;; (`::open`).  A defeat met again while open answers false and lowers the read's mark
;; (`::open-low`) to that index, and a value that met an index below its own start is
;; provisional and is not kept.  The defeats left provisional when the first of them
;; closes form a cycle, which `close-cycle` breaks (design ruling 18).  See docs/nmtms.md,
;; "A defeat-dependency cycle".

(def ^:private no-low Long/MAX_VALUE)

(defn- marked
  "`[(f) low]`: `f`'s value and the least index of an open defeat it met again.  The mark
  of the computation around `f` is lowered to `low` too."
  [memo f]
  (let [saved (get @memo ::open-low no-low)]
    (vswap! memo assoc ::open-low no-low)
    (let [r (f) low (get @memo ::open-low no-low)]
      (vswap! memo assoc ::open-low (min saved low))
      [r low])))

(defn- opened
  "`(f)` with the defeat key `k` open at index `n`."
  [memo k n f]
  (vswap! memo assoc-in [::open k] n)
  (try (f) (finally (vswap! memo update ::open dissoc k))))

(defn- kept
  "`(f)`, kept in the read's memo under `k` unless it met a defeat open when it started."
  [memo k f]
  (let [v (get @memo k ::absent)]
    (if (identical? ::absent v)
      (let [n (count (::open @memo)) [r low] (marked memo f)]
        (when (>= low n) (vswap! memo assoc k r))
        r)
      v)))

(defn- key-loser
  "`[kind own loser]` for the defeat key `k`: a `defeat` handle (`in-force?`, kind 0),
  `[::guard d]` (`guard-in-force?`, kind 1) or `[::conflict c x]` (`conflict-in-force?`,
  kind 2); `own` is the handle of the defeat or `contradicts`, and `loser` the handle it
  removes."
  [recs k]
  (let [target #(defeat-target* (:sentence (p/get-sentex recs %)))]
    (cond (integer? k)          [0 k (target k)]
          (= ::guard (first k)) [1 (second k) (target (second k))]
          :else                 [2 (second k) (nth k 2)])))

(defn- cycle-order
  "The cycle members `ms`, `[key f]` pairs, in content order of the handle each key
  removes, then of the defeat itself (`key-loser`), each `(sentexHandle h)` the defeat
  names read as `h`'s content, so no handle number decides the order."
  [recs ms]
  (let [content #(let [s (p/get-sentex recs %)] [(:sentence s) (:context s)])
        named   #(let [s (p/get-sentex recs %)]
                   [(mapv (fn [a] (if-let [h (sx/handle-id a)] (content h) a)) (:sentence s))
                    (:context s)])]
    (nm/sort-by-content-key
     (fn [[k]] (let [[kind own loser] (key-loser recs k)] [(content loser) (named own) kind]))
     ms)))

(def ^:private enumerated-members
  "The most members of one cycle whose assignments `close-cycle` enumerates: 2^8
  assignments, each member read once per assignment."
  8)

(defn- close-cycle
  "Break the cycle `ms` (`[key f]` pairs, opened at index `n`) in content order
  (`cycle-order`).  A cycle of at most `enumerated-members` members takes the first
  assignment in content order, in force first, that every member reads as its own value,
  with the members removing another loser held at its values.  A larger cycle, or one
  with no consistent assignment, starts every member out of force, and at most 2m + 1
  passes over m members read each member at the current values, until a pass changes no
  value.  A key a member's read opens that rests on a member joins the members, which
  start again, so each key that joins costs another 2^m · m member reads, plus
  (2m + 1) · m when no assignment is consistent, or (2m + 1) · m above
  `enumerated-members`.  A value a member's read kept, one that read no held member,
  stays in the memo, so a cycle closed inside that read and resting on no member is
  closed once per read.  A guard defeat's seen justifications (`guard-covered`) are
  those its read under the chosen values left.  See docs/nmtms.md, \"A defeat-dependency cycle\".

  Answers nil with every member's value kept in the memo, or `{:low i :members ms'}` when a
  member's read met a defeat open at an index `i` below `n`: the members rest on that
  defeat, which the frame owning it closes with them."
  [{:keys [memo recs]} n ms]
  (let [loser     #(peek (key-loser recs %))
        seen-key  (fn [k] (when (and (vector? k) (= ::guard (first k))) [::guard-seen (second k)]))
        ;; met again inside its own read a member answers false, so its own target does
        ;; not count against it; two defeats of one loser do not compete, so neither is held
        ;; while the other is read
        ;; a value the read kept in the memo stays there: `kept`, `in-force-once` and
        ;; `route-answer` keep a value opened at index i only when its read met no defeat
        ;; open below i, and every key the read opens has i > n, while a held member
        ;; answers at n, so a kept value read no held member and holds under every
        ;; assignment.  The read's own marks, and the guard justifications of the other
        ;; members, are put back as they stood.
        read      (fn [members vals [k f]]
                    (let [saved @memo
                          c     (count (::cycle saved []))
                          held  (into {} (keep (fn [[o]] (when (not= (loser k) (loser o))
                                                           [o [n (get vals o false)]])))
                                      members)
                          seen  (seen-key k)]
                      (vswap! memo update ::assumed (fnil into {}) held)
                      (let [[r low] (marked memo #(opened memo k n f))
                            found   (subvec (vec (::cycle @memo [])) (min c (count (::cycle @memo []))))]
                        (vswap! memo (fn [m] (reduce (fn [m rk] (if-let [[_ v] (find saved rk)] (assoc m rk v) (dissoc m rk)))
                                                     m
                                                     (into [::assumed ::open ::open-low ::cycle ::depth ::low]
                                                           (comp (keep seen-key) (remove #{seen}))
                                                           (keys members)))))
                        [r low found])))
        ;; each member read once in content order, at the values the reads before it left
        ;; (`step?`) or at `vals`: `[vals' outer-low new-members]`
        sweep     (fn [members order vals step?]
                    (reduce (fn [[vs lo new] [k :as m]]
                              (let [[r low found] (read members (if step? vs vals) m)]
                                [(assoc vs k r) (min lo (if (< low n) low no-low))
                                 (into new (remove (fn [[fk]] (contains? members fk))) found)]))
                            [vals no-low []]
                            order))
        ;; every assignment read: `[a outer-low new-members]`, `a` the first consistent one
        ;; with the seen justifications its reads left, or nil
        enumerate (fn [members order]
                    (let [ks  (mapv first order)
                          m   (count ks)
                          sks (keep seen-key ks)]
                      (vswap! memo #(apply dissoc % sks))
                      (reduce (fn [[best lo new] bits]
                                (let [a (zipmap ks (map #(bit-test bits (- m 1 %)) (range m)))
                                      [a' low found] (sweep members order a false)]
                                  [(or best (when (= a a') (into a (select-keys @memo sks))))
                                   (min lo low) (into new found)]))
                              [nil no-low []]
                              (range (dec (bit-shift-left 1 m)) -1 -1))))
        start     (fn [members] (zipmap (keys members) (repeat false)))]
    (loop [members (into {} ms), vals nil, i 0]
      (let [order           (cycle-order recs (vec members))
            enum?           (and (nil? vals) (<= (count members) enumerated-members))
            vals            (when-not enum? (or vals (start members)))
            [vals' low new] (if enum? (enumerate members order) (sweep members order vals true))]
        (cond
          (< low no-low) {:low low :members (vec members)}
          (seq new)      (recur (into members new) nil 0)
          enum?          (if vals'
                           (do (vswap! memo into vals') nil)
                           (recur members (start members) 0))
          (or (= vals vals') (>= i (* 2 (count members))))
          (do (vswap! memo into vals') nil)
          :else (recur members vals' (inc i)))))))

(defn- in-force-once
  "`(f)`, whether the defeat key `k` (`cycle-order`) is in force at the reader, kept in the
  read's memo.  Met again while open it answers false, and held by `close-cycle` it
  answers the value held; either lowers the read's mark.  A value that met a key open
  below its own is kept nowhere, and its key joins the cycle that lower key closes.  A
  cycle whose members rest on a key open below its own index (`close-cycle`) joins the
  cycle that key closes, and lowers the read's mark to it."
  [{:keys [memo] :as st} k f]
  (let [m @memo, v (get m k ::absent)]
    (cond
      (not (identical? ::absent v)) v
      (contains? (::open m) k)      (do (vswap! memo update ::open-low (fnil min no-low) (get-in m [::open k])) false)
      (contains? (::assumed m) k)   (let [[i held] (get-in m [::assumed k])]
                                      (vswap! memo update ::open-low (fnil min no-low) i)
                                      held)
      :else
      (let [n (count (::open m)) c (count (::cycle m []))
            [r low] (marked memo #(opened memo k n f))]
        (cond
          (< low n) (do (vswap! memo update ::cycle (fnil conj []) [k f]) r)
          (and (= low n) (> (count (::cycle @memo [])) c))
          (let [ms (conj (subvec (::cycle @memo) c) [k f])]
            (vswap! memo update ::cycle subvec 0 c)
            (if-let [{:keys [low members]} (close-cycle st n ms)]
              (do (vswap! memo update ::cycle (fnil into []) members)
                  (vswap! memo update ::open-low (fnil min no-low) low)
                  r)
              (in-force-once st k f)))
          :else (do (vswap! memo assoc k r) r))))))

;; ---- a second route at the reader ----------------------------------------------

(defonce ^{:private true
           :doc "A `(fn [kb rel a b reader])` answering whether `reader` reaches `b` from `a`
  over the fact relation `rel` a `transitiveInArgInverse` preserves a claim along, or nil.
  Installed by `vaelii.impl.inherit` at load, which owns that walk; nil reads every such
  path as unreached."}
  route-reach
  (atom nil))

(defonce ^{:private true
           :doc "A pair `[goals reach]` installed by `vaelii.impl.inherit` at load, which owns
  the claim search: `(goals kb j)` answers `[goals stated]` for the rule firing `j`, the
  goals it matched through a reach and the antecedent handles that state a literal, or nil
  when it reads no goal off `j`; `(reach kb goal reader)` answers whether `reader` reaches
  the ground `goal` from a claim it reads.  nil leaves every firing to `route-reaches?`."}
  firing-reach
  (atom nil))

(defn install-route-reach!
  "Register the walks a second route is read through: `reach`, which `route-reaches?` asks
  for a path over a fact relation, and `goals` and `goal-reach`, a rule firing's goals and
  the backward search for one (`firing-reach`).  `vaelii.impl.inherit`'s, once, when it
  loads.  Global, as the walks dispatch on the `kb` they are handed."
  [reach goals goal-reach]
  (reset! route-reach reach)
  (reset! firing-reach [goals goal-reach]))

(def ^:dynamic *routes*
  "The second-route answers of the read that opened the search, a volatile map, while a
  search runs, and nil outside one.  A read nested in the search answers its own second
  routes into the same map, so a route met again on one path reads as not reaching
  (`route-answer`)."
  nil)

(defn- open-marked
  "`[(f) settled?]`: `f`'s value, and whether its computation read no route question open
  in the search's memo `m` (`caches/*open-mark*`).  The mark of the computation around `f`
  is lowered as `f` lowered it."
  [m f]
  (let [saved (get @m ::low Long/MAX_VALUE)]
    (vswap! m assoc ::low Long/MAX_VALUE)
    (let [r (f) low (get @m ::low Long/MAX_VALUE)]
      (vswap! m assoc ::low (min saved low))
      [r (= Long/MAX_VALUE low)])))

(defn- route-answer
  "`(f)`, the answer to the second-route question `k`, memoized for one read in the memo of
  the read that opened the search (`*routes*`, else `st`'s).  `f` runs under
  `tax/*search*`, `:visibility` with `with-excepts?` and `:belief` without.  A question met
  again while it is being answered reads false.  An answer that read false off a question
  still open above it, or that met a defeat the read has open (`marked`), is provisional
  and is not kept, so an answer kept never depends on which question the read asked
  first.  A cache entry computed inside the search is held by the same rule
  (`caches/*open-mark*`)."
  [{:keys [memo]} with-excepts? k f]
  (let [m (or *routes* memo)
        v (get @m k ::absent)]
    (cond
      (vector? v)       (do (vswap! m update ::low (fnil min Long/MAX_VALUE) (second v)) false)
      (not= ::absent v) v
      :else
      (let [d   (inc (get @m ::depth 0))
            low (get @m ::low Long/MAX_VALUE)
            n   (count (::open @memo))]
        (vswap! m assoc k [::open d] ::depth d ::low Long/MAX_VALUE)
        (let [[r flow] (marked memo
                               #(binding [*routes*            m
                                          tax/*search*        (if with-excepts? :visibility :belief)
                                          caches/*open-mark*  (partial open-marked m)]
                                  (f)))
              low' (::low @m)
              open (if (< low' d) low' Long/MAX_VALUE)]
          (vswap! m (fn [mm] (-> (if (or (< open d) (< flow n)) (dissoc mm k) (assoc mm k r))
                                 (assoc ::depth (dec d) ::low (min low open)))))
          r)))))

(defn- witness-paths
  "The witness edges among `sentences` (`{handle sentence}`, one justification's
  antecedents) joined into paths, as `{:rel :a :b :edges}`: the `genl` edges, and the edges
  of a relation some `transitiveInArgInverse` among them preserves a claim along.  A firing
  depends on each path's two ends, which a second route can reach.  A `genlCx` edge is on
  no path, so a justification resting on one the reader does not see has no second route
  (docs/contexts.md, \"An except on a `genlCx` edge\")."
  [sentences]
  (let [binary    (fn [s] (when (and (seq? s) (= 2 (count (nm/args s))))
                            [(nm/functor s) (first (nm/args s)) (second (nm/args s))]))
        preserved (into #{} (keep (fn [s] (when (and (seq? s) (= 'transitiveInArgInverse (nm/functor s)))
                                            (last (nm/args s)))))
                        (vals sentences))
        edges     (into [] (keep (fn [[h s]]
                                   (when-let [[f a b] (binary s)]
                                     (when (or (= 'genl f) (contains? preserved f))
                                       [h f a b]))))
                        sentences)]
    (into []
          (mapcat (fn [[rel es]]
                    (let [out  (group-by #(nth % 2) es)
                          tgts (into #{} (map #(nth % 3)) es)]
                      (for [a (distinct (remove tgts (map #(nth % 2) es)))]
                        (loop [n a, hs #{}]
                          (if-let [[h _ _ b] (first (remove #(contains? hs (first %)) (out n)))]
                            (recur b (conj hs h))
                            {:rel rel :a a :b n :edges hs}))))))
          (group-by second edges))))

(defn- route-reaches?
  "Does `ctx` reach `b` from `a` over `rel` on the edges it believes, and with
  `with-excepts?` sees: the scoped `genl` closure, or the installed fact-relation walk
  (`route-reach`), memoized for one read (`route-answer`)."
  [{:keys [kb tax ctx] :as st} with-excepts? rel a b]
  (route-answer st with-excepts? [::route ctx with-excepts? rel a b]
                #(case rel
                   genl   (tax/genl? tax a b ctx)
                   (boolean (when-let [f @route-reach] (f kb rel a b ctx))))))

(defn- firing-stands?
  "Does the rule firing `j` stand at `ctx` with the handles `gone` forced OUT: no handle of
  `gone` states one of its literals, and the backward search `firing-reach` installs finds
  each goal it matched through a reach, over the claims and edges `ctx` believes, and with
  `with-excepts?` sees, with the placed defeats applied.  Each goal's answer is memoized
  for one read (`route-answer`), so the justifications sharing a goal ask it once.  nil
  when it reads no goal off `j`."
  [{:keys [kb ctx] :as st} with-excepts? j gone]
  (when-let [[goals-of reach] @firing-reach]
    (when-let [[goals stated] (goals-of kb j)]
      (and (not-any? #(contains? stated %) gone)
           (every? (fn [g] (route-answer st with-excepts? [::goal ctx with-excepts? g]
                                         #(binding [tax/*network-belief* false] (reach kb g ctx))))
                   goals)))))

(defn- rerouted
  "`{justification-id #{handle}}`: for each justification of a handle of `region` that rests
  on a handle of `forced`, the forced handles it reads at their label, when the firing
  stands at the reader another way.  A rule firing stands when the backward search finds
  each goal it matched through a reach reached by a claim the reader believes, over edges
  it believes, and with `with-excepts?` a claim and edges it also sees (`firing-stands?`).
  Any other justification stands when every forced handle is a witness edge on a path its
  antecedents name and the reader reaches both ends of each such path
  (`route-reaches?`).  A read inside the search reads its own second routes the same way.
  Nothing is re-derived (docs/nmtms.md, \"Where the layer stops\").  Asks only of a
  justification a forced handle reaches."
  [{:keys [tms recs] :as st} region forced with-excepts?]
  (into {}
        (keep (fn [j]
                (let [gone (filterv #(contains? forced %) (:antecedents j))]
                  (when (seq gone)
                    (let [stands (firing-stands? st with-excepts? j (set gone))]
                      (if (some? stands)
                        (when stands [(:id j) (set gone)])
                        (let [sentences (into {} (keep (fn [h] (when-let [s (p/get-sentex recs h)]
                                                                 [h (:sentence s)])))
                                              (:antecedents j))
                              paths     (witness-paths sentences)
                              on-path   (into #{} (mapcat :edges) paths)]
                          (when (and (every? #(contains? on-path %) gone)
                                     (every? (fn [{:keys [rel a b edges]}]
                                               (or (not-any? #(contains? forced %) edges)
                                                   (route-reaches? st with-excepts? rel a b)))
                                             paths))
                            [(:id j) (set gone)]))))))))
        (into [] (comp (mapcat #(jtms/supports tms %)) (distinct) (keep #(jtms/justification tms %)))
              region)))

(defn- with-routes
  "`belief-only` with the forced handles `routes` names for a justification
  (`rerouted`) read at their label beside the one `belief-only` names."
  [belief-only routes]
  (if (empty? routes)
    belief-only
    (fn [j] (let [a (belief-only j) r (get routes (:id j))]
              (cond (nil? r) a
                    (nil? a) r
                    :else    (conj r a))))))

(defn- except-hidden-in
  "Is the handle `h`, IN in the network, hidden by the excepts alone, where `excepted?` is
  `except-hidden-fn`'s predicate at one context: IN no longer once each handle of its
  support an except in force names is forced OUT (`jtms/region-in`).  No `defeat` and no
  verdict is read.  With `st`, a read's state, a justification resting on a forced witness
  edge stands where the reader reaches the path's ends another way (`rerouted`)."
  [tms excepted? h st]
  (let [region (support tms h (constantly false))
        forced (into #{} (filter excepted?) region)]
    (and (seq forced)
         (not (contains? (jtms/region-in tms region region #{} forced
                                         (with-routes belief-only-antecedent
                                           (when st (rerouted st region forced true)))
                                         #{})
                         h)))))

(defn except-closure-hidden-fn
  "A predicate `(fn [handle])` answering whether `ctx` reads `handle`, IN in the network, as
  hidden by the excepts alone: an except in force there names it, or names a handle every
  justification route of it rests on.  **nil** when no context of `ctx`'s ancestor set
  states an except (`except-hidden-fn`).  What a placement reads, a firing's and a
  nogood's alike: the `except` roster and the network, and no `defeat`.  With `read?`, the
  visibility a read asks, a firing that rests on an excepted witness edge stands where
  `ctx` reaches the path's ends another way (`rerouted`).  The predicate holds a memo for
  its own lifetime."
  ([kb ctx] (except-closure-hidden-fn kb ctx false))
  ([kb ctx read?]
   (when-let [excepted? (except-hidden-fn kb ctx)]
     (let [tms (reasoning/tms kb)
           st  (when read? {:kb kb :ctx ctx :tms tms :recs (:records kb) :tax (reasoning/taxonomy kb)
                            :memo (volatile! {})})]
       (memoize (fn [h] (boolean (and (jtms/in? tms h) (except-hidden-in tms excepted? h st)))))))))

(defn- reaching-targets
  "The handles of `targets` that a handle `supports?` answers for rests on through any
  chain, `support`'s reverse: a forward walk over the justifications from each target,
  stopped at the first such handle.  nil once the walks have visited `budget` handles."
  [tms targets supports? budget]
  (loop [ts (seq targets), seen #{}, stack (vec (take 1 ts)), left (long budget), acc []]
    (let [d (peek stack)]
      (cond
        (nil? ts) acc
        ;; this target's walk is done: a supporter rests on it, or none does
        (or (nil? d) (supports? d))
        (let [more (next ts)]
          (recur more #{} (vec (take 1 more)) left (cond-> acc (some? d) (conj (first ts)))))
        (contains? seen d) (recur ts seen (pop stack) left acc)
        (zero? left) nil
        :else (recur ts (conj seen d)
                     (into (pop stack) (comp (keep #(jtms/justification tms %)) (map :consequence))
                           (jtms/dependents tms d))
                     (dec left) acc)))))

(defn- genlCx-excepts
  "`[context except-handle]` for each stored `except` naming a handle in the support of a
  `genlCx` supporter of the view `sups` (`tax/supporter-view`'s keys), and for each stored
  `except` of one of those, transitively.  While no more `except`s are stored than `sups`
  counts, the direct ones are read forward from their targets (`reaching-targets`, under
  the same budget); otherwise from each supporter's support, one probe per handle
  (`reads/as-stored-naming-by-context`), with no target set built.  The targets are read
  in every context, as `named-entries` reads them: an `except` hides a supporter from
  every reader under its context.  Nothing read while no `except` is stored."
  [kb {n :count :keys [supports? handles]}]
  (let [idx (:index kb)]
    (when (reads/stores-any? idx sx/except-functor)
      (let [tms    (reasoning/tms kb)
            naming (fn [h] (for [[c hs] (reads/as-stored-naming-by-context idx sx/except-functor h)
                                 eh hs]
                             [c eh]))
            direct (if-some [ts (when (<= (reads/stored-count-with-functor idx sx/except-functor)
                                          (long n))
                                  (reaching-targets tms (reads/as-stored-named-global idx sx/except-functor)
                                                    supports? n))]
                     (mapcat naming ts)
                     (mapcat (fn [s] (mapcat naming (support tms s (constantly false) true))) (handles)))]
        ((fn step [todo seen]
           (lazy-seq
            (when-let [[[_ eh :as e] & more] (seq todo)]
              (if (contains? seen eh)
                (step more seen)
                (cons e (step (concat more (naming eh)) (conj seen eh)))))))
         direct #{})))))

(defn genlCx-except-contexts
  "The contexts stating an `except` that reaches the support of a `genlCx` supporter of the
  view `sups` (`genlCx-excepts`), with the contexts stating an `except` of one of those,
  transitively, as a sorted set: what splits the readers under a moved edge into classes
  (`tax/context-move`)."
  [kb sups]
  (into (sorted-set-by #(compare (str %1) (str %2))) (map first) (genlCx-excepts kb sups)))

(defn genlCx-excepted?
  "Does a stored `except` reach the support of a `genlCx` supporter of the view `sups`
  (`genlCx-excepts`): the `genlCx` filter gate (`kb/supporter-reaches?`)."
  [kb sups]
  (boolean (seq (genlCx-excepts kb sups))))

(defn closure-excepted-anywhere?
  "Is `handle` hidden from at least one context by the excepts alone
  (`except-closure-hidden-fn`)?  Reads the excepts naming a handle of its support and the
  contexts stating them, so it costs the support and not the standing excepts on other
  targets."
  [kb handle]
  (let [idx (:index kb)]
    (boolean
     (when (reads/stores-any? idx sx/except-functor)
       (let [tms (reasoning/tms kb)
             ctxs (into #{} (comp (mapcat #(reads/as-stored-naming-by-context idx sx/except-functor %))
                                  (map first))
                        (support tms handle (constantly false)))]
         (some #(when-let [hidden? (except-closure-hidden-fn kb %)] (hidden? handle)) ctxs))))))

(defn defeated-anywhere?
  "Can a placed defeat remove `handle` from some context's belief: a stored `defeat` names
  a handle of its support?  One count read per handle of the support, and none on the
  standing defeats on other targets."
  [kb handle]
  (let [idx (:index kb)]
    (boolean (when (reads/stores-any? idx sx/defeat-functor)
               (some #(reads/stored-naming? idx sx/defeat-functor %)
                     (support (reasoning/tms kb) handle (constantly false)))))))

(defn- named-entries
  "`[[defeat targets] [except targets]]`, each entry keyed by its functor and present when
  a fact of the functor is stored, the first only with `defeats?`: a delay of the handles
  the stored `defeat`s and `except`s name (`reads/as-stored-named-global`), so a caller
  that needs only whether one is stored reads two counts, and one that counts or probes
  them reads the index by the key."
  [kb defeats?]
  (let [idx   (:index kb)
        entry (fn [f] (clojure.lang.MapEntry/create f (delay (reads/as-stored-named-global idx f))))]
    (seq (cond-> []
           (and defeats? (reads/stores-any? idx sx/defeat-functor)) (conj (entry sx/defeat-functor))
           (reads/stores-any? idx sx/except-functor) (conj (entry sx/except-functor))))))

(defn supporter-roster
  "What the taxonomy's whole-KB gate callback answers for a reader's belief
  (`tax/install-supporter-visibility!`): nil when no `except` and no `defeat` is stored,
  else the entries `[defeat targets]` and `[except targets]`, each a delay of the set of
  handles the stored facts of that functor name.  Two counts on the index."
  [kb]
  (named-entries kb true))

(defn except-roster
  "`supporter-roster` over the stored `except`s alone: what a firing's witness search
  reads (`tax/*network-belief*`)."
  [kb]
  (named-entries kb false))

(defn placed-reads?
  "Does a read owe the walk over the placed nogoods (`defeat-hidden-fn`): a `defeat` is
  stored, or a placed `(contradicts …)` beside a stored `except`, which can lower a
  member's class at the reader that sees it (`conflict-loser?`)."
  [kb]
  (let [idx (:index kb)]
    (boolean (or (reads/stores-any? idx sx/defeat-functor)
                 (and (reads/stores-any? idx sx/except-functor)
                      (pos? (reads/stored-count-with-functor idx 'contradicts)))))))

(defn- exemption-reads?
  "Can a placement be exempt at some reader (`exempt-justifications`): a `(contradicts …)`
  is stored beside a `siblingDisjointException` or an equality edge.  The whole-KB gate
  of `exempting-at?`."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (and (or (tax/sib-exceptions? tax) (seq (tax/equality-edges tax)))
         (pos? (reads/stored-count-with-functor (:index kb) 'contradicts)))))

(defn- denial-stored?
  "Is a denial of `pred` stored: a unary one in its denied terms, or the predicate
  extent, which holds both polarities, counting more facts than its positive shapes do.
  A gate over every context, read in a few counts; the walk asks each handle at its
  reader."
  [kb pred]
  (let [idx (:index kb)]
    (boolean
     (or (seq (reads/as-stored-unary-denied-terms idx pred))
         (> (reads/stored-count-with-functor idx pred)
            (transduce (map #(reads/stored-count-shape-tuples-global idx pred %)) +
                       (reads/as-stored-shape-lengths idx pred)))))))

(defn- roster-reads?
  "Can the declared roster hide a handle at some reader: a predicate on the roster by a
  declaration off the global roster (`decide/declared`) has a stored denial
  (`denial-stored?`), a rule reading it or a rule concluding it, or a rule's consequent
  functor is a variable.
  A reader that sees the declaration and one that does not read those apart.  Read over
  every context: it is the whole-KB gate of `walk-reads?`, and each reader scopes it
  (`roster-state`)."
  [kb]
  (let [idx (:index kb)]
    (boolean (when-let [declared (seq (decide/declared (reasoning/taxonomy kb)))]
               (or (seq (reads/as-stored-rules-by-consequent-global idx p/var-consequent-key))
                   (some (fn [[[_ pred]]]
                           (or (denial-stored? kb pred)
                               (seq (reads/as-stored-rules-by-antecedent-global idx pred))
                               (seq (reads/as-stored-rules-by-consequent-global idx pred))))
                         declared))))))

(defn walk-reads?
  "Does a belief-filtered read owe the walk (`defeat-hidden-fn`): `placed-reads?`, a
  placement some reader can exempt (`exemption-reads?`), or a declared roster that can
  hide a handle at some reader (`roster-reads?`)."
  [kb]
  (boolean (or (placed-reads? kb) (exemption-reads? kb) (roster-reads? kb))))

(defn- exempting-at?
  "Can a placement be exempt at a reader with ancestor set `up`: `exemption-reads?`, a
  `(contradicts …)` stated in a context of `up`, and an exemption source the reader sees,
  which is a `siblingDisjointException` or an equality relation stated in a context of
  `up`.  Each extent is read by context (`reads/stores-in?`), so the answer is flat in the
  placements and sources stated where the reader does not see."
  [kb up]
  (let [idx (:index kb)
        in? #(reads/stores-in? idx % up)]
    (boolean (and (exemption-reads? kb)
                  (in? 'contradicts)
                  (or (in? 'siblingDisjointException)
                      (some in? rewrite/equality-relations))))))

;; The roster reading decides which declarations the reader sees (`roster-state`), through
;; `in-force?`, whose verdict reads the roster (`roster-member-fn`): the two recur into
;; each other.  `verdict-at` and `mark-defeated` recur through a mark's own defeat.
(declare in-force?)

(defn- roster-state
  "What the declared roster reads at a reader with ancestor set `up`: `:on?`, its roster
  reading (`decide/reader-reading`), which sees a declaration IN in the network, stated in
  a context of `up`, hidden by no except in force there and named by no `defeat` in force
  at the reader (`in-force?`, read over the global roster); `:inert?`, whether a predicate
  it reads on the roster by a declaration has a stored denial (`denial-stored?`); and
  `:void?`, whether a predicate declared where it does not see is read by a rule stated in
  `up`, or one it sees declared is concluded by one, or a rule stated in `up` concludes a
  variable functor.
  The rules are read off the antecedent index over every context and kept by `up`: the
  index has no by-context entry point.  `:inert?` and `:void?` read the denial and the
  rules before `seen?`, so `in-force?` runs only for a predicate one of them reads."
  [kb tax tms up excepted?]
  (let [declared  (decide/declared tax)
        idx       (:index kb)
        base      (delay {:kb kb :tax tax :tms tms :recs (:records kb) :idx idx :up up
                          :excepted? excepted? :exempting? (exempting-at? kb up)
                          :roster {:on? (decide/global-reading tax)}})
        ;; each declaration's answer is read once per roster state, with a memo of its own
        answers   (volatile! {})
        defeated? (fn [h]
                    (let [v (get @answers h ::absent)]
                      (if (identical? ::absent v)
                        (let [r (boolean
                                 (when-let [ds (seq (reads/as-stored-naming idx sx/defeat-functor h up))]
                                   (let [st (assoc @base :memo (volatile! {}))]
                                     (some #(in-force? st %) ds))))]
                          (vswap! answers assoc h r)
                          r)
                        v)))
        seen?    (fn [h c] (and (contains? up c) (jtms/in? tms h) (not (and excepted? (excepted? h)))
                                (not (defeated? h))))
        on?      (if (seq declared) (decide/reader-reading tax seen?) (decide/global-reading tax))]
    (if (empty? declared)
      {:on? on?}
      (let [recs  (:records kb)
            sees? (fn [[_ ds]] (boolean (some (fn [[h c]] (seen? h c)) ds)))]
        {:on?    on?
         :inert? (boolean (some (fn [[[_ pred] :as e]] (and (denial-stored? kb pred) (sees? e)))
                                declared))
         :void?  (boolean
                  (or (some (fn [[[_ pred] :as e]]
                              (and (some #(contains? up (:context (p/get-sentex recs %)))
                                         (reads/as-stored-rules-by-antecedent-global idx pred))
                                   (not (sees? e))))
                            declared)
                      (some (fn [[[_ pred] :as e]]
                              (and (seq (reads/as-stored-rules-by-consequent-in idx pred up))
                                   (sees? e)))
                            declared)
                      (and (seq (reads/as-stored-rules-by-consequent-in idx p/var-consequent-key up))
                           (some sees? declared))))}))))

(defn- reader-state
  "What the walk reads at `ctx`, with the one-read memo, or nil when `ctx` is a variable,
  the read takes the network reading (`tax/*network-belief*`), or no defeat is stored, no
  except is in force at `ctx` and no placement can be exempt at `ctx` (`exempting-at?`).
  `:closable?` is true when only a defeat stated in a context `ctx` sees can hide a
  handle there: no except is stated in one, no placement can be exempt (`region-at`) and
  the declared roster hides nothing there (`roster-state`).
  The ancestor set is the unscoped one (`tax/context-up-global`), as `excepts-seen`'s is:
  the scoped `context-up` is itself filtered by what the reader does not believe."
  [kb ctx]
  (let [idx   (:index kb)
        ndefs (reads/stored-count-at idx [sx/defeat-functor])]
    (when-not (or tax/*network-belief* (sx/variable? ctx) (not (walk-reads? kb)))
      (let [tax        (reasoning/taxonomy kb)
            up         (tax/context-up-global tax ctx)
            tms        (reasoning/tms kb)
            excepted?  (except-hidden-fn kb ctx)
            exempting? (exempting-at? kb up)
            roster     (roster-state kb tax tms up excepted?)
            hides?     (boolean (or (:inert? roster) (:void? roster)))]
        (when (or (pos? ndefs) excepted? exempting? hides?)
          {:kb kb :ctx ctx :tms tms :recs (:records kb) :tax tax :up up
           :idx idx
           :excepted? excepted?
           :exempting? exempting?
           :roster roster
           :closable? (not (or excepted? exempting? hides?))
           :conflicts? (pos? (reads/stored-count-with-functor (:index kb) 'contradicts))
           :memo (volatile! {})})))))

(defn- sees-defeat?
  "Is a defeat stated in a context of the reader's ancestor set: the contexts `defeat`'s
  predicate extent lists, intersected with that set, kept in the read's memo.  The extent
  holds both polarities, and no `(not (defeat …))` is stored: `checks/check-no-defeat`
  refuses `defeat` in every asserted literal, a negation included, and the engine stores
  only the positive form."
  [{:keys [idx up memo]}]
  (let [v (get @memo ::sees-defeat ::absent)]
    (if (identical? ::absent v)
      (let [r (reads/stores-in? idx sx/defeat-functor up)]
        (vswap! memo assoc ::sees-defeat r)
        r)
      v)))

(defn- mark-key?
  "Is taxonomy key `k` a permuting or `reifiable_function` mark's: `[:prop :symmetric p]`,
  `[:commuting p g]` or `[:prop :reifiable f]`?"
  [k]
  (case (nth k 0 nil)
    :prop      (contains? #{:symmetric :reifiable} (nth k 1 nil))
    :commuting true
    false))

(defn- in-mark-support?
  "Is `t` in the support of a mark statement (`support`, read upward): `t` or a handle
  above it installs a mark key (`mark-key?`, `reads/as-stored-installed-keys`), each step
  up a justification that rests on the handle below and concludes a handle that is not a
  premise, since `support` does not descend past one."
  [tms idx t]
  (loop [seen #{}, stack [t]]
    (if-let [x (peek stack)]
      (let [stack (pop stack)]
        (cond
          (contains? seen x) (recur seen stack)
          (some mark-key? (reads/as-stored-installed-keys idx x)) true
          :else (recur (conj seen x)
                       (into stack (comp (keep #(jtms/justification tms %))
                                         (filter #(some #{x} (jtms/rests-on %)))
                                         (map :consequence)
                                         (remove #(jtms/premise? tms %)))
                             (jtms/dependents tms x)))))
      false)))

(defn- mark-hazard?
  "Does a defeat stated in a context the reader sees name a handle in the support of a
  statement of a permuting or `reifiable_function` mark (`mark-key?`)?  A defeat hides a
  `:monotonic` handle only through such a mark: a `respell` justification rests on its
  marks and takes its class from the written row alone (`jtms/class-antecedents`).  Read
  once per read and kept in its memo, from the smaller side by index counts: the defeats
  stated in contexts of the reader's ancestor set, each target walked up its dependents
  (`in-mark-support?`), or the mark statements, each walked down its support with an index
  read per handle.  The marks are read from every context, since a mark the reader does
  not see still sorts the rows it reads (`tax/has-prop?`)."
  [{:keys [tms tax idx recs up memo] :as st}]
  (let [v (get @memo ::mark-hazard ::absent)]
    (if (identical? ::absent v)
      (let [t  @tax
            r  (boolean
                (and (sees-defeat? st)
                     (if (<= (reads/stored-count-with-functor-in idx sx/defeat-functor up)
                             (+ (count (get-in t [:props :symmetric])) (count (:commuting t))
                                (count (get-in t [:props :reifiable]))))
                       (some #(some->> (defeat-target* (:sentence (p/get-sentex recs %)))
                                       (in-mark-support? tms idx))
                             (reads/as-stored-with-functor-in idx sx/defeat-functor up))
                       (some (fn [k]
                               (some (fn [m] (some #(reads/as-stored-naming idx sx/defeat-functor % up)
                                                   (support tms m (constantly false))))
                                     (keys (tax/supporters tax k))))
                             (concat (map #(vector :prop :symmetric %) (get-in t [:props :symmetric]))
                                     (for [[p gs] (:commuting t), g gs] [:commuting p g])
                                     (map #(vector :prop :reifiable %) (get-in t [:props :reifiable])))))))]
        (vswap! memo assoc ::mark-hazard r)
        r)
      v)))

(defn- region-at
  "The support of `h` the walk reads at the reader (`support` with `stop?`), or nil when
  nothing in it can be hidden there: the reader's state is `:closable?` and no defeat is
  stated in a context it sees (`sees-defeat?`, read before any support handle).  A read
  there costs the defeat extent's contexts the reader sees, flat in the depth of the
  support and in the defeats stated elsewhere."
  [{:keys [tms closable?] :as st} h stop?]
  (when (or (not closable?) (sees-defeat? st))
    (support tms h stop?)))

(defn- by-content
  "The handles `hs` in content order (sentence, then context)."
  [recs hs]
  (nm/sort-by-content-key (fn [d] (let [s (p/get-sentex recs d)] [(:sentence s) (:context s)])) hs))

(defn- nogood-justifications
  "The justifications of the handle `x` under `nogood-informant`."
  [tms x]
  (into [] (comp (keep #(jtms/justification tms %)) (filter #(= nogood-informant (:informant %))))
        (jtms/supports tms x)))

(defn- member-sets
  "Each `nogood` justification of the defeat `d` naming `l`, paired with the members of
  the placed nogood it concludes: `[j members contradicts]`, where `contradicts` is the
  `(contradicts …)` at `d`'s context with a `nogood` justification on the same
  antecedents, read off the term index by `l`.  A defeat several nogoods share has one
  pair per nogood, in content order of their `contradicts`."
  [{:keys [kb recs tms]} d l]
  (when-let [js (seq (nogood-justifications tms d))]
    (let [ctx   (:context (p/get-sentex recs d))
          ctrs  (into [] (keep (fn [h]
                                 (let [c (p/get-sentex recs h) s (:sentence c)]
                                   (when (and (seq? s) (= 'contradicts (first s)) (= ctx (:context c)))
                                     [h (into #{} (map sx/handle-id) (rest s))
                                      (into #{} (map #(set (:antecedents %)))
                                            (nogood-justifications tms h))]))))
                      (reads/as-stored-with-term (:index kb) (sx/sentex-handle l)))
          order (zipmap (by-content recs (map first ctrs)) (range))]
      (sort-by (comp order peek)
               (for [j js, [h ms antes] ctrs :when (contains? antes (set (:antecedents j)))]
                 [j ms h])))))

(defn- mark-defeated
  "The handles of `region`, a support, that a defeat in force at the reader names and that
  lie in the support of a mark a `respell` justification of `region` rests on
  (`jtms/respell-informant`, every antecedent but the first)."
  [{:keys [tms idx up] :as st} region]
  (let [marks (into #{} (comp (mapcat #(jtms/supports tms %)) (keep #(jtms/justification tms %))
                              (filter #(= jtms/respell-informant (:informant %)))
                              (mapcat #(rest (:antecedents %))))
                    region)]
    (into #{} (filter (fn [t] (some #(in-force? st %) (reads/as-stored-naming idx sx/defeat-functor t up))))
          (into #{} (mapcat #(support tms % (constantly false))) marks))))

(defn- roster-member-fn
  "`(fn [h])`: is the handle `h` a roster literal as the reader reads the roster
  (`roster-state`'s `:on?`)?"
  [{:keys [recs tax roster]}]
  (fn [h] (boolean (some-> (p/get-sentex recs h) :sentence
                           (as-> s (decide/roster-literal? tax s (:on? roster)))))))

(defn- roster-inert?
  "Is the handle `x` a denial of a literal the reader reads on the roster and the global
  roster does not hold: inert at the reader, where the network, reading the global roster,
  holds it IN?"
  [{:keys [recs tax roster]} x]
  (let [s (:sentence (p/get-sentex recs x))]
    (boolean (and (sx/negation? s)
                  (decide/roster-literal? tax (second s) (:on? roster))
                  (not (decide/roster-literal? tax (second s) (decide/global-reading tax)))))))

(defn- excepted-rule?
  "Does a believed `exceptWhen` stand against the rule at `rh`: one stored against it,
  IN in the network, read off the term index once the rule is on the watched roster
  (`provers/rule-exception-entries` reads the same records)."
  [{:keys [tms recs idx]} rh]
  (boolean (and (reads/watched-rule? idx rh)
                (some #(when-let [s (:sentence (p/get-sentex recs %))]
                         (and (sx/exceptWhen-meta? s) (= rh (sx/exceptWhen-rule-handle s))
                              (jtms/in? tms %)))
                      (reads/as-stored-with-term idx (sx/sentex-handle rh))))))

(defn- roster-void
  "The ids of the justifications of `x` the reader reads void: a rule firing valid in the
  network, whose conclusion `x` is a roster literal at the reader, and whose rule is no
  roster rule there: an antecedent off the reader's roster, an `unknown` antecedent, a
  `set/defaultRule`, or a believed `exceptWhen`.  The network reads the antecedents on
  the union over every reader and the conclusion on the global roster
  (`checks/network-void?`), so such a firing is valid there through a declaration this
  reader does not see, or because its conclusion is on the roster only by a declaration
  this reader sees."
  [{:keys [tms recs tax roster] :as st} x]
  (let [on? (:on? roster)
        s   (:sentence (p/get-sentex recs x))]
    (when (and s (not (sx/negation? s)) (decide/roster-literal? tax s on?))
      (into #{}
            (comp (keep #(jtms/justification tms %))
                  (filter (fn [j]
                            (and (not (jtms/forced? tms :void (:id j)))
                                 (when-let [r (p/get-sentex recs (:informant j))]
                                   (when-let [antes (seq (:antecedent r))]
                                     (or (:defeasible r)
                                         (some sx/unknown? antes)
                                         (some #(not (decide/roster-literal? tax % on?)) antes)
                                         (excepted-rule? st (:informant j))))))))
                  (map :id))
            (jtms/supports tms x)))))

(defn- verdict-at
  "`decide/verdict` over `members` with the classes the reader reads: the network's, or,
  where an except in force at the reader reaches the members' support, or a defeat in
  force there reaches a mark a `respell` justification in it rests on (`mark-defeated`),
  the classes the support carries with those targets forced OUT
  (`jtms/classes-in-region`).  nil when such a target hides a member.  The roster is the
  reader's (`roster-member-fn`)."
  [{:keys [tms excepted?] :as st} members]
  (let [roster? (roster-member-fn st)
        marks?  (mark-hazard? st)
        region  (when (or excepted? marks?)
                  (into #{} (mapcat #(support tms % (constantly false) true)) members))
        ex      (cond-> #{}
                  excepted? (into (filter excepted?) region)
                  marks?    (into (mark-defeated st region)))]
    (if (empty? ex)
      (decide/verdict #(or (jtms/defeat-class tms %) :default) roster? members)
      (let [in (jtms/region-in tms region region #{} ex belief-only-antecedent #{})]
        (when (every? #(contains? in %) members)
          (let [classes (jtms/classes-in-region tms region in)]
            (decide/verdict #(get classes % :default) roster? members)))))))

;; `in-force?` reads whether the defeat itself is believed and seen at the reader
;; (`believed-in`), and `believed-in` reads which defeats are in force over the support
;; it walks: a defeat's own support holds its target, so the two recur into each other.
;; `guard-in-force?` reads a guard defeat's blockers through `believed-in` too
;; (`guard-seen-fn`).
(declare believed-in)

(defn- unseen-fn
  "`(fn [h])`: does the reader not believe and see the handle `h`, IN in the network
  (`believed-in` with the excepts)?  Each answer is kept in the read's memo (`kept`).  The
  exemptions read the reader's bindings and equality supporters through it
  (`decide/exempt-at?`)."
  [{:keys [memo] :as st}]
  (fn [h] (kept memo [::unseen h] #(not (believed-in st h true)))))

(defn- in-force?
  "Is the defeat at `d` in force at the reader: IN, no except in force hiding it, and IN
  at the reader through one of its `nogood` justifications whose nogood convicts its
  target there.  A nogood convicts when the verdict at the reader over its members names
  the target and no `siblingDisjointException`, equality edge or binding the reader reads
  removes it (`decide/exempt-at?`).  The justification is read with the defeat's other
  justifications invalid, the excepts in force and the target exempt
  (`placed-belief-only`).  A `guard` justification never counts here (`guard-covered`).
  A defeat met again while it is being read closes a cycle (`in-force-once`)."
  [{:keys [tms recs excepted?] :as st} d]
  (in-force-once
   st d
   (fn []
     (let [l (defeat-target* (:sentence (p/get-sentex recs d)))]
       (boolean
        (and l (jtms/in? tms d)
             (not (and excepted? (excepted? d)))
             (let [pairs    (member-sets st d l)
                   convicts (into #{} (comp (map second) (distinct)
                                            (filter #(and (= {:defeat l} (verdict-at st %))
                                                          (not (decide/exempt-at? (:kb st) % (:up st)
                                                                                  (unseen-fn st))))))
                                  pairs)
                   through  (into #{} (keep (fn [[j ms]] (when (convicts ms) (:id j)))) pairs)]
               (and (seq through)
                    (believed-in st d true (into #{} (remove through) (jtms/supports tms d)))))))))))

(defn- conflict-in-force?
  "Is the placed `(contradicts …)` at `c` a conflict the reader decides against its member
  `x`: placed for a nogood in a context the reader sees, IN and hidden by no except in
  force there, a conflict in the network on the roster the reader reads
  (`decide/verdict` answers `:hard`, `roster-member-fn`), the verdict at the reader over
  its members naming `x` (`verdict-at`, whose classes the reader's excepts lower), and `c`
  IN at the reader through one of its `nogood` justifications, read as `in-force?` reads a
  defeat's.  A contradicts met again while it is being read
  closes a cycle (`in-force-once`)."
  [{:keys [tms recs up excepted?] :as st} c x]
  (in-force-once
   st [::conflict c x]
   (fn []
     (let [sx  (p/get-sentex recs c)
           ms  (into #{} (map sx/handle-id) (rest (:sentence sx)))
           njs (into #{} (map :id) (nogood-justifications tms c))]
       (boolean
        (and (contains? up (:context sx)) (jtms/in? tms c)
             (not (excepted? c))
             (seq njs)
             ;; a conflict in the network, the roster read as this reader reads it: a
             ;; decided nogood's `defeat` governs its loser, and an except of it releases it
             (= :hard (decide/verdict #(or (jtms/defeat-class tms %) :default)
                                      (roster-member-fn st)
                                      ms))
             (= {:defeat x} (verdict-at st ms))
             (not (decide/exempt-at? (:kb st) ms up (unseen-fn st)))
             (believed-in st c true (into #{} (remove njs) (jtms/supports tms c)))))))))

(defn- conflicts-naming
  "The placed `(contradicts …)` handles that name `x` and are conflicts the reader decides
  against it (`conflict-in-force?`).  Read only while an except is in force at the reader:
  a conflict's members are `:monotonic` in the network, and only an except lowers one
  (docs/nmtms.md, \"A nogood placed as a conclusion\")."
  [{:keys [kb recs excepted? conflicts?] :as st} x]
  (when (and excepted? conflicts?)
    (into [] (filter (fn [c] (let [s (:sentence (p/get-sentex recs c))]
                               (and (seq? s) (= 'contradicts (first s))
                                    (conflict-in-force? st c x)))))
          (reads/as-stored-with-term (:index kb) (sx/sentex-handle x)))))

(defn- own-loser
  "What a placed nogood's or a guard's justification `j` removes from belief: `[:defeat
  l]` for the target `l` of the `defeat` it concludes, or of the `defeat` stored in the same context
  under a justification with the same antecedents; `[:conflict c]` for a `(contradicts
  …)` `c` with no such `defeat`, whose member a reader whose excepts lower its class reads
  as defeated (`conflict-in-force?`); nil for another justification."
  [{:keys [tms recs idx]} j]
  (if (= guard-informant (:informant j))
    (some->> (defeat-target* (:sentence (p/get-sentex recs (:consequence j)))) (vector :defeat))
    (when (= nogood-informant (:informant j))
      (let [c (p/get-sentex recs (:consequence j))
            s (:sentence c)]
        (or (some->> (defeat-target* s) (vector :defeat))
            (let [antes (set (:antecedents j))]
              (some (fn [a]
                      (when (some (fn [dh]
                                    (some #(and (= nogood-informant (:informant %))
                                                (= antes (set (:antecedents %))))
                                          (keep #(jtms/justification tms %) (jtms/supports tms dh))))
                                  (reads/as-stored-naming idx sx/defeat-functor a #{(:context c)}))
                        [:defeat a]))
                    (:antecedents j)))
            (when (= 'contradicts (nm/functor s))
              [:conflict (:consequence j)]))))))

(defn- placed-belief-only
  "`belief-only-antecedent` with the exemption: a placed nogood's justification reads its
  own loser at its label when nothing but its own reading hides the loser at the reader,
  so the nogood's conclusions do not rest on the handle they hide.  A `defeat`'s target is
  exempt when a defeat or a conflict hides it (`by-defeat`) and nothing else does
  (`by-other`); a conflict's member is exempt when that conflict's placements alone hide
  it (`by-conflict`, `{handle #{contradicts}}`)."
  [st by-defeat by-conflict by-other]
  (fn [j]
    (or (belief-only-antecedent j)
        (when-let [[k x] (own-loser st j)]
          (case k
            :defeat   (when (and (or (contains? by-defeat x) (contains? by-conflict x))
                                 (not (contains? by-other x)))
                        x)
            :conflict (let [same? (let [s (:sentence (p/get-sentex (:recs st) x))]
                                    (fn [c] (= s (:sentence (p/get-sentex (:recs st) c)))))]
                        (some (fn [[m cs]]
                                (when (and (every? same? cs) (not (contains? by-defeat m))
                                           (not (contains? by-other m)))
                                  m))
                              by-conflict)))))))

(defn- exempt-justifications
  "The `nogood` justifications of the placed `(contradicts …)` or `defeat` at `x` whose
  nogood the reader reads no conviction of (`decide/exempt-at?`): an inherited placement
  whose mark route a `siblingDisjointException` the reader sees exempts, whose two fillers
  the reader reads as one class, or whose binding the reader does not read as binding the
  functor.  A defeat several nogoods share loses only the justifications of the exempt
  ones (`member-sets`)."
  [{:keys [kb tms recs up] :as st} x]
  (let [s       (:sentence (p/get-sentex recs x))
        exempt? #(decide/exempt-at? kb % up (unseen-fn st))]
    (if (and (seq? s) (= 'contradicts (first s)))
      (let [js (nogood-justifications tms x)]
        (when (and (seq js) (exempt? (into #{} (map sx/handle-id) (rest s))))
          (into #{} (map :id) js)))
      (when-let [l (defeat-target* s)]
        (into #{} (keep (fn [[j ms]] (when (exempt? ms) (:id j)))) (member-sets st x l))))))

(defn guard-owners
  "The ids of the justifications among `js` the `guard` justification `g` belongs to: of
  those whose rule and antecedents `g`'s antecedents hold and whose bindings `g` carries
  (read off `recs`; a `g` with no bindings matches on its antecedents alone), each that
  no other one of the same rule holds a proper superset of the antecedents of.  A guard
  justification rests on its firing's antecedents, so a second firing of the rule with
  equal bindings over a subset of them is not taken for its owner."
  [recs g js]
  (let [ga   (set (:antecedents g))
        gb   (:bindings (p/get-justification recs (:id g)))
        held (into [] (comp (filter #(every? ga (conj (:antecedents %) (:informant %))))
                            (filter #(or (empty? gb)
                                         (= gb (:bindings (p/get-justification recs (:id %))))))
                            (map (fn [j] [j (set (:antecedents j))])))
                   js)
        within? (fn [[j a] [k b]] (and (= (:informant j) (:informant k))
                                       (< (count a) (count b)) (every? b a)))]
    (into #{} (keep (fn [ja] (when-not (some #(within? ja %) held) (:id (first ja))))) held)))

(defn- guard-justifications-of
  "The `guard` justifications of the defeat `d`."
  [tms d]
  (into [] (comp (keep #(jtms/justification tms %))
                 (filter #(= guard-informant (:informant %))))
        (jtms/supports tms d)))

(defn- guard-seen-fn
  "`(fn [g])`: is every blocker of the guard justification `g` of a defeat of `x` believed
  and seen at the reader?  A blocker is an antecedent of `g` other than `x` and the rule
  and antecedents of a firing of `x` that `g` belongs to (`guard-owners`).  The firing's
  own antecedents are not read: where one is not believed the firing is void there, and
  dropping it moves nothing."
  [{:keys [tms recs] :as st} x]
  (let [js (delay (into [] (keep #(jtms/justification tms %)) (jtms/supports tms x)))]
    (fn [g]
      (let [owners (guard-owners recs g @js)
            fired  (into #{x} (comp (filter #(contains? owners (:id %)))
                                    (mapcat #(conj (:antecedents %) (:informant %))))
                         @js)]
        (not-any? #(and (not (contains? fired %)) ((unseen-fn st) %)) (:antecedents g))))))

(defn- guard-in-force?
  "Is the guard defeat at `d`, naming `x`, in force at the reader: IN, no except in force
  hiding it, and one of its `guard` justifications seen there (`guard-seen-fn`).  The
  justifications are read inside the defeat's own read and kept in the read's memo for
  `guard-covered`, so a guard defeat whose blocker rests on a firing another guard
  defeat removes is met again as a cycle (`in-force-once`), not read without end."
  [{:keys [tms excepted? memo] :as st} d x]
  (in-force-once st [::guard d]
                 #(boolean (and (jtms/in? tms d)
                                (not (and excepted? (excepted? d)))
                                (seq (let [seen (filterv (guard-seen-fn st x)
                                                         (guard-justifications-of tms d))]
                                       (vswap! memo assoc [::guard-seen d] seen)
                                       seen))))))

(defn- guard-covered
  "The justifications of `x` a guard defeat in force at the reader covers: those a
  justification of that defeat belongs to (`guard-owners`), where that justification's
  blockers are believed and seen at the reader (docs/naf.md, \"A guard below the
  placement places a defeat\")."
  [{:keys [tms idx up memo recs] :as st} x]
  (let [gjs (into [] (mapcat (fn [d] (when (guard-in-force? st d x)
                                       (get @memo [::guard-seen d]))))
                  (reads/as-stored-naming idx sx/defeat-functor x up))]
    (when (seq gjs)
      (let [js (into [] (keep #(jtms/justification tms %)) (jtms/supports tms x))]
        (into #{} (mapcat #(guard-owners recs % js)) gjs)))))

(defn- believed-set
  "The handles of `h`'s support the reader believes, or ::all when the walk hides none of
  them.  Each justification a guard defeat covers there is dropped (`guard-covered`),
  each `nogood` justification of a placement the reader exempts is dropped
  (`exempt-justifications`), each of the justification ids `invalid` is dropped, and each
  target hidden at the reader in `h`'s support is forced OUT — a defeat in force naming it, a placed conflict the reader
  decides against it (`conflicts-naming`), and, with `with-excepts?`, an except in force
  naming it (`jtms/region-in` over the support).  A justification that rests on a forced
  witness edge reads it at its label where the reader reaches the path's ends another way
  (`rerouted`).  With no except stated in a context the reader sees and no defeat it sees
  reaching a permuting mark (`mark-hazard?`), a `:monotonic` handle is taken at its label,
  since a defeat is in force only over a `:default` target, only an except lowers a class,
  and only a `respell` justification rests on a handle that caps no class; and the
  support is not walked when nothing in it can be hidden there (`region-at`)."
  [{:keys [tms excepted? exempting? up idx roster] :as st} h with-excepts? invalid]
  (if-let [region (region-at st h (if (or excepted? (:inert? roster) (:void? roster))
                                    (constantly false)
                                    #(and (= :monotonic (jtms/defeat-class tms %))
                                          (not (mark-hazard? st)))))]
    (let [;; every defeat naming `x` is read, so the cycle a read meets is the same
          ;; whichever defeat the index lists first
          by-def  (into #{} (filter (fn [x] (reduce (fn [hit d] (or (in-force? st d) hit))
                                                    false
                                                    (reads/as-stored-naming idx sx/defeat-functor x up))))
                        region)
          by-conf (into {} (keep (fn [x] (when-let [cs (seq (conflicts-naming st x))] [x (set cs)])))
                        region)
          other   (cond-> (if (and with-excepts? excepted?) (into #{} (filter excepted?) region) #{})
                    (:inert? roster) (into (filter #(roster-inert? st %)) region))
          by-cov  (into {} (keep (fn [x] (when-let [js (not-empty (guard-covered st x))] [x js])))
                        region)
          invalid (cond-> (into invalid (mapcat val) by-cov)
                    exempting?      (into (mapcat #(exempt-justifications st %)) region)
                    (:void? roster) (into (mapcat #(roster-void st %)) region))
          forced  (-> by-def (into (keys by-conf)) (into other))]
      (if (and (empty? forced) (empty? invalid))
        ::all
        (let [belief (with-routes (placed-belief-only st (into by-def (keys by-cov)) by-conf other)
                       (when (seq forced) (rerouted st region forced with-excepts?)))]
          (jtms/region-in tms region region #{} forced belief invalid))))
    ::all))

(defn- believed-in
  "Does the reader believe the handle `h` (`with-excepts?` false), or believe and see it
  (true): `h` is among the support handles `believed-set` reads as believed there."
  ([st h with-excepts?] (believed-in st h with-excepts? #{}))
  ([st h with-excepts? invalid]
   (let [in (believed-set st h with-excepts? invalid)]
     (or (= ::all in) (contains? in h)))))

(defn defeat-hidden-fn
  "A predicate `(fn [handle])` answering whether `ctx` reads `handle`, IN in the network, as
  removed by the placed defeats it sees, or **nil** when no defeat is stored.  With
  `with-excepts?` false this is belief: `handle` is not believed at `ctx`.  With it true
  it is visibility as well: the excepts in force at `ctx` are forced OUT beside the
  defeats, so a handle resting on an excepted handle and a defeated one is hidden.

  A defeat is in force at `ctx` while it is IN, stated in a context `ctx` sees, not hidden
  by an except in force, its nogood's verdict at `ctx` names its target
  (`decide/verdict`), and it is believed and seen at `ctx` with its own target exempt.
  The predicate holds a memo for its own lifetime and nothing past it."
  [kb ctx with-excepts?]
  (when-let [st (reader-state kb ctx)]
    (fn [handle]
      (boolean (and (jtms/in? (:tms st) handle)
                    (not (believed-in st handle with-excepts?)))))))

(defn defeats-hiding
  "The defeats in force at `ctx` whose targets lie in `handle`'s support, and the placed
  conflicts `ctx` decides against a handle there (`conflicts-naming`), in content order:
  what `defeat-hidden-fn` forced OUT to read `handle` as not believed there."
  [kb handle ctx]
  (when-let [{:keys [tms recs up idx] :as st} (reader-state kb ctx)]
    (by-content recs (into [] (comp (mapcat #(concat (filter (fn [d] (in-force? st d))
                                                             (reads/as-stored-naming idx sx/defeat-functor % up))
                                                     (conflicts-naming st %)))
                                    (distinct))
                           (support tms handle (constantly false))))))

(defn defeats-of
  "The defeats naming `handle` that are in force at `ctx`, and the placed conflicts `ctx`
  decides against it (`conflicts-naming`), in content order."
  [kb handle ctx]
  (when-let [{:keys [recs up idx] :as st} (reader-state kb ctx)]
    (by-content recs (into (filterv #(in-force? st %) (reads/as-stored-naming idx sx/defeat-functor handle up))
                           (conflicts-naming st handle)))))

(defn- roster-at
  "`roster-state` at `ctx` outside a read walk: over the unscoped ancestor set, as
  `reader-state` reads it, since which declarations a reader sees is read as the excepts
  it sees are (`excepts-seen`), and with the excepts in force there."
  [kb ctx]
  (let [tax (reasoning/taxonomy kb)]
    (roster-state kb tax (reasoning/tms kb)
                  (if (sx/variable? ctx) #{} (tax/context-up-global tax ctx))
                  (when-not (sx/variable? ctx) (except-hidden-fn kb ctx)))))

(defn roster-hidden-own-fn
  "A predicate `(fn [h])` answering whether the declared roster alone hides the handle `h`
  at its own context: a denial inert there (`roster-inert?`), or a handle with no premise
  mark every justification of which is a firing void there (`roster-void`); or nil when
  no declaration off the global roster is stored.  A justification the network holds void
  (`:void`) counts for neither side.  Both read the roster and `h`'s
  justifications only, so the answer is the same before and after a write that moves no
  declaration and removes none of `h`'s justifications.  The reader state of each context
  is kept for the predicate's lifetime."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (when (seq (decide/declared tax))
      (let [tms  (reasoning/tms kb)
            recs (:records kb)
            sts  (volatile! {})
            at   (fn [c] (or (get @sts c)
                             (let [st {:recs recs :tax tax :tms tms :idx (:index kb) :roster (roster-at kb c)}]
                               (vswap! sts assoc c st)
                               st)))]
        (fn [h]
          (boolean
           (when-let [c (:context (p/get-sentex recs h))]
             (let [st (at c)]
               (or (roster-inert? st h)
                   (and (not (jtms/premise? tms h))
                        (let [js (remove #(jtms/forced? tms :void %) (jtms/supports tms h))]
                          (and (seq js) (= (count js) (count (roster-void st h)))))))))))))))

(defn verdict-at-reader
  "`decide/verdict` over the placed nogood `members` as `ctx` reads it (`verdict-at`): the
  network's classes, or those `ctx`'s excepts leave; the network's verdict when the walk
  reads nothing at `ctx` (`reader-state`), over the roster `ctx` reads (`roster-state`)."
  [kb members ctx]
  (if-let [st (reader-state kb ctx)]
    (verdict-at st members)
    (let [tms (reasoning/tms kb)]
      (decide/verdict #(or (jtms/defeat-class tms %) :default)
                      (roster-member-fn {:recs (:records kb) :tax (reasoning/taxonomy kb)
                                         :roster (roster-at kb ctx)})
                      members))))

(defn roster-inert-at?
  "Is the handle `h`, IN in the network, a denial `ctx` reads as inert: the denial of a
  literal on the roster by a declaration `ctx` sees (`roster-state`)?"
  [kb h ctx]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (and (jtms/in? (reasoning/tms kb) h) (seq (decide/declared tax))
                  (roster-inert? {:recs (:records kb) :tax tax :roster (roster-at kb ctx)} h)))))

(defn roster-reading
  "The roster reading `(fn [kind pred])` of `ctx` (`roster-state`'s `:on?`)."
  [kb ctx]
  (:on? (roster-at kb ctx)))

(defn roster-void-at
  "The ids of the justifications of `h` that `ctx` reads void (`roster-void`): rule
  firings the network holds valid through a declaration `ctx` does not see."
  [kb h ctx]
  (let [tax (reasoning/taxonomy kb)]
    (when (seq (decide/declared tax))
      (roster-void {:tms (reasoning/tms kb) :recs (:records kb) :idx (:index kb) :tax tax
                    :roster (roster-at kb ctx)}
                   h))))

(defn defeat-member-sets
  "The member sets of the placed nogoods whose `defeat` is the handle `d`, one per nogood
  in content order of their `(contradicts …)`, or nil."
  [kb d]
  (let [recs (:records kb)]
    (when-let [l (defeat-target* (:sentence (p/get-sentex recs d)))]
      (into [] (comp (map second) (distinct))
            (member-sets {:kb kb :recs recs :tms (reasoning/tms kb)} d l)))))

;; ---- the reads: belief and visibility at a reader --------------------------------
;;
;; believed(C) = in − superseded − defeat-hidden(C), visible(C) = believed(C) −
;; except-hidden(C), each answered by the walk over the asked handle's support, with no
;; state kept between reads.  See docs/nmtms.md, "A nogood placed as a conclusion".

(defn- either-fn
  "A predicate true where `f` or `g` is, or the one of them that is not nil, or nil."
  [f g]
  (cond (and f g) (fn [h] (boolean (or (f h) (g h))))
        :else     (or f g)))

(def ^:dynamic *unscoped-own*
  "True while a read that names no reader is answered unscoped (`vantage/answers` with
  nothing to witness, or no reader to fan over): `hidden-fn` of a variable context then
  answers `own-hidden-fn`, so the read believes a handle as its own context does.  False
  for the engine's own unscoped joins, which read the network."
  false)

(defn own-hidden-fn
  "A predicate `(fn [handle])` answering whether `handle`, IN in the network, is not
  believed at the context it is stored in (`defeat-hidden-fn` there, belief only), or nil
  when the walk reads nothing (`walk-reads?`).  The belief filter of every read that names
  no reader (docs/nmtms.md, \"A read with no reader\")."
  [kb]
  (when (walk-reads? kb)
    (let [recs (:records kb)]
      (fn [handle]
        (boolean
         (when-let [c (:context (p/get-sentex recs handle))]
           (when-let [hid (defeat-hidden-fn kb c false)]
             (hid handle))))))))

(defn believed-own?
  "Is `handle` believed as the context it is stored in reads it: IN in the network and
  not removed there (`own-hidden-fn`)?  The answer of every read that names no reader."
  [kb handle]
  (boolean (and (jtms/in? (reasoning/tms kb) handle)
                (not (when-let [hid (own-hidden-fn kb)] (hid handle))))))

(defn own-seq
  "`s`, realized under `*unscoped-own*` one element at a time: a read that names no
  context answers as each handle's own context believes it."
  [s]
  (lazy-seq
   (binding [*unscoped-own* true]
     (when-let [c (seq s)]
       (cons (first c) (own-seq (rest c)))))))

(defn belief-hidden-fn
  "A predicate `(fn [handle])` answering whether `view-context` does not believe `handle`,
  IN in the network, by the placed defeats it sees (`defeat-hidden-fn`, belief only), or
  nil when the walk reads nothing there.  An `except` is visibility and is not applied."
  [kb view-context]
  (when (walk-reads? kb)
    (defeat-hidden-fn kb view-context false)))

(defn hidden-fn
  "A predicate `(fn [handle]) -> boolean` answering whether `view-context` does not see
  `handle`, or **nil** when it hides nothing.  Every belief-filtered read with a concrete
  context asks this.  An except in force naming `handle` hides it
  (`except-hidden-fn`); for a handle IN in the network, so does resting only on an
  excepted handle (`except-closure-hidden-fn`), or not being believed there by the placed
  defeats (`defeat-hidden-fn` with the excepts).  Nil stays the O(1) gate for the KB that
  excepts nothing and holds no placed nogood.  A variable context under `*unscoped-own*`
  answers `own-hidden-fn`.  Inside a second-route search for a belief read (`tax/*search*`
  `:belief`) this answers `belief-hidden-fn`.  Under the network reading
  (`tax/*network-belief*`), the one a placement in `chain` reads, no defeat is read and
  the excepts alone hide."
  [kb view-context]
  (cond
    tax/*network-belief* (either-fn (except-hidden-fn kb view-context)
                                    (except-closure-hidden-fn kb view-context true))
    (and *unscoped-own* (sx/variable? view-context)) (own-hidden-fn kb)
    (= :belief tax/*search*) (belief-hidden-fn kb view-context)
    :else (either-fn (except-hidden-fn kb view-context)
                     (if (walk-reads? kb)
                       (defeat-hidden-fn kb view-context true)
                       (except-closure-hidden-fn kb view-context true)))))

(defn excepted?
  "Is the sentex at `handle` hidden from `view-context` (`hidden-fn`)?  The one-shot form,
  for a caller with a single handle to ask about."
  [kb handle view-context]
  (boolean (when-let [hidden? (hidden-fn kb view-context)] (hidden? handle))))

(defn excepted-in-network?
  "Is `handle` hidden from `view-context` by the excepts alone
  (`except-closure-hidden-fn`)?  What a placement reads, a firing's and a nogood's: the
  `except` roster and the network, and no `defeat`."
  [kb handle view-context]
  (boolean (when-let [hid (except-closure-hidden-fn kb view-context)] (hid handle))))

(defn without-excepted
  "Drop the `[handle …]` matches whose handle `view-context` does not see (`hidden-fn`),
  and answer the **identical seq** when it hides nothing, which is almost every read of
  almost every KB."
  [kb view-context matches]
  (if-let [hidden? (hidden-fn kb view-context)]
    (remove #(hidden? (first %)) matches)
    matches))
