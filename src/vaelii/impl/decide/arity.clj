;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.arity
  "The arity family: a tuple whose length breaks the length a reader binds its functor
  to, and two predicates a `genl` edge relates whose own lengths differ, each placed as a
  conclusion (`chain/place-arities!`).  See docs/nmtms.md, \"A nogood placed as a
  conclusion\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- arity ---------------------------------------------------------------
;;
;; A tuple of `Q` whose length breaks the length `Q` is bound to is a one-member nogood,
;; and two predicates a predicate `genl` edge relates whose own lengths differ are a
;; nogood of their bindings.  The bindings are the roster spellings, read as storage
;; (`sx/arity-binding`) off the index family `:arity-binding` (docs/indexing.md, "The
;; arity bindings").  The candidate index keeps the shapes some stored binding breaks
;; under `::cand-shapes`, a shape's lengths read off the shape roster
;; (`reads/as-stored-shape-lengths`) and its tuples off the shape trie
;; (`reads/as-stored-shape-tuples-global`); `:arity` holds the tuples of those shapes,
;; `::pairs` the pairs, by lower end in `::pairs-by` with `::pair-count` per end,
;; `:arity-pairs` the bindings of the pairs' ends, and `::at-conflict` the functors whose
;; own length differs from one above them.  `::conflict-up` holds every type at or above a
;; functor of `::at-conflict`, closed upward over the edges active at the `genl`
;; generation `::conflict-gen`, so the functors under a conflict below a type are read by
;; a walk down that enters only its types.
;;
;; The exact lengths stored at or above a type, and its own exact lengths and `arityMin`
;; floors, are its entries in a weighted LRU (`entry`, register row N8), computed off the
;; binding family and the unscoped `genl` closure when a write or a settle reads them, a
;; type's lengths from its parents' held answers.  A binding write evicts the entries it moves, and the relation moves (J5) of a
;; `genl` edge evict every entry at or below its lower end (`lengths-lru`), so an eviction
;; costs a recompute and changes no answer.
;;
;; A `:monotonic` membership `(T P)` binds P's length when T reaches an exact-arity class
;; through `:monotonic` `genl` edges (`meta-held`).  What binds a relation's length is one
;; function, read the same at every context (`relation-length`).  The candidates read
;; the superset over every class: the entries hold the lengths each type reaches through
;; the unscoped closure under `[::meta T]`, and the types of P's stored memberships under
;; `[::types P]`; `::meta-by-type` names the functors whose candidates read a type's
;; lengths, so an edge moving below the type recomputes them.

(defn- binding-of
  "`[P kind value]` of the stored fact `sx` when it binds a relation's length
  (`sx/arity-binding`), else nil."
  [sx]
  (when (nil? (:antecedent sx))
    (sx/arity-binding (:sentence sx))))

(defn- fact-shape
  "`[q n]` for a stored fact `sx` whose sentence is a positive tuple of `n` arguments with
  a symbol functor, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (<= 2 (count s)))
      (let [f (first s)]
        (when (and (symbol? f) (not= 'not f) (not (sx/variable? f)))
          [f (dec (count s))])))))

(defn- values-of
  "The values of the `kind` pairs among `kinds` (`[kind value]`, as the family lists
  them)."
  [kinds kind]
  (into #{} (keep (fn [[k v]] (when (= k kind) v))) kinds))

(defn- exact-at
  "The exact lengths `p` stores: one probe of the bound predicates, and `p`'s kinds where
  it holds one."
  [kb p]
  (let [idx (:index kb)]
    (when (reads/stored-arity-bound? idx p)
      (values-of (reads/as-stored-arity-binding-kinds idx p) :exact))))

(defn- exact-bound?
  "Does `p` store an exact length?"
  [kb p]
  (boolean (seq (exact-at kb p))))

(defn- exact-above
  "The predicates at or above `q` storing an exact length, `q`'s unscoped closure cut to
  them through the write view `w` (`decide/write-view`).  `memo`, a volatile map, holds
  the cut by component (`genls-global-union`): a caller asking it of many predicates over
  one still taxonomy and index keeps one, and each ancestor is cut once."
  ([kb w q] (exact-above kb w q (volatile! {})))
  ([kb w q memo] ((:genls-global-union w) q (filter #(exact-bound? kb %)) memo)))

(defn- exact-handles
  "The handles of `q`'s stored exact bindings."
  [kb q]
  (into [] (keep (fn [[h kind]] (when (= :exact kind) h)))
        (reads/as-stored-arity-bindings-global (:index kb) q)))

(defn- membership-of
  "`[T x]` for a stored fact `sx` whose sentence is the positive membership `(T x)` of a
  symbol in a symbol type, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and sx (nil? (:antecedent sx)) (seq? s) (= 2 (count s)))
      (let [[t x] s]
        (when (and (symbol? t) (symbol? x) (not= 'not t)
                   (not (sx/variable? t)) (not (sx/variable? x)))
          [t x])))))

(def ^:private exact-classes
  "The exact-arity classes, each a type (`sx/exact-arity-classes`)."
  (set (keys sx/exact-arity-classes)))

(defn- meta-paths
  "`{n [[h ctx] …]}`: for each exact length `n` of an exact-arity class at or above the
  type `t` (`sx/exact-arity-classes`), the supporters of one shortest path of `genl` edges
  from `t` up to the class, an edge entering the walk when `ok?` takes one of its
  supporters `[h ctx]`.  An exact class `t` names its own length with no edge.  The walk
  enters only the types the unscoped closure carries to an exact class, and expands
  parents and supporters in name order.  Unscoped; `ok?` decides each supporter
  (`meta-held` admits the `:monotonic` ones)."
  [tax t ok?]
  (let [reaches? (fn [x] (or (contains? exact-classes x)
                             (some #(tax/genl?-global tax x %) exact-classes)))]
    (if-not (reaches? t)
      {}
      (loop [q (conj clojure.lang.PersistentQueue/EMPTY [t []]), seen #{t}, acc {}]
        (if-let [[x path] (peek q)]
          (let [acc  (let [n (get sx/exact-arity-classes x)]
                       (cond-> acc (and n (not (contains? acc n))) (assoc n path)))
                nxt  (into []
                           (keep (fn [y]
                                   (when-let [sup (->> (tax/supporters tax [:genl x y])
                                                       (filter ok?)
                                                       (nm/sort-by-content-key #(nm/print-key (second %)) compare)
                                                       first)]
                                     [y (conj path sup)])))
                           (nm/sort-by-content-key nm/print-key compare
                                                   (filter #(and (not (contains? seen %)) (reaches? %))
                                                           (tax/direct-genls-global tax x))))]
            (recur (into (pop q) nxt) (into seen (map first) nxt) acc))
          acc)))))

(defn- unscoped-meta-paths
  "`meta-paths` of `t` over every edge of the unscoped closure, whatever its class: the
  superset the candidates and the routes read, which `meta-held` cuts to the `:monotonic`
  edges.  A class is read off the network and not
  the store, since a re-assert raises a stored record's class in place and a derived
  membership has no stored class."
  [tax t]
  (meta-paths tax t (constantly true)))

;; ---- the length entries ------------------------------------------------------

(def lengths-cache-limit
  "The most weight one KB's length entries hold before the least recently used are
  evicted, an entry weighing one plus the lengths and floors it holds (`entry`): the
  shipped default the cache profile scales and the memory guard shrinks."
  262144)

(defn- weigh
  "An entry's weight: one, plus each length or floor it holds."
  ^long [v]
  (if (set? v) (inc (count v)) (+ 1 (count (:own v)) (count (:mins v)))))

(defn- evict-below!
  "Drop the entries of `lru` at or below a term of `ends`, a type's lengths and the
  lengths it reaches as a metatype (`[::meta t]`): an end's specializations read where
  they number no more than `lru`'s entries (`tax/specs-global-within`), else each entry
  asked whether it reaches the end.  Unscoped, since the entries are the unscoped
  closure's, a superset over every reader (`decide/write-view`)."
  [tax lru ends]
  (doseq [end ends
          :let [n (caches/lru-size lru)]
          :when (pos? n)]
    (if-let [ts (tax/specs-global-within tax end n)]
      (caches/lru-evict! lru (into (vec ts) (map #(vector ::meta %)) ts))
      (caches/lru-evict-if! lru (constantly true)
                            #(let [k (if (and (vector? %) (= ::meta (first %))) (second %) %)]
                               (or (= end k) (tax/genl?-global tax k end)))))))

(defn- lengths-lru
  "`kb`'s length entries, brought current with the taxonomy `tax`: emptied when its
  relations were rebuilt (`tax/relation-epoch`) or the `genl` generation went back, else
  rid of every entry at or below the lower end of an edge moved since the generation they
  last read (`tax/moves-since`)."
  [kb tax]
  (let [a   (reasoning/arity-lengths kb)
        g   (tax/relation-gen tax :genl)
        e   (tax/relation-epoch tax)
        lru @a
        {:keys [gen epoch]} lru]
    (cond
      (nil? lru)
      (reset! a (assoc (caches/weighted-lru
                        (caches/limit-thunk :arity-lengths lengths-cache-limit) weigh)
                       :gen g :epoch e))

      (and (= g gen) (= e epoch)) lru

      (or (not= e epoch) (< g (long gen)))
      (do (caches/lru-clear! lru) (reset! a (assoc lru :gen g :epoch e)))

      :else
      (do (evict-below! tax lru (tax/moves-since tax :genl gen)) (reset! a (assoc lru :gen g))))))

(defn- own-entry
  "`{:own :mins}`: `f`'s own exact lengths and `arityMin` floors, one probe of the bound
  predicates and `f`'s kinds where it holds one."
  [kb f]
  (let [idx   (:index kb)
        kinds (when (reads/stored-arity-bound? idx f) (reads/as-stored-arity-binding-kinds idx f))]
    {:own (values-of kinds :exact) :mins (values-of kinds :min)}))

(defn- types-entry
  "The types of `f`'s stored memberships, off the unary roster at `f`, in every context:
  the length entries are a superset over every reader (`decide/write-view`)."
  [kb f]
  (let [recs (:records kb)]
    (into #{} (keep (fn [h] (when-let [[t x] (membership-of (p/get-sentex recs h))]
                              (when (= x f) t))))
          (reads/as-stored-unary-with-arg-global (:index kb) f))))

(defn- exact-xf
  "Each term's stored exact lengths (`exact-at`)."
  [kb]
  (mapcat #(exact-at kb %)))

(defn- lengths-of
  "The exact lengths stored at or above `f`, what `xf` makes of `f`'s unscoped `genl`
  closure, built from its parents' answers, which `kb`'s length entries hold by component
  representative (`tax/genls-global-union-held`).  Unscoped, since the candidates it
  serves are a superset over every reader, which each reader scopes
  (`decide/write-view`)."
  [kb w f xf]
  (let [lru (lengths-lru kb (:tax w))]
    (tax/genls-global-union-held (:tax w) f xf #(caches/lru-get lru %) #(caches/lru-put! lru %1 %2))))

(defn- own-held
  "`{:own :mins}` of `f` (`own-entry`), held in `kb`'s length entries under `[::own f]`
  (`lengths-lru`), with `tax` the taxonomy."
  [kb tax f]
  (let [lru (lengths-lru kb tax)]
    (or (caches/lru-get lru [::own f])
        (caches/lru-put! lru [::own f] (own-entry kb f)))))

(defn- types-held
  "The types of `f`'s stored memberships (`types-entry`), held in `kb`'s length entries
  under `[::types f]`."
  [kb tax f]
  (let [lru (lengths-lru kb tax)]
    (or (caches/lru-get lru [::types f])
        (caches/lru-put! lru [::types f] (types-entry kb f)))))

(defn- meta-lengths
  "The exact lengths the type `t` reaches through the unscoped closure
  (`unscoped-meta-paths`), held in `kb`'s length entries under `[::meta t]`."
  [kb tax t]
  (let [lru (lengths-lru kb tax)]
    (or (caches/lru-get lru [::meta t])
        (caches/lru-put! lru [::meta t] (set (keys (unscoped-meta-paths tax t)))))))

(defn- meta-of
  "`[lengths types]`: the exact lengths `f`'s stored memberships can bind it to
  (`meta-lengths` of each type `types-held` names), and the types giving one."
  [kb tax f]
  (reduce (fn [[ls ts :as acc] t]
            (let [m (meta-lengths kb tax t)]
              (if (seq m) [(into ls m) (conj ts t)] acc)))
          [#{} #{}] (types-held kb tax f)))

(defn- entry
  "`{:lengths :own :mins}` of `f`: the exact lengths stored at or above `f` (`lengths-of`),
  and `f`'s own exact lengths and `arityMin` floors (`own-held`), read through the write
  view `w` (`decide/write-view`).  With `meta?`, also `:meta` and `:meta-types`, the
  lengths `f`'s metatype memberships bind it to and their types (`meta-of`), which only a
  functor with a stored tuple reads."
  ([kb w f] (entry kb w f true))
  ([kb w f meta?]
   (let [[ml mt] (if meta? (meta-of kb (:tax w) f) [#{} #{}])]
     (assoc (own-held kb (:tax w) f)
            :lengths (lengths-of kb w f (exact-xf kb)) :meta ml :meta-types mt))))

(defn- binding-pred-of
  "The predicate the stored record `sx` binds or can bind the length of, or nil: a roster
  binding's (`binding-of`), or the member of a membership whose type reaches an
  exact-arity class (`meta-lengths`)."
  [kb sx]
  (or (first (binding-of sx))
      (when-let [[t x] (membership-of sx)]
        (when (seq (meta-lengths kb (reasoning/taxonomy kb) t))
          x))))

(defn- binding-pred
  "The predicate the stored record at `h` binds the length of (`binding-pred-of`), or nil."
  [kb h]
  (some->> (p/get-sentex (:records kb) h) (binding-pred-of kb)))

(defn- put-lengths!
  "Hold `ls` as the exact lengths stored at or above `f` in `kb`'s length entries, under
  `f`'s component representative."
  [kb w f ls]
  (caches/lru-put! (lengths-lru kb (:tax w)) (tax/genl-representative (:tax w) f) ls))

(defn- evict!
  "Drop the entries of the types `ts` from `kb`'s length entries: their lengths, and with
  `own?` their own lengths and floors too."
  [kb w ts own?]
  (caches/lru-evict! (lengths-lru kb (:tax w))
                     (cond-> (vec ts) own? (into (map #(vector ::own %)) ts))))

(defn- noted
  "`c` with the handles `hs` journaled (`journal/note`) and queued under `::moved` for the
  settle to place their nogoods again (`take-moved!`)."
  [c hs]
  (-> (journal/note c hs) (update ::moved (fnil into #{}) hs)))

(defn- note-placement-left!
  "Queue the arity candidates and bindings a `(contradicts …)` sentex `sx` leaving the store
  names, so the settle places their nogoods where they stand (`take-moved!`): a `genlCx`
  edge under the placement can have left with it."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)))
      (let [cands (reasoning/nogood-candidates kb)
            c     @cands
            hs    (into #{} (comp (keep sx/handle-id)
                                  (filter #(or (contains? (:arity c) %) (binding-pred kb %))))
                        (rest s))]
        (when (seq hs)
          (swap! cands update ::moved (fnil into #{}) hs))))))

(defn- shape-handles
  "The stored tuples of shape `[q n]`, one read of the shape trie, in every context: the
  candidate rows are a superset over every reader, and a placement keeps a reader's."
  [kb [q n]]
  (reads/as-stored-shape-tuples-global (:index kb) q n))

(defn- breaks-entry?
  "Does a tuple of `n` arguments break a length of the entry `e` (`entry`): one stored at
  or above its functor, one a metatype membership binds it to, or its `arityMin`?"
  [{:keys [lengths mins meta]} n]
  (boolean (or (some #(not= n %) lengths) (some #(not= n %) meta) (some #(> % n) mins))))

(defn- meta-typed
  "`c` with the types `ts` whose lengths bind `f` (`meta-of`) recorded in
  `::meta-by-type`, and those no longer giving one dropped."
  [c f ts]
  (let [old (get-in c [::meta-types-of f] #{})]
    (if (= old ts)
      c
      (let [c (reduce (fn [c t] (let [fs (disj (get-in c [::meta-by-type t]) f)]
                                  (if (seq fs) (assoc-in c [::meta-by-type t] fs)
                                      (update c ::meta-by-type dissoc t))))
                      c (remove ts old))
            c (reduce (fn [c t] (update-in c [::meta-by-type t] (fnil conj #{}) f)) c (remove old ts))]
        (if (seq ts) (assoc-in c [::meta-types-of f] ts) (update c ::meta-types-of dissoc f))))))

(defn- binding-noted
  "`c` with the binding `h` of `p`, of `kind`, journaled and queued (`noted`), entering
  `:arity-pairs` when it is stored (`stored?`) as an exact binding of an end of a pair and
  leaving it when it leaves."
  [c p h kind stored?]
  (let [c (noted c [h])]
    (cond
      (not stored?)                        (cond-> c (:arity-pairs c) (update :arity-pairs disj h))
      (and (= :exact kind)
           (pos? (get-in c [::pair-count p] 0))) (update c :arity-pairs (fnil conj #{}) h)
      :else                                c)))

(defn- count-end
  "`c` with the pair count of `q` moved by `d`: `q`'s exact bindings enter `:arity-pairs`
  when it becomes an end of a pair, and leave when it stops being one."
  [kb c q d]
  (let [k  (get-in c [::pair-count q] 0)
        k' (+ k d)
        hs #(exact-handles kb q)
        c  (if (zero? k') (update c ::pair-count dissoc q) (assoc-in c [::pair-count q] k'))]
    (cond
      (and (zero? k) (pos? k')) (-> c (update :arity-pairs (fnil into #{}) (hs)) (noted (hs)))
      (and (pos? k) (zero? k')) (-> c (update :arity-pairs #(reduce disj % (hs))) (noted (hs)))
      :else                     c)))

(defn- set-pairs
  "`c` with the pairs whose lower end is `f` replaced by the set `new`, in `::pairs`, by
  lower end in `::pairs-by`, and in the pair counts of their ends."
  [kb c f new]
  (let [old (get-in c [::pairs-by f] #{})
        new (or new #{})]
    (if (= old new)
      c
      (let [gone (remove new old)
            came (remove old new)
            c    (-> c
                     (update ::pairs #(into (reduce disj (or % #{}) gone) came))
                     (update ::pairs-by #(if (seq new) (assoc % f new) (dissoc % f))))
            c    (reduce #(count-end kb %1 %2 -1) c (mapcat identity gone))]
        (reduce #(count-end kb %1 %2 1) c (mapcat identity came))))))

(defn- spread-lengths
  "The types at or below `t` that `ns` adds an exact length to, `lengths-of` answering
  the lengths each held before the write: a walk down that stops at a type holding all of
  `ns`, since every type below it holds them too."
  [w t ns lengths-of]
  ((:specs-global-while w) t (fn [f] (let [l (lengths-of f)] (some #(not (contains? l %)) ns)))))

(defn- conflict-raised
  "`c` with the types above `f` added to `::conflict-up`, the walk up stopping at a type
  the set holds; `c` unchanged while the set is unbuilt (`conflict-up-current`)."
  [w c f]
  (if-let [up (when (::conflict-gen c) (::conflict-up c))]
    (assoc c ::conflict-up (into up ((:genls-global-while w) f #(or (= f %) (not (contains? up %))))))
    c))

(defn- recompute-arity
  "`c` with the arity candidates of the functors `fs` recomputed from their entries
  (`entry`).  `extra` is nil, or a delay of the predicates storing a length above the
  upper end of a `genl` edge stored but not yet installed.  A shape `[f n]` is a
  candidate when a length at or above `f` is not `n` or `f`'s `arityMin` is above `n`.  An
  `f` is in `::at-conflict` when it stores two lengths or one that differs from a length
  above it (a rebuild leaves out one with no `genl` parent and no tuple, `arity-rebuilt`),
  and only such an `f` reads the predicates above it to name its pairs `[f g]`:
  `g` above `f` storing a different exact length.  An `f` storing one length reads the
  predicates storing another (`tax/genls-global-union`, a memo per length across `fs`),
  and one storing two reads every predicate storing one (`memo`), through the write view
  `w` (`decide/write-view`)."
  [kb w c fs extra memo]
  (let [idx       (:index kb)
        by-length (volatile! {})]
    (reduce
     (fn [c f]
       (let [lengths (reads/as-stored-shape-lengths idx f)]
         (if (and (empty? lengths) (not (reads/stored-arity-bound? idx f))
                  (empty? (get-in c [::pairs-by f])))
           ;; no tuple, no binding and no pair: nothing of `f` can change
           c
           (let [{above :lengths own :own e-meta :meta-types :as e} (entry kb w f (seq lengths))
                 c         (meta-typed c f e-meta)
                 c         (reduce
                            (fn [c n]
                              (let [shape [f n]
                                    was?  (contains? (::cand-shapes c) shape)
                                    now?  (breaks-entry? e n)]
                                (cond
                                  (= was? now?) c
                                  now?  (let [hs (shape-handles kb shape)]
                                          (-> c
                                              (update ::cand-shapes (fnil conj #{}) shape)
                                              (update :arity (fnil into #{}) hs)
                                              (noted hs)))
                                  :else (let [hs (shape-handles kb shape)]
                                          (-> c
                                              (update ::cand-shapes disj shape)
                                              (update :arity #(reduce disj % hs))
                                              (noted hs))))))
                            c (sort lengths))
                 conflict? (boolean (and (seq own) (or (< 1 (count own)) (some #(not= (first own) %) above))))
                 c         (cond
                             (and conflict? (contains? (::at-conflict c) f)) c
                             conflict?                       (conflict-raised w (update c ::at-conflict (fnil conj #{}) f) f)
                             (contains? (::at-conflict c) f) (update c ::at-conflict disj f)
                             :else                           c)]
             (set-pairs kb c f
                        (when conflict?
                          (into #{}
                                (keep (fn [g]
                                        (let [og (exact-at kb g)]
                                          (when (and (not= g f) (seq og)
                                                     (some (fn [a] (some #(not= a %) og)) own))
                                            [f g]))))
                                (if (< 1 (count own))
                                  (into ((:genls-global-union w) f (filter #(exact-bound? kb %)) memo)
                                        (some-> extra deref))
                                  ;; one length `a`: the predicates that pair with `f` are
                                  ;; those storing a length other than `a`, and the cut to
                                  ;; them holds those alone, where the cut to every bound
                                  ;; predicate is the closure once every type stores one
                                  (let [a     (first own)
                                        other (fn [g] (some #(not= a %) (exact-at kb g)))
                                        m     (or (get @by-length a)
                                                  (let [m (volatile! {})] (vswap! by-length assoc a m) m))]
                                    (into ((:genls-global-union w) f (filter other) m)
                                          (filter other) (some-> extra deref)))))))))))
     c fs)))

(defn- conflict-up-built
  "`c` with `::conflict-up` built from `::at-conflict` under the `genl` generation as it
  stands."
  [w c]
  (reduce #(conflict-raised w %1 %2)
          (assoc c ::conflict-up #{} ::conflict-gen (tax/relation-gen (:tax w) :genl))
          (::at-conflict c)))

(defn- moved-below
  "`c` with every functor at or below an end of `ends` recomputed whose `genl` parents hold
  an exact length (`lengths-of`): `ends` are the lower ends of the edges whose activation
  moved, by a write or by belief (`tax/moves-since`), and an edge coming back brings its
  upper end's lengths below its lower end.  An end with no parent holding a length is
  passed over: an edge leaving leaves the rows a superset, which each reader scopes
  (`exempt-at?`) and a later recompute of the functor narrows."
  [kb w c ends]
  (if (or (empty? ends) (zero? (reads/stored-count-arity-bound (:index kb))))
    c
    (let [reaches? (fn [t] (some #(seq (lengths-of kb w % (exact-xf kb)))
                                 ((:direct-genls-global w) t)))
          fs       (into #{} (comp (filter reaches?) (mapcat (:specs-global w))) ends)]
      (if (seq fs) (recompute-arity kb w c fs nil (volatile! {})) c))))

(defn- under
  "The terms of `fs` at or below one of the predicates `ps` over the unscoped `genl`
  closure (`w`, `decide/write-view`): one walk up from each term to the first of `ps`
  (`tax/genls-global-meets?`), or the specializations of `ps` walked, whichever reads
  fewer.  `missed`, a volatile set kept for one `ps` over one still taxonomy, holds the
  types a walk found below none of `ps`, which later walks do not enter."
  ([w fs ps] (under w fs ps (volatile! #{})))
  ([w fs ps missed]
   (let [fs (set fs)
         ps (set ps)]
     (if (< (count fs) (* 4 (count ps)))
       (into #{} (filter #((:genls-global-meets? w) % ps missed)) fs)
       (into #{} (comp (mapcat (:specs-global w)) (filter fs)) ps)))))

(defn- members-of
  "The stored members of the type `t`, off `t`'s extent."
  [kb t]
  (let [recs (:records kb)]
    (into #{} (keep (fn [h] (when-let [[t' x] (membership-of (p/get-sentex recs h))]
                              (when (= t t') x))))
          (reads/as-stored-with-functor (:index kb) t))))

(defn- meta-moved
  "`c` with the functors recomputed whose metatype lengths an edge moved below an end of
  `ends` can have moved (`entry`): the functors `::meta-by-type` names under a type at or
  below an end, and the members of each type at or below an end that reaches an
  exact-arity class now (`meta-lengths`).  An end reaching no exact-arity class walks
  no type below it."
  [kb w c ends]
  (if (empty? ends)
    c
    (let [tax (:tax w)
          lit (fn [t] (seq (meta-lengths kb tax t)))
          fs  (-> #{}
                  (into (mapcat #(get-in c [::meta-by-type %]))
                        (under w (keys (::meta-by-type c)) ends))
                  (into (comp (filter lit) (mapcat (:specs-global w)) (filter lit)
                              (mapcat #(members-of kb %)))
                        ends))]
      (if (seq fs) (recompute-arity kb w c fs nil (volatile! {})) c))))

(defn- conflict-up-current
  "`c` brought current with the `genl` edges moved since the generation `::conflict-gen`
  (`tax/moves-since`): `::conflict-up` raised from each type it holds that is the lower
  end of a moved edge, since no other type's parents moved, and the functors below each
  moved end recomputed (`moved-below`); `::conflict-up` built whole when unbuilt, and
  only built when the relation was rebuilt from nothing, which a recover follows with a
  rebuild of the rows (`arity-rebuilt`).  A functor leaving `::at-conflict` and an edge
  leaving leave the set a superset, which costs the walk in `conflicts-below` the types
  it holds in excess and changes no answer."
  [kb w c]
  (let [tax  (:tax w)
        g    (tax/relation-gen tax :genl)
        seen (::conflict-gen c)]
    (cond
      (= g seen) c

      (and seen (< g seen)) (conflict-up-built w c)

      :else
      (let [ends (tax/moves-since tax :genl (or seen 0))
            c    (if seen
                   (reduce #(conflict-raised w %1 %2) (assoc c ::conflict-gen g)
                           (filter (or (::conflict-up c) #{}) ends))
                   (conflict-up-built w c))]
        (meta-moved kb w (moved-below kb w c ends) ends)))))

(defn- conflicts-below
  "`[c fs]`: `c` with `::conflict-up` current, and `fs` the functors of `::at-conflict`
  below `t`, other than those in `skip`.  The walk down from `t` enters only the types of
  `::conflict-up`, and every type on a path from `t` down to such a functor is one, so it
  costs the types between `t` and the functors below it, none when no functor is."
  [kb w c t skip]
  (let [c  (conflict-up-current kb w c)
        up (::conflict-up c)
        ac (::at-conflict c)]
    [c (into #{} (filter #(and (contains? ac %) (not (contains? skip %))))
             ((:specs-global-while w) t #(contains? up %)))]))

(defn- length-arrived
  "`c` after the exact length `n` arrives at `p`, which stored no `n` before: `n` reaches
  the types below `p` missing it (`spread-lengths`, each type's lengths before the write
  read with `p`'s `n` left out), whose entries take it, and which are recomputed with
  `p`.  A functor below `p` that already held `n` keeps its shapes, and its pairs change
  only by `[f p]`, and only when it is in `::at-conflict`, so those are joined without a
  recompute."
  [kb w c p n]
  (let [;; the answers this walk holds for the types below `p` lack `n`, and each of them
        ;; that `n` changes is replaced below
        before  (mapcat (fn [g] (cond-> (exact-at kb g) (= g p) (disj n))))
        old     #(lengths-of kb w % before)
        changed (spread-lengths w p #{n} old)
        _       (doseq [f (conj changed p)] (put-lengths! kb w f (conj (old f) n)))
        c       (recompute-arity kb w c (conj changed p) nil (volatile! {}))
        op      (exact-at kb p)
        [c below] (conflicts-below kb w c p (conj changed p))]
    (reduce (fn [c f]
              (if (some (fn [a] (some #(not= a %) op)) (exact-at kb f))
                (set-pairs kb c f (conj (get-in c [::pairs-by f] #{}) [f p]))
                c))
            c below)))

(defn- edge-arrived
  "`c` after the `genl` edge `sub`→`super` is stored and before it is installed: the
  lengths at or above `super` reach the types below `sub` missing one, whose entries take
  them, and those types are recomputed, and so is each functor below `sub` in
  `::at-conflict`, with the predicates storing a length above `super` as `extra`.  `sub`
  storing two lengths is recomputed too, since a rebuild leaves a predicate with no `genl`
  parent and no tuple out of `::at-conflict` (`arity-rebuilt`).  No other functor is
  recomputed when no length is stored at or above `super`: the edge then brings no length
  and no pair."
  [kb w c sub super]
  (let [split? (fn [c fs]
                 (and (not (contains? fs sub)) (not (contains? (::at-conflict c) sub))
                      (< 1 (count (:own (own-held kb (:tax w) sub))))))]
    (if-let [ls (not-empty (lengths-of kb w super (exact-xf kb)))]
      (let [old     #(lengths-of kb w % (exact-xf kb))
            changed (spread-lengths w sub ls old)
            _       (doseq [f changed] (put-lengths! kb w f (into (old f) ls)))
            memo    (volatile! {})
            extra   (delay ((:genls-global-union w) super (filter #(exact-bound? kb %)) memo))
            [c below] (conflicts-below kb w c sub changed)
            fs      (into changed below)]
        (recompute-arity kb w c (cond-> fs (split? c fs) (conj sub)) extra memo))
      (if (split? c #{}) (recompute-arity kb w c #{sub} nil (volatile! {})) c))))

(defn- region-left
  "`c` after a length or an edge above every type of `region` leaves: the region's entries
  are evicted and every functor in it recomputed."
  [kb w c region]
  (evict! kb w region false)
  (recompute-arity kb w c region nil (volatile! {})))

(defn- arity-rebuilt
  "`c` with the candidates computed for each functor of a stored fact
  (`reads/as-stored-children` at the trie root), each lower end of an active `genl` edge
  (`tax/genl-edges`) and each functor a write named while they were owed (`::arrived`),
  one memo across them, and `::conflict-up` built from them.  A candidate shape needs a
  stored tuple and a pair needs a `genl` parent, so the bindings of a predicate with
  neither are not read: such a predicate storing two lengths enters `::at-conflict` when
  an edge below it arrives (`edge-arrived`)."
  [kb w c]
  (let [fs (-> #{}
               (into (filter #(and (symbol? %) (not (sx/variable? %))))
                     (reads/as-stored-children (:index kb) []))
               (into (map first) (tax/genl-edges (:tax w)))
               (into (::arrived c)))]
    (conflict-up-built
     w (recompute-arity kb w (dissoc c ::conflict-up ::conflict-gen ::arrived ::meta-by-type ::meta-types-of) fs nil (volatile! {})))))

(defn- tuples-of
  "The candidate tuples of `c` whose shape `[q n]` passes `keep?`, read by candidate shape."
  [kb c keep?]
  (let [ar (or (:arity c) #{})]
    (into #{} (comp (filter keep?)
                    (mapcat #(shape-handles kb %))
                    (filter #(contains? ar %)))
          (::cand-shapes c))))

(defn- pair-sets
  "The member sets of the pair `[f g]`: one exact binding of each, of two lengths."
  [kb [f g]]
  (let [ex (fn [q] (filter #(= :exact (second %)) (reads/as-stored-arity-bindings-global (:index kb) q)))]
    (for [[hf _ a] (ex f)
          [hg _ b] (ex g) :when (not= a b)]
      #{hf hg})))

(defn- note-arity!
  "Keep the arity candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving, after the index write.  While the candidates are owed whole (`::owed`), it
  only adds the functors `sx` names to `::arrived`, which the first sync computes with
  the rest (`arity-rebuilt`).  A tuple of a candidate shape enters `:arity`, and a shape is tested
  against the lengths at or above its functor and the functor's `arityMin` when one of
  its tuples arrives (`breaks-entry?`); a candidate shape whose last tuple leaves the
  shape roster leaves `::cand-shapes`.  An exact length arriving at a predicate reaches
  the types below it that miss it (`length-arrived`), and an edge arriving, a `genl` edge
  or a cover's edge per part (`tax/installed-edges`), brings its upper end's lengths below
  its lower end (`edge-arrived`, while any binding is stored).  A length or an edge
  leaving reads the lengths of the types below it again (`region-left`), and a binding
  that moves no length recomputes its own predicate.  An edge is not installed when its
  record is stored, so its arrival reads the upper end's lengths from its entry; a
  departing edge may still be installed, which leaves a superset."
  [kb w sx stored?]
  (let [cands (reasoning/nogood-candidates kb)]
    (if (::owed @cands)
      ;; a sync that read the store before this write fails its compare-and-set on this
      ;; swap and reads the store again (`decide/synced`)
      (let [fs (-> (if-let [[q] (fact-shape sx)] #{q} #{})
                   (into (comp (map first) (filter symbol?))
                         (when (nil? (:antecedent sx)) (tax/installed-edges (:sentence sx))))
                   (into (some-> (membership-of sx) rest)))]
        (swap! cands update ::arrived (fnil into #{}) fs))
      (let [idx (:index kb)
            h   (:id sx)
            s   (:sentence sx)]
        (when-let [[q n :as shape] (fact-shape sx)]
          (let [c @cands]
            (if stored?
              (let [e (when-not (contains? (::cand-shapes c) shape) (entry kb w q))]
                (when (or (nil? e) (breaks-entry? e n))
                  (let [hs (when e (shape-handles kb shape))]
                    (swap! cands
                           (fn [c]
                             (if (contains? (::cand-shapes c) shape)
                               (-> c (update :arity (fnil conj #{}) h) (noted [h]))
                               (let [hs (conj (set hs) h)]
                                 (-> c
                                     (cond-> e (meta-typed q (:meta-types e)))
                                     (update ::cand-shapes (fnil conj #{}) shape)
                                     (update :arity (fnil into #{}) hs)
                                     (noted hs)))))))))
              (when (contains? (:arity c) h)
                (let [gone? (not (contains? (reads/as-stored-shape-lengths idx q) n))]
                  (swap! cands
                         (fn [c]
                           (cond-> (-> c (update :arity #(some-> % (disj h))) (noted [h]))
                             gone? (update ::cand-shapes #(some-> % (disj shape)))))))))))
        (when-let [[p kind v] (binding-of sx)]
          ;; `p`'s own lengths and floors move with any binding of it
          (evict! kb w [p] true)
          (let [others? (boolean (some (fn [[h' k' v']] (and (not= h h') (= kind k') (= v v')))
                                       (reads/as-stored-arity-bindings-global idx p)))
                had?    (or (not stored?) others?)
                has?    (or stored? others?)]
            (swap! cands (fn [c]
                           (let [c (binding-noted c p h kind stored?)]
                             (cond
                               (and (= :exact kind) (not had?) has?)
                               (length-arrived kb w c p v)

                               (and (= :exact kind) had? (not has?))
                               (region-left kb w c ((:specs-global w) p))

                               :else
                               (recompute-arity kb w c #{p} nil (volatile! {}))))))
            ;; a binding leaving can leave another one convicting where it did not: the
            ;; candidates under its predicate and the pairs at it are placed again
            (when-not stored?
              (swap! cands (fn [c]
                             (let [qs (under w (map first (::cand-shapes c)) [p])]
                               (update c ::moved (fnil into #{})
                                       (concat (tuples-of kb c (fn [[q]] (contains? qs q)))
                                               (mapcat #(apply concat (pair-sets kb %))
                                                       (filter #(some #{p} %) (::pairs c)))))))))))
        ;; a membership moves its member's types, and recomputes the member when its
        ;; type reaches an exact-arity class (`meta-lengths`)
        (when-let [[t x] (membership-of sx)]
          (caches/lru-evict! (lengths-lru kb (:tax w)) [[::types x]])
          (when (seq (meta-lengths kb (:tax w) t))
            (swap! cands #(-> (recompute-arity kb w % #{x} nil (volatile! {})) (noted [h])))))
        (when (nil? (:antecedent sx))
          (let [edges (filter (fn [[sub super]] (and (symbol? super) (not= sub super)))
                              (tax/installed-edges s))]
            (when (and (seq edges) (pos? (reads/stored-count-arity-bound idx)))
              (doseq [[sub super] edges]
                (swap! cands #(if stored?
                                (edge-arrived kb w % sub super)
                                (region-left kb w % ((:specs-global w) sub))))))))))))

(defn- visible-bindings
  "`{:exact {n #{h}} :min {m #{h}} :var #{h}}`: the bindings of `p` a reader with ancestor
  set `up` reads, each IN, stated in `up` and not `hidden?`."
  [kb p up hidden?]
  (let [tms (reasoning/tms kb)]
    (reduce (fn [m [h kind v _]]
              (if (and (jtms/in? tms h) (not (and hidden? (hidden? h))))
                (if (= :var kind)
                  (update m :var (fnil conj #{}) h)
                  (update-in m [kind v] (fnil conj #{}) h))
                m))
            {} (when up (reads/as-stored-arity-bindings (:index kb) p up)))))

(defn- held-bindings
  "`{:exact {n #{h}} :min {m #{h}} :var #{h}}`: the stored bindings of `p` in every
  context, each IN and not `hidden?`.  Every context, since a relation's length is read
  the same at every context (`relation-length`)."
  [kb p hidden?]
  (let [tms (reasoning/tms kb)
        idx (:index kb)]
    (if-not (reads/stored-arity-bound? idx p)
      {}
      (reduce (fn [m [h kind v _]]
                (if (and (jtms/in? tms h) (not (and hidden? (hidden? h))))
                  (if (= :var kind)
                    (update m :var (fnil conj #{}) h)
                    (update-in m [kind v] (fnil conj #{}) h))
                  m))
              {} (reads/as-stored-arity-bindings-global idx p)))))

(defn- meta-held
  "`{n #{h}}`: the exact lengths `q`'s metatype memberships bind it to, each with the
  memberships binding it.  A membership `(T q)` binds when it is IN at `:monotonic` and
  not `hidden?`, and `T` reaches an exact-arity class through edges each with a
  supporter that is the same (`meta-paths`), in any context, since a relation's length is
  read the same at every context (`relation-length`).  Reads nothing for a `q` whose
  stored memberships bind no length (`meta-of`)."
  [kb q hidden?]
  (let [tax (reasoning/taxonomy kb)]
    (if (empty? (first (meta-of kb tax q)))
      {}
      (let [tms   (reasoning/tms kb)
            recs  (:records kb)
            ok?   (fn [[h _]] (and (= :monotonic (jtms/defeat-class tms h))
                                   (not (and hidden? (hidden? h)))))
            memo  (volatile! {})
            lens  (fn [t] (or (get @memo t)
                              (let [ls (keys (meta-paths tax t ok?))] (vswap! memo assoc t ls) ls)))]
        (reduce (fn [m h]
                  (let [r (p/get-sentex recs h)]
                    (if-let [[t x] (membership-of r)]
                      (if (and (= x q) (jtms/in? tms h) (ok? [h (:context r)]))
                        (reduce #(update %1 %2 (fnil conj #{}) h) m (lens t))
                        m)
                      m)))
                {} (reads/as-stored-unary-with-arg-global (:index kb) q))))))

(defn- meta-routes
  "`[[h ctx path n] …]`: each stored membership `(T q)`, at handle `h` in `ctx`, with the
  supporters `path` of the edges by which `T` reaches an exact-arity class of length `n`
  (`unscoped-meta-paths`), in content order of the memberships' types, in every context:
  the routes are a superset each placement context scopes.  Empty for a `q` whose
  memberships reach no exact-arity class (`meta-of`)."
  [kb tax q]
  (when (seq (first (meta-of kb tax q)))
    (let [recs (:records kb)]
      (->> (reads/as-stored-unary-with-arg-global (:index kb) q)
           (keep (fn [h] (let [r (p/get-sentex recs h)]
                           (when-let [[t x] (membership-of r)]
                             (when (= x q) [h (:context r) t])))))
           (nm/sort-by-content-key (fn [[_ c t]] [(nm/print-key t) (nm/print-key c)]) compare)
           (mapcat (fn [[h c t]] (for [[n path] (sort-by key (unscoped-meta-paths tax t))]
                                   [h c path n])))
           vec))))

(defn- shape-length
  "The length an engine grammar term's `:shape` gives it (`predicates/shape-of`), with
  no grounds: `{:exact n}` for a fixed argument list, `{:min n}` for one with an
  `:optional` or `:variadic` tail; nil for a term with no shape."
  [q]
  (when-let [{:keys [args optional variadic]} (when (symbol? q) (predicates/shape-of q))]
    (assoc (if (or optional variadic) {:min (count args)} {:exact (count args)})
           :via q :grounds #{})))

(defn- own-bindings
  "`q`'s own bindings (`held-bindings`), its metatype memberships' lengths (`meta-held`)
  merged into `:exact`."
  [kb q hidden?]
  (update (held-bindings kb q hidden?) :exact
          #(not-empty (merge-with into % (meta-held kb q hidden?)))))

(defn- reduce-own
  "The binding `q`'s own bindings `own` give it: under `variable_arity` its single
  `arityMin` floor, else its single exact length; nil for none, or for two."
  [q own]
  (cond
    (seq (:var own))   (when (= 1 (count (:min own)))
                         (let [[m hs] (first (:min own))] {:min m :via q :grounds hs}))
    (seq (:exact own)) (when (= 1 (count (:exact own)))
                         (let [[n hs] (first (:exact own))] {:exact n :via q :grounds hs}))))

(defn released?
  "Does a `variable_arity` binding of `q`, IN in any context, release it?  `relation-length`
  answers `{:min m}` or nil for such a `q` and does not report the release, which
  `admitsArgnum` and the integrity pass's undeclared-arity read beside it."
  [kb q]
  (boolean (seq (:var (held-bindings kb q nil)))))

(defn- bound-above
  "The predicates above `q`, `q` left out, storing an exact or `variable_arity` binding,
  over the unscoped closure: a relation's length is read the same at every context
  (docs/taxonomy.md, \"Arity\"), so the cut reads every `genl` edge whoever can see it.
  `tax/genls-global-union` probes the bound predicates once per type above `q`."
  [kb q]
  (let [idx    (:index kb)
        bound? (fn [p] (and (reads/stored-arity-bound? idx p)
                            (some (fn [[kind]] (not= :min kind))
                                  (reads/as-stored-arity-binding-kinds idx p))))]
    (if (pos? (reads/stored-count-arity-bound idx))
      (disj (tax/genls-global-union (reasoning/taxonomy kb) q (filter bound?) (volatile! {})) q)
      #{})))

(defn relation-length
  "What binds `q`'s length, as `{:exact n :via p}` or `{:min m :via q}`, or nil, read the
  same at every context: an engine term's `:shape` (`shape-length`), else `q`'s own
  bindings (`reduce-own`), else the one exact length the bound predicates above it agree
  on, none of them `variable_arity`, with `:via` the first of them by name.  `hidden?`
  drops the handles a reader does not believe or see, or is nil.  With `grounds?`, the
  result also carries `:grounds #{h}`: the bindings stating the length, an engine term's
  own bindings stating its shape's length.  The rule is docs/taxonomy.md's \"Arity\"; the
  argument-position check, `describe`, `admitsArgnum` and the integrity pass call it
  without grounds, and the arity nogood with them."
  ([kb q] (relation-length kb q nil false))
  ([kb q hidden? grounds?]
   (or (when-let [s (shape-length q)]
         (if-not grounds?
           (dissoc s :grounds)
           ;; the shape decides; an own binding stating the shape's length is the ground a
           ;; placed nogood rests on, and one stating another length binds nothing
           (let [own (own-bindings kb q hidden?)]
             (assoc s :grounds (or (if (:exact s)
                                     (get-in own [:exact (:exact s)])
                                     (get-in own [:min (:min s)]))
                                   #{})))))
       (let [own (own-bindings kb q hidden?)]
         (if (or (seq (:var own)) (seq (:exact own)))
           (cond-> (reduce-own q own) (not grounds?) (dissoc :grounds))
           ;; the predicates above grouped by the exact lengths they store, each group in
           ;; name order, the smallest group first: a second length leaves `q` unbound, so
           ;; the rest go unread, and the first believed binding of a group names `:via`
           (let [idx    (:index kb)
                 cut    (bound-above kb q)
                 kinds  (into {} (map (fn [p] [p (reads/as-stored-arity-binding-kinds idx p)])) cut)
                 by-len (update-vals
                         (reduce (fn [m p] (reduce #(update %1 %2 (fnil conj []) p) m
                                                   (values-of (kinds p) :exact)))
                                 {} cut)
                         sort)
                 seen   (volatile! {})
                 held   (fn [p] (if-let [e (find @seen p)]
                                  (val e)
                                  (let [b (held-bindings kb p hidden?)]
                                    (vswap! seen assoc p b) b)))
                 holds? (fn [n p] (contains? (:exact (held p)) n))
                 vias   (reduce (fn [acc [n ps]]
                                  (if-let [p (first (filter #(holds? n %) ps))]
                                    (cond-> (assoc acc n p) (seq acc) reduced)
                                    acc))
                                {} (sort-by (comp count val) by-len))]
             (when (and (= 1 (count vias))
                        (not-any? #(and (contains? (kinds %) [:var nil]) (seq (:var (held %)))) cut))
               (let [[n via] (first vias)]
                 (cond-> {:exact n :via via}
                   grounds? (assoc :grounds (into #{} (mapcat #(get (:exact (held %)) n))
                                                  (filter #(holds? n %) (get by-len n)))))))))))))

(defn- breaks?
  "Does a tuple of `n` arguments break `binding`?"
  [binding n]
  (boolean (or (and (:exact binding) (not= n (:exact binding)))
               (and (:min binding) (< n (:min binding))))))

(defn- convicts?
  "Does a tuple of `n` arguments break the binding `b` (`relation-length`), with the
  binding `hb` among its grounds when `hb` is given?"
  [b n hb]
  (boolean (and b (breaks? b n) (or (nil? hb) (contains? (:grounds b) hb)))))

(defn- pair-at?
  "Does a reader with ancestor set `up` read the predicates `f` and `g` bound to two
  different lengths: one exact length visible for each, neither `variable_arity`?"
  [kb f g up hidden?]
  (let [bf (visible-bindings kb f up hidden?)
        bg (visible-bindings kb g up hidden?)]
    (boolean (and (empty? (:var bf)) (empty? (:var bg))
                  (= 1 (count (:exact bf))) (= 1 (count (:exact bg)))
                  (not= (key (first (:exact bf))) (key (first (:exact bg))))))))

;; ---- the nogoods placed as conclusions -------------------------------------
;;
;; No reader decides an arity nogood: the settle places each one where its members and
;; the binding that convicts it are seen together (`chain/place-arities!`), justified by
;; the binding and the `genl` edges up to the predicate stating it.  The index queues the
;; handles whose nogoods moved under `::moved` (`noted`).  Which binding binds a functor
;; depends on the bindings a reader sees and believes, so a reader that reads no
;; conviction through a placement is exempt from it (`exempt-at?`).

(defn held?
  "Does the candidate index `c` keep an arity candidate or the binding of a pair, or owe
  them whole (`::owed`)?"
  [c]
  (boolean (or (::owed c) (seq (:arity c)) (seq (:arity-pairs c)))))

(defn member?
  "Is `h` an arity candidate of `c`, or a stored binding (`binding-pred`)?"
  [kb c h]
  (or (contains? (:arity c) h) (some? (binding-pred kb h))))

(defn moved?
  "Has the index queued a handle whose arity nogoods the settle places again
  (`take-moved!`), or does it owe the candidates whole (`::owed`)?"
  [c]
  (boolean (or (::owed c) (seq (::moved c)))))

(defn take-moved!
  "The handles whose arity nogoods moved since the last call, and the queue emptied
  (`noted`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old #{})))

(defn- shape-of
  "`[q n]` of the stored tuple `h`, or nil."
  [kb h]
  (some-> (p/get-sentex (:records kb) h) fact-shape))

(defn nogoods-holding
  "The arity nogoods `c` keeps with a member or a ground among the handles `hs`, each
  `{:members #{h} :shape [q n]}` for a candidate tuple or `{:members #{hf hg} :pair [f
  g]}` for one exact binding of each end of a pair: a candidate tuple of `hs`, and for a
  binding of `hs` the candidate tuples of a functor at or below its predicate (`w`,
  `decide/write-view`) and the pairs with its predicate at either end."
  [kb w c hs]
  (let [recs     (:records kb)
        ;; one fetch of each record of `hs` answers both its binding and its shape
        [ps own] (reduce (fn [[ps own :as acc] h]
                           (if-let [sx (p/get-sentex recs h)]
                             [(if-some [b (binding-pred-of kb sx)] (conj ps b) ps)
                              (if (contains? (:arity c) h) (assoc own h (fact-shape sx)) own)]
                             acc))
                         [#{} {}] hs)
        pairs    (filter (fn [[f g]] (or (contains? ps f) (contains? ps g))) (::pairs c))]
    (-> []
        (into (comp (filter #(contains? (:arity c) %))
                    (keep (fn [h] (when-let [sh (if (contains? own h) (get own h) (shape-of kb h))]
                                    {:members #{h} :shape sh}))))
              (into (set hs)
                    (when (seq ps)
                      (let [qs (under w (map first (::cand-shapes c)) ps)]
                        (tuples-of kb c (fn [[q]] (contains? qs q)))))))
        (into (for [pr pairs, ms (pair-sets kb pr)] {:members ms :pair pr}))
        distinct
        vec)))

(defn members-under
  "The candidate tuples of `c` whose functor is at or below one of the predicates `ps` or
  is bound through a type at or below one of them (`::meta-by-type`), and the bindings of
  the pairs whose lower end is: those a `genl` edge whose lower end is one of `ps` can
  give or take a route (`w`, `decide/write-view`)."
  [kb w c ps]
  (when (and (seq ps) (held? c))
    (let [missed (volatile! #{})
          qs     (-> (under w (map first (::cand-shapes c)) ps missed)
                     (into (mapcat #(get-in c [::meta-by-type %]))
                           (under w (keys (::meta-by-type c)) ps missed)))
          fs     (under w (keys (::pairs-by c)) ps missed)]
      (-> (tuples-of kb c (fn [[q]] (contains? qs q)))
          (into (comp (mapcat #(get-in c [::pairs-by %])) (mapcat #(pair-sets kb %)) cat) fs)))))

(defn reached
  "The candidate tuples of `c` a binding stated in a context of `below` convicts: each
  candidate shape whose functor's own bindings, or those of a predicate above it storing
  an exact length (`w`, `decide/write-view`), include one stated there, or whose metatype
  route has its membership or an edge stated there (`meta-routes`).  A pair's bindings
  are candidates, which `decide/handles-at` reads by context.  One memo of the cut
  closures (`exact-above`) and one of the predicates read serve every shape."
  [kb w c below]
  (when (and (seq below) (seq (:arity c)))
    (let [idx  (:index kb)
          memo (volatile! {})
          read (volatile! {})
          in?  (fn [p] (let [v (get @read p ::unread)]
                         (if (identical? ::unread v)
                           (let [v (boolean (and (reads/stored-arity-bound? idx p)
                                                 (seq (reads/as-stored-arity-bindings idx p below))))]
                             (vswap! read assoc p v)
                             v)
                           v)))]
      (tuples-of kb c (fn [[q]] (or (in? q) (some in? (exact-above kb w q memo))
                                    (and (contains? (::meta-types-of c) q)
                                         (some (fn [[_ ctx path]]
                                                 (or (contains? below ctx)
                                                     (some #(contains? below (second %)) path)))
                                               (meta-routes kb (:tax w) q)))))))))

(defn- roster-binding?
  "Is the stored record at `h` a roster binding (`binding-of`)?"
  [recs h]
  (boolean (some-> (p/get-sentex recs h) binding-of)))

(defn- binding-handle?
  "Is the stored record at `h` a binding (`binding-pred`): a roster binding, or a
  metatype membership?"
  [kb h]
  (some? (binding-pred kb h)))

(defn routes
  "Each way a binding convicts the arity nogood `ng` (`nogoods-holding`) over the unscoped
  taxonomy, as `{:choices [[[handle context]]] :links [[sub super]] :excluded-at f}`: for
  a tuple of shape `[q n]`, each own binding of `q` it breaks and each exact binding of a
  predicate above `q` (`w`, `decide/write-view`) it breaks, with the subsumption from `q`
  to that predicate, and each metatype membership of `q` whose length it breaks, with the
  edges up to the exact-arity class among the choice's supporters (`meta-routes`); for a
  pair `[f g]`, the subsumption between the two.  A route convicts only where the reader
  reads its binding as what binds `q` (`exempt-at?`).  While no binding the conviction
  reads is hidden from any context (`hidden-anywhere?`), a tuple's route is left out at
  every placement context when `q`'s length (`relation-length`) does not convict through
  it, and a pair's at a placement context that reads no two lengths (`pair-at?`)."
  [kb w _c {:keys [members shape pair]} hidden-anywhere?]
  (let [idx         (:index kb)
        up          (:context-up-global w)
        bound-xf    (filter #(reads/stored-arity-bound? idx %))
        bindings-of (fn [p] (sort-by first (reads/as-stored-arity-bindings-global idx p)))
        handles-of  (fn [p] (map first (reads/as-stored-arity-bindings-global idx p)))]
    (cond
      shape
      (let [[q n]   shape
            h       (first members)
            ps      (sort (disj (exact-above kb w q) q))
            b       (delay (relation-length kb q nil true))
            mrs     (meta-routes kb (:tax w) q)
            ;; every binding of `q` and of a bound predicate above it, and every
            ;; membership and edge a metatype route of `q` rests on, which is what a
            ;; reader's binding of `q` can read
            hidable (delay (boolean (or (some hidden-anywhere?
                                              (mapcat handles-of
                                                      (cons q (disj ((:genls-global-union w) q bound-xf (volatile! {}))
                                                                    q))))
                                        (some hidden-anywhere?
                                              (mapcat (fn [[hm _ path]] (cons hm (map first path))) mrs)))))
            route   (fn [hb choice links]
                      {:choices [choice] :links links
                       :excluded-at (fn [_] (and (not @hidable) (not (convicts? @b n hb))))})]
        (-> []
            (into (keep (fn [[hb kind v ctx]]
                          (when (or (and (= :exact kind) (not= n v)) (and (= :min kind) (> v n)))
                            (route hb [[hb ctx]] []))))
                  (bindings-of q))
            (into (for [p ps
                        [hb kind v ctx] (bindings-of p)
                        :when (and (= :exact kind) (not= n v) (not= h hb))]
                    (route hb [[hb ctx]] [[q p]])))
            (into (for [[hm ctx path len] mrs :when (not= n len)]
                    (route hm (into [[hm ctx]] path) [])))))

      pair
      (let [[f g]   pair
            hidable (delay (boolean (some hidden-anywhere? (mapcat handles-of [f g]))))]
        [{:choices [[]] :links [pair]
          :excluded-at (fn [pctx] (and (not @hidable) (not (pair-at? kb f g (up pctx) nil))))}]))))

(defn note-reading-moved!
  "Queue the arity nogoods `h` can ground, for the settle to place them again
  (`take-moved!`): an `except` of `h` arrived or left, or `h`'s class moved, which moves
  whether a reader reads a binding through it (`routes`).  A binding queues itself, and a
  `genl` edge the candidate tuples of the functors bound through a type at or below its
  lower end (`::meta-by-type`), read over the unscoped closure since the queue is a
  superset the placement scopes."
  [kb h]
  (let [cands (reasoning/nogood-candidates kb)]
    (if (binding-handle? kb h)
      (swap! cands update ::moved (fnil conj #{}) h)
      (let [s (some-> (p/get-sentex (:records kb) h) :sentence)]
        (when (and (seq? s) (= 'genl (first s)) (= 3 (count s)) (seq (::meta-by-type @cands)))
          (let [tax (reasoning/taxonomy kb)
                sub (second s)
                c   @cands
                fs  (into #{} (comp (filter #(or (= sub %) (tax/genl?-global tax % sub)))
                                    (mapcat #(get-in c [::meta-by-type %])))
                          (keys (::meta-by-type c)))]
            (when (seq fs)
              (swap! cands update ::moved (fnil into #{})
                     (tuples-of kb c (fn [[q]] (contains? fs q)))))))))))

(defn kind-of
  "The kind the arity nogood over the member handles `ms` reports under, read off the
  candidate index `c`: `:arity` for a candidate tuple, `:arity-descension` for one binding
  of each end of a pair; else nil."
  [kb c ms]
  (cond
    (and (= 1 (count ms)) (contains? (:arity c) (first ms))) :arity
    (= 2 (count ms))
    (let [[f g] (map #(binding-pred kb %) ms)]
      (when (and f g (or (contains? (::pairs c) [f g]) (contains? (::pairs c) [g f])))
        :arity-descension))))

(defn owned?
  "Is the placed nogood over `members` with antecedents but the `genlCx` edges `core` one
  this family places (`chain/place-arities!`): one member and a binding (`binding-of`)
  among the other antecedents, or two bindings and nothing else but `genl` edges?"
  [kb members core]
  (let [recs   (:records kb)
        others (remove (set members) core)]
    (boolean
     (case (count members)
       1 (some #(binding-handle? kb %) others)
       2 (and (every? #(roster-binding? recs %) members)
              (every? #(= 'genl (some-> (p/get-sentex recs %) :sentence first)) others))
       false))))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no conviction of the arity nogood over the
  handles `ms`: a candidate tuple whose length breaks no binding of its functor
  (`relation-length`, the same at every reader but for `hidden?`), or one binding of each
  end of a pair the reader does not read as two lengths (`pair-at?`).  `hidden?` names the handles the reader does not believe or see,
  or is nil.  False for any other set."
  [kb c ms up hidden?]
  (boolean
   (case (kind-of kb c ms)
     :arity            (when-let [[q n] (shape-of kb (first ms))]
                         (not (convicts? (relation-length kb q hidden? false) n nil)))
     :arity-descension (let [[f g] (map #(binding-pred kb %) ms)]
                         (not (pair-at? kb f g up hidden?)))
     nil)))

(defn binding-grounds
  "The bindings among the antecedents `antes` of a placed arity nogood's justification."
  [kb antes]
  (filterv #(binding-handle? kb %) antes))

(def family
  "The arity family's entry in `decide/registry`.  Each nogood of it is placed as a
  conclusion (`chain/place-arities!`).  A recover empties the length entries and owes the
  candidates whole (`::owed`): the first sync after it computes them off the binding
  family (`arity-rebuilt`) and queues every one, since a store written with no belief
  holds no placement."
  {:grounds   {:forced-monotonic          sx/arity-binding-functors
               :forced-between-predicates '#{genl}}
   :note!     (fn [kb w sx stored?]
                (note-arity! kb w sx stored?)
                (when-not stored? (note-placement-left! kb sx)))
   :recovered (fn [kb _]
                (reset! (reasoning/arity-lengths kb) nil)
                (swap! (reasoning/nogood-candidates kb) assoc ::owed true))
   :synced?   (fn [tax c] (and (not (::owed c)) (= (::conflict-gen c) (tax/relation-gen tax :genl))))
   :sync      (fn [kb w c] (if (::owed c)
                             (arity-rebuilt kb w (dissoc c ::owed))
                             (conflict-up-current kb w c)))
   :handles   (fn [_ c] (concat (:arity c) (:arity-pairs c)))
   :holds?    (fn [_ c h] (or (contains? (:arity c) h) (contains? (:arity-pairs c) h)))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-cache
 {:cache    :arity-lengths
  :label    "Arity lengths"
  :scope    :kb
  :unit     "functors, and the lengths and floors their entries hold"
  :limit    (caches/limit-thunk :arity-lengths lengths-cache-limit)
  :counters :kb
  :note     (str "Per functor, the exact lengths stored at or above it, its own lengths "
                 "and arityMin floors, and the types of its memberships; per type, the "
                 "exact lengths it reaches through the genl closure. A "
                 "binding or membership write evicts the entries it moves, a genl edge's "
                 "relation move every entry at or below its lower end; past the bound, and "
                 "under memory pressure, the least recently used go first.")
  ;; the LRU's own tally answers the hits while it exists; before the family's first read
  ;; there is none, and nothing has been counted
  :read     (fn [kb] (if-let [lru @(reasoning/arity-lengths kb)]
                       {:entries (caches/lru-weight lru)}
                       {:entries 0 :hits 0 :misses 0}))
  :clear    (fn [kb] (or (some-> @(reasoning/arity-lengths kb) caches/lru-clear!) 0))
  :trim     (fn [kb target]
              (or (some-> @(reasoning/arity-lengths kb) (caches/lru-trim! target)) 0))})

(caches/register-derived
 {:id :N3 :label "Arity candidates" :kind :cache :keyed-by :functor
  :holds-content? false
  :reads [:index :records :T1 :J5 :N8]
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :edge-belief :K :declared :K
               :settle-pass :K :recover :R :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates :arity] [:nogood-candidates :arity-pairs]
       [:nogood-candidates ::cand-shapes] [:nogood-candidates ::pairs]
       [:nogood-candidates ::pairs-by] [:nogood-candidates ::pair-count]
       [:nogood-candidates ::at-conflict] [:nogood-candidates ::conflict-up]
       [:nogood-candidates ::conflict-gen] [:nogood-candidates ::moved]
       [:nogood-candidates ::owed] [:nogood-candidates ::arrived]
       [:nogood-candidates ::meta-by-type] [:nogood-candidates ::meta-types-of]]
  :bound "one entry per tuple of a shape a stored binding breaks, per pair of predicates storing two lengths and its bindings, and per type at or above a predicate under a conflict"
  :note "the shapes the stored bindings break, read off the shape roster, the pairs, and the handles queued for the settle to place again; a recover owes them whole (`::owed`) and the first sync computes them off the binding family; the functors below the lower end of a `genl` edge whose activation moved, by a write or by belief, are recomputed at the next write or sync through the relation moves (J5), and `::conflict-up` raised with them, whole when the generation restarts"})

(caches/register-derived
 {:id :N8 :label "Arity lengths" :cache :arity-lengths :kind :cache :keyed-by :functor
  :holds-content? false
  :reads [:index :records :T1 :J5]
  :retired-by {:stored :K :removed :K :edge :K :edge-belief :K :settle-pass :K
               :recover :W :caches-cleared :W}
  :computed :write :imaged? false :at [[:arity-lengths]]
  :value (fn [kb] (when-let [^java.util.LinkedHashMap m (:map (caches/value-at kb [:arity-lengths]))]
                    (locking m (into {} m))))
  :note "per functor, the exact lengths stored at or above it, its own lengths and floors, and the types of its memberships, and per type the exact lengths it reaches through the genl closure, in a weighted LRU; a binding or membership write evicts the entries it moves, and the relation moves (J5) evict every entry at or below a moved edge's lower end at the next read, the settle's sync and placement reads included"})
