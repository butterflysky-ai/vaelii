;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide
  "The nogood candidate index.  Each family keeps its rows of one candidate index
  (`:nogood-candidates`), which the placement detectors read; this namespace runs the
  families as one index, holds the forced-monotonic roster, and decides a placed nogood
  from its members' classes (`verdict`).  See docs/nmtms.md, \"A nogood placed as a
  conclusion\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.decide.related :as related]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn write-view
  "The unscoped closures of `tax`, under their `tax/…-global` names, and `tax` itself as
  `:tax`: the taxonomy a family keeps its rows through, handed to `:note!`, `:recovered`
  and `:sync`.  The rows are a superset over every reader, kept where no reader exists,
  and each reader scopes what it reads."
  [tax]
  {:tax                 tax
   :genls-global        (partial tax/genls-global tax)
   :direct-genls-global (partial tax/direct-genls-global tax)
   :specs-global        (partial tax/specs-global tax)
   :genl?-global        (partial tax/genl?-global tax)
   :genls-global-meets? (partial tax/genls-global-meets? tax)
   :genls-global-among  (partial tax/genls-global-among tax)
   :genls-global-union  (partial tax/genls-global-union tax)
   :specs-global-while  (partial tax/specs-global-while tax)
   :genls-global-while  (partial tax/genls-global-while tax)
   :context-up-global   (partial tax/context-up-global tax)
   :context-down-global (partial tax/context-down-global tax)})

(def registry
  "Every family, each a map of the parts the candidate index runs, `w` a `write-view`:

  * `:grounds`, `{kind #{functor}}`: the roster literals the family reads as stored
    grounds rather than as members, under the roster kind that reads them
    (`:forced-between-predicates` for a functor read only between predicate-spelled
    arguments).  Absent for a family that reads none.
  * `:note!` `(fn [kb w sx stored?])`, at the store and removal choke points; absent for
    a family the settle installs.
  * `:recovered` `(fn [kb w])`: writes the rows the family computes off the store once
    recover has emptied the index.
  * `:synced?` `(fn [tax c])` and `:sync` `(fn [kb w c] c)`: rows derived from the
    taxonomy, read again when it moved.
  * `:handles` `(fn [kb c])`, every handle some reader can read as a member; `:holds?`
    `(fn [kb c h])` answers whether `h` is among them with a few map reads, or off the
    index for a member the family reads there (the related-types family's cover pairs).  Every update that
    can move a handle into or out of it journals it (`journal/note`).  Absent for the
    negation family, whose members are an index family (`reads/as-stored-opposed-in`).
  Every family places its nogoods as conclusions (`chain/place-nogoods!`)."
  [tuple/converse-family arity/family negation/family tuple/marks-family membership/family
   related/family inherited/family])

(def held-members
  "The roster members no family reads among its grounds, each with the reason it is on the
  roster (docs/nmtms.md, \"The forced-monotonic roster\")."
  '{genlCx     "every context's ancestor set reads the stored edges"
    except     "withdrawing one un-hides its target, so the OUT set of a round would shrink"
    orthogonal "the one member of the related-types family's clash of it, which is a conflict and never a defeat"
    rewriteOf  "withdrawing one un-merges two terms, so the OUT set of a round would shrink"
    sameAs     "withdrawing one un-merges two terms, so the OUT set of a round would shrink"
    equals     "withdrawing one un-merges two terms, so the OUT set of a round would shrink"
    injection  "a premise of core.txt's rules concluding (functional P) and (functionalInArg P 1)"
    surjection "a premise of core.txt's rule concluding (functional P)"
    bijection  "a premise of core.txt's rules concluding (injection P) and (surjection P)"})

(def baseline-roster
  "The engine's own roster, `{kind #{predicate …}}`: every family's `:grounds` and every
  `held-members` member, held on every KB whether or not it is stated."
  (reduce #(merge-with into %1 %2)
          {:forced-monotonic (set (keys held-members)) :forced-between-predicates #{}}
          (keep :grounds registry)))

(def roster-kinds "The two roster properties." (set (keys baseline-roster)))

(defn- declarations
  "`{handle context}` of the stored declarations giving `pred` the roster property
  `kind`, believed or not, or nil when no believed one does.  Read KB-wide: each reader
  keeps the ones it sees (`on-roster?`)."
  [tax kind pred]
  (when (tax/has-prop? tax kind pred)
    (tax/prop-supporter-contexts tax kind pred)))

(defn global?
  "Is `pred` on the global roster as `kind`: a `baseline-roster` member.  Every reader
  reads it on the roster, and no declaration moves it.  A declaration in any context,
  CxUniverse's included, puts its predicate on the roster at the readers that believe it
  (`on-roster?`, docs/nmtms.md, \"The forced-monotonic roster\")."
  [_tax kind pred]
  (contains? (baseline-roster kind) pred))

(defn on-roster?
  "Does `pred` carry the roster property `kind` (`:forced-monotonic` or
  `:forced-between-predicates`).  The 3-arity is the union over every reader: `global?`,
  or a believed declaration in any context.  The 4-arity is one reader's: `global?`, or
  a declaration `[handle context]` `seen?` holds of."
  ([tax kind pred]
   (or (contains? (baseline-roster kind) pred) (tax/has-prop? tax kind pred)))
  ([tax kind pred seen?]
   (or (global? tax kind pred)
       (boolean (some (fn [[h c]] (seen? h c)) (declarations tax kind pred))))))

(defn global-reading
  "The roster reading `(fn [kind pred])` every reader shares (`global?`)."
  [tax]
  (partial global? tax))

(defn reader-reading
  "The roster reading `(fn [kind pred])` of a reader that sees the declarations `[handle
  context]` `seen?` holds of (`on-roster?`, 4-arity)."
  [tax seen?]
  (fn [kind pred] (on-roster? tax kind pred seen?)))

(defn roster
  "Every predicate `on-roster?` as `kind`, over every reader."
  [tax kind]
  (into (baseline-roster kind) (tax/props tax kind)))

(defn declared
  "`{[kind pred] {handle context}}`: every predicate on the roster by a believed
  declaration and off the global roster (`global?`), with its declarations.  Empty on a
  KB that declares only baseline members.  Read KB-wide, the union over every reader,
  which a read walk splits into the declarations its reader sees and misses."
  [tax]
  (into {} (for [kind roster-kinds
                 pred (tax/props tax kind)
                 :when (not (global? tax kind pred))]
             [[kind pred] (tax/prop-supporter-contexts tax kind pred)])))

(defn- predicate-spelled?
  "Is `x` spelled as a predicate of arity 2 or more: `nm/predicate?` and not
  `nm/type-symbol?`, so camelCase with an uppercase letter after the first character.  A
  bare lowercase word satisfies the type spelling as well and is read as a type
  (docs/naming.md)."
  [x]
  (and (nm/predicate? x) (not (nm/type-symbol? x))))

(defn roster-literal?
  "Is `literal` on the forced-monotonic roster: its functor is `on-roster?` as
  `:forced-monotonic`, or as `:forced-between-predicates` with every argument spelled as a
  predicate of arity 2 or more.  The 2-arity reads the union over every reader; the
  3-arity reads the roster reading `on?` (`global-reading`, `reader-reading`)."
  ([tax literal] (roster-literal? tax literal (partial on-roster? tax)))
  ([_tax literal on?]
   (let [f (nm/functor literal)]
     (boolean (and (symbol? f)
                   (or (on? :forced-monotonic f)
                       (and (on? :forced-between-predicates f)
                            (next literal)
                            (every? predicate-spelled? (rest literal)))))))))

(defn literal-declarations
  "`{handle context}` of the stored declarations that put `literal` on the roster and
  are not `global?`: empty when the global roster holds `literal` or no declaration
  does."
  [tax literal]
  (let [f (nm/functor literal)]
    (if (or (not (symbol? f)) (roster-literal? tax literal (global-reading tax)))
      {}
      (cond-> (or (declarations tax :forced-monotonic f) {})
        (and (next literal) (every? predicate-spelled? (rest literal)))
        (merge (declarations tax :forced-between-predicates f))))))

(defn note-candidate!
  "Keep `:nogood-candidates` in step with the fact `sx` arriving (`stored?` true) or
  leaving.  Runs at the store primitive and the removal choke point, after the index
  write."
  [kb sx stored?]
  (let [w (write-view (reasoning/taxonomy kb))]
    (doseq [{:keys [note!]} registry :when note!]
      (note! kb w sx stored?))))

(defn offer!
  "Offer the stored facts `sxs` to the tuple candidates again (`tuple/offer!`), with
  `only` `:converse` to the converse candidates alone."
  ([kb sxs] (offer! kb sxs nil))
  ([kb sxs only]
   (let [w (write-view (reasoning/taxonomy kb))]
     (doseq [sx sxs] (tuple/offer! kb w sx only)))))

(defn rebuild-candidates!
  "Recompute `:nogood-candidates` from storage, for `recover`: each family computes its
  rows off the store (`:recovered`), and no record is read for a family that stores no
  fact it reads."
  [kb]
  (let [cands (reasoning/nogood-candidates kb)
        w     (write-view (reasoning/taxonomy kb))]
    (reset! cands {})
    (doseq [{:keys [recovered]} registry :when recovered]
      (recovered kb w))
    (swap! cands journal/restart)))

(defonce ^{:private true
           :doc "`[candidates-atom taxonomy candidates]` of the last `synced` read: the index
  it answered and the taxonomy value it was synced against.  `:synced?` reads only the
  taxonomy and the index, so a read finding both identical answers from here; a settle
  reads them several times an assert.  A
  volatile vector, as `provers/registry-support`: a lost race costs a recompute."}
  sync-memo
  (volatile! nil))

(defn drop-memos
  "Empty `sync-memo`, and return nil.  It is process-wide and holds the taxonomy value of
  the last KB read, which holds a view of that KB, so it keeps its records and index
  reachable until another KB is read; `vaelii.core/close!` calls this last.  A KB still
  open recomputes its entry on its next read."
  []
  (vreset! sync-memo nil)
  nil)

(defn candidate?
  "Is `h` among `candidate-handles` of the candidate index `c` of `kb`?"
  [kb c h]
  (boolean (some #(% kb c h) (keep :holds? registry))))

(defn- handles-of-index
  "Every handle some reader can read as a nogood member of a family of the candidate
  index `c` of `kb`."
  [kb c]
  (into #{} (mapcat #(% kb c)) (keep :handles registry)))

(defn synced
  "The candidate index after each family's rows derived from the taxonomy are read again
  where it moved (`:synced?`, `:sync`), and its candidates by the context they are stated
  in read again off the journal (`journal/indexed`, read by `handles-at`)."
  [kb]
  (let [tax   (reasoning/taxonomy kb)
        cands (reasoning/nogood-candidates kb)
        t     @tax
        [a mt mc] @sync-memo]
    (if (and (identical? a cands) (identical? mt t) (identical? mc @cands))
      mc
      (let [recs (:records kb)
            _    (reduce (fn [c {:keys [synced? sync]}]
                           (if (or (nil? sync) (synced? tax c))
                             c
                             (swap! cands #(if (synced? tax %) % (sync kb (write-view tax) %)))))
                         @cands registry)
            c    (swap! cands journal/indexed #(candidate? kb %1 %2)
                        #(:context (p/get-sentex recs %)) #(handles-of-index kb %))]
        (vreset! sync-memo [cands t c])
        c))))

(defn candidate-handles
  "Every handle some reader can read as a nogood member of a family."
  [kb]
  (handles-of-index kb (synced kb)))

(defn handles-at
  "The candidates of `c`, as `synced` answers it, stated in a context of the ancestor set
  `up` or in none: every handle a reader with ancestor set `up` can read as a nogood
  member, which a `genlCx` edge's placement pass reads
  (`special/drain-context-moves!`)."
  [c up]
  (journal/at c up))

(defn take-edge-cursor!
  "`[since first?]`: the `genlCx` generation the last call read when it has moved since,
  else nil, so `tax/moves-since` reads the edges moved after it; and
  `first?`, true when no call has read it since the candidate index was emptied
  (`rebuild-candidates!`), so every placement may be owed.  The settle's drain reads it
  once a pass (`special/drain-context-moves!`)."
  [kb]
  (let [gen     (tax/relation-gen (reasoning/taxonomy kb) :genlCx)
        [old _] (swap-vals! (reasoning/nogood-candidates kb)
                            #(if (= gen (::genlcx %)) % (assoc % ::genlcx gen)))]
    [(when (not= gen (::genlcx old)) (or (::genlcx old) 0))
     (not (contains? old ::genlcx))]))

(defn placements-owed?
  "Is every placement owed: no placement pass has read the edge cursor since the
  candidate index `c` was emptied (`rebuild-candidates!`, `take-edge-cursor!`)?"
  [c]
  (not (contains? c ::genlcx)))

(defn moves
  "`[c pos moved]`: the candidate index as `synced` answers it, its journal position, and
  the handles journaled since the position `since` (`journal/since`), which hold every
  handle that entered or left the candidates since; nil when the journal does not reach
  back to `since`, and a reader reads the index whole."
  [kb since]
  (let [c (synced kb)]
    [c (journal/position c) (journal/since c since)]))

(defn note-reading-moved!
  "An `except` of `h` arrived or left, or `h`'s class moved: queue what `h` grounds for the
  families whose placement reads what a reader believes and sees
  (`arity/note-reading-moved!`)."
  [kb h]
  (arity/note-reading-moved! kb h))

(defn arity-held?
  "Does the arity index keep a candidate or the binding of a pair (`arity/held?`), read
  off the index as written, with no sync?"
  [kb]
  (arity/held? @(reasoning/nogood-candidates kb)))

(defn placed-kind
  "The kind a nogood over the member handles `ms` placed as a conclusion reports under,
  read off the members' sentences: `:negation` for a `B` beside `(not B)`, the membership
  family's kind (`membership/kind-of`), the related-types family's (`related/kind-of`),
  the tuple families' (`tuple/kind-of`), the arity family's (`arity/kind-of`),
  `:inherited` for a set the inherited detector found (`inherited/inherited-clashes`), or
  nil for any other set."
  [kb ms]
  (let [recs (:records kb)]
    (or (when (contains? (inherited/inherited-clashes kb) ms) :inherited)
        (when (= 2 (count ms))
          (let [[a b] (map #(:sentence (p/get-sentex recs %)) ms)]
            (when (or (= a (list 'not b)) (= b (list 'not a))) :negation)))
        (let [w (write-view (reasoning/taxonomy kb))]
          (or (membership/kind-of w recs ms) (related/kind-of w recs ms)))
        (let [c (synced kb)] (or (tuple/kind-of kb c ms) (arity/kind-of kb c ms))))))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no conviction of the placed nogood over the
  member handles `ms`: a membership nogood whose separation a `siblingDisjointException`
  it sees removes (`membership/exempt-at?`), a contradicted `orthogonal` whose separation
  such an exception removes (`related/exempt-at?`),
  a determinant pair whose fillers it reads as one class (`tuple/exempt-at?`), or an
  arity nogood it reads no binding for (`arity/exempt-at?`).  `hidden?` names the handles
  the reader does not believe or see, or is nil.  False for any other nogood."
  [kb ms up hidden?]
  (let [tax  (reasoning/taxonomy kb)
        recs (:records kb)]
    (or (membership/exempt-at? tax recs ms up)
        (related/exempt-at? (write-view tax) recs ms up)
        (and (seq (tax/equality-edges tax)) (tuple/exempt-at? kb (synced kb) ms up hidden?))
        (and (arity-held? kb) (arity/exempt-at? kb (synced kb) ms up hidden?)))))

(defn verdict
  "The verdict on nogood `members` from `class-of` (`handle -> defeat-class`) and
  `roster?` (`handle -> boolean`, is the member a roster literal): `{:defeat h}` for a
  unique weakest defeasible member off the roster, `:dilemma` for a defeasible minimum two
  such members share, and `:hard` when no member off the roster is defeasible.  A roster
  member is never a loser, whatever its class (docs/reference.md, item 7 of \"The
  function\")."
  [class-of roster? members]
  (let [ranked (into [] (keep (fn [h] (let [c (class-of h)]
                                        (when (and (strength/defeasible? c) (not (roster? h)))
                                          [h c]))))
                     members)]
    (if (empty? ranked)
      :hard
      (let [floor   (reduce min (map #(strength/rank-of (peek %)) ranked))
            weakest (filterv #(= floor (strength/rank-of (peek %))) ranked)]
        (if (= 1 (count weakest)) {:defeat (ffirst weakest)} :dilemma)))))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :J1 :label "Candidate journal" :kind :journal :keyed-by :handle :reads [:N1 :N3 :N5]
  :holds-content? false
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :declared :K :edge-belief :K
               :inherited :K :settle-pass :K :recover :R :image-install :R}
  :computed :write :imaged? false :at [[:nogood-candidates ::journal/journal]]
  :note "the handles each family's update moved into or out of a reader's reach, by position; restarted past 16,384, by `rebuild-candidates!` and at an image install"})

(caches/register-derived
 {:id :J2 :label "Candidates by context" :kind :cache :keyed-by :context :reads [:J1 :N1]
  :holds-content? false
  :retired-by {:stored :K :removed :K :respelled :K :edge-belief :K :inherited :K :recover :R
               :image-install :R}
  :computed :read :imaged? false :at [[:nogood-candidates ::journal/at]]
  :note "the candidates by context and the J1 position they were indexed at, brought up to date at a read (`synced`); whole when J1 lost the position"})

(caches/register-derived
 {:id :J6 :label "Placement edge cursor" :kind :counter :keyed-by :global :reads [:J5]
  :holds-content? false
  :retired-by {:settle-pass :Q :recover :R :image-install :R}
  :computed :settle :imaged? :state :at [[:nogood-candidates ::genlcx]]
  :note "the `genlCx` generation the settle's context-move drain last read (`take-edge-cursor!`, `special/drain-context-moves!`), once a pass, for every `genlCx` family and the placement reach; absent after `rebuild-candidates!`, which owes every placement"})

(caches/register-derived
 {:id :X1 :label "Sync memo" :kind :cache :keyed-by :global :reads [:N1 :T1]
  :holds-content? false
  :retired-by (assoc (caches/on-every :I) :closed :W) :computed :read :imaged? false
  :var #'sync-memo
  :value (fn [_] @sync-memo)
  :note "one slot for the process: the candidates atom, taxonomy value and candidates of the last `synced` read, compared by identity; another KB's read evicts it"})

