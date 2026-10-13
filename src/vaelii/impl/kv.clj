;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.kv
  "The key-value substrate the index rests on, and the one `IndexStore`
  implementation written over it.

  The index — the trie, the secondary roots, the rule indexes, the exception
  re-check index, and the inverted term index — is *all* sets and counters keyed
  by structured vectors.  `KvIndexStore` encodes that structure once, in terms of a
  small `KvBackend` protocol; a backend is then just an adapter that says how a
  scalar, a counter, and a set live in some store.  An in-memory map
  (`vaelii.impl.memory`) and an on-disk WAL (`vaelii.impl.disk.kv`) are two such
  adapters; a SQL or overlay backend is another.

  ## The count-aware trie

  A sentex is indexed by its trie path.  Every node, identified by its path
  prefix, is exactly three keys:

    count-key  [:trie :count prefix]  ->  integer: how many sentexes live at the leaves
                                     under this prefix (selectivity without walking).
    set-key    [:trie :children prefix]  ->  a SET: the next possible token labels (the
                                     node's child edges).
    leaf-key   [:trie :handles prefix]  ->  a SET: the handles of the sentexes whose path
                                     ends exactly here.

  **Child edges and leaf handles are separate keys because the trie is ragged.**
  Paths differ in length with arity, so one sentex's *full* path can be a proper
  prefix of another's: `(rel A B)` in `CxCee` keys as `[rel A B CxCee]`,
  and `(rel A B CxCee X)` in `CxDee` keys as `[rel A B CxCee X
  CxDee]` — the first path is an interior node of the second.  Storing both
  handles and child tokens in one set therefore mixed them, and a caller could not
  tell them apart by type (a handle is an integer, and so is the token `1970`).  Two
  keys make the distinction structural: `lookup` reads only the leaf key at its
  terminus, so it can never return a token as a handle, and `children` reads only
  the child set, so `plan`'s fan-out divisor can never count a handle as a branch.

  Alongside the trie sit eleven smaller count tries whose last level is the context — the
  argument roots, the predicate extent, the two rule indexes, the rule extent, the
  opposed bodies, the self tuples, the arity bindings, the taxonomy's supporters and the
  mint family's two
  (\"The count tries that end in the context\" below) — and three flat sets whose
  cardinality is their own size: the context root, the exception re-check index and the
  inverted term index.  One more flat set, the **term roster**
  `[:term-roster]`, holds the term index's *names* rather than handles, so the
  vocabulary can be listed and counted in O(terms) instead of a walk over every record.

  Contract: lookup expects a *full* path (sentence tokens + a context slot; the
  context may itself be a variable).  A short pattern terminates on an interior
  node, whose leaf key is empty, so it yields nothing rather than that node's child
  labels dressed up as handles.

  ## The `KvBackend`

  Logical keys are structured vectors and set members are bare values; a backend
  turns those into whatever its store wants (an in-memory map uses them directly; the
  on-disk backend nippy-frames them into its log).  The required ops are
  `kv-batch` (the whole index write for one sentex lands as one unit — one batched
  write) and `kv-intersect` (the multi-column narrowing `sentexes-with-args` needs, one
  set intersection rather than N fetch-and-filter reads).  A batch op is a vector
  `[op key & args]` with `op` one of `:put`, `:delete`, `:increment`,
  `:decrement`, `:add-to-set`, `:remove-from-set`; `kv-batch`
  returns one reply per op in order (only `:increment`/`:decrement` replies — the post-op
  counter value — are read; the rest are placeholders that keep the vector aligned).

  **`kv-member?` is a membership test, not a fetch**, and it is its own op because on
  several backends those cost different orders.  `exception-rule?` is the gate
  `chain/rule-view-of` takes once per candidate rule per new datum, so answering it by
  materializing the roster and testing the result makes forward chaining a product of
  two KB-sized quantities.  A flat-map backend hands the stored set back by reference
  and hides the distinction entirely; a dense one holds the roster as an `IntPostings`,
  where 1e5 gate calls against a roster of 1,000 cost 15,926 ms built-then-tested
  against 87 ms on the flat map — so the op exists to let each backend answer with the
  probe it already has (a hash lookup, a binary search, a bitmap test)."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p
             :refer [kv-batch kv-clear! kv-count kv-entries kv-get
                     kv-intersect kv-load kv-member? kv-members unknown-op!]]
            [vaelii.impl.sentex :as sx]))

(def index-layout-version
  "Which key shapes this build's index is written in.

  The key families below — `[:trie :count|:children|:handles prefix]`, the context root,
  the five count tries ending in the context, the exception index, the term index and the
  rosters — *are*
  the index's portable form, so a dump of them is only readable by a build that agrees on
  them.  An index written in a layout this build does not use reads as **empty** rather
  than as wrong (a lookup finds no key and answers nothing), which is fail-safe and
  undiagnosable — so the layout is stated as a number and checked, rather than discovered
  by a KB that quietly stopped answering.

  **Bump it whenever a key shape changes**: a new family, a renamed tag, a different
  arity, or a different value type at an existing key.

  2 scopes the argument roots by predicate (`[:argument-root pred pos term]`) and adds
  the `[:argument-slot pos term]` roster that keeps the predicate-agnostic reads
  answerable.  3 adds the `[:unary-slot term]` roster beside it, which is what lets a
  membership question read a term's types without fetching every fact that names it.
  4 keys the argument roots as a count trie over `[pred pos term ctx]`: a node's
  `[:argument-root :count|:children [pred pos term]]` and the leaf
  `[:argument-root :handles [pred pos term ctx]]`.  5 replaces the functor root with the
  predicate extent, a count trie over `[pred ctx]`, and keys the two rule indexes as count
  tries over `[key ctx]` (`:rule-antecedent`, `:rule-consequent`).  6 adds the rule
  extent, a count trie over `[kind ctx]` (`:rule-extent`), and the antecedent trie's root
  level, `[:rule-antecedent-keys]`.  7 adds the bodies stored in both polarities: the
  count trie `:opposed` over `[body ctx]`, its root level `[:opposed-bodies]`, and the
  members by context, `[:opposed-in ctx]`.  8 adds the taxonomy's supporter families: a
  count trie over `[k ctx]` keyed by the key a declaration installs (`:tax-support`), and
  `[:tax-installs h]`.  9 adds the mint family: the `:mint` count trie over `[term ctx]`
  with its root level `[:mint-terms]`, and the `:mint-in` count trie over `[ctx]`.  10
  adds the shape roster, `[:shape-count f n]` and `[:shape-lengths f]`, `[:unary-multi]`,
  the terms the unary roster lists two or more predicates of, and the self-tuple count
  trie over `[pred ctx]` (`:self-tuple`).  11 adds the same terms by predicate,
  `[:unary-kept pred]` and `[:unary-kept-types]`, and the terms a stored denial names by
  predicate, `[:unary-denied pred]` and `[:unary-denied-types]`.  12 adds the arity
  bindings: the count trie `:arity-binding` over `[pred kind value ctx]`, with
  `[:arity-binding-kinds pred]` and `[:arity-bound]` above its nodes.  13 replaces the
  shape counter with the count trie `:shape-tuple` over `[f n ctx]`, the positive facts of
  functor `f` holding `n` arguments, with `[:shape-lengths f]` above its nodes.  14 adds
  the count trie `:tax-named` over `[rel functor ctx]`, the positive `except` and `defeat`
  facts naming a stored supporter of a taxonomy relation."
  14)

(defn apply-op
  "Apply one `kv-batch` write op to map `m`, returning `[m' reply]`.  Only
  `:increment`/`:decrement` carry a meaningful reply (the post-op counter value); the
  rest reply nil.  `:remove-from-set` drops the key when the set empties, so an absent
  key and an empty set are indistinguishable — a set with no members does not exist.

  **The op semantics live here, with the protocol that names them, and not in the
  backends.**  Both map-shaped backends fold their writes through this — the in-memory
  one (`vaelii.impl.memory`) over its state map, the on-disk one
  (`vaelii.impl.disk.kv`) over the RAM half of its write-ahead log, where it is also
  what *replays* the log, since a WAL frame there is the write op itself rather than
  the resulting value.  Written twice, the two copies could answer one op differently,
  and the disk side is replay: a seventh op added to the live path and missed in the
  fold would be a write that applies once and never comes back.

  An unrecognized op goes to `unknown-op!`, which every adapter shares: a bulk load
  taking the transient path, a dense backend's own batch, a fork decorator's, and an
  ordinary write taking this one may not disagree about what an unreadable op is.

  `:decrement` floors at zero, per the `KvBackend` contract: these counters are
  cardinalities.  The floor is in every fold rather than in one of them, because the WAL
  replays through this and the live write went through a backend — a floor applied on
  only one side would make a reopened store disagree with the one that wrote it."
  [m [op k a]]
  (case op
    :put  [(assoc m k a) nil]
    :delete  [(dissoc m k) nil]
    :increment (let [v (inc (long (get m k 0)))] [(assoc m k v) v])
    :decrement (let [v (max 0 (dec (long (get m k 0))))] [(assoc m k v) v])
    :add-to-set [(update m k (fnil conj #{}) a) nil]
    :remove-from-set (let [s (disj (get m k) a)]
                       [(if (empty? s) (dissoc m k) (assoc m k s)) nil])
    (unknown-op! op)))

;; ---- the family registry -------------------------------------------------

(def index-families
  "The index families, one row per key tag (the first element of every key the index
  writes), as data.  `dense-kv`'s handle-posting test reads `:leaf`, the importer's
  records-only test reads `:source`, and the root-roster keys below read `:root`.
  docs/indexing.md, \"The index-family registry\", states what each field decides.

  - `:shape` — `:trie`, `:count-trie` (`[tag :count|:children node]` and `[tag
    :handles (conj node ctx)]`), `:set` or `:counter`.
  - `:leaf` — `:handles` (int postings) or `:names` (terms, keys); nil for a counter.
  - `:context-last?` — whether the key's last level is the context.
  - `:children?` — whether a node lists the contexts below it.
  - `:root` — the tag of the roster one level above the family's nodes, where one is
    stored.
  - `:canon?` — whether a key term is `sx/canon`'d.
  - `:source` — what the write posts from: `:sentex` (`index-sentex`), `:rule`
    (`rules/index-rule`, `rules/index-exception`), `:justification` (`special/post-mint!`)
    or `:taxonomy` (`taxonomy`'s `post!`).
  - `:class` — what a KB without the family loses: `:access-path`, `:scan-recoverable` or
    `:sole-witness`, with `:class-evidence` holding `:oracle` (test vars) and `:via`
    (the families the other path reads), `:writes` (the writes that read the family,
    empty when none does) or `:readers`."
  (let [ctrie (fn [source m] (merge {:shape :count-trie :leaf :handles :context-last? true
                                     :children? true :canon? false :source source} m))
        roster (fn [source m] (merge {:shape :set :leaf :names :context-last? false
                                      :children? false :canon? false :source source} m))
        scan  (fn [& writes] {:class :scan-recoverable :class-evidence {:writes (vec writes)}})
        sole  (fn [& readers] {:class :sole-witness :class-evidence {:readers (vec readers)}})
        term-oracle {:class :access-path
                     :class-evidence {:oracle '[vaelii.arg-root-retrieval-test/the-families-agree-with-the-term-index]
                                      :via [:term-index]}}
        membership (scan "decide.membership's placement of a term's memberships, on a fact, a cover or an edge move")
        arity      (scan "decide.arity's arity rows, on a binding fact and the first sync after recover")
        opposed    (scan "chain/place-negations! and chain/place-nogoods!, on a fact and a genlCx edge")
        rules      (sole "chain/fire-rules-for" "resolution/concluding-rule-handles" "the solve's program")
        mints      (sole "special's mint withdrawal and its genlCx edge routes")
        supporters (sole "the taxonomy's supporter reads" "reindex")]
    {:trie (merge {:shape :trie :leaf :handles :context-last? true :children? true
                   :canon? false :source :sentex}
                  (sole "plan's count-at and children" "kb's leaf-at, the assert dedup" "lookup"))
     :context-root (merge (roster :sentex {:leaf :handles :context-last? true})
                          (scan "special/entail-under-context-edge and the other genlCx edge arms"))
     :predicate-extent (ctrie :sentex term-oracle)
     :argument-root (ctrie :sentex {:canon? true :class :access-path
                                    :class-evidence {:oracle '[vaelii.arg-root-retrieval-test/a-sample-of-the-arg-root-oracle-runs-at-default
                                                               vaelii.matches-hierarchical-test/a-sample-of-the-hierarchical-oracle-runs-at-default]
                                                     :via [:trie]}})
     :argument-slot (roster :sentex (assoc term-oracle :canon? true))
     :unary-slot (roster :sentex (assoc term-oracle :canon? true))
     :unary-multi (roster :sentex membership)
     :unary-kept (roster :sentex (assoc membership :root :unary-kept-types))
     :unary-kept-types (roster :sentex membership)
     :unary-denied (roster :sentex (assoc membership :root :unary-denied-types))
     :unary-denied-types (roster :sentex membership)
     :shape-tuple (ctrie :sentex (assoc arity :root :shape-lengths))
     :shape-lengths (roster :sentex arity)
     :self-tuple (ctrie :sentex (scan "decide.tuple's irreflexivity candidates, on a fact"))
     :opposed (ctrie :sentex (assoc opposed :root :opposed-bodies))
     :opposed-bodies (roster :sentex opposed)
     :opposed-in (merge (roster :sentex {:leaf :handles :context-last? true}) opposed)
     :arity-binding (ctrie :sentex (assoc arity :root :arity-binding-kinds))
     :arity-binding-kinds (roster :sentex (assoc arity :root :arity-bound))
     :arity-bound (roster :sentex arity)
     :rule-extent (ctrie :sentex rules)
     :rule-antecedent (ctrie :rule (assoc rules :root :rule-antecedent-keys))
     :rule-antecedent-keys (roster :rule rules)
     :rule-consequent (ctrie :rule rules)
     :exception-index (roster :rule (merge {:leaf :handles}
                                           (sole "except's exceptWhen re-check on a fact or an edge")))
     :tax-support (ctrie :taxonomy supporters)
     :tax-installs (roster :taxonomy supporters)
     :tax-named (ctrie :sentex {:class :access-path
                                :class-evidence {:oracle '[vaelii.index-test/the-named-supporter-family-agrees-with-the-naming-trie]
                                                 :via [:trie :tax-installs]}})
     :mint (ctrie :justification (assoc mints :root :mint-terms))
     :mint-terms (roster :justification mints)
     :mint-in (ctrie :justification mints)
     :term-index (roster :sentex (merge {:leaf :handles :canon? true :root :term-roster}
                                        (scan "special/trigger-entailments" "special/migrate-handle-metas"
                                              "except/conflicts-naming" "settle's partners"
                                              "chain/placed-justifications-within")))
     :term-roster (roster :sentex (scan))}))

(defn- root-of
  "The tag of family `tag`'s root roster (`index-families`)."
  [tag]
  (:root (index-families tag)))

;; ---- logical keys -------------------------------------------------------
;; Structured vectors — a backend encodes them (used directly as map keys in memory;
;; nippy-framed on disk).  The trie node's three keys share the [:trie …] prefix and
;; differ only in the :count/:children/:handles tag; the roots and indexes take
;; their own tags.

(defn- count-key [prefix] [:trie :count prefix])
(defn- set-key   [prefix] [:trie :children prefix])
;; leaf handles live under their own key, never mixed into the child-token set —
;; see the ragged-path note in the namespace docstring.
(defn- leaf-key  [prefix] [:trie :handles prefix])

;; the context root — the trie is ordered [pred args… ctx], so it narrows only
;; left-to-right: it cannot count "context C" (the deepest level) without fixing everything
;; to its left.  A flat set; cardinality is the set's own size.
(defn- ctx-key  [c]     [:context-root c])

;; ---- the count tries that end in the context -----------------------------
;; Thirteen families share one shape: a count trie whose last level is the context.  A
;; `node` is the path above the context, and each node is three keys under the family's
;; `tag` — its count (how many handles sit under it, in every context), its children (the
;; contexts that state one) and, per child, the leaf holding that context's handles:
;;
;;   :argument-root     node [pred pos term]   `pred`'s facts with `term` at 1-based `pos`
;;   :predicate-extent  node [pred]            `pred`'s facts, either polarity
;;   :rule-antecedent   node [key]             the rules with an antecedent on `key`
;;   :rule-consequent   node [key]             the rules whose consequent files under `key`
;;   :rule-extent       node [kind]            every rule (`:rule`), and the rules a solve
;;                                             reads (`:solve`)
;;   :opposed           node [body]            the facts of a body stored in both
;;                                             polarities, either polarity
;;   :self-tuple        node [pred]            `pred`'s ground positive binary self
;;                                             tuples `(pred a a)`
;;   :shape-tuple       node [f n]             `f`'s positive facts of `n` arguments
;;   :arity-binding     node [pred kind value] the facts binding `pred`'s length
;;                                             (`sx/arity-binding`): kind `:exact`,
;;                                             `:min` or `:var`, value nil for `:var`
;;   :tax-support       node k                 the supporters of taxonomy key `k`, which
;;                                             the taxonomy writers post (below)
;;   :tax-named         node [rel f]           the positive `(f (sentexHandle H))` facts,
;;                                             `f` `except` or `defeat`, whose H installs
;;                                             a key of relation `rel` (`key-relation`)
;;   :mint              node [term]            the mints about `term`
;;   :mint-in           node []                every mint
;;
;; So "what is stated under this node in the contexts a reader sees" reads the node's
;; children, intersected with the reader's ancestor set, and the leaves it keeps.  The
;; `:rule-antecedent` trie's root level, the keys some stored rule takes, is the one level
;; above a node any read asks for, and it is stored under its own tag,
;; `:rule-antecedent-keys`, because its members are keys rather than contexts.  The
;; `:opposed` trie's root level is `opposed-bodies-key` for the same reason.

(defn- node-count-key [tag node]     [tag :count node])
(defn- node-ctxs-key  [tag node]     [tag :children node])
(defn- node-leaf-key  [tag node ctx] [tag :handles (conj node ctx)])
(def ^:private opposed-bodies-key [(root-of :opposed)])
(defn- opposed-in-key [ctx] [:opposed-in ctx])

;; ---- the argument family's keys ------------------------------------------
;; The argument roots are the `:argument-root` trie, and the family adds two rosters
;; beside it: the slot roster that keeps the predicate-AGNOSTIC reads answerable without
;; a second copy of the postings, and the unary slice of that roster a membership question
;; reads.  `arg-slots` below canonicalizes the term on the way in and the argument reads
;; (`sentexes-with-args`, the `reads` entry points) canonicalize on the way out, so a term reaching a key here is already
;; `sx/canon`'d: a lazy seq and the `PersistentList` it is `=` to agree in any Clojure map
;; but freeze to different nippy bytes, so a key built from an uncanonicalized term misses
;; a durable backend's stored key and reports the fact absent
;; (`index_edge_test/the-argument-root-canonicalizes-a-compound-term` is the pin).

(defn- arg-ctxs-key  [node] (node-ctxs-key :argument-root node))
(defn- arg-leaf-key  [node ctx] (node-leaf-key :argument-root node ctx))

(defn- slot-key
  "The slot roster key: the predicates present at `(pos, term)`.

  This keeps the predicate-AGNOSTIC reads answerable without a second copy of the
  postings — the coarse read is a union over a handful of scoped leaves rather than one
  wide bucket.  Its members are predicates, so it is vocabulary-scaled."
  [pos term]
  [:argument-slot pos term])

(defn- unary-slot-key
  "The unary slice of the slot roster: the predicates `term` is the LONE argument of.

  `kb/types-of` — the retrieval every definitional check bottoms out on — asks what types
  a term holds, and `slot-key` cannot answer it: `(T x)` and `(P x y)` both put `x` at
  position 1, share the roster entry and share the trie node below it, so the only way to
  tell them apart was to fetch every record at that node and read its arity.  A term at
  argument 1 of n binary facts therefore cost n record fetches per membership question,
  and every assert asks one.

  A deliberate **superset**: the entry is written by every unary fact rather than
  reference-counted on the first, so a predicate used at two arities with one term is
  listed here whichever arity arrived first.  Over-answering costs one posting read that
  the caller's arity filter drops; under-answering would lose a membership."
  [term]
  [:unary-slot term])

;; the key both index stores' non-trie writes carry, through `flat-family-adds` /
;; `flat-family-retires` below, so the two stores key the term index identically.
(defn term-key [term]  [:term-index (sx/canon term)])
;; the term roster — ONE set holding every name the term index is keyed by, so the
;; vocabulary is listable and countable without walking the records.  Its own key
;; family, because its members are terms rather than handles: a backend that packs the
;; handle families into int postings routes `[:term-roster]` to its ordinary set storage.
(def ^:private roster-key [(root-of :term-index)])

;; The terms the unary roster lists two or more predicates of, which the membership
;; family reads for the terms that can form a nogood.  Its members are terms.
(def ^:private unary-multi-key [:unary-multi])

;; The same terms by predicate: `[:unary-kept pred]` holds each term of `unary-multi-key`
;; whose unary roster lists `pred`, and `unary-kept-types-key` every predicate whose set
;; is not empty.  The membership family reads the terms under a type a separation or a
;; `genl` edge moves there.  Their members are terms and predicates.
(defn- unary-kept-key [pred] [:unary-kept pred])
(def ^:private unary-kept-types-key [(root-of :unary-kept)])

;; The terms denied a predicate: `[:unary-denied pred]` holds each term a stored `(not
;; (pred term))` names, and `unary-denied-types-key` every predicate whose set is not
;; empty.  The membership family reads the terms with a denial under a type a cover or a
;; `genl` edge moves there.  Their members are terms and predicates.
(defn- unary-denied-key [pred] [:unary-denied pred])
(def ^:private unary-denied-types-key [(root-of :unary-denied)])

;; The shape roster: per functor, the lengths its positive facts are stored at, the root
;; level of the `:shape-tuple` trie, so a length leaves with its node's last fact.  Its
;; members are numbers.
(def ^:private shape-lengths-tag (root-of :shape-tuple))
(defn- shape-lengths-key [f]   [shape-lengths-tag f])

;; The arity bindings' first two levels: `arity-bound-key` holds every predicate with a
;; stored length binding, which the arity family's ancestor cut probes once per type it
;; visits, and `[:arity-binding-kinds pred]` the `[kind value]` of each of `pred`'s
;; `:arity-binding` nodes.  Their members are predicates and pairs.
(def ^:private arity-binding-kinds-tag (root-of :arity-binding))
(defn- arity-binding-kinds-key [pred] [arity-binding-kinds-tag pred])
(def ^:private arity-bound-key [(root-of arity-binding-kinds-tag)])

(defn arg-slots
  "`[[pred pos term] ...]` - the argument-root nodes a fact enters, each term canonical.
  Empty for a rule and for a non-fact, matching `root-keys`.

  The canonicalization is here rather than in the key constructors so a term reaching a
  key or a backend read is canonical whichever of the three rosters it is going into."
  [sentex]
  (let [b (sx/body sentex)]
    (if (and (sequential? b) (seq b) (symbol? (first b)))
      (let [pred (first b)]
        (into [] (keep-indexed (fn [i a]
                                 (when (sx/indexable-term? a) [pred (inc i) (sx/canon a)])))
              (rest b)))
      [])))

(defn- self-tuple?
  "Is `sentex` a ground positive binary tuple `(p a a)` with a plain symbol functor?"
  [sentex]
  (let [s (:sentence sentex)]
    (boolean (and (nil? (:antecedent sentex)) (seq? s) (= 3 (count s))
                  (let [[f a b] s]
                    (and (symbol? f) (not= 'not f) (not (sx/variable? f)) (= a b)
                         (sx/ground-term? s)))))))

(defn- arity-binding
  "`[pred kind value]` of a fact `sentex` binding a relation's length
  (`sx/arity-binding`), else nil."
  [sentex]
  (when (nil? (:antecedent sentex))
    (sx/arity-binding (:sentence sentex))))

(defn- fact-shape
  "`[f n]` for a positive fact of `n` arguments with a plain symbol functor, else nil."
  [sentex]
  (let [s (:sentence sentex)]
    (when (and (nil? (:antecedent sentex)) (seq? s) (<= 2 (count s)) (not (sx/negation? s)))
      (let [f (first s)]
        (when (and (symbol? f) (not (sx/variable? f)))
          [f (dec (count s))])))))

(defn- fact-nodes
  "`[[tag node] ...]` - the count-trie nodes a sentex enters.  A fact enters its predicate
  extent, then the argument-root node of each indexable top-level argument, a ground
  positive binary self tuple its `:self-tuple` node, a positive fact its `:shape-tuple`
  node, and a length binding its `:arity-binding` node.  A negative
  fact enters its positive body's nodes (polarity lives in the record), so
  `sentexes-with-functor` covers both polarities.  A rule enters the rule extent's
  `[:rule]` node, and its `[:solve]` node when a solve reads it (`:solve` among its
  `:engines`); its predicates live in the rule indexes.  Empty for a non-fact."
  [sentex]
  (if (some? (:antecedent sentex))
    (cond-> [[:rule-extent [:rule]]]
      (contains? (:engines sentex) :solve) (conj [:rule-extent [:solve]]))
    (let [b (sx/body sentex)]
      (if (and (sequential? b) (seq b) (symbol? (first b)))
        (let [ab (arity-binding sentex)
              sh (fact-shape sentex)]
          (cond-> (into [[:predicate-extent [(first b)]]]
                        (map (fn [node] [:argument-root node]))
                        (arg-slots sentex))
            (self-tuple? sentex) (conj [:self-tuple [(first b)]])
            sh                   (conj [:shape-tuple sh])
            ab                   (conj [:arity-binding ab])))
        []))))

(defn root-keys
  "The handle postings a sentex enters outside the trie and the term index: its context
  root always, plus the leaf under each of its `fact-nodes` in its context."
  [sentex]
  (let [c (:context sentex)]
    (into [(ctx-key c)] (map (fn [[tag node]] (node-leaf-key tag node c))) (fact-nodes sentex))))

(defn sentex-terms
  "The distinct terms that make a sentex findable: its indexable content terms (see
  sentex/index-terms — connective-free, no numbers/strings/variables) plus its
  context."
  [sentex]
  (conj (sx/index-terms sentex) (:context sentex)))

;; ---- the term roster ----------------------------------------------------
;; Membership is *derived from the postings*, never counted separately: a name enters
;; the roster when the first sentex to mention it is indexed (its `[:term-index term]` posting
;; is empty) and leaves when the last one is unindexed (its posting is exactly that
;; handle).  Both are decided from the pre-write state, so each stays one extra read per
;; name and the index write remains a single batch.  Only *symbols* are rostered: a
;; ground compound keys the term index too, but it is a sentence fragment, not a name.

(defn roster-retires
  "The write ops retiring the names in `terms` that `handle` is the last mention of —
  read BEFORE their postings are removed, so a name dies exactly when its posting is
  `#{handle}`."
  [backend terms handle]
  (into [] (comp (filter symbol?)
                 (filter (fn [t]
                           (let [k (term-key t)]
                             (and (= 1 (long (kv-count backend k)))
                                  (contains? (kv-members backend k) handle)))))
                 (map (fn [t] [:remove-from-set roster-key t])))
        terms))

;; ---- the count tries' nodes, and the slot roster --------------------------
;; A fact enters one leaf per node through `root-keys`, and the node above that leaf
;; here: the context joins the node's children and the node's count goes up.  A
;; retraction reads the leaf and the children BEFORE the batch, so it decides from the
;; pre-write state whether the leaf empties (the context leaves the children) and whether
;; the node empties (its count key goes, which a map backend would otherwise keep as 0).
;; The rule indexes take the same two halves in `family-apply!` (`post-node!` / `retire-node!`).
;;
;; The predicate-scoped argument roots answer `(P ?x B)` directly, but they cannot
;; answer the predicate-AGNOSTIC public reads (`sentexes-with-arg` / `count-with-arg`,
;; which `settle` uses for functional-predicate clash detection and the planner for
;; selectivity).  Rather than keep a second copy of every posting, the slot roster holds
;; the *predicates* present at a slot, so the coarse read is a union over a handful of
;; nodes.  A predicate enters when its node is created and leaves when its node empties.

(defn- unary-slot
  "`[pred term]` when `sentex` is a unary fact about an indexable term, else nil - the
  one entry it owes the unary roster, derived from the same positive body `arg-slots`
  reads so a negation is listed under the type it denies exactly as its argument root
  is."
  [sentex]
  (let [b (sx/body sentex)]
    (when (and (sequential? b) (= 2 (count b)) (symbol? (first b))
               (sx/indexable-term? (nth b 1)))
      [(first b) (sx/canon (nth b 1))])))

(defn- node-add
  "Write ops entering context `c` under the `tag` trie's `node`: the context joins the
  node's children and the count goes up.  They follow the leaf add in the batch, so a
  backend that answers a node's count from its leaves (`dense-roots`) replies with the
  count after the add."
  [tag node c]
  [[:add-to-set (node-ctxs-key tag node) c] [:increment (node-count-key tag node)]])

(defn- node-retire
  "`{:tag :node :dies? :ops}` - whether taking `handle` out of the `tag` trie's `node` in
  context `c` empties the node, and the write ops that keep its count and children right.
  Read BEFORE the leaf removal: the leaf empties when it is exactly `#{handle}`, and the
  node empties when that leaf is its only child."
  [backend tag node c handle]
  (let [leaf  (node-leaf-key tag node c)
        lone? (and (= 1 (long (kv-count backend leaf)))
                   (kv-member? backend leaf handle))
        dies? (and lone? (= 1 (long (kv-count backend (node-ctxs-key tag node)))))]
    {:tag   tag
     :node  node
     :dies? dies?
     :ops   (cond-> [(if dies?
                       [:delete (node-count-key tag node)]
                       [:decrement (node-count-key tag node)])]
              lone? (conj [:remove-from-set (node-ctxs-key tag node) c]))}))

(defn- node-retires
  "`node-retire` for each of `sentex`'s `fact-nodes`."
  [backend sentex handle]
  (let [c (:context sentex)]
    (mapv (fn [[tag node]] (node-retire backend tag node c handle)) (fact-nodes sentex))))

(defn- kept-adds
  "Write ops entering term `t` under `unary-kept-key` for each predicate of `preds`, and
  each predicate whose set it is the first term of in `unary-kept-types-key`, read before
  the write."
  [backend t preds]
  (into [] (mapcat (fn [pred]
                     (cond-> [[:add-to-set (unary-kept-key pred) t]]
                       (zero? (long (kv-count backend (unary-kept-key pred))))
                       (conj [:add-to-set unary-kept-types-key pred]))))
        preds))

(defn- kept-retires
  "Write ops taking term `t` out of `unary-kept-key` for each predicate of `preds`, and
  each predicate whose set it is the last term of out of `unary-kept-types-key`, read
  before the write."
  [backend t preds]
  (into [] (mapcat (fn [pred]
                     (let [k (unary-kept-key pred)]
                       (cond-> [[:remove-from-set k t]]
                         (and (== 1 (long (kv-count backend k))) (kv-member? backend k t))
                         (conj [:remove-from-set unary-kept-types-key pred])))))
        preds))

(defn slot-adds
  "Conj onto the transient `ops` the write ops entering a sentex's predicates in their
  slots, one per `[:argument-root [pred pos term]]` of `fnodes` (`fact-nodes`) whose node
  holds no context yet - read BEFORE the postings are written, so a predicate is entered
  exactly by the fact that creates its node.  Returns `ops`.

  The unary roster is the exception and takes no read at all: its entry is written by
  every unary fact rather than by the first, because the node that guards the others is
  `[pred 1 term]`, which a *binary* fact of the same predicate about the same term also
  creates - so a reference count read off it would skip the unary entry whenever the
  binary fact arrived first, and a missing entry there loses a membership.  An
  `:add-to-set` of a member already present is a no-op inside the same batch.  A term
  joins `unary-multi-key` when the entry is its second predicate, which two reads of the
  unary roster decide, and `unary-kept-key` under each predicate it then holds
  (`kept-adds`)."
  [ops backend sentex fnodes]
  (let [ops (reduce (fn [ops [tag node]]
                      (if (and (identical? :argument-root tag)
                               (zero? (long (kv-count backend (arg-ctxs-key node)))))
                        (let [[pred pos t] node] (conj! ops [:add-to-set (slot-key pos t) pred]))
                        ops))
                    ops fnodes)]
    (if-let [[pred t] (unary-slot sentex)]
      (let [k (unary-slot-key t)
            n (long (kv-count backend k))
            ops (conj! ops [:add-to-set k pred])]
        (if (and (pos? n) (not (kv-member? backend k pred)))
          (as-> ops ops
            (reduce conj! ops (kept-adds backend t (cond-> [pred] (== 1 n) (into (kv-members backend k)))))
            (cond-> ops (== 1 n) (conj! [:add-to-set unary-multi-key t])))
          ops))
      ops)))

(defn- slot-retires
  "Write ops retiring the predicates whose argument-root node `retires` (from
  `node-retires`) says empties.

  A **unary** fact retires the unary entry with its position-1 slot, and a fact of any
  other arity leaves it alone: the extra op is owed by the sentexes that wrote one and by
  no others, so a KB of binary facts pays nothing for a roster it never enters.  The
  entry therefore outlives the last unary fact wherever a *binary* one of the same
  predicate is what empties the node — the ragged-arity case the naming invariant already
  refuses — and that is the superset `unary-slot-key` describes: a stale entry costs one
  posting read and the caller's arity filter drops it.  A term leaves `unary-multi-key`
  with the entry that leaves it one predicate, read off the unary roster's size, and
  leaves `unary-kept-key` under the predicate leaving and, with it, under the one left
  (`kept-retires`)."
  [backend sentex retires]
  (let [unary (unary-slot sentex)]
    (into [] (comp (filter #(and (:dies? %) (= :argument-root (:tag %))))
                   (mapcat (fn [{[pred pos t] :node}]
                             (let [k     (unary-slot-key t)
                                   n     (when (and unary (= 1 pos)) (long (kv-count backend k)))
                                   kept? (and n (< 1 (long n)) (kv-member? backend k pred))]
                               (cond-> [[:remove-from-set (slot-key pos t) pred]]
                                 n     (conj [:remove-from-set k pred])
                                 kept? (into (kept-retires backend t (if (== 2 (long n))
                                                                       (kv-members backend k)
                                                                       [pred])))
                                 (and kept? (== 2 (long n)))
                                 (conj [:remove-from-set unary-multi-key t]))))))
          retires)))

(defn- ->count
  "A trie counter as a long.  The `Long/parseLong` arm is for a backend that replies
  in bytes; both in-memory backends store a boxed `Long` (`memory.clj`, `dense_kv.clj`),
  and routing those through `(str)` and back allocated a String per counter read on the
  default index — once per ground pattern token per frontier node, so on the path of
  every `find-sentex-handle` and every `prefix-estimate` step of the planner."
  [reply]
  (cond
    (nil? reply)    0
    (number? reply) (long reply)
    :else           (Long/parseLong (str reply))))

(defn- shape-adds
  "Conj onto the transient `ops` the write op entering `sentex`'s length in its functor's
  lengths.  No read."
  [ops sentex]
  (if-let [[f n] (fact-shape sentex)]
    (conj! ops [:add-to-set (shape-lengths-key f) n])
    ops))

(defn- binding-adds
  "Write ops entering a length binding's `[kind value]` in its predicate's kinds where
  its node holds no handle yet, and the predicate in `arity-bound-key` with its first
  kind, read before the write."
  [backend sentex]
  (when-let [[p kind v :as node] (arity-binding sentex)]
    (when (zero? (->count (kv-get backend (node-count-key :arity-binding node))))
      (let [k (arity-binding-kinds-key p)]
        (cond-> [[:add-to-set k [kind v]]]
          (zero? (long (kv-count backend k))) (conj [:add-to-set arity-bound-key p]))))))

(defn- binding-retires
  "Write ops taking a length binding's `[kind value]` out of its predicate's kinds with
  the node `retires` (from `node-retires`) says empties, and the predicate out of
  `arity-bound-key` with its last kind, read before the write."
  [backend retires]
  (when-let [{[p kind v] :node} (first (filter #(and (:dies? %) (= :arity-binding (:tag %))) retires))]
    (let [k (arity-binding-kinds-key p)]
      (cond-> [[:remove-from-set k [kind v]]]
        (== 1 (long (kv-count backend k))) (conj [:remove-from-set arity-bound-key p])))))

(defn- shape-retires
  "Write ops taking a length out of its functor's lengths with the `:shape-tuple` node
  `retires` (from `node-retires`) says empties."
  [retires]
  (when-let [{[f n] :node} (first (filter #(and (:dies? %) (= :shape-tuple (:tag %))) retires))]
    [[:remove-from-set (shape-lengths-key f) n]]))

;; ---- the bodies stored in both polarities -----------------------------------
;; A body B is **opposed** while a `(not B)` and a `B` are both stored, in any contexts,
;; and its **members** are the handles of both polarities.  Three keys hold the family:
;; the body joins `opposed-bodies-key`, each member enters B's `:opposed` node under its
;; context, and each member enters `[:opposed-in ctx]`, the members stated in `ctx` of
;; every opposed body.  The last is a context-first leaf beside the context-last trie: a
;; `genlCx` edge's placement pass reads the members stated in the contexts the edge
;; newly exposes, and keyed context last that read would visit every opposed body.
;;
;; The writes read the trie before the write (`trie`, `{:count f :leaves f}`): a body
;; joins on the first record of its second polarity, which enters the other polarity's
;; records with it, and leaves on the last record of either polarity, which takes every
;; member out.  A `[:false B]` prefix is exact, because the body is one token there; a
;; positive prefix `(sx/key-stream B)` also counts a longer sentence that extends it, so
;; the positive side is read as the leaves one level below it, and its count as the
;; node's count less the denials.

(defn- opposed-side
  "`[B denial?]` for a fact whose body `B` is a compound, else nil."
  [sentex]
  (when (nil? (:antecedent sentex))
    (let [s (:sentence sentex)]
      (when (seq? s)
        (let [neg? (sx/negation? s)
              b    (if neg? (second s) s)]
          (when (and (seq? b) (seq b)) [b neg?]))))))

(defn- member-adds
  "Write ops entering `handle`, stated in `c`, as a member of the opposed body `b`."
  [b c handle]
  (into [[:add-to-set (node-leaf-key :opposed [b] c) handle]
         [:add-to-set (opposed-in-key c) handle]]
        (node-add :opposed [b] c)))

(defn- opposed-adds
  "Write ops the fact `sentex`, stored under `handle`, owes the opposed family, read
  before the write.  A positive fact reads one trie count, the `[:false B]` count, and
  nothing more when it is 0."
  [backend trie sentex handle]
  (when-let [[b neg?] (opposed-side sentex)]
    (let [c      (:context sentex)
          denied (long ((:count trie) [:false b]))
          join   (fn [others]
                   (into [[:add-to-set opposed-bodies-key b]]
                         (mapcat (fn [[c' hs]] (mapcat #(member-adds b c' %) hs)))
                         (cons [c [handle]] others)))]
      (cond
        (pos? denied) (cond (kv-member? backend opposed-bodies-key b) (member-adds b c handle)
                            ;; a body with denials that is not opposed stores no
                            ;; positive, so this fact is its first
                            (not neg?) (join ((:leaves trie) [:false b])))
        neg?          (let [pre (vec (sx/key-stream b))]
                        (when (pos? (long ((:count trie) pre)))
                          (when-let [pos (seq ((:leaves trie) pre))]
                            (join pos))))))))

(defn- opposed-retires
  "Write ops taking the fact `sentex`, stored under `handle`, out of the opposed family,
  read before the write: its own postings, or every member's when it is the last record
  of its polarity.  One membership read for a body that is not opposed."
  [backend trie sentex handle]
  (when-let [[b neg?] (opposed-side sentex)]
    (when (kv-member? backend opposed-bodies-key b)
      (let [c      (:context sentex)
            denied (long ((:count trie) [:false b]))
            all    (->count (kv-get backend (node-count-key :opposed [b])))]
        (if (== 1 (if neg? denied (- all denied)))
          (-> [[:remove-from-set opposed-bodies-key b] [:delete (node-count-key :opposed [b])]]
              (into (mapcat (fn [c']
                              (into [[:remove-from-set (node-ctxs-key :opposed [b]) c']]
                                    (mapcat (fn [h] [[:remove-from-set (node-leaf-key :opposed [b] c') h]
                                                     [:remove-from-set (opposed-in-key c') h]]))
                                    (kv-members backend (node-leaf-key :opposed [b] c')))))
                    (kv-members backend (node-ctxs-key :opposed [b]))))
          (into [[:remove-from-set (node-leaf-key :opposed [b] c) handle]
                 [:remove-from-set (opposed-in-key c) handle]]
                (:ops (node-retire backend :opposed [b] c handle))))))))

(defn- denial-slot
  "`[pred term body]` when `sentex` is a denial `(not (pred term))` of a unary fact about
  an indexable term (`unary-slot`), `body` its `(pred term)`, else nil."
  [sentex]
  (let [s (:sentence sentex)]
    (when (and (nil? (:antecedent sentex)) (sx/negation? s))
      (when-let [[pred t] (unary-slot sentex)] [pred t (second s)]))))

(defn- denied-adds
  "Write ops entering the fact `sentex`'s term under `unary-denied-key` when it is the
  first stored denial `(not (pred term))`, read off the trie's `[:false body]` count
  before the write, and the predicate in `unary-denied-types-key` when the term is the
  first it lists."
  [backend trie sentex]
  (when-let [[pred t b] (denial-slot sentex)]
    (when (zero? (long ((:count trie) [:false b])))
      (let [k (unary-denied-key pred)]
        (cond-> [[:add-to-set k t]]
          (zero? (long (kv-count backend k))) (conj [:add-to-set unary-denied-types-key pred]))))))

(defn- denied-retires
  "Write ops taking the fact `sentex`'s term out of `unary-denied-key` when it is the last
  stored denial `(not (pred term))`, read before the write, and the predicate out of
  `unary-denied-types-key` with the last term it lists."
  [backend trie sentex]
  (when-let [[pred t b] (denial-slot sentex)]
    (when (== 1 (long ((:count trie) [:false b])))
      (let [k (unary-denied-key pred)]
        (cond-> [[:remove-from-set k t]]
          (and (== 1 (long (kv-count backend k))) (kv-member? backend k t))
          (conj [:remove-from-set unary-denied-types-key pred]))))))

(defn key-relation
  "The taxonomy relation key `k` (`[:genl a b]`, `[:genlCx a b]`, a flat-cache key)
  belongs to: `:genl`, `:genlCx`, or `:flat` for every flat-cache key."
  [k]
  (let [r (nth k 0)] (if (or (= :genl r) (= :genlCx r)) r :flat)))

(defn- named-supporter
  "`[functor target]` when `sentex` is a positive `(functor (sentexHandle target))` fact
  with `functor` `except` or `defeat`, else nil: the facts the `:tax-named` family files."
  [sentex]
  (let [s (:sentence sentex)]
    (when (and (nil? (:antecedent sentex)) (seq? s) (= 2 (count s))
               (or (= sx/except-functor (first s)) (= sx/defeat-functor (first s))))
      (when-let [h (sx/handle-id (second s))] [(first s) h]))))

(defn- named-relations
  "The relations (`key-relation`) of the taxonomy keys `h` installs, read off
  `[:tax-installs h]`."
  [backend h]
  (into #{} (map key-relation) (kv-members backend [:tax-installs h])))

(defn- named-adds
  "Write ops entering the fact `sentex`, stored under `handle`, under `[rel f]` in the
  `:tax-named` family for each relation its target supports, read before the write."
  [backend sentex handle]
  (when-let [[f h] (named-supporter sentex)]
    (let [c (:context sentex)]
      (into [] (mapcat (fn [rel] (into [[:add-to-set (node-leaf-key :tax-named [rel f] c) handle]]
                                       (node-add :tax-named [rel f] c))))
            (named-relations backend h)))))

(defn- named-retires
  "Write ops taking the fact `sentex`, stored under `handle`, out of the `:tax-named`
  family, read before the write.  A leaf not holding `handle` takes no op: the taxonomy
  retires an entry whose target stops supporting the relation (`tax/retire!`)."
  [backend sentex handle]
  (when-let [[f h] (named-supporter sentex)]
    (let [c (:context sentex)]
      (into [] (comp (filter #(kv-member? backend (node-leaf-key :tax-named [% f] c) handle))
                     (mapcat (fn [rel] (into [[:remove-from-set (node-leaf-key :tax-named [rel f] c) handle]]
                                             (:ops (node-retire backend :tax-named [rel f] c handle))))))
            (named-relations backend h)))))

(defn trie-reads
  "The two trie reads the opposed family's writes take, over `count-at` (prefix ->
  count) and `children` and `leaf` (prefix -> set): `:count`, and `:leaves`, the
  `[child handles]` of each child of a prefix whose leaf one level below holds a handle."
  [count-at children leaf]
  {:count  count-at
   :leaves (fn [prefix]
             (into [] (keep (fn [ch] (let [hs (leaf (conj prefix ch))] (when (seq hs) [ch hs]))))
                   (children prefix)))})

;; ---- the non-trie write path ---------------------------------------------
;; `KvIndexStore` and `ColumnarIndexStore` store the trie differently and store
;; everything under it identically: the inverted term index, the context root, the
;; predicate extent, the argument trie, the term roster and the argument-slot roster are
;; `key -> set` and `key -> count` families over one backend.  The two builders below
;; produce that half of a write — the ops and the per-family counts together.  Each store
;; conjes its own trie ops, then the adds' ops, and hands the counts to the profile tally
;; with its own `:levels` (and `:dead` on the retire).  One definition fixes three things across the
;; two stores: which families a sentex enters, the order its ops land in, and the numbers
;; the tally reports.  The order belongs to the definition because `assert_cost_test` pins
;; the per-family read/write counts one assert costs, on either store.  `:roots` counts
;; the root postings, the count-trie nodes' ops and the opposed family's ops together.
;; `trie` is the store's own trie reads (`trie-reads`), which only the opposed family
;; takes.

(defn flat-family-adds
  "`{:ops ops :counts {:terms n :roots n :roster n :slots n}}` — conjes onto the transient
  `ops` the non-trie write ops entering `sentex` under `handle`, and reports the number
  of ops each family took.  `:ops` is the transient `conj!` returned: the caller keeps
  using it, and seals it with `persistent!`.

  The families conj straight onto `ops`, so no vector is built per family or per sentex;
  the order is terms, roots, nodes, opposed, named, roster, slots, and `assert_cost_test`
  pins the per-family counts.  Every read runs here, before the caller batches the ops, so
  a name enters the term roster and a predicate enters its argument slot exactly on the
  first sentex to carry it."
  [ops backend trie sentex handle]
  (let [c       (:context sentex)
        fnodes  (fact-nodes sentex)                     ; derived from the sentex alone
        n0      (count ops)
        ;; terms, and the names among them no stored sentex mentions yet (reads the
        ;; pre-write postings), which enter the roster after the opposed and named ops
        [ops fresh]
        (loop [s (seq (sentex-terms sentex)) ops ops fresh nil]
          (if s
            (let [t (first s) k (term-key t)]
              (recur (next s) (conj! ops [:add-to-set k handle])
                     (if (and (symbol? t) (not (pos? (long (kv-count backend k)))))
                       (conj fresh t)
                       fresh)))
            [ops fresh]))
        n1      (count ops)
        ops     (reduce (fn [ops [tag node]] (conj! ops [:add-to-set (node-leaf-key tag node c) handle]))
                        (conj! ops [:add-to-set (ctx-key c) handle])
                        fnodes)
        ops     (reduce (fn [ops [tag node]]
                          (-> ops
                              (conj! [:add-to-set (node-ctxs-key tag node) c])
                              (conj! [:increment (node-count-key tag node)])))
                        ops fnodes)
        ops     (reduce conj! ops (opposed-adds backend trie sentex handle)) ; reads the trie
        ops     (reduce conj! ops (named-adds backend sentex handle))        ; reads the target's installs
        n2      (count ops)
        ops     (reduce (fn [ops t] (conj! ops [:add-to-set roster-key t])) ops fresh)
        n3      (count ops)
        ops     (-> ops
                    (slot-adds backend sentex fnodes)                         ; reads the pre-write postings
                    (shape-adds sentex)
                    (as-> ops (reduce conj! ops (binding-adds backend sentex)))
                    (as-> ops (reduce conj! ops (denied-adds backend trie sentex))))] ; the trie
    {:ops    ops
     :counts {:terms  (- (long n1) (long n0))
              :roots  (- (long n2) (long n1))
              :roster (- (long n3) (long n2))
              :slots  (- (long (count ops)) (long n3))}}))

(defn flat-family-retires
  "`{:ops [...] :counts {:terms n :roots n :roster n :slots n}}` — the mirror of
  `flat-family-adds`: the ops taking `handle` out of those same families, and the
  number of ops each family takes.

  Every read runs here, before the caller batches the ops, so a name leaves the term
  roster, a predicate leaves its argument slot and a node leaves the argument trie
  exactly on the last sentex to carry it."
  [backend trie sentex handle]
  (let [terms   (sentex-terms sentex)
        roots   (root-keys sentex)                      ; derived from the sentex alone
        retires (node-retires backend sentex handle)    ; reads the pre-write postings
        nodes   (into [] (mapcat :ops) retires)
        opposed (opposed-retires backend trie sentex handle) ; likewise, and the trie
        named   (named-retires backend sentex handle)   ; likewise, and the target's installs
        roster  (roster-retires backend terms handle)   ; likewise
        slots   (-> (slot-retires backend sentex retires) (into (shape-retires retires))
                    (into (binding-retires backend retires))
                    (into (denied-retires backend trie sentex)))]
    {:ops    (concat (map (fn [t] [:remove-from-set (term-key t) handle]) terms)
                     (map (fn [k] [:remove-from-set k handle]) roots)
                     nodes opposed named roster slots)
     :counts {:terms  (count terms)
              :roots  (+ (count roots) (count nodes) (count opposed) (count named))
              :roster (count roster)
              :slots  (count slots)}}))

;; ---- reading the family --------------------------------------------------

(defn- count-at* [backend prefix] (->count (kv-get backend (count-key prefix))))

(defn- kv-trie
  "`trie-reads` over the trie `backend` holds, untallied."
  [backend]
  (trie-reads #(count-at* backend %) #(kv-members backend (set-key %))
              #(kv-members backend (leaf-key %))))

(defn- seen-ctxs
  "The children of the `tag` trie's `node` a reader with ancestor set `ctxs` sees, or
  every child when `ctxs` is nil.  The intersection iterates the smaller side: the node's
  children filtered by membership in `ctxs`, or `ctxs` probed against the children with
  `kv-member?`, so it costs min(|children|, |ctxs|) probes."
  [backend tag node ctxs]
  (let [k (node-ctxs-key tag node)]
    (cond
      (nil? ctxs) (kv-members backend k)
      (<= (long (kv-count backend k)) (count ctxs))
      (filterv #(contains? ctxs %) (kv-members backend k))
      :else (filterv #(kv-member? backend k %) ctxs))))

(defn- node-handles
  "The handles under the `tag` trie's `node` in the contexts `seen-ctxs` returns.  One
  context hands its leaf back as stored."
  [backend tag node ctxs]
  (let [cs (seen-ctxs backend tag node ctxs)]
    (case (count cs)
      0 #{}
      1 (kv-members backend (node-leaf-key tag node (first cs)))
      (reduce (fn [acc c] (into acc (kv-members backend (node-leaf-key tag node c)))) #{} cs))))

(defn- nodes-intersect
  "The handles under every one of `nodes` (two or more, one predicate), per context: the
  contexts all of them state and the reader sees, then one `kv-intersect` of the leaves
  in each."
  [backend nodes ctxs]
  (let [common (reduce (fn [cs node]
                         (let [k (arg-ctxs-key node)]
                           (filterv #(kv-member? backend k %) cs)))
                       (vec (seen-ctxs backend :argument-root (first nodes) ctxs))
                       (rest nodes))
        leaves (fn [c] (kv-intersect backend (mapv #(arg-leaf-key % c) nodes)))]
    (case (count common)
      0 #{}
      1 (leaves (nth common 0))
      (reduce (fn [acc c] (into acc (leaves c))) #{} common))))

(defn- roster-union
  "The union of `preds`' nodes at `(pos, term)`, in the contexts `ctxs` (every context
  when nil).  A roster holds ONE predicate in the common case — a term occupies a given
  position under one predicate — and that node's handles are handed straight back."
  [backend preds pos term ctxs]
  (case (count preds)
    0 #{}
    1 (node-handles backend :argument-root [(first preds) pos term] ctxs)
    (reduce (fn [acc pd] (into acc (node-handles backend :argument-root [pd pos term] ctxs)))
            #{} preds)))

(def sealed-prefix
  "The count prefix of the batch-seal counter: incremented as the **last** op of every
  `index-sentex` batch and decremented as the last op of an unindex's cleanup batch,
  so it equals the indexed-sentex count exactly when every batch landed whole.  The
  durable open's coverage gate compares it against the record count: the WAL logs one
  frame per op, so a torn tail keeps a batch's *prefix* — the root counter `count-at
  []` reads is op 0 and survives every tear, which is what makes it the wrong
  instrument — while this counter is the op a tear loses first.  A namespaced keyword,
  so it collides with no term path; only the count key is written, so no trie walk
  ever meets it.  Zero on a store whose index arrived by `index-load` replay or was
  written before the counter existed — the gate falls back to the root count there."
  [::sealed])

(defn- unindex-present!
  "Take `handle`, stored at the trie leaf of `pth` (`sx/path sentex`), out of every
  index family — the caller has established it is there (`unindex-sentex!`).  Two
  batches instead of a round trip per trie level: one to drop the leaf handle and
  decrement every level's counter, whose replies decide which nodes died; one to delete
  the dead nodes' keys, detach them from their parents, and clean the term index and
  roots."
  [backend sentex pth handle]
  (let [n        (count pth)
        flat     (flat-family-retires backend (kv-trie backend) sentex handle) ; reads the pre-write postings
        prefixes (mapv #(subvec pth 0 %) (range n -1 -1))          ; leaf .. root
        replies  (kv-batch backend
                           (cons [:remove-from-set (leaf-key pth) handle]
                                 (map (fn [prefix] [:decrement (count-key prefix)]) prefixes)))
        dead     (keep (fn [[prefix c]] (when (<= (long c) 0) prefix))
                       (map vector prefixes (rest replies)))]
    (kv-batch backend
              (concat
               (mapcat (fn [prefix]
                         ;; the node is empty: drop its counter *and* both of its
                         ;; sets, or an orphaned [:trie :count prefix] leaves
                         ;; plan/prefix-estimate costing off a phantom count forever;
                         ;; then detach its edge from the parent's child set.
                         (cond-> [[:delete (count-key prefix)]
                                  [:delete (set-key prefix)]
                                  [:delete (leaf-key prefix)]]
                           (pos? (count prefix))
                           (conj [:remove-from-set (set-key (subvec pth 0 (dec (count prefix))))
                                  (nth pth (dec (count prefix)))])))
                       dead)
               (:ops flat)
               ;; the batch seal, last on purpose — `sealed-prefix` says why
               [[:decrement (count-key sealed-prefix)]]))
    ;; the mirror of the assert tally in `index-sentex`, and the reason it is a separate
    ;; one: `dead` is the only quantity here the sentex does not decide.  Every other
    ;; number is a property of what is being retracted; how many trie nodes empty
    ;; is a property of what is left behind it (`vaelii.impl.profile`).
    (when (prof/profiling?)
      (prof/record-index-retract sentex (assoc (:counts flat)
                                               :levels (inc n)
                                               :dead   (count dead))))
    handle))

(defn- node-count-in
  "How many handles the `tag` trie's `node` holds in the contexts `seen-ctxs` keeps: one
  leaf count per kept context."
  [backend tag node ctxs]
  (transduce (map #(kv-count backend (node-leaf-key tag node %))) + 0
             (seen-ctxs backend tag node ctxs)))

;; ---- the family methods ------------------------------------------------------
;; `KvIndexStore` answers every family `index-families` names through the seven `family-*`
;; methods, dispatching on the tag with a `case` the registry generates (`by-shape`).  A
;; trie and a count trie share one key shape — `[f :count node]`, `[f :children node]`,
;; `[f :handles path]` — and a flat set or a counter is `(into [f] path)`.

(defn- bad-family!
  [op msg data]
  (throw (ex-info (str (name op) ": " msg) (merge {:type :bad-args :op op} data))))

(defn family-ctxs
  "`ctxs` as a family read takes it: nil for `p/every-context`, the set otherwise.  Throws
  on nil, which a reader passes by forgetting its ancestor set.  Both implementers call it."
  [op ctxs]
  (cond
    (nil? ctxs) (bad-family! op "ctxs is a set of contexts or p/every-context, never nil" {:ctxs nil})
    (identical? ctxs p/every-context) nil
    :else ctxs))

(defmacro ^:private by-shape
  "`case` on the family tag `f`: `tries` for a trie or count trie, `flat` for a set,
  `counter` for a counter, each group of tags read off `index-families` at compile time."
  [op f tries flat counter]
  (let [tags (fn [& shapes]
               (apply list (sort (keep (fn [[t r]] (when (some #{(:shape r)} shapes) t))
                                       index-families))))]
    `(case ~f
       ~(tags :trie :count-trie) ~tries
       ~(tags :set) ~flat
       ~@(when-let [ts (seq (tags :counter))] [ts counter])
       (bad-family! ~op "no family has this tag" {:family ~f}))))

(defmacro ^:private root-tag
  "The `:root` of family tag `f` in `index-families`, or nil, as a `case`."
  [f]
  `(case ~f ~@(mapcat (fn [[t r]] (when-let [x (:root r)] [t x])) (sort-by key index-families)) nil))

(defn- flat-key [f path] (into [f] path))

(defn- flat-handles
  "The union of the flat sets `(conj node c)` of family `f` over the contexts `ctxs`."
  [backend f node ctxs]
  (case (count ctxs)
    0 #{}
    1 (kv-members backend (flat-key f (conj node (first ctxs))))
    (reduce (fn [acc c] (into acc (kv-members backend (flat-key f (conj node c))))) #{} ctxs)))

;; A batch decides each op against the store as the ops before it in the batch left it, so
;; it equals the ops applied one call at a time.  `staged` holds that view: the ops written
;; so far, and per key the members they added and removed and the counter they set, laid
;; over the backend's reads.

(defn- stage-member? [backend st k x]
  (let [{:keys [add rem]} (get-in @st [:sets k])]
    (cond (contains? add x) true
          (contains? rem x) false
          :else             (kv-member? backend k x))))

(defn- stage-count [backend st k]
  (let [{:keys [add rem]} (get-in @st [:sets k])]
    (- (+ (long (kv-count backend k)) (count (remove #(kv-member? backend k %) add)))
       (count (filter #(kv-member? backend k %) rem)))))

(defn- stage-members [backend st k]
  (let [{:keys [add rem]} (get-in @st [:sets k])]
    (reduce disj (into (set (kv-members backend k)) add) rem)))

(defn- stage-counter [backend st k]
  (let [cs (:counts @st)]
    (if (contains? cs k) (get cs k) (->count (kv-get backend k)))))

(defn- stage! [backend st [op k x :as o]]
  (let [n (case op
            :increment (inc (long (stage-counter backend st k)))
            :decrement (max 0 (dec (long (stage-counter backend st k))))
            :delete    0
            nil)]
    (vswap! st (fn [s]
                 (cond-> (update s :ops conj o)
                   n (assoc-in [:counts k] n)
                   (= :add-to-set op) (update-in [:sets k] (fn [m] {:add (conj (:add m #{}) x)
                                                                    :rem (disj (:rem m #{}) x)}))
                   (= :remove-from-set op) (update-in [:sets k] (fn [m] {:add (disj (:add m #{}) x)
                                                                         :rem (conj (:rem m #{}) x)})))))))

(defn- roster-entry
  "`[tag key member]` of the root roster above family `f`'s `path`: `[r]` holding a one-token
  path's token, else `[r first]` holding the rest (one token bare, several as a vector)."
  [f path]
  (when-let [r (root-tag f)]
    (when (seq path)
      (if (== 1 (count path))
        [r [r] (nth path 0)]
        (let [more (subvec path 1)]
          [r [r (nth path 0)] (if (== 1 (count more)) (nth more 0) more)])))))

(defn- post-root! [backend st f path]
  (when-let [[r k m] (roster-entry f path)]
    (when-not (stage-member? backend st k m)
      (let [first? (zero? (long (stage-count backend st k)))]
        (stage! backend st [:add-to-set k m])
        (when first? (post-root! backend st r (subvec k 1)))))))

(defn- retire-root! [backend st f path]
  (when-let [[r k m] (roster-entry f path)]
    (when (stage-member? backend st k m)
      (let [last? (== 1 (long (stage-count backend st k)))]
        (stage! backend st [:remove-from-set k m])
        (when last? (retire-root! backend st r (subvec k 1)))))))

(defn- post-node!
  "Stage `h` into count trie `f`'s leaf `lp`: the leaf, the node's children and count, and
  the root roster when the node was empty.  The node's count after, or nil."
  [backend st f lp h]
  (when (= :trie f) (bad-family! 'family-apply! "the trie is written by index-sentex" {:family f}))
  (let [node (pop lp) c (peek lp) leaf (node-leaf-key f node c)
        kids (node-ctxs-key f node) cnt (node-count-key f node)]
    (when-not (stage-member? backend st leaf h)
      (let [empty? (zero? (long (stage-count backend st kids)))]
        (stage! backend st [:add-to-set leaf h])
        (stage! backend st [:add-to-set kids c])
        (stage! backend st [:increment cnt])
        (when empty? (post-root! backend st f node))
        (stage-counter backend st cnt)))))

(defn- retire-node!
  "Stage `h` out of count trie `f`'s leaf `lp` — out of whichever context holds it when `lp`
  ends in `p/any-context` — and the node's children, count and root roster where they
  empty.  The node's count after, or nil."
  [backend st f lp h]
  (when (= :trie f) (bad-family! 'family-apply! "the trie is written by index-sentex" {:family f}))
  (let [node (pop lp) kids (node-ctxs-key f node)
        ;; the context may be nil (a raw taxonomy's supporter), so it is found boxed
        found (if (identical? p/any-context (peek lp))
                (some #(when (stage-member? backend st (node-leaf-key f node %) h) [%])
                      (stage-members backend st kids))
                [(peek lp)])]
    (when-let [[c] found]
      (let [leaf (node-leaf-key f node c) cnt (node-count-key f node)]
        (when (stage-member? backend st leaf h)
          (let [lone? (== 1 (long (stage-count backend st leaf)))
                dies? (and lone? (== 1 (long (stage-count backend st kids))))]
            (stage! backend st [:remove-from-set leaf h])
            (stage! backend st (if dies? [:delete cnt] [:decrement cnt]))
            (when lone? (stage! backend st [:remove-from-set kids c]))
            (when dies? (retire-root! backend st f node))
            (stage-counter backend st cnt)))))))

(defn- post-flat! [backend st f path x]
  (let [k (flat-key f path)]
    (when-not (stage-member? backend st k x)
      (let [first? (zero? (long (stage-count backend st k)))]
        (stage! backend st [:add-to-set k x])
        (when first? (post-root! backend st f path))
        (stage-count backend st k)))))

(defn- retire-flat!
  "Stage `x` out of flat set `f` at `path`.  A flat set keeps no roster of the contexts a
  path may end in, so a `path` ending in `p/any-context` throws `:bad-args`."
  [backend st f path x]
  (when (and (seq path) (identical? p/any-context (peek (vec path))))
    (bad-family! 'family-apply! "a flat set's retire names its context" {:family f}))
  (let [k (flat-key f path)]
    (when (stage-member? backend st k x)
      (let [last? (== 1 (long (stage-count backend st k)))]
        (stage! backend st [:remove-from-set k x])
        (when last? (retire-root! backend st f path))
        (stage-count backend st k)))))

(defn- apply-family-ops!
  "`family-apply!` over `backend`: one `kv-batch` of the ops staged in order, and the
  replies."
  [backend ops]
  (let [st      (volatile! {:ops []})
        replies (mapv (fn [[op f lp h]]
                        (let [lp (vec lp)]
                          (case op
                            :post   (by-shape 'family-apply! f (post-node! backend st f lp h)
                                              (post-flat! backend st f lp h)
                                              (bad-family! 'family-apply! "a counter takes no post or retire" {:family f}))
                            :retire (by-shape 'family-apply! f (retire-node! backend st f lp h)
                                              (retire-flat! backend st f lp h)
                                              (bad-family! 'family-apply! "a counter takes no post or retire" {:family f}))
                            (bad-family! 'family-apply! "an op is :post or :retire" {:family f :family-op op}))))
                      ops)]
    (when-let [written (seq (:ops @st))] (kv-batch backend written))
    replies))

(defrecord KvIndexStore [backend]
  p/IndexStore
  ;; One batch, not three round trips: the trie levels, the inverted term index, and
  ;; the secondary roots land together.  On the in-memory backends the batch applies
  ;; in one swap, so a reader never sees a sentex half-indexed.  Durability is
  ;; another matter: the disk WAL logs one frame per op, all in one write
  ;; (`disk/kv.clj`, `apply-ops!`), so a crash that tears that write persists a
  ;; *prefix* — e.g. an argument-root posting whose predicate never entered the slot
  ;; roster, which under-answers the predicate-agnostic reads while the trie and the
  ;; scoped reads see the fact.  The
  ;; record/index boundary remains; `vaelii.impl.reindex` is the repair for both.
  (index-sentex [_ sentex handle]
    (let [pth  (sx/path sentex)
          n    (count pth)
          ;; the trie ops, then the families' (`flat-family-adds` reads the pre-write
          ;; postings), then the batch seal, last on purpose — `sealed-prefix` says why
          trie (reduce (fn [ops i]
                         (let [prefix (subvec pth 0 i)]
                           (-> ops
                               (conj! [:increment (count-key prefix)])
                               (conj! (if (< i n)
                                        [:add-to-set (set-key prefix)  (nth pth i)] ; child edge
                                        [:add-to-set (leaf-key prefix) handle])))))  ; leaf handle
                       (transient []) (range (inc n)))
          flat (flat-family-adds trie backend (kv-trie backend) sentex handle)]
      (kv-batch backend
                (-> (:ops flat)
                    (conj! [:increment (count-key sealed-prefix)])
                    persistent!))
      ;; what this assert cost the index, per family, when somebody is asking
      ;; (`vaelii.impl.profile`).  The trie depth is this store's own number; the four
      ;; family counts come back with the ops that produced them, so the tally cannot
      ;; disagree with `ColumnarIndexStore`'s.
      (when (prof/profiling?)
        (prof/record-index-write sentex (assoc (:counts flat) :levels (inc n))))
      handle))

  ;; **Gated on the handle being at the leaf.**  The counters are decremented without
  ;; looking, and a node whose count reaches zero is deleted with every handle at its
  ;; leaf — so one stray unindex (a handle never indexed here, or indexed and already
  ;; removed) would take live nodes, and the sentexes stored under them, out of the
  ;; trie.  One membership probe on the leaf — a hash lookup on every backend, no
  ;; protocol read tallied — makes a stray unindex a no-op instead.
  ;;
  ;; **And says so**, because the no-op is safe and not therefore right.  The caller is
  ;; `integrate/sentex-removed!`, which deletes the record on the next line whether or
  ;; not anything came out of the index: a genuine record/index divergence therefore
  ;; leaves the trie handing out a handle whose record is gone, which shows up as a
  ;; corrupted store several operations later and nowhere near here.  Silence made that
  ;; indistinguishable from a caller retracting a handle twice.  `reindex` is the repair,
  ;; and the log is what tells somebody to run it.
  (unindex-sentex! [_ sentex handle]
    (let [pth (sx/path sentex)]
      (if (kv-member? backend (leaf-key pth) handle)
        (unindex-present! backend sentex pth handle)
        (trove/log! {:level :warn :id ::unindex-absent
                     :data {:handle handle :path pth :context (:context sentex)}})))
    handle)

  ;; Every read below tallies the **family** that answered it (`vaelii.impl.profile`),
  ;; one entry per protocol call: a deref and a `nil?` check when nobody is asking, and
  ;; the one measurement that says whether a family a KB pays to maintain is ever read.
  ;; What a call *cost* is a separate question — the trie's is the fan tally in `lookup`.
  ;;
  ;; The trie is two families to a reader even though it is one structure on disk, and
  ;; the split is the whole reason the tally is worth reading: these three are the
  ;; **cost model's** probes (`plan`'s selectivity and fan-out divisor), and `lookup`
  ;; below is **retrieval**.  A run that reads the counts a hundred times per walk is
  ;; using the trie to plan, not to fetch, and a family roster that added them together
  ;; would report that as one number meaning neither.
  (count-at [_ prefix] (prof/record-read :trie-counts) (count-at* backend prefix))

  (children [_ prefix] (prof/record-read :trie-counts) (vec (kv-members backend (set-key prefix))))

  ;; The terminus reads the *leaf* key, so an under-long pattern — which stops on an
  ;; interior node — yields nothing instead of that node's child tokens, and a full
  ;; path that also happens to be interior (ragged arity) yields its own handles
  ;; without the child token sitting at the same prefix.
  ;;
  ;; **Structural walk.**  A positive-fact key linearizes nested compounds into arity
  ;; markers (see `vaelii.impl.sentex`), so a query token is one of three:
  ;;   * a variable — matches exactly one complete stored form.  If the child is an
  ;;     atom it advances one level; if the child is a marker it **skips** the whole
  ;;     subterm the marker's arity spans (`skip-one` / `skip-n`, recursing for nested
  ;;     arity).  This is what lets `(p ?y b)` bind a whole compound of unknown depth.
  ;;   * a marker `[::subterm k]` — matched exactly, like any token; the query's own
  ;;     next k linearized forms then match the subterm's elements.
  ;;   * anything else (an atom, or a whole list token in a `:false`/`:rule` key) —
  ;;     matched exactly by `count-at`.
  ;; Only child *sets* are read while walking; handles are read solely at the terminus,
  ;; so the skip can never cross into a leaf handle or read a marker as one.  This is a
  ;; superset filter — `res/unify` is the source of truth — and a markerless (flat)
  ;; key, holding no marker for the skip to read, walks one level per token.
  ;;
  ;; With a `ctxs` set the last token, the context level, keeps only the children in
  ;; `ctxs` (`seen-ctxs`, the argument roots' by-context read), so the walk reads no leaf
  ;; stated where the reader cannot see.  A context is an atom, so no marker is in `ctxs`.
  (lookup [this pattern] (p/lookup this pattern nil))
  (lookup [_ pattern ctxs]
    (prof/record-read :trie-lookup)
    ;; Eager vectors throughout: a lazy `mapcat` per level is a seq and a lock per child
    ;; token, on the walk every join's partially bound literal takes.
    (letfn [(child-tokens [prefix] (kv-members backend (set-key prefix)))
            (skip-one [prefix]                         ; advance past one complete form
              (reduce (fn [acc c]
                        (if (sx/subterm-mark? c)
                          (into acc (skip-n (conj prefix c) (sx/subterm-arity c)))
                          (conj acc (conj prefix c))))
                      []
                      (child-tokens prefix)))
            (skip-n [prefix n]                         ; advance past n complete forms
              (if (zero? n)
                [prefix]
                (reduce (fn [acc p] (into acc (skip-n p (dec n)))) [] (skip-one prefix))))]
      ;; `visits` and `widest` describe the walk itself: one probe per frontier node per
      ;; level, and how wide the frontier ever got.  A narrowing walk holds the frontier
      ;; at one node and visits one per level; a walk that got stuck behind a variable
      ;; visits that level's whole child set, which is the fan the secondary roots exist
      ;; to avoid.  Two long ops per level whether or not anybody is counting; the tally
      ;; itself is a deref when the instrument is off.
      (loop [frontier [[]]                             ; node prefixes reached so far
             qs pattern
             visits 0
             widest 1]
        (if (empty? qs)
          ;; one node reached — the walk that narrowed all the way — answers its leaf set
          ;; as stored rather than copied into a new one
          (let [hs (if (== 1 (count frontier))
                     (set (kv-members backend (leaf-key (nth frontier 0))))
                     (into #{} (mapcat (fn [prefix] (kv-members backend (leaf-key prefix)))) frontier))]
            (prof/record-fan pattern (+ visits (count frontier)) widest (count hs))
            hs)
          (let [q (first qs)
                ctx-level? (and ctxs (nil? (next qs)))
                frontier'
                (into []
                      (mapcat
                       (fn [prefix]
                         (cond
                           (and ctx-level? (sx/variable? q))
                           (mapv #(conj prefix %) (seen-ctxs backend :trie prefix ctxs))
                           (sx/variable? q) (skip-one prefix)
                           (and ctx-level? (not (contains? ctxs q))) nil
                           (pos? (count-at* backend (conj prefix q))) [(conj prefix q)])))
                      frontier)]
            (recur frontier' (rest qs)
                   (+ visits (count frontier))
                   (max widest (count frontier'))))))))

  ;; The exact leaf — one hash read of the node the path names, no walk and no fan.
  ;; Tallied as retrieval like `lookup` beside it, because that is what it is; it records
  ;; no fan, having none to record.
  (leaf-at [_ path] (prof/record-read :trie-lookup) (kv-members backend (leaf-key (vec path))))

  ;; The predicate extent: every context's leaf, or the one leaf a predicate stated in one
  ;; context has, handed back as stored.  The count is the node's own.
  (sentexes-with-functor [_ pred]
    (prof/record-read :predicate-extent)
    (node-handles backend :predicate-extent [pred] nil))
  (count-with-functor    [_ pred]
    (prof/record-read :predicate-extent)
    (->count (kv-get backend (node-count-key :predicate-extent [pred]))))

  ;; Multi-column narrowing. With the argument roots scoped by predicate, a named
  ;; functor needs NO predicate-extent intersection: `(rel ?x B C)` reads the nodes
  ;; `[rel 2 B]` and `[rel 3 C]`, a single bound argument is one node, and no bound
  ;; argument is the predicate extent's node `[rel]`.  With `ctxs`, each node's contexts
  ;; are intersected with the reader's ancestor set before a leaf is read, so no handle
  ;; stored where the reader cannot see is returned.  A `nil` pred
  ;; (a variable functor) has no scope to read, so it unions the slot roster's nodes per
  ;; column and intersects the columns.  The result stays a superset of the
  ;; positional-trie hits — it does not constrain numeric arguments — which the caller's
  ;; `unify` filters exact.
  (sentexes-with-args [this pred pos-terms] (p/sentexes-with-args this pred pos-terms nil))
  (sentexes-with-args [_ pred pos-terms ctxs]
    (cond
      (nil? pred)
      (if (empty? pos-terms)
        #{}
        (reduce (fn [acc [pos term]]
                  (prof/record-read :argument-slot)
                  (prof/record-read :argument-root)
                  (let [term (sx/canon term)
                        s    (roster-union backend (kv-members backend (slot-key pos term))
                                           pos term ctxs)]
                    (if (nil? acc) s (set/intersection acc s))))
                nil pos-terms))
      (empty? pos-terms) (do (prof/record-read :predicate-extent)
                             (node-handles backend :predicate-extent [pred] ctxs))
      :else
      (do (prof/record-read :argument-root)
          (let [nodes (mapv (fn [[pos term]] [pred pos (sx/canon term)]) pos-terms)]
            (if (nil? (next nodes))
              (node-handles backend :argument-root (nth nodes 0) ctxs)
              (nodes-intersect backend nodes ctxs))))))

  (sentexes-with-terms [_ terms]
    (prof/record-read :term-index)
    (if (empty? terms) #{} (kv-intersect backend (mapv term-key terms))))

  ;; The family methods (`family-ctxs`, `by-shape` above): untallied, since the `reads`
  ;; entry point that calls one tallies the logical read it serves.
  (family-count [_ f path ctxs]
    (let [cs (family-ctxs 'family-count ctxs) path (vec path)]
      (by-shape 'family-count f
                (if cs (node-count-in backend f path cs) (->count (kv-get backend (node-count-key f path))))
                (if cs
                  (transduce (map #(kv-count backend (flat-key f (conj path %)))) + 0 cs)
                  (kv-count backend (flat-key f path)))
                (->count (kv-get backend (flat-key f path))))))
  (family-children [_ f path ctxs]
    (let [cs (family-ctxs 'family-children ctxs) path (vec path)]
      (by-shape 'family-children f
                (if cs (seen-ctxs backend f path cs) (set (kv-members backend (node-ctxs-key f path))))
                (let [k (flat-key f path)]
                  (if cs (filterv #(kv-member? backend k %) cs) (set (kv-members backend k))))
                (bad-family! 'family-children "a counter has no children" {:family f}))))
  (family-child-count [_ f path]
    (by-shape 'family-child-count f
              (kv-count backend (node-ctxs-key f (vec path)))
              (kv-count backend (flat-key f path))
              (bad-family! 'family-child-count "a counter has no children" {:family f})))
  (family-leaf [_ f path]
    (by-shape 'family-leaf f
              (or (kv-members backend [f :handles (vec path)]) #{})
              (or (kv-members backend (flat-key f path)) #{})
              (bad-family! 'family-leaf "a counter has no leaf" {:family f})))
  (family-member? [_ f path x]
    (by-shape 'family-member? f
              (kv-member? backend [f :handles (vec path)] x)
              (kv-member? backend (flat-key f path) x)
              (bad-family! 'family-member? "a counter has no leaf" {:family f})))
  (family-handles [_ f node ctxs]
    (let [cs (family-ctxs 'family-handles ctxs) node (vec node)]
      (by-shape 'family-handles f
                (node-handles backend f node cs)
                (if cs
                  (flat-handles backend f node cs)
                  (bad-family! 'family-handles "a flat set lists no contexts to range" {:family f}))
                (bad-family! 'family-handles "a counter has no leaf" {:family f}))))
  (family-apply! [_ ops] (apply-family-ops! backend ops))

  ;; the flat-map index *is* the portable projection, so both directions are the
  ;; backend's own enumeration and install — no key is reshaped on the way through.
  ;; minus the batch-seal counter: it describes the WAL's own health, not the
  ;; records, so it is no part of the portable projection — a dump carries it to no
  ;; store that can read it as anything, and the cross-backend parity of this seq is
  ;; what `index-dump-test` pins
  (index-entries [_]         (remove (fn [[k _]] (= k (count-key sealed-prefix)))
                                     (kv-entries backend)))
  (index-load    [_ entries] (kv-load    backend entries))

  (clear-index! [_] (kv-clear! backend) nil))

;; ---- the registry, read by the importer ----------------------------------------

(defn justification-family-entry?
  "Is `entry`, a `[key value]` index entry, one of a family the stored justifications
  derive rather than the stored sentexes (`:source :justification` in `index-families`)?"
  [entry]
  (let [k (when (sequential? entry) (first entry))]
    (and (vector? k) (= :justification (:source (index-families (first k)))))))
