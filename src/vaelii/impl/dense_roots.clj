;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-roots
  "A key-interning `KvBackend` (`vaelii.impl.kv`) for the columnar index's non-trie
  families — the context root, the count tries ending in the context, the opposed members
  by context, the exception index, and the inverted term index.

  Those families are flat `structured-vector-key → handle-set` maps, and the columnar
  measurement (`bench/…/densetrie.clj`) found their **boxed vector keys**
  (`[:term-index term]`, `[:context-root ctx]`, …) to be ~150 MB — the majority of the
  columnar index once the trie went native.  This backend keeps the *values* as
  `IntPostings` (Phase 1's tiered
  `int[]`/Roaring set) but collapses the keys: the term is interned to an `int` through
  the **shared trie dictionary** (`vaelii.impl.tokens`) — so a predicate/individual gets
  the same id the trie edges use — and the whole key becomes one packed `long`
  (`family | pos | term-id`) into a single primitive `Long2ObjectOpenHashMap`.  No boxed
  vectors, no HAMT nodes, one map.

  It stays a full `KvBackend` so the existing composition (an embedded `KvIndexStore`
  over it) is unchanged: only the recognized index families are int-routed; any other key
  — a counter keyed by the vocabulary, a scalar, the contract test's synthetic keys —
  falls back to a plain in-memory backend (in the columnar store the trie is native, so no
  `[:trie …]` key ever reaches here).

  **Every handle family routes**, the count tries' leaves included: an argument leaf's
  `(pred, pos, ctx)` scope, and any other count trie leaf's context scope `(ctx, 0, ctx)`,
  is interned to a dense id of its own (`argfam-id`) and rides the `pos` field, which
  the flat families do not use.  The tries' child sets and every name set (the term,
  slot and membership rosters, the keys a handle installs) route as packed keys too, their
  members held as ids in the shared dictionary.  So the fallback holds only the
  vocabulary's counters, and the fact-scaled mass is one packed map — or, under a
  snapshot, one mapped run.  Single-writer, like every index;
  `kv-members` / `kv-intersect` materialize a fresh Clojure set at the boundary — but
  `kv-intersect` builds it at the size of the *answer*, narrowing through
  `postings/intersect-postings` in whichever representation each posting is in, a mapped run
  included.  Proven set-equal to `MemoryKvBackend` on the index families by
  `dense_roots_oracle_test` —
  which, like every behavioural check, cannot see a family that falls back when it should
  route, since the fallback answers identically; `dense_routing_test` reads the
  representation and covers that.

  **Single-*threaded*, which is narrower than single-writer.**  The mapped-section fields
  on `DenseRoots` are `^:unsynchronized-mutable`, so installing or thawing a snapshot
  publishes through no barrier and a second thread may read this backend mid-install —
  `mapped?` true against a `mkeys` it has not seen, say.  The atom- and lock-based
  backends give an incidental reader beside the writer a consistent view; this one does
  not.  Same trade as `vaelii.impl.columnar`, whose docstring states it: these fields are
  read on the hot lookup path, and a volatile read there buys a guarantee the engine's own
  single writer never needs."
  (:require [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.dense-roots :as dense-roots-types])
  (:import [it.unimi.dsi.fastutil.longs Long2ObjectOpenHashMap]
           [vaelii.impl.types.dense_roots DenseRoots]))

;; ---- the argument roots, and what this backend's packing costs them ----------
;;
;; The argument family is the index layer's (`vaelii.impl.kv`): it spells the keys and it
;; does the reading.  What reaches here is the ordinary generic ops over those keys.
;; `route` packs a leaf `[:argument-root :handles [pred pos term ctx]]` with its
;; `(pred, pos, ctx)` scope interned to a dense id that rides the `pos` field, and a
;; node's children `[:argument-root :children [pred pos term]]` with its `(pred, pos)`
;; scope, its members held as context ids.  A node's count is computed from its leaves.
;; So the predicate-SCOPED reads, which is what `sentexes-with-args` makes for a named
;; functor and so the overwhelmingly common query shape, are packed-long lookups: one for
;; the node's contexts and one per leaf read, and `kv-intersect` narrows in the postings'
;; own representation, a mapped run included.
;;
;; The predicate-AGNOSTIC reads cost one lookup more.  The index layer takes them over the
;; slot roster — `[:argument-slot pos term]` → the predicates present there, a name set
;; packed under the position and the term — and unions the scoped postings.
;; That roster is *one predicate* in the common case (a term occupies a given position
;; under one predicate), so the union is a single set handed straight back and the cost
;; over a maintained node union is the roster read itself.  A handful of predicates is a
;; handful of packed lookups.
;;
;; Maintaining an agnostic union here instead would mean a second posting per
;; `(pos, term)` holding what the scoped postings already hold — the family's whole
;; fact-scaled mass, stored twice — to save one lookup on a read that is usually a union
;; of one.  The roster is already maintained, one predicate id per argument node.

(defn dense-roots
  "A key-interning `KvBackend` sharing `dict` (the columnar trie's token dictionary) so a
  term interned by the trie and by a root get the same id."
  [dict]
  (dense-roots-types/->DenseRoots dict (tok/token-dict) (Long2ObjectOpenHashMap.)
                                  (mem/->MemoryKvBackend (atom {}))
                                  nil nil nil 0))

(defn fallback-entries
  "The entries the routed families do **not** claim: the counters keyed by a predicate,
  functor, rule key or kind, and the one `:mint-in` node's children.  All are
  **vocabulary-scaled**, which is what lets a snapshot write them as one nippy blob and
  load them resident without the blob tracking the fact count (`disk/index_snapshot.clj`,
  \"The residency split\")."
  [^DenseRoots b] (p/kv-entries (.-fallback b)))

(defn load-fallback! [^DenseRoots b entries] (p/kv-load (.-fallback b) entries) nil)

;; ---- the scope dictionary, as a snapshot section ------------------------
;; The packed argument keys cite scope ids, so an image that carries the keys has to
;; carry the table that decodes them.  It rides `roots.csr` — the file whose key column
;; is its only reader — rather than a log beside `tokens.log`, and the reason is the
;; failure each shape can have.  `tokens.log` is durable ground truth: appended as facts
;; arrive, cited by the mapped trie edges, and able to disagree with an image written at
;; some other time — which is what `:duplicate-tokens` exists to repair.  This table is
;; written in the same pass as the column that cites it and discarded with it, so the two
;; cannot drift apart at all.  A second log would buy nothing and inherit that repair.

(defn argfam-table
  "The scope dictionary as `{:preds int[] :positions int[] :contexts int[]}`, indexed by
  scope id, with each predicate and context taken through `remap` into the durable
  dictionary's id space — the same `int[]` the packed keys' term halves are remapped by.
  A node's scope `[pred pos]` has no context and writes -1 there; a context scope
  `[ctx 0 ctx]` writes its context as the predicate and 0 as the position.

  A scope's names are interned into the term dictionary when the scope is
  (`argfam-id`), so every id here has a term id to be written as."
  [^DenseRoots b ^ints remap]
  (let [af   (.-argfam b)
        dict (.-dict b)
        n    (long (tok/token-count af))
        ps   (int-array n)
        qs   (int-array n)
        cs   (int-array n)
        durable #(int (aget remap (int (tok/token-id dict %))))]
    (dotimes [i n]
      (let [[pred pos ctx :as scope] (tok/id-token af i)]
        (aset ps i (int (durable pred)))
        (aset qs i (int pos))
        (aset cs i (int (if (= 3 (count scope)) (durable ctx) -1)))))
    {:preds ps :positions qs :contexts cs}))

(defn load-argfam!
  "Rebuild the scope dictionary from a snapshot's table, ids implied by position — the
  same first-writer-wins order `vaelii.impl.tokens` allocates in, so an id read out of a
  packed key names the scope it named when the image was written."
  [^DenseRoots b ^ints preds ^ints positions ^ints contexts n]
  (let [af   (.-argfam b)
        dict (.-dict b)]
    (tok/clear-tokens! af)
    (dotimes [i (long n)]
      (let [pair [(tok/id-token dict (aget preds i)) (aget positions i)]]
        (tok/intern-token! af (if (neg? (aget contexts i))
                                pair
                                (conj pair (tok/id-token dict (aget contexts i)))))))
    (let [loaded (long (tok/token-count af))]
      (when (not= loaded (long n))
        (throw (ex-info (str "the argument-root scope dictionary reloaded as " loaded
                             " entries where the image holds " n
                             " — the ids the packed keys cite have shifted")
                        {:type :torn-snapshot :loaded loaded :entries n})))))
  nil)

