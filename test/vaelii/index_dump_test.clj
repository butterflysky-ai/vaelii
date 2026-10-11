;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.index-dump-test
  "The index in a dump: written by `:variant :records+index`, and read back only when it
  can be proved to describe the records beside it.

  Two claims, and they pull in opposite directions.

  **The projection is the protocol's.**  Four index backends hold the index four
  different ways — a map of boxed prefix vectors, int postings, a native int-token trie
  in parallel arrays, a WAL over a RAM map — and they must all export the *same entries*,
  because that shape is what they have in common rather than what any of them holds.  An
  index written by one must load into another.

  **And the entries are never trusted.**  An index that does not match its records is
  worse than no index: every lookup answers confidently and short, and nothing in the
  engine is positioned to notice — a stale trie node simply reports fewer handles.  So
  the second half of this namespace breaks each precondition in turn and asserts the
  rebuild fires, with the right reason.  Discarding the cache is always safe, which is
  the property that makes the whole thing an optimization rather than a risk."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.import :as imp]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── scaffolding ───────────────────────────────────────────────────────

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-idx-" nm "-") (into-array FileAttribute []))))

(defn- rm-rf! [^File d] (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- fresh-dump-dir ^File [nm]
  (doto (temp-dir nm) (rm-rf!)))                 ; export! makes its own directory

;; Own db numbers, outside the suite's block, one pair per backend — this namespace is
;; *about* the four backends, so it names them all rather than running on whichever one
;; the suite's gate selected.
(def ^:private index-backends
  [{:backend :memory          :space 88}
   {:backend :memory-dense    :space 88}
   {:backend :memory-columnar :space 88}
   {:backend :disk-log}])

(defn- open-kb!
  "An empty KB on `opts`, plus the thunk that closes and deletes whatever it needed."
  [opts nm]
  (if (= :disk-log (:backend opts))
    (let [d  (temp-dir nm)
          kb (v/open-kb {:backend :disk-log :dir (.getPath d) :recover? false})]
      [(doto kb (tu/clear-kb!)) #(do (backend/close-dir! (.getPath d)) (rm-rf! d))])
    ;; The three `:memory*` backends share one record store on space 88, and the registry
    ;; behind it is process-global — so the fixture is cleared on the way OUT as well as
    ;; on the way in, or the last one to run stays resident for the JVM's life.
    (let [kb (doto (v/open-kb (assoc opts :recover? false)) (tu/clear-kb!))]
      [kb #(tu/clear-kb! kb)])))

(defn- with-kb* [opts nm f]
  (let [[kb close!] (open-kb! opts nm)]
    (try (f kb) (finally (close!)))))

;;; ── the KB under test ─────────────────────────────────────────────────

(defn- terms []
  (tu/with-terms [bird penguin animal flies feathered parentOf grandparentOf
                  Tweety Opus Ann Bob Cid CxIndex]
    {:bird bird :penguin penguin :animal animal :flies flies :feathered feathered
     :parentOf parentOf :grandparentOf grandparentOf
     :Tweety Tweety :Opus Opus :Ann Ann :Bob Bob :Cid Cid :ctx CxIndex}))

(defn- build!
  "Every index family in one KB: the trie (ragged paths, a numeric token, a negative
  fact), all three roots, the rule index, the exception index, the term index, the
  roster, and the mint family, which an argument declaration's mints write with the
  entailment pinned on.  An index dump that dropped a family would otherwise pass on the
  families it did keep."
  [kb {:keys [bird penguin animal flies feathered parentOf grandparentOf
              Tweety Opus Ann Bob Cid ctx]}]
  (v/assert kb (list 'genl penguin bird) ctx {:strength :monotonic})
  (v/assert kb (list 'genl bird animal) ctx {:strength :monotonic})
  (v/assert kb (list 'genl animal 'thing) ctx {:strength :monotonic})
  (v/assert kb (list 'arg parentOf 1 animal) ctx {:strength :monotonic})
  ;; a rule with an exception — the rule index and the exception index, and a
  ;; meta-sentex whose sentence embeds a handle
  (v/assert kb (list 'exceptWhen (list penguin '?b)
                     (list 'set/defaultRule
                           (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
            ctx)
  (v/assert kb (vr/rule-sentence [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                 (list grandparentOf '?x '?z))
            ctx {:direction :forward})
  (v/assert kb (list bird Tweety) ctx {:strength :monotonic})
  (v/assert kb (list feathered Tweety) ctx)
  (v/assert kb (list bird Opus) ctx)
  (v/assert kb (list penguin Opus) ctx)
  ;; each mints `(animal x)`, a record a justification files in the mint family
  (tu/with-entailing
    (v/assert kb (list parentOf Ann Bob) ctx)
    (v/assert kb (list parentOf Bob Cid) ctx))
  ;; a numeric argument (a trie token that is not a handle) and a ragged path
  (v/assert kb (list 'bornInYear Tweety 1970) ctx)
  ;; a negative fact — roots under its positive body's functor
  (v/assert kb (list 'not (list feathered Opus)) ctx))

;;; ── the projection is the protocol's ──────────────────────────────────

(defn- entries-of [kb] (into #{} (p/index-entries (:index kb))))

(deftest every-index-backend-exports-the-same-entries
  ;; The claim the format rests on: `[key value]` is what four different resident
  ;; layouts have in common.  A dense backend that quietly diverged — a family it stopped
  ;; posting, a key it spells differently — fails here and nowhere else, because every
  ;; other test asks a backend only what it can answer for itself.
  (let [t (terms)
        by-backend
        (into {}
              (for [opts index-backends]
                [(:backend opts)
                 (with-kb* opts "project" (fn [kb] (build! kb t) (entries-of kb)))]))
        reference (get by-backend :memory)]
    (is (pos? (count reference)) "the fixture indexed nothing — the comparison is vacuous")
    (doseq [[b entries] (dissoc by-backend :memory)]
      (testing (str b)
        (is (= reference entries)
            (str b " projects a different index than :memory — "
                 (pr-str {:missing (take 3 (set/difference reference entries))
                          :extra   (take 3 (set/difference entries reference))})))))))

(deftest the-entries-are-the-index-not-a-derivation-of-it
  ;; `index-entries` streams what the store holds.  If it re-derived instead, an index
  ;; that had drifted from its records would export as though it had not — and the
  ;; fingerprint would then certify a lie.
  (tu/with-cleared-kb [kb tu/fresh]
    (let [t (terms)]
      (build! kb t)
      (let [before (entries-of kb)]
        (p/clear-index! (:index kb))
        (is (empty? (entries-of kb)) "a cleared index projects nothing")
        (v/reindex kb)
        (is (= before (entries-of kb)) "and a rebuilt one projects what the live one did")))))

;;; ── what the dump says ────────────────────────────────────────────────

(defn- index-meta [^File dir]
  (read-string (slurp (io/file dir "index" "index.edn"))))

(deftest a-records-plus-index-dump-says-what-it-is-keyed-in-and-what-it-describes
  (tu/with-cleared-kb [kb tu/fresh]
    (let [dir (fresh-dump-dir "meta")]
      (try
        (build! kb (terms))
        (let [summary (export/export! kb dir {:variant :records+index :compression :none})
              m       (imp/read-meta dir)
              im      (index-meta dir)]
          (testing "meta.edn names the variant, and counts the entries"
            (is (= :records+index (:variant m)))
            (is (= (:index-entries summary) (:index-entry-count m)))
            (is (pos? (:index-entries summary))))
          (testing "index.edn carries the layout version and the records fingerprint"
            (is (= kv/index-layout-version (:index-layout im)))
            (is (= (:index-entries summary) (:entry-count im)))
            (is (= (count (tu/sentex-ids kb)) (:count (:records im))))
            (is (= (apply max (tu/sentex-ids kb)) (:max-handle (:records im))))
            (is (integer? (:digest (:records im))))))
        (finally (rm-rf! dir))))))

(deftest a-records-dump-writes-no-index-and-is-otherwise-the-same
  (tu/with-cleared-kb [kb tu/fresh]
    (let [a (fresh-dump-dir "plain") b (fresh-dump-dir "withidx")]
      (try
        (build! kb (terms))
        (let [sa (export/export! kb a {:compression :none})
              sb (export/export! kb b {:variant :records+index :compression :none})]
          (is (zero? (:index-entries sa)))
          (is (not (.exists (io/file a "index"))))
          (is (pos? (:index-entries sb)))
          (is (= (dissoc sa :bytes :elapsed-ms :dir :variant :index-entries)
                 (dissoc sb :bytes :elapsed-ms :dir :variant :index-entries))
              "the records side of the two dumps is the same dump"))
        (finally (rm-rf! a) (rm-rf! b))))))

(deftest the-digest-is-stable-across-exports-and-moves-with-the-records
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [rel Aye Bee CxIndex]
      (let [a (fresh-dump-dir "d1") b (fresh-dump-dir "d2") c (fresh-dump-dir "d3")]
        (try
          (build! kb (terms))
          (export/export! kb a {:variant :records+index :compression :none})
          (export/export! kb b {:variant :records+index :compression :none})
          (is (= (:records (index-meta a)) (:records (index-meta b)))
              "two exports of one KB fingerprint alike, or nothing downstream can compare")
          (v/assert kb (list rel Aye Bee) CxIndex)
          (export/export! kb c {:variant :records+index :compression :none})
          (is (not= (:records (index-meta a)) (:records (index-meta c)))
              "and one more record is a different KB")
          (finally (rm-rf! a) (rm-rf! b) (rm-rf! c)))))))

;;; ── replay and rebuild agree ──────────────────────────────────────────

(defn- index-reads
  "Every read the `IndexStore` protocol has, over everything this KB mentions — the
  comparison `columnar_index_oracle_test` makes between two live stores, made here
  between a replayed index and a rebuilt one."
  [kb sentexes]
  (let [index (:index kb)
        paths (mapv sx/path sentexes)
        pfxs  (into #{} (mapcat (fn [pth] (map #(subvec pth 0 %) (range (inc (count pth)))))) paths)
        terms (into #{} (mapcat #(conj (sx/index-terms %) (:context %))) sentexes)
        ctxs  (into #{} (map :context) sentexes)
        preds (into #{} (keep (fn [s] (let [b (sx/body s)]
                                        (when (and (sequential? b) (symbol? (first b)))
                                          (first b)))))
                    sentexes)
        args  (into #{} (for [s sentexes
                              :let [b (sx/body s)]
                              :when (and (sequential? b) (symbol? (first b)))
                              [i a] (map-indexed vector (rest b))]
                          [(inc i) a]))]
    {:lookup   (into {} (for [pth paths
                              pat (cons pth (for [i (range (count pth))] (assoc pth i '?v)))]
                          [pat (p/lookup index pat)]))
     :counts   (into {} (for [pfx pfxs] [pfx (p/count-at index pfx)]))
     :children (into {} (for [pfx pfxs] [pfx (set (p/children index pfx))]))
     :ctx      (into {} (for [c ctxs] [c [(reads/as-stored-in-context index c)
                                          (reads/stored-count-in-context index c)]]))
     :functor  (into {} (for [pr preds] [pr [(p/sentexes-with-functor index pr)
                                             (p/count-with-functor index pr)]]))
     :arg      (into {} (for [[pos t] args] [[pos t] [(reads/as-stored-with-arg-global index pos t)
                                                      (reads/stored-count-with-arg-global index pos t)]]))
     :rules    (into {} (for [pr preds] [pr [(reads/as-stored-rules-by-antecedent-global index pr)
                                             (reads/as-stored-rules-by-consequent-global index pr)]]))
     :except   [(reads/watched-rules index)
                (into {} (for [pr preds] [pr (reads/watched-rules-on index pr)]))
                (into {} (for [h (tu/sentex-ids kb)] [h (reads/watched-rule? index h)]))]
     :terms    [(reads/stored-terms-global index) (reads/stored-term-count-global index)
                (into {} (for [t terms] [t (reads/as-stored-with-term index t)]))]
     :entries  (entries-of kb)}))

(defn- answers
  "What the KB says, as opposed to what its index holds — the check that survives a
  mistake in the oracle above."
  [kb {:keys [bird flies grandparentOf Tweety Opus Ann Cid ctx]}]
  {:flies-tweety (count (v/sentexes-matching kb (list flies Tweety) ctx))
   :flies-opus   (count (v/sentexes-matching kb (list flies Opus) ctx))
   :grandparent  (count (v/sentexes-matching kb (list grandparentOf Ann Cid) ctx))
   :birds        (count (v/sentexes-matching kb (list bird '?x) ctx))
   :ask-flies    (boolean (seq (v/ask kb (list flies Tweety) ctx)))
   :isa          (v/isa? kb Opus bird)
   :terms        (count (v/terms kb))
   :mints        (let [idx (:index kb)]
                   (into #{} (for [x (reads/as-stored-mint-terms idx)
                                   h (reads/as-stored-mints-about-global idx x)]
                               [(:sentence (v/sentex kb h)) (:context (v/sentex kb h))])))})

(defn- import-into
  "Import `dir` into a fresh KB on `opts` and hand `(f kb summary)` the result."
  [opts nm dir f]
  (with-kb* opts nm (fn [kb] (f kb (imp/import-dump kb dir)))))

(deftest a-replayed-index-and-a-rebuilt-one-are-the-same-index
  ;; The required test.  Import the same dump twice — once with its index, once with
  ;; the index taken away so the importer has to rebuild — and compare every read the
  ;; protocol has, plus the queries the KB answers.
  (let [t       (terms)
        src-dir (fresh-dump-dir "both")
        source  (tu/with-cleared-kb [src tu/fresh]
                  (build! src t)
                  (export/export! src src-dir {:variant :records+index :compression :none})
                  (answers src t))]
    (try
      (is (seq (:mints source)) "the source files mints, so the comparison is not vacuous")
      (doseq [opts index-backends]
        (testing (str (:backend opts))
          (let [replayed (import-into opts "replay" src-dir
                                      (fn [kb s]
                                        (is (= :replayed (:index s)) "the dump's index was used")
                                        [(index-reads kb (map #(v/sentex kb %) (tu/sentex-ids kb)))
                                         (answers kb t)]))
                ;; the same dump with its index hidden: the importer must rebuild, and
                ;; land in exactly the same place
                bare-dir (fresh-dump-dir "bare")]
            (try
              (rm-rf! bare-dir)
              (.mkdirs bare-dir)
              (doseq [^File f (.listFiles src-dir) :when (.isFile f)]
                (io/copy f (io/file bare-dir (.getName f))))
              (import-into opts "rebuild" bare-dir
                           (fn [kb s]
                             (is (= :rebuilt (:index s)))
                             (is (= :absent (:reason s)))
                             (is (= (first replayed)
                                    (index-reads kb (map #(v/sentex kb %) (tu/sentex-ids kb))))
                                 "a replayed index answers differently than a rebuilt one")
                             (is (= (second replayed) (answers kb t))
                                 "and the KB itself answers differently")
                             (is (= (:mints source) (:mints (answers kb t)))
                                 "an import files the mints the exporting KB filed")))
              (finally (rm-rf! bare-dir))))))
      (finally (rm-rf! src-dir)))))

;;; ── each precondition, broken ─────────────────────────────────────────

(defn- exported
  "A `:records+index` dump of the standard fixture, for `(f dir terms)` to tamper with.
  The terms are handed on because they are gensyms: a test that re-invented them would
  be querying a vocabulary the dump has never heard of, and would pass on nothing."
  [nm f]
  (let [dir (fresh-dump-dir nm)
        t   (terms)]
    (try
      (tu/with-cleared-kb [src tu/fresh] (build! src t)
        (export/export! src dir {:variant :records+index :compression :none}))
      (f dir t)
      (finally (rm-rf! dir)))))

(defn- rebuild-reason
  "Import `dir` into a fresh memory KB and report what became of its index."
  [dir]
  (with-kb* (first index-backends) "reason" (fn [kb] (select-keys (imp/import-dump kb dir)
                                                                  [:index :reason :entries]))))

(deftest a-layout-this-build-does-not-read-rebuilds
  ;; The sharpest of the three: an index in another layout reads as *empty* rather than
  ;; as wrong, so nothing downstream would ever notice it had been replayed.
  (exported "layout"
            (fn [dir _t]
              (let [f (io/file dir "index" "index.edn")
                    m (read-string (slurp f))]
                (spit f (pr-str (assoc m :index-layout (inc kv/index-layout-version))))
                (is (= {:index :rebuilt :reason :layout-changed} (rebuild-reason dir)))))))

(deftest records-the-entries-were-not-derived-from-rebuild
  (exported "records"
            (fn [dir _t]
              (let [f (io/file dir "index" "index.edn")
                    m (read-string (slurp f))]
                (spit f (pr-str (update-in m [:records :digest] inc)))
                (is (= {:index :rebuilt :reason :records-differ} (rebuild-reason dir)))))))

(deftest a-truncated-entry-stream-rebuilds-and-installs-nothing-of-itself
  (exported "truncated"
            (fn [dir t]
              (let [f   (io/file dir "index" "entries.nippy.stream")
                    ^bytes all (with-open [in (io/input-stream f)] (.readAllBytes in))]
                (with-open [out (io/output-stream f)]
                  (.write out all 0 (quot (alength all) 2)))
                (is (= {:index :rebuilt :reason :entries-truncated} (rebuild-reason dir)))
                (testing "and the KB is whole anyway — discarding the cache is always safe"
                  (with-kb* (first index-backends) "trunc-kb"
                    (fn [kb]
                      (imp/import-dump kb dir)
                      (is (pos? (count (v/sentexes-matching kb (list (:bird t) '?x) (:ctx t))))
                          "a rebuild after a broken replay left the KB unqueryable"))))))))

(deftest a-plain-records-dump-reports-absent-and-is-otherwise-identical
  (let [dir (fresh-dump-dir "plain-absent")]
    (try
      (tu/with-cleared-kb [src tu/fresh] (build! src (terms))
        (export/export! src dir {:compression :none}))
      (is (= {:index :rebuilt :reason :absent} (rebuild-reason dir)))
      (finally (rm-rf! dir)))))

(deftest a-remapped-import-refuses-the-index-because-its-postings-name-ghosts
  ;; An index entry is a posting of *handles*, so an import that could not put every
  ;; record where the dump said must not replay one: the postings would name records that
  ;; are not there.  Provoked here by taking one frame's `:id` away — the frame is then a
  ;; record with no handle to preserve, which is exactly the form a dialect that does
  ;; not number its records has, and one minted handle is enough to void the whole index.
  (exported "remapped"
            (fn [dir _t]
              (let [f       (io/file dir "sentexes.nippy.stream")
                    frames  (vec (frames/read-chunked-seq f :none))
                    stripped (cons (dissoc (first frames) :id) (rest frames))]
                (frames/write-frames! f stripped {:compression :none :chunk-size 10000})
                (let [r (rebuild-reason dir)]
                  (is (= :rebuilt (:index r)))
                  (is (= :handles-remapped (:reason r))))
                (with-kb* (first index-backends) "remap"
                  (fn [kb]
                    (is (= :remapped (:handle-policy (imp/import-dump kb dir)))
                        "and the import says so, which is what the index decision reads")))))))

(deftest a-truncated-stream-refuses-rather-than-importing-a-prefix
  ;; a torn chunk is indistinguishable from a clean EOF — the decompressor cannot tell a truncated
  ;; file from a finished one — so the frames read are counted against what meta.edn
  ;; states.  The failure this closes: a smaller KB reported as a successful import.
  (exported "truncated"
            (fn [dir _t]
              (let [f      (io/file dir "sentexes.nippy.stream")
                    frames (vec (frames/read-chunked-seq f :none))]
                (frames/write-frames! f (butlast frames)
                                      {:compression :none :chunk-size 10000})
                (with-kb* (first index-backends) "trunc"
                  (fn [kb]
                    (let [e (is (thrown? clojure.lang.ExceptionInfo
                                         (imp/import-dump kb dir)))]
                      (is (= :truncated-dump (:type (ex-data e))))
                      (is (= (dec (count frames)) (:read (ex-data e))))
                      (is (= (count frames) (:stated (ex-data e)))))))))))

;;; ── the records-only path ─────────────────────────────────────────────

(deftest the-records-only-path-replays-too-and-skips-its-inline-build
  ;; That path indexes inline while storing, which is its whole optimization.  A dump
  ;; carrying a replayable index has a cheaper one still, so it skips the inline build
  ;; and installs instead — and must land in the same index either way.
  (let [dir (fresh-dump-dir "records-only")]
    (try
      (tu/with-cleared-kb [src tu/fresh]
        (build! src (terms))
        (export/export! src dir {:variant :records+index :compression :none}))
      (let [replayed (with-kb* (first index-backends) "ro-replay"
                       (fn [kb]
                         (let [s (imp/import-dump kb dir {:belief? false})]
                           (is (= :replayed (:index s)))
                           [(entries-of kb) (:sentexes s) (:rules s)])))
            inline   (let [bare (fresh-dump-dir "ro-bare")]
                       (try
                         (.mkdirs bare)
                         (doseq [^File f (.listFiles dir) :when (.isFile f)]
                           (io/copy f (io/file bare (.getName f))))
                         (with-kb* (first index-backends) "ro-inline"
                           (fn [kb]
                             (let [s (imp/import-dump kb bare {:belief? false})]
                               (is (= :inline (:index s)) "no index to replay, so it built inline")
                               [(entries-of kb) (:sentexes s) (:rules s)])))
                         (finally (rm-rf! bare))))]
        (is (= replayed inline)
            "the replayed index differs from the one the inline build produced"))
      (finally (rm-rf! dir)))))
