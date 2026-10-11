;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.residency
  "What a **mapped index snapshot** takes off the heap, and what it does not.

  Residency is the lever here: keep the working set in RAM and page the cold tail.  `vaelii.impl.disk.index-snapshot` implements it for the columnar
  index — the CSR skeleton, the roots' key column and the token dictionary are read into
  heap, the leaf handles and the roots' handle run are `mmap`ed.  This measures the split
  rather than asserting it, and it is the gate the design is judged by: *loading more
  facts over the same vocabulary must not grow resident heap in proportion*.

  The corpus is deliberately **vocabulary-fixed**: the same individuals, types and
  predicates at every N, so the only thing that grows is the number of facts over them.
  That is the form the question is about — a KB whose vocabulary has settled and whose
  extent has not.  Two sizes, and the answer is the *growth* between them rather than
  either figure, so the number means the same on any machine.

  RAM is jol retained heap of the index store — structural, so contention-immune.  A
  mapped section reads as ~0 here **because it is not on the heap at all**: a
  `MappedByteBuffer` is an address and a length, and its pages live in the OS page cache.
  That is the measurement, not a gap in it; the bytes are reported separately from the
  files they came from.

  Run: `lein bench-residency [facts] [multiple] [individuals]`
       (default 25000 facts, ×4, over 400 individuals)."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.core :as v]
            [vaelii.host.io.generate :as gen]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.index-snapshot :as snap]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]))

(defn- tmpdir ^String []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-residency-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- mb ^double [^long b] (/ b 1048576.0))

(defn- file-bytes ^long [dir n]
  (let [f (java.io.File. (str (snap/snapshot-root dir) "/" n))]
    (if (.exists f) (.length f) 0)))

(defn- index-heap
  "The index store's retained heap, split into the shared dictionary and the two
  structures over it.  The dictionary is measured once and subtracted from each, since
  jol counts shared structure under whichever root reaches it."
  [kb]
  (let [idx  (:index kb)
        dict (postings/retained [(:dict idx)])]
    {:whole (postings/retained [idx])
     :dict  dict
     :trie  (- (postings/retained [(:trie idx)]) dict)
     :roots (- (postings/retained [(:roots idx)]) dict)}))

(defn- load! [dir facts individuals]
  (let [kb (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})]
    (v/clear! kb)
    (gen/load-into kb {:facts facts :rules 0 :individuals individuals
                       :types 40 :predicates 30 :chain? false})
    kb))

(defmacro ^:private timed [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (/ (- (System/nanoTime) t0#) 1e6)]))

(defn- run-one
  "Load `facts` over a fixed vocabulary, measure the rebuilt (fully resident) index, then
  close, reopen mapped, and measure again — and time both opens, since the image is
  supposed to buy the rebuild back as well as the heap.  The rebuilt open is produced by
  deleting the commit marker, which is exactly the fallback every mismatch takes."
  [facts individuals]
  (let [dir (tmpdir)]
    (try
      (let [kb    (load! dir facts individuals)
            n     (count (p/sentex-ids (:records kb)))
            terms (reads/stored-term-count-global (:index kb))
            ;; the rebuilt index — every posting on the heap, which is what
            ;; `:disk-columnar` has held since it shipped
            rebuilt (index-heap kb)]
        (disk/close-dir! dir)                                  ; writes the image
        (let [[kb2 map-ms] (timed (v/open-kb {:records :disk :index :snapshot
                                              :dir dir :recover? :auto}))
              mapped (index-heap kb2)
              files  {:trie     (file-bytes dir "trie.csr")
                      :roots    (file-bytes dir "roots.csr")
                      :tokens   (file-bytes dir "tokens.log")
                      :fallback (file-bytes dir "roots-fallback.nippy")}]
          ;; touch every mapped posting once, so the reading is of a *warm* mapped index
          ;; rather than of one nothing has read yet
          (dorun (v/sentexes-matching kb2 '(?p ?x ?y) 'CxGenerated))
          (disk/close-dir! dir)
          (snap/discard! dir)                                  ; the fallback, on purpose
          (let [[_ rebuild-ms] (timed (v/open-kb {:records :disk :index :snapshot
                                                  :dir dir :recover? :auto}))]
            {:facts n :terms terms :rebuilt rebuilt :mapped mapped :files files
             :map-ms map-ms :rebuild-ms rebuild-ms})))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

(defn- report [label {:keys [facts terms rebuilt mapped files map-ms rebuild-ms]}]
  (println (format "\n── %s: %,d records over %,d distinct terms ──" label facts terms))
  (println "  index store, retained heap        rebuilt      mapped")
  (doseq [[k n] [["dictionary" :dict] ["trie (skeleton + leaves)" :trie] ["roots + term index" :roots]]]
    (println (format "    %-30s %7.1f MB  %7.1f MB" k (mb (rebuilt n)) (mb (mapped n)))))
  (println (format "    %-30s %7.1f MB  %7.1f MB   %.2f×"
                   "WHOLE INDEX" (mb (:whole rebuilt)) (mb (:whole mapped))
                   (/ (double (:whole rebuilt)) (max 1.0 (double (:whole mapped))))))
  (println (format "  on disk: trie %.1f MB · roots %.1f MB · dictionary %.1f MB · roster %.1f MB"
                   (mb (:trie files)) (mb (:roots files)) (mb (:tokens files)) (mb (:fallback files))))
  (println (format "  open (index + recover): mapped %,.0f ms · rebuilt %,.0f ms   %.2f×"
                   map-ms rebuild-ms (/ rebuild-ms (max 1.0 map-ms)))))

(defn- growth [label small big f]
  (let [a (double (f small)) b (double (f big))
        fa (double (:facts small)) fb (double (:facts big))]
    (println (format "  %-34s %6.2f×   (facts %.2f×)" label (/ b (max 1.0 a)) (/ fb fa)))))

(defn- run [facts multiple individuals]
  (let [small (run-one facts individuals)
        big   (run-one (* facts multiple) individuals)]
    (report "small" small)
    (report "big"   big)
    (println "\n══ the gate: growth over a FIXED vocabulary ══")
    (println (format "  %,d → %,d records, %,d → %,d distinct terms\n"
                     (:facts small) (:facts big) (:terms small) (:terms big)))
    (growth "rebuilt index, resident"  small big #(-> % :rebuilt :whole))
    (growth "mapped index, resident"   small big #(-> % :mapped  :whole))
    (growth "  of which the dictionary" small big #(-> % :mapped :dict))
    (growth "  of which the trie"       small big #(-> % :mapped :trie))
    (growth "  of which the roots"      small big #(-> % :mapped :roots))
    (growth "mapped sections, on disk"  small big #(+ (-> % :files :trie) (-> % :files :roots)))
    (println (str "\n  Read the mapped rows against the fact multiple beside them.  A row that\n"
                  "  tracks the vocabulary is flat; one that tracks the extent is not, and the\n"
                  "  design is only worth what the difference between them is."))))

(defn -main [& args]
  (let [facts       (Long/parseLong (or (first args) "25000"))
        multiple    (Long/parseLong (or (second args) "4"))
        individuals (Long/parseLong (or (nth args 2 nil) "400"))]
    (run facts multiple individuals)
    (shutdown-agents)
    (System/exit 0)))
