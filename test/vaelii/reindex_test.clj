;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reindex-test
  "The index is derived state: `reindex` must rebuild all of it — trie, roots, term
  index, rule index — from the records alone, such that every read answers as it
  did before the index was destroyed."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (com.sun.management ThreadMXBean)
           (java.lang.management ManagementFactory)))

(deftest reindex-rebuilds-a-destroyed-index
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [dog animal barksAt growls Muffet Rex]
      (v/assert kb (list 'genl dog animal) 'CxUniverse)
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (v/assert kb (list barksAt Muffet Rex) 'CxUniverse)
      (v/assert-rule kb [(list dog '?x)] (list growls '?x) 'CxUniverse {:direction :forward})
      (let [snap (fn []
                   {:dog-extent    (count (v/sentexes-matching kb (list dog '?x) 'CxUniverse))
                    :functor-count (v/count-with-functor kb barksAt)
                    :arg-count     (v/count-with-arg kb 1 Muffet)
                    :term-find     (count (v/find-sentexes kb Muffet))
                    :isa?          (v/isa? kb Muffet animal)
                    :derived?      (boolean (seq (v/sentexes-matching kb (list growls Muffet) 'CxUniverse)))
                    :backward?     (v/provable? kb (list growls Muffet) 'CxUniverse)})
            before (snap)]
        (testing "the content is really there before the damage"
          (is (:derived? before) "the rule fired forward")
          (is (:isa? before)))
        (p/clear-index! (:index kb))
        (testing "the damage is real: an empty index answers nothing"
          (is (zero? (v/count-with-functor kb barksAt))))
        (let [{:keys [sentexes rules]} (reindex/reindex kb)]
          (is (pos? sentexes))
          (is (= 1 rules) "the one rule was re-registered in the rule index"))
        (v/recover kb)
        (testing "every read answers as before the index was destroyed"
          (is (= before (snap))))))))

(deftest reindex-rebuilds-a-variable-consequent-rule
  ;; A rule concluding `(?p ?x ?y)` (reasoning/27's consequent half) files its consequent
  ;; under the `p/var-consequent-key` catch-all rather than a canonical `?var0`.  `reindex`
  ;; must rebuild that posting from the record so a backward goal still reaches the rule.
  ;; A `set/backwardRule` isolates the backward path: it never fires forward, so the
  ;; conclusion is reachable only by expanding the rule from `concluding-rule-handles`.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [holds loves Tom Ann]
      (v/assert kb (list 'set/backwardRule
                         (list 'implies (list holds '?p '?x '?y) (list '?p '?x '?y)))
                'CxUniverse)
      (v/assert kb (list holds loves Tom Ann) 'CxUniverse)
      (let [var0?  (fn [t] (re-find #"var0" (str t)))
            snap   (fn [] {:backward? (v/provable? kb (list loves Tom Ann) 'CxUniverse)
                           :roster-clean? (not-any? var0? (reads/stored-terms-global (:index kb)))})
            before (snap)]
        (testing "the backward goal reaches the var-consequent rule, and ?var0 never rostered"
          (is (:backward? before))
          (is (:roster-clean? before)))
        (p/clear-index! (:index kb))
        (let [{:keys [rules]} (reindex/reindex kb)]
          (is (= 1 rules) "the var-consequent rule was re-registered"))
        (v/recover kb)
        (testing "and both survive a rebuild from the records alone"
          (is (= before (snap))))))))

;; ---- the allocation of an index write ----------------------------------------

(def ^:private ^ThreadMXBean thread-mx (ManagementFactory/getThreadMXBean))

(defn- bytes-per-sentex
  "Bytes this thread allocates per sentex over `index-one!` of every `[sentex handle]` in
  `sxs` into a cleared `store`, after four unmeasured passes.  The store is cleared again
  before the result returns, so the test leaves its space as it found it."
  [store sxs]
  (let [pass (fn []
               (p/clear-index! store)
               (let [a (.getCurrentThreadAllocatedBytes thread-mx)]
                 (doseq [[s h] sxs] (reindex/index-one! store s h))
                 (- (.getCurrentThreadAllocatedBytes thread-mx) a)))]
    (try
      (dotimes [_ 4] (pass))
      (quot (long (pass)) (count sxs))
      (finally (p/clear-index! store)))))

(deftest a-reindexed-sentex-allocates-no-op-vector-per-family
  ;; `flat-family-adds` conjes each family's ops onto the store's one transient batch, so
  ;; a write allocates no vector per family.  Bytes per sentex over this corpus are
  ;; 27.5 KB on `KvIndexStore` over the memory backend and 18.6 KB on the columnar store
  ;; on JDK 25 (compact object headers, project.clj), and 29.3 KB and 20.6 KB on JDK 17.
  ;; The budgets are 34000 and 24000; a per-family vector costs 37.0 KB and 27.5 KB on
  ;; JDK 25, over both.
  (let [n   600
        ind #(symbol (str "Ind" %))
        sxs (into []
                  (map-indexed (fn [i s] [s (inc i)]))
                  (for [i (range n)
                        s (cond-> [(sx/sentex (list 'dog (ind i)) 'CxUniverse)
                                   (sx/sentex (list 'parentOf (ind i) (ind (mod (* 7 i) n))) 'CxUniverse)
                                   (sx/sentex (list 'likes (ind i) (list 'friendOf (ind (inc i)))) 'CxUniverse)]
                            (zero? (mod i 5)) (conj (sx/sentex (list 'not (list 'dog (ind i))) 'CxUniverse)))]
                    s))]
    (is (< (long (bytes-per-sentex (mem/memory-index-store {:space 83}) sxs)) 34000)
        "KvIndexStore, bytes per sentex")
    (is (< (long (bytes-per-sentex (columnar/columnar-index-store {:space 83}) sxs)) 24000)
        "ColumnarIndexStore, bytes per sentex")))
