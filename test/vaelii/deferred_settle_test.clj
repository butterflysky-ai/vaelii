;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.deferred-settle-test
  "`with-deferred-settle` / `assert-many` / `bulk-assert-facts!`: assert a batch with
  belief settled once at the end instead of per assert.

  Same belief, fewer settles.  The `exceptWhen` sweep runs in settle, so a conclusion
  the exception blocks stays believed until the closing settle: the mid-batch reading
  shows the settle was deferred."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- except-rule [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq)))))

;; ---- same belief as per-assert -------------------------------------------
;; The excepted binding (Opus) has its conclusion placed while `(bird Opus)` is
;; asserted — before `(penguin Opus)` arrives — so under deferral it is swept only
;; at the closing settle.  The answers must match the per-assert version in
;; `except_test`: Tweety flies, Opus does not, nothing was arbitrated.

(tu/deftest-kb deferred-settle-reaches-the-same-belief-as-per-assert
  (tu/with-terms [bird penguin flies Tweety Opus CxBird]
    (v/with-deferred-settle kb
      (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
                CxBird)
      (v/assert kb (list bird Tweety) CxBird)
      (v/assert kb (list bird Opus) CxBird)
      (v/assert kb (list penguin Opus) CxBird))
    (testing "the unexcepted binding concludes"
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxBird))))
    (testing "the excepted binding was swept by the closing settle"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))
    (testing "blocking is not rebutting, and nothing was arbitrated"
      (is (empty? (v/sentexes-matching kb (list 'not (list flies Opus)) CxBird)))
      (is (empty? (v/conflicts kb))))))

;; ---- the settle is genuinely deferred ------------------------------------
;; If the sweep ran per assert, `(flies Opus)` would vanish the instant
;; `(penguin Opus)` is stored.  Under deferral it must still be believed *inside*
;; the batch and gone only after it closes — the observable difference.

(tu/deftest-kb deferral-postpones-the-exception-sweep-to-the-batch-end
  (tu/with-terms [bird penguin flies Opus CxBird]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (is (seq (v/sentexes-matching kb (list flies Opus) CxBird))
        "flies Opus is placed while only bird is known")
    (v/with-deferred-settle kb
      (v/assert kb (list penguin Opus) CxBird)
      (testing "mid-batch: settle deferred, so the queued sweep has not run"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxBird)))))
    (testing "the closing settle ran the sweep"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))))

;; ---- the cached relations are unsettled inside the batch too ------------

(tu/deftest-kb a-taxonomy-read-inside-the-batch-is-the-unsettled-one
  ;; `tax/add-edge` activates an edge on the assert path, before any settle labels it, so
  ;; a mid-batch unscoped `genl?` / `isa?` reads a superset of the believed edges
  ;; (docs/taxonomy.md), and the negation pair is placed by the closing settle
  (tu/with-terms [dog_t mammal_t Muffet CxD]
    (v/assert kb (list dog_t Muffet) CxD {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t mammal_t) CxD)
      (v/assert kb (list 'not (list 'genl dog_t mammal_t)) CxD {:strength :monotonic})
      (testing "mid-batch the edge is active — this batch's unscoped belief is not computed yet"
        (is (v/genl? kb dog_t mammal_t))
        (is (v/isa? kb Muffet mammal_t)))
      (testing "and no reader decides the pair before the settle places it"
        (is (v/genl? kb dog_t mammal_t CxD))))
    (testing "and the closing settle defeats the default supporter and drops the edge"
      (is (not (v/genl? kb dog_t mammal_t CxD)))
      (is (not (v/isa? kb Muffet mammal_t CxD)))
      (is (empty? (v/sentexes-matching kb (list 'genl dog_t mammal_t) CxD))
          "the edge's supporter is stored but not believed, so it does not match either"))))

;; ---- assert-many: derive + return handles --------------------------------

(tu/deftest-kb assert-many-chains-per-fact-and-settles-once
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxFam]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxFam {:direction :forward})
    (let [hs (v/assert-many kb [(list parentOf Tom Bob) (list parentOf Bob Ann)]
                            CxFam)]
      (testing "one handle back per input sentence, in order"
        (is (= 2 (count hs)))
        (is (every? nat-int? hs)))
      (testing "chaining ran per fact, so the grandparent is derived after the settle"
        (is (seq (v/sentexes-matching kb (list grandparentOf Tom Ann) CxFam))))
      (testing "the returned handles are the asserted facts"
        (is (= (set hs)
               (set [(v/handle-of kb (list parentOf Tom Bob) CxFam)
                     (v/handle-of kb (list parentOf Bob Ann) CxFam)])))))))

;; ---- bulk-assert-facts!: the fast path lands what the slow one lands ------
;; one corpus through both entry points into two unrelated contexts, compared on the four
;; things the docstring names: stored sentexes, index, beliefs, `count-with-functor`

(tu/deftest-kb bulk-assert-facts-lands-what-per-fact-assert-lands
  (tu/with-terms [edgeOf CxBulk CxSlow]
    (let [inds  (mapv #(tu/tmp-ind (str "Node" %)) (range 24))
          facts (mapv (fn [a b] (list edgeOf a b)) inds (rest (cycle inds)))
          n     (count facts)
          idx   (:index kb)]
      (let [hs (v/bulk-assert-facts! kb facts CxBulk)]
        (is (= n (count hs)) "one handle back per input fact, in order"))
      (doseq [f facts] (v/assert kb f CxSlow {:chain? false}))

      (testing "same stored sentexes — one per fact on each side"
        (is (= n (reads/stored-count-in-context idx CxBulk) (reads/stored-count-in-context idx CxSlow))))
      (testing "same count-with-functor — the predicate extent took both halves"
        (is (= (* 2 n) (v/count-with-functor kb edgeOf)))
        (is (= (* 2 n) (p/count-at idx [edgeOf]))))
      (testing "same beliefs — every fact matches and is IN on both sides"
        (doseq [f facts]
          (is (seq (v/sentexes-matching kb f CxBulk)))
          (is (seq (v/sentexes-matching kb f CxSlow)))
          (is (v/in? kb (v/handle-of kb f CxBulk)))
          (is (v/in? kb (v/handle-of kb f CxSlow)))))
      (testing "same index — each argument root holds both halves' handles"
        (doseq [t inds, pos [1 2]]
          (is (= (count (filter #(= CxBulk (:context (v/sentex kb %)))
                                (reads/as-stored-with-arg-global idx pos t)))
                 (count (filter #(= CxSlow (:context (v/sentex kb %)))
                                (reads/as-stored-with-arg-global idx pos t)))))))
      (testing "provenance is the one documented difference: the bulk premise carries none"
        (is (nil? (v/provenance kb (v/handle-of kb (first facts) CxBulk))))
        (is (some? (v/provenance kb (v/handle-of kb (first facts) CxSlow))))))))

(tu/deftest-kb bulk-assert-facts-reports-its-rate-to-on-progress
  ;; The load rate is what makes the next regression noticeable, so the entry point reports
  ;; it rather than leaving every caller to time the call.  The closing event fires
  ;; *after* the deferred settle, so it covers the whole load.
  (tu/with-terms [edgeOf CxRate]
    (let [inds   (mapv #(tu/tmp-ind (str "Rate" %)) (range 12))
          facts  (mapv (fn [a b] (list edgeOf a b)) inds (rest (cycle inds)))
          events (atom [])]
      (v/bulk-assert-facts! kb facts CxRate {:on-progress #(swap! events conj %)})
      (is (= 1 (count @events)) "one event: the corpus is under the 100,000-fact window")
      (let [{:keys [phase total elapsed-ms facts-per-sec]} (first @events)]
        (is (= :done phase))
        (is (= (count facts) total))
        (is (number? elapsed-ms))
        (is (pos? facts-per-sec) "a rate, not a duration — comparable across corpus sizes")))))

;; ---- nesting composes: only the outermost settles ------------------------

(tu/deftest-kb nested-deferred-settle-composes
  (tu/with-terms [bird penguin flies Opus CxBird]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              CxBird)
    (v/assert kb (list bird Opus) CxBird)
    (v/with-deferred-settle kb
      (v/with-deferred-settle kb
        (v/assert kb (list penguin Opus) CxBird))
      (testing "an inner block does not settle; the outer one still owns it"
        (is (seq (v/sentexes-matching kb (list flies Opus) CxBird)))))
    (testing "the outermost settle swept it"
      (is (empty? (v/sentexes-matching kb (list flies Opus) CxBird))))))
