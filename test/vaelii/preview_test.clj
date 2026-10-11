;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.preview-test
  "`preview`: what a batch would do to the KB, without leaving it done.  A test that
  stores or derives compares `content` before and after (docs/preview.md, \"Tests\")."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as viol]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- content
  "The KB's live records, as the pair a preview must not move."
  [kb]
  [(tu/sentex-ids kb) (tu/justification-ids kb)])

(defn- sentences [entries] (mapv :sentence entries))

(defn- placed?
  "Is `s` a sentence a placed nogood stores?  Its `sentexHandle` arguments name the
  handles the batch allocated, which the rollback frees."
  [s]
  (contains? '#{contradicts defeat} (first s)))

(defn- except-rule [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq)))))

;; ---- 1. the property everything rests on ---------------------------------

(tu/deftest-kb a-preview-leaves-the-kb-byte-identical
  (tu/with-terms [dog friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (let [before (content kb)
          _      (v/preview kb {:add [[(list dog Rex) CxStory]]})]
      (testing "same live sentexes and justifications, at the same handles"
        (is (= before (content kb))))
      (testing "and nothing the batch would have stored is findable"
        (is (nil? (v/handle-of kb (list dog Rex) CxStory)))
        (is (nil? (v/handle-of kb (list friendly Rex) CxStory)))))))

;; ---- 2. what a batch would derive ----------------------------------------

(tu/deftest-kb a-batch-that-derives-reports-what-it-derives
  (tu/with-terms [dog friendly Rex CxStory]
    (let [rh     (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x))
                           CxStory {:direction :forward})
          before (content kb)
          r      (v/preview kb {:add [[(list dog Rex) CxStory]]})]
      (testing "the premise and its consequence both come back"
        (is (= [(list dog Rex) (list friendly Rex)] (sentences (:believed-added r)))))
      (testing "nothing is reported removed, refused, or dropped"
        (is (empty? (:believed-removed r)))
        (is (empty? (:refused r)))
        (is (empty? (:violations r)))
        (is (false? (:bounded? r))))
      (testing "the derived line carries the justification that made it"
        (let [j (:justification (second (:believed-added r)))]
          (is (= rh (:informant j)))
          (is (= (v/readable-sentence (v/sentex kb rh)) (:rule j)))
          (is (= [(list dog Rex)] (:antecedents j)))))
      (testing "the asserted line is a premise and needs no justification"
        (is (true? (:premise? (first (:believed-added r)))))
        (is (nil? (:justification (first (:believed-added r))))))
      (is (= before (content kb))))))

(tu/deftest-kb the-antecedents-name-the-edges-the-placement-saw-across
  (tu/with-terms [puppy dog mortal Muffet CxLow CxMid]
    (let [mid  (v/assert kb (list 'genlCx CxMid 'CxUniverse) 'CxUniverse)
          low  (list 'genlCx CxLow CxMid)
          genl (list 'genl puppy dog)
          rule (vr/rule-sentence [(list dog '?x)] (list mortal '?x))
          rh   (do (v/assert kb low 'CxUniverse)
                   (v/assert kb genl 'CxUniverse)
                   (v/assert kb rule CxLow {:direction :forward}))
          r    (v/preview kb {:add [[(list puppy Muffet) CxMid]]})]
      (testing "every edge the firing rests on, in the stored content order"
        (is (= [{:informant rh :strength :monotonic :rule (v/readable-sentence (v/sentex kb rh))
                 :antecedents [genl low (list 'genlCx CxMid 'CxUniverse) (list puppy Muffet)]}]
               (keep :justification (:believed-added r)))))
      (let [ph     (v/assert kb (list puppy Muffet) CxMid)
            ch     (v/handle-of kb (list mortal Muffet) CxLow)
            before (content kb)
            gone   (first (filter #(= ch (:handle %)) (:believed-removed (v/preview kb {:remove [mid]}))))]
        (testing "removing one edge withdraws the conclusion and names the edge missing"
          (is (= :unsupported (:reason gone)))
          (is (= [[mid]] (mapv :missing (:support (:detail gone))))))
        (is (= before (content kb)))
        (v/retract! kb ph)))))

(tu/deftest-kb two-derivations-name-the-content-least-in-either-batch-order
  (tu/with-terms [aa bb cc Rex CxStory]
    (let [ra (v/assert kb (vr/rule-sentence [(list aa '?x)] (list cc '?x)) CxStory {:direction :forward})
          _  (v/assert kb (vr/rule-sentence [(list bb '?x)] (list cc '?x)) CxStory {:direction :forward})
          j  (fn [order]
               (->> (v/preview kb {:add (mapv #(vector (list % Rex) CxStory) order)})
                    :believed-added (filter #(= (list cc Rex) (:sentence %))) first
                    :justification))]
      (doseq [order [[aa bb] [bb aa]]]
        (is (= ra (:informant (j order))) (pr-str order))))))

(tu/deftest-kb content-the-batch-would-create-is-reported-without-a-handle
  (tu/with-terms [dog Rex CxStory]
    (let [r (v/preview kb {:add [[(list dog Rex) CxStory]]})]
      (testing "a handle that no longer names anything is worse than none"
        (is (nil? (:handle (first (:believed-added r)))))))))

;; ---- 3. what a batch would take away -------------------------------------

(tu/deftest-kb a-batch-that-defeats-an-existing-belief-reports-the-removal
  (tu/with-terms [flies Tweety CxStory]
    (let [h      (v/assert kb (list flies Tweety) CxStory)
          before (content kb)
          r      (v/preview kb {:add [[(list 'not (list flies Tweety)) CxStory
                                       {:strength :monotonic}]]})]
      (testing "the defeated belief is named, with its handle — it is still stored"
        (is (= [(list flies Tweety)] (sentences (:believed-removed r))))
        (is (= h (:handle (first (:believed-removed r)))))
        (is (= :defeated (:reason (first (:believed-removed r))))))
      (testing "and the negation is what arrived, with the nogood it places"
        (is (= [(list 'not (list flies Tweety))] (remove placed? (sentences (:believed-added r)))))
        (is (= '[contradicts defeat] (map first (filter placed? (sentences (:believed-added r)))))))
      (testing "belief is unchanged afterwards — the defeat was hypothetical"
        (is (true? (v/in? kb h))))
      (is (= before (content kb))))))

(tu/deftest-kb a-batch-whose-mark-a-reader-decides-reports-the-removal
  ;; A late `irreflexive` mark takes the `:default` self tuple OUT at its own context with
  ;; no label moving: the settle places the nogood's `defeat` (docs/nmtms.md, "The nogood
  ;; families"), and the settle's window names the tuple.
  (tu/with-terms [near Dora CxStory]
    (let [h      (v/assert kb (list near Dora Dora) CxStory)
          before (content kb)
          r      (v/preview kb {:add [[(list 'irreflexive near) CxStory]]})]
      (is (= [(list near Dora Dora)] (sentences (:believed-removed r))))
      (is (= h (:handle (first (:believed-removed r)))))
      (is (v/believed? kb h CxStory) "the mark was hypothetical")
      (is (= before (content kb))))))

(tu/deftest-kb previewing-a-removal-reports-what-loses-its-support
  (tu/with-terms [dog friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (let [h      (v/assert kb (list dog Rex) CxStory)
          ch     (v/handle-of kb (list friendly Rex) CxStory)
          before (content kb)
          r      (v/preview kb {:remove [h]})]
      (testing "the premise and everything solely resting on it"
        (is (= #{(list dog Rex) (list friendly Rex)} (set (sentences (:believed-removed r)))))
        (is (= #{h ch} (set (map :handle (:believed-removed r)))))
        (is (every? #{:unsupported} (map :reason (:believed-removed r)))))
      (testing "both are believed again afterwards, at the same handles"
        (is (true? (v/in? kb h)))
        (is (true? (v/in? kb ch))))
      (testing "a removal is previewed by suspending the premise, never by deleting"
        (is (= before (content kb)))))))

(tu/deftest-kb a-removal-with-another-witness-is-not-reported-removed
  (tu/with-terms [dog canine friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (v/assert kb (vr/rule-sentence [(list canine '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (v/assert kb (list dog Rex) CxStory)
    (let [h      (v/assert kb (list canine Rex) CxStory)
          before (content kb)
          r      (v/preview kb {:remove [h]})]
      (testing "the conclusion keeps its other derivation, so only the premise goes"
        (is (= [(list canine Rex)] (sentences (:believed-removed r)))))
      (is (= before (content kb))))))

(tu/deftest-kb removing-an-inert-sentex-moves-no-belief
  (tu/with-terms [note Rex CxStory]
    (let [h      (v/assert-inert kb (list note Rex) CxStory)
          before (content kb)
          r      (v/preview kb {:remove [h]})]
      (is (= [[] []] [(:believed-added r) (:believed-removed r)]))
      (is (= before (content kb)))
      (v/edit! kb {:remove [h]}))))

(tu/deftest-kb a-suspended-edge-leaves-the-closures-for-the-window
  (tu/with-terms [puppy dog CxLow]
    (let [edge   (v/assert kb (list 'genl puppy dog) 'CxUniverse)
          cxe    (v/assert kb (list 'genlCx CxLow 'CxUniverse) 'CxUniverse)
          before (content kb)
          orig   @#'settle/drain-recheck!
          seen   (atom [])
          read   #(vector (v/in? kb edge) (v/genl? kb puppy dog)
                          (v/in? kb cxe) (v/sees? kb CxLow 'CxUniverse))]
      ;; read in each pass, where the passes' re-chains read the closures too
      (with-redefs-fn {#'settle/drain-recheck! (fn [k] (swap! seen conj (read)) (orig k))}
        #(v/preview kb {:remove [edge cxe]}))
      (testing "inside the window the closures answer without the OUT edges"
        (is (= [false false false false] (first @seen))))
      (testing "and through them again once the rollback puts them back"
        (is (= [true true true true] (last @seen) (read))))
      (is (= before (content kb))))))

;; ---- 4. exceptions, in both directions -----------------------------------

(tu/deftest-kb previewing-the-fact-that-triggers-an-exception-reports-the-block
  (tu/with-terms [bird penguin flies Opus CxStory]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              CxStory)
    (v/assert kb (list bird Opus) CxStory)
    (let [ch     (v/handle-of kb (list flies Opus) CxStory)
          before (content kb)
          r      (v/preview kb {:add [[(list penguin Opus) CxStory]]})]
      (testing "the conclusion the exception would block"
        (is (= [(list flies Opus)] (sentences (:believed-removed r))))
        (is (= ch (:handle (first (:believed-removed r))))))
      (testing "and it is still there, at the same handle, still believed"
        (is (= ch (v/handle-of kb (list flies Opus) CxStory)))
        (is (true? (v/in? kb ch))))
      (testing "the sweep is suppressed for the preview, so nothing was deleted"
        (is (= before (content kb)))))))

(tu/deftest-kb previewing-a-removal-that-releases-an-exception-reports-the-revival
  (tu/with-terms [bird penguin flies Opus CxStory]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              CxStory)
    (v/assert kb (list bird Opus) CxStory)
    (let [ph     (v/assert kb (list penguin Opus) CxStory {:strength :monotonic})
          _      (is (empty? (v/sentexes-matching kb (list flies Opus) CxStory))
                     "the exception holds, so there is no conclusion to start from")
          before (content kb)
          r      (v/preview kb {:remove [ph]})]
      (testing "removing the blocker would derive the conclusion again"
        (is (contains? (set (sentences (:believed-added r))) (list flies Opus))))
      (testing "the revived line has no handle — a re-derivation mints a fresh one"
        (is (nil? (:handle (first (filter #(= (list flies Opus) (:sentence %))
                                          (:believed-added r)))))))
      (testing "and the rollback collects it: the exception blocks again"
        (is (empty? (v/sentexes-matching kb (list flies Opus) CxStory)))
        (is (= before (content kb)))))))

;; ---- 5. the derivation path's own refusals -------------------------------

(tu/deftest-kb a-conclusion-the-derivation-path-would-drop-is-reported-as-a-violation
  ;; pinned to the constraint reading: the entailment reading mints instead of
  ;; dropping an arg conviction (docs/argtypes.md)
  (tu/without-entailing
   (tu/with-terms [person rock parentOf looksLike Boulder Muffet CxStory]
     (v/assert kb (list 'genl person 'thing) CxStory)
     (v/assert kb (list 'genl rock 'thing) CxStory)
     (v/assert kb (list 'arg parentOf 1 person) CxStory)
     (v/assert kb (list rock Boulder) CxStory)
     (v/assert kb (vr/rule-sentence [(list looksLike '?x)] (list parentOf '?x Muffet)) CxStory {:direction :forward})
     (let [before (content kb)
           r      (v/preview kb {:add [[(list looksLike Boulder) CxStory]]})]
       (testing "the drop is reported where a real run would report it"
         (is (= [:arg-type] (mapv :violation (:violations r))))
         (is (= [(list parentOf Boulder Muffet)] (mapv :sentence (:violations r)))))
       (testing "only the admissible half of the batch is believed"
         (is (= [(list looksLike Boulder)] (sentences (:believed-added r)))))
       (testing "the KB's own ledger is left as it was found"
         (is (empty? (v/violations kb))))
       (is (= before (content kb)))))))

;; A calculus files its inconsistency from inside a read, on the reader's thread.  A
;; reader thread files one after the preview has taken its baseline; the rollback removes
;; what the batch filed and keeps the reader's entry.
(tu/deftest-kb a-preview-rollback-keeps-what-a-reader-filed-beside-it
  (tu/without-entailing
   (tu/with-terms [person rock parentOf looksLike Boulder Muffet CxStory]
     (v/assert kb (list 'genl person 'thing) CxStory)
     (v/assert kb (list 'genl rock 'thing) CxStory)
     (v/assert kb (list 'arg parentOf 1 person) CxStory)
     (v/assert kb (list rock Boulder) CxStory)
     (v/assert kb (vr/rule-sentence [(list looksLike '?x)] (list parentOf '?x Muffet)) CxStory {:direction :forward})
     (let [entry  {:violation :qualitative-inconsistency :calculus :rcc8
                   :context CxStory :sentence nil}
           filed? (atom false)
           orig   clashes/opened
           r      (with-redefs [clashes/opened
                                (fn [& args]
                                  ;; a plain Thread, which conveys no binding, as a
                                  ;; reader's own thread does not
                                  ;; the first call is after the preview's baseline
                                  (when (compare-and-set! filed? false true)
                                    (doto (Thread. #(viol/report-unstamped kb entry)) .start .join))
                                  (apply orig args))]
                    (v/preview kb {:add [[(list looksLike Boulder) CxStory]]}))]
       (is @filed? "the reader filed while the preview ran")
       (testing "the preview reports the batch's drop and not the reader's entry"
         (is (= [:arg-type] (mapv :violation (:violations r)))))
       (testing "the rollback removes the batch's entry and keeps the reader's"
         (is (= [entry] (v/violations kb))))
       (v/clear-violations! kb)))))

(tu/deftest-kb a-conclusion-the-derivation-path-would-arbitrate-is-previewed-as-a-contradiction
  ;; a disjointness clash names an opposing sentex, so the firing is placed and
  ;; arbitrated rather than dropped
  (tu/with-terms [fish mammal swims Willy CxStory]
    (v/assert kb (list 'disjoint fish mammal) CxStory)
    (v/assert kb (vr/rule-sentence [(list swims '?x)] (list fish '?x)) CxStory {:direction :forward})
    (v/assert kb (list mammal Willy) CxStory)
    (let [before (content kb)
          r      (v/preview kb {:add [[(list swims Willy) CxStory]]})]
      (testing "nothing is dropped — the conclusion is admissible, it is merely contested"
        (is (empty? (:violations r))))
      (testing "both the trigger and the contested conclusion would be believed, with the
                nogood they place"
        (is (= #{(list swims Willy) (list fish Willy)}
               (set (remove placed? (sentences (:believed-added r))))))
        (is (= '[contradicts] (map first (filter placed? (sentences (:believed-added r)))))))
      (testing "and the contradiction it would open is what the reviewer is shown"
        (is (= 1 (count (:contradictions r)))))
      (is (= before (content kb))))))

;; ---- 6. refusals -------------------------------------------------------

(tu/deftest-kb a-refused-line-is-reported-and-the-rest-of-the-batch-is-previewed
  (tu/with-terms [dog Rex CxStory]
    (let [before (content kb)
          r      (v/preview kb {:add [['(lives_in ?x ?y) CxStory]
                                      [(list dog Rex) CxStory]]})]
      (testing "the bad line is named by position, in check-edit's shape"
        (is (= [[:add 0 :naming]] (mapv (juxt :in :index :type) (:refused r)))))
      (testing "the good line is still previewed"
        (is (= [(list dog Rex)] (sentences (:believed-added r)))))
      (is (= before (content kb))))))

(tu/deftest-kb an-unknown-handle-in-remove-is-refused-not-ignored
  (let [before (content kb)
        r      (v/preview kb {:remove [999999]})]
    (is (= [[:remove 0 :unknown-handle]] (mapv (juxt :in :index :type) (:refused r))))
    (is (empty? (:believed-removed r)))
    (is (= before (content kb)))))

;; ---- 7. re-asserting what is already there -------------------------------

(tu/deftest-kb previewing-a-sentence-the-kb-already-derives-adds-nothing-and-marks-nothing
  ;; removed too, the handle the add marked is suspended as a premise, and only the audit
  ;; says it was not one
  (doseq [remove? [false true]]
    (tu/with-terms [dog friendly Rex CxStory]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
      (v/assert kb (list dog Rex) CxStory)
      (let [ch     (v/handle-of kb (list friendly Rex) CxStory)
            before (content kb)
            r      (v/preview kb (cond-> {:add [[(list friendly Rex) CxStory]]}
                                   remove? (assoc :remove [ch])))]
        (testing (str "it is already believed, so the diff is empty, remove? " remove?)
          (is (empty? (:believed-added r)))
          (is (empty? (:believed-removed r))))
        (testing "and it is a derived datum again, not a premise"
          (is (false? (v/premise? kb ch))))
        (is (= before (content kb)))))))

(tu/deftest-kb previewing-a-premise-the-kb-already-holds-restores-its-strength
  (tu/with-terms [dog Rex CxStory]
    (let [h      (v/assert kb (list dog Rex) CxStory {:strength :monotonic})
          before (content kb)]
      (v/preview kb {:add [[(list dog Rex) CxStory {:strength :default}]]})
      (testing "the weaker restatement does not survive the preview"
        (is (true? (v/premise? kb h)))
        (is (= :monotonic (v/defeat-class kb h))))
      (is (= before (content kb))))))

(tu/deftest-kb previewing-a-premise-at-a-stronger-class-restores-the-weaker-one
  ;; the direction the rollback's raw `put-premise-mark` is for: `strength/max` alone
  ;; undoes a weakening, and would keep a class the batch raised.  With the handle also
  ;; removed, the suspension records the raised class, so only the audit can restore it.
  (doseq [remove? [false true]]
    (tu/with-terms [dog Rex CxStory]
      (let [h      (v/assert kb (list dog Rex) CxStory {:strength :default})
            before (content kb)]
        (is (= :default (v/defeat-class kb h))
            "the baseline the preview has to put the KB back to")
        (v/preview kb (cond-> {:add [[(list dog Rex) CxStory {:strength :monotonic}]]}
                        remove? (assoc :remove [h])))
        (testing (str "the class the preview raised is not one it may leave behind, remove? " remove?)
          (is (true? (v/premise? kb h)))
          (is (= :default (v/defeat-class kb h)))
          (is (= :default (p/premise-strength (:records kb) h)) "the record recover reads"))
        (is (= before (content kb)))))))

(tu/deftest-kb previewing-a-mirror-spelling-leaves-the-row-s-spellings-as-found
  ;; the batch folds `(sib B A)` into the stored `(sib A B)` row and records the spelling;
  ;; a rollback that kept it would split the row when the `symmetric` mark leaves
  (tu/with-terms [sib Aa Bb CxStory]
    (let [m (v/assert kb (list 'symmetric sib) CxStory)
          h (v/assert kb (list sib Aa Bb) CxStory)]
      (v/preview kb {:add [[(list sib Bb Aa) CxStory]]})
      (is (nil? (integrate/spellings kb h)))
      (v/retract! kb m)
      (is (= [(list sib Aa Bb)] (map :sentence (v/sentexes-matching kb (list sib '?p '?q) CxStory)))))))

;; ---- 8. bounds ---------------------------------------------------------

(tu/deftest-kb max-results-caps-each-half-of-the-diff-and-says-so
  (tu/with-terms [dog friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (let [before (content kb)
          r      (v/preview kb {:add [[(list dog Rex) CxStory]]} {:max-results 1})]
      (is (= 1 (count (:believed-added r))))
      (is (true? (:bounded? r)) "a capped answer must not read as a complete one")
      (is (= before (content kb))))))

(tu/deftest-kb an-unbounded-run-says-it-was-unbounded
  (tu/with-terms [dog Rex CxStory]
    (is (false? (:bounded? (v/preview kb {:add [[(list dog Rex) CxStory]]}))))))

(tu/deftest-kb the-cap-takes-the-content-first-entries-not-the-first-stored
  ;; The batch lists its facts in the reverse of their content order, so a handle ranking
  ;; would show the last line.  Under `*print-length*` 2 the three sentences print alike,
  ;; so only a key built with the print bounds off keeps the content order.
  (doseq [[label report] [["preview" v/preview]
                          ["edit-with-consequences!" v/edit-with-consequences!]]
          print-length   [nil 2]]
    (tu/with-terms [likes Subject CxStory]
      (let [objs (mapv #(tu/tmp-ind %) ["Alpha" "Beta" "Gamma"])
            fact (fn [o] [(list likes Subject o) CxStory])
            r    (binding [*print-length* print-length]
                   (report kb {:add (mapv fact (reverse objs))} {:max-results 1}))
            row  (str label " under *print-length* " print-length)]
        (is (= 1 (count (:believed-added r))) row)
        (is (true? (:bounded? r)) row)
        (is (= (list likes Subject (first objs)) (:sentence (first (:believed-added r))))
            row)
        (doseq [h (:added r)] (v/retract! kb h))))))

(tu/deftest-kb a-chaining-bound-that-cuts-the-answer-says-so
  (doseq [opts [{:max-derivations 1} {:max-depth 1}]]
    (tu/with-terms [a b c d Rex CxStory]
      (doseq [[x y] [[a b] [b c] [c d]]]
        (v/assert kb (vr/rule-sentence [(list x '?x)] (list y '?x)) CxStory {:direction :forward}))
      (let [before (content kb)
            r      (v/preview kb {:add [[(list a Rex) CxStory]]} opts)]
        (is (= [(list a Rex) (list b Rex)] (sentences (:believed-added r))) (pr-str opts))
        (is (true? (:bounded? r)) (pr-str opts))
        (is (= before (content kb)))))))

;; ---- 9. an empty batch --------------------------------------------------

(tu/deftest-kb an-empty-batch-previews-nothing-and-moves-nothing
  (let [before (content kb)
        r      (v/preview kb {})]
    (is (= {:believed-added [] :believed-removed [] :refused [] :violations []
            :contradictions [] :bounded? false}
           r))
    (is (= before (content kb)))))

;; ---- 10. the mixed batch -----------------------------------------------

(tu/deftest-kb adds-land-before-removes-in-a-preview-as-they-do-in-an-edit
  (tu/with-terms [dog canine friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (v/assert kb (vr/rule-sentence [(list canine '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (let [h      (v/assert kb (list dog Rex) CxStory)
          ch     (v/handle-of kb (list friendly Rex) CxStory)
          before (content kb)
          r      (v/preview kb {:add    [[(list canine Rex) CxStory]]
                                :remove [h]})]
      (testing "the added premise re-derives what the removed one was supporting"
        (is (= #{(list canine Rex)} (set (sentences (:believed-added r)))))
        (is (= [(list dog Rex)] (sentences (:believed-removed r))))
        (is (not (contains? (set (map :handle (:believed-removed r))) ch))
            "the conclusion keeps a witness through the batch and never flickers out"))
      (is (= before (content kb))))))

;; ---- 11. the oracle: does the preview predict the edit? ------------------
;; Compared by sentence: created and re-derived content lands on a fresh handle.

(defn- believed-sentences
  "Every datum its own context believes as `{handle sentence}`, read off the whole network
  rather than a region, so the oracle shares no code with `preview`."
  [kb]
  (into {} (comp (filter #(v/in? kb %)) (map (fn [h] [h (v/readable-sentence (v/sentex kb h))])))
        (jtms/in-datums (reasoning/tms kb))))

(defn- edit-diff
  "The belief diff a real `edit` of `batch` produces, as `{:added #{S} :removed #{S}}`."
  [kb batch]
  (let [before (believed-sentences kb)]
    (v/edit! kb batch)
    (let [after (believed-sentences kb)
          s     #(set (map (fn [x] (if (placed? x) (first x) x)) (vals %)))]
      {:added   (s (apply dissoc after (keys before)))
       :removed (s (apply dissoc before (keys after)))})))

(defn- preview-diff
  "The sentences `r` adds and removes, each placed nogood's by its functor (`placed?`)."
  [r]
  (let [s #(set (map (fn [x] (if (placed? x) (first x) x)) (sentences %)))]
    {:added (s (:believed-added r)) :removed (s (:believed-removed r))}))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-derives
  (tu/with-terms [dog friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (let [batch {:add [[(list dog Rex) CxStory]]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-defeats
  (tu/with-terms [flies Tweety CxStory]
    (v/assert kb (list flies Tweety) CxStory)
    (let [batch {:add [[(list 'not (list flies Tweety)) CxStory
                        {:strength :monotonic}]]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-blocks-a-conclusion
  (tu/with-terms [bird penguin flies Opus CxStory]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              CxStory)
    (v/assert kb (list bird Opus) CxStory)
    (let [batch {:add [[(list penguin Opus) CxStory]]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-removes-a-premise
  (tu/with-terms [dog friendly Rex CxStory]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) CxStory {:direction :forward})
    (let [h     (v/assert kb (list dog Rex) CxStory)
          batch {:remove [h]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-releases-an-exception
  (tu/with-terms [bird penguin flies Opus CxStory]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              CxStory)
    (v/assert kb (list bird Opus) CxStory)
    (let [ph    (v/assert kb (list penguin Opus) CxStory)
          batch {:remove [ph]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

;; ---- 12. the clash that withdraws nothing --------------------------------

(tu/deftest-kb a-batch-that-opens-a-dilemma-reports-it-rather-than-a-withdrawal
  (tu/with-terms [flies Tweety CxStory]
    (let [h      (v/assert kb (list flies Tweety) CxStory)
          before (content kb)
          r      (v/preview kb {:add [[(list 'not (list flies Tweety)) CxStory]]})]
      (testing "nothing was withdrawn, because nothing was defeated"
        (is (empty? (:believed-removed r)))
        (is (true? (v/in? kb h))))
      (testing "but the clash the batch would open is named, with both sides"
        (is (= 1 (count (:contradictions r))))
        (is (= #{(list flies Tweety) (list 'not (list flies Tweety))}
               (set (map :sentence (:sides (first (:contradictions r))))))))
      (is (= before (content kb))))))

(tu/deftest-kb a-dilemma-the-kb-already-has-is-not-the-batch-s-doing
  (tu/with-terms [flies Tweety dog Rex CxStory]
    (v/assert kb (list flies Tweety) CxStory)
    (v/assert kb (list 'not (list flies Tweety)) CxStory)
    (is (= 1 (count (v/contradictions kb))) "the standing dilemma is the baseline")
    (let [r (v/preview kb {:add [[(list dog Rex) CxStory]]})]
      (is (empty? (:contradictions r))
          "an unrelated line is not answerable for a clash that was already there"))))

(tu/deftest-kb a-preview-reads-no-placed-nogood-its-window-does-not-touch
  ;; the standing dilemmas sit in contexts the line's context does not see
  (tu/with-terms [flies dog Rex CxSide]
    (let [n     8
          birds (repeatedly n #(tu/tmp-ind "Bird"))]
      (doseq [b birds :let [c (tu/tmp-ctx "Story")]]
        (v/assert kb (list flies b) c)
        (v/assert kb (list 'not (list flies b)) c))
      (is (= n (count (v/contradictions kb))))
      (let [read (atom 0)
            real @#'clashes/reports-over
            r    (with-redefs [clashes/reports-over (fn [kb hs]
                                                      (swap! read + (count hs))
                                                      (real kb hs))]
                   (v/preview kb {:add [[(list dog Rex) CxSide]]}))]
        (is (empty? (:contradictions r)))
        (is (zero? @read))))))

(defn- oracle-op
  "One line of a random batch or of the stream between batches, over the routes a
  reader's dilemmas read: a negation pair, two memberships of separated types and the
  separation itself, a self tuple under a mark and a predicate edge bringing a
  predicate under it, an inherited claim and the denials it convicts, and a fact no
  nogood reads.  `t` holds the terms; each line is `[sentence context opts]`."
  [^java.util.Random rng {:keys [ctxs inds] :as t}]
  (let [pick #(nth % (.nextInt rng (count %)))
        x    (pick inds)
        k    (.nextInt rng 11)
        ;; the declarations monotonic, the rest a default three times in four
        opts (if (or (contains? #{4 6 8} k) (zero? (.nextInt rng 4))) {:strength :monotonic} {})]
    [(case k
       0 (list (:flies t) x)
       1 (list 'not (list (:flies t) x))
       2 (list (:fish t) x)
       3 (list (:mammal t) x)
       4 (list 'disjoint (:fish t) (:mammal t))
       5 (list (:self t) x x)
       6 (list 'genl (:sub t) (:self t))
       7 (list (:sub t) x x)
       8 (list (:carries t) (:hauler t) x)
       9 (list 'not (list (:carries t) (:cart t) x))
       10 (list (:ledger t) x x))
     (pick ctxs)
     opts]))

(defn- opened-both
  "`preview`'s answer for `batch`, and the `:contradictions` the same preview answers
  when it reads the reports of every stored `(contradicts …)`, from one run, so both
  read the same handles."
  [kb batch]
  (let [opened   clashes/opened
        removed  clashes/standing-removed
        full     (atom nil)
        answer   (atom nil)
        r        (with-redefs [clashes/opened
                               (fn [kb window]
                                 (reset! full (opened kb (reads/as-stored-with-functor (:index kb) 'contradicts)))
                                 (opened kb window))
                               clashes/standing-removed
                               (fn [kb o]
                                 (reset! answer (removed kb @full))
                                 (removed kb o))]
                   (v/preview kb batch))]
    [r @answer]))

(defn- oracle-mismatch
  "The first `[step batch]` of `seed`'s stream whose preview answers `:contradictions`
  other than the full read's, or moves the KB's own, over `steps` steps, or nil."
  [kb seed steps]
  (tu/with-terms [flies fish mammal self sub carries hauler cart ledger
                  CxTop CxA CxB CxAB CxSide A B C]
    (let [rng (java.util.Random. (long seed))
          t   {:flies flies :fish fish :mammal mammal :self self :sub sub :carries carries
               :hauler hauler :cart cart :ledger ledger
               ;; `CxSide` sees none of the others
               :ctxs [CxTop CxA CxB CxAB CxSide] :inds [A B C]}
          m   {:strength :monotonic}]
      (doseq [[sub sup] [[CxA CxTop] [CxB CxTop] [CxAB CxA] [CxAB CxB]]]
        (v/assert kb (list 'genlCx sub sup) CxTop m))
      (doseq [s [(list 'irreflexive self) (list 'binary_predicate carries)
                 (list 'transitiveInArgInverse carries 1 'genl) (list 'genl hauler 'animal)
                 (list 'genl cart hauler)]]
        (v/assert kb s CxTop m))
      (loop [step 0, stored []]
        (when (< step steps)
          (let [[s c opts] (oracle-op rng t)
                h          (try (v/assert kb s c opts) (catch clojure.lang.ExceptionInfo _ nil))
                stored     (cond-> stored (integer? h) (conj h))]
            (let [batch  {:add    (vec (repeatedly (.nextInt rng 3) #(oracle-op rng t)))
                          :remove (if (and (seq stored) (zero? (.nextInt rng 2)))
                                    [(nth stored (.nextInt rng (count stored)))]
                                    [])}
                  before (v/contradictions kb)
                  [r full] (opened-both kb batch)]
              (if (and (= full (:contradictions r)) (= before (v/contradictions kb)))
                (recur (inc step) stored)
                [step batch]))))))))

(tu/deftest-kb a-preview-opens-the-dilemmas-the-full-read-opens-over-a-random-stream
  ;; one seed of the `^:slow` sweep, so `:default` runs the harness
  (is (nil? (oracle-mismatch kb 0 25))))

(tu/deftest-kb ^:slow a-preview-opens-the-dilemmas-the-full-read-opens-over-random-streams
  (doseq [seed (range 1 9)]
    (is (nil? (oracle-mismatch kb seed 40)) (str "seed " seed))))

;; ---- 13. equality: the second way a belief stops being one ---------------

(tu/deftest-kb a-merge-reports-the-spelling-it-supersedes
  (tu/with-terms [barks Rex Rexy CxStory]
    (let [h      (v/assert kb (list barks Rexy) CxStory)
          before (content kb)
          r      (v/preview kb {:add [[(list 'sameAs Rex Rexy) CxStory]]})]
      (testing "the retired spelling stops being believed, and says why"
        (let [e (first (filter #(= (list barks Rexy) (:sentence %)) (:believed-removed r)))]
          (is (some? e) "the superseded spelling was not reported")
          (is (= h (:handle e)))
          (is (= :superseded (:reason e)))))
      (testing "and the restatement under the representative arrives, naming no rule"
        (let [e (first (filter #(= (list barks Rex) (:sentence %)) (:believed-added r)))]
          (is (= 'rewriteOf (:informant (:justification e))))
          (is (not (contains? (:justification e) :rule)))))
      (testing "the merge is undone: the original spelling is believed again"
        (is (true? (v/in? kb h)))
        (is (false? (v/same-class? kb Rex Rexy))))
      (is (= before (content kb))))))

;; ---- 14. a throw during application ------------------------------------

(tu/deftest-kb a-line-that-throws-only-once-an-earlier-line-lands-is-reported-not-thrown
  ;; the second line closes a `genl` cycle with the first, which is refused
  (tu/with-terms [fish mammal CxStory]
    (let [before (content kb)
          r      (v/preview kb {:add [[(list 'genl fish mammal) CxStory]
                                      [(list 'genl mammal fish) CxStory]]})]
      (testing "the pre-flight passed it — the KB it was checked against had neither"
        (is (= [(list 'genl fish mammal)] (sentences (:believed-added r)))))
      (testing "so the refusal comes from the application, at its own index"
        (is (= [[:add 1 :not-well-formed]] (mapv (juxt :in :index :type) (:refused r)))))
      (is (= before (content kb))))))

;; ---- the opts roster ------------------------------------------------------

(tu/deftest-kb a-consequence-entry-point-option-nothing-reads-is-refused
  ;; every key is a bound, so a misspelt one read as absent is a cap silently off
  (tu/with-terms [dog Muffet CxCap]
    (let [batch {:add [[(list dog Muffet) CxCap]]}]
      (testing "preview refuses the singular typo, naming its roster"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/preview kb batch {:max-result 5})))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (= [:max-result] (:unknown (ex-data e))))
          (is (re-find #":max-results" (ex-message e)))))
      (testing "edit-with-consequences reads only :max-results and says so"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/edit-with-consequences! kb batch {:max-depth 3})))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (= [:max-depth] (:unknown (ex-data e))))))
      (testing "a cap that is not a positive integer is refused at both entry points"
        ;; read as no cap, a string or a zero would answer whole with `:bounded?` false
        (doseq [[label bad] [["a string" "1"] ["zero" 0] ["a negative" -1]]
                entry-point        [#(v/preview kb batch {:max-results bad})
                                    #(v/edit-with-consequences! kb batch {:max-results bad})]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (entry-point)) label)]
            (is (= :unknown-option (:type (ex-data e))) label)
            (is (= bad (:limit (ex-data e))) label)
            (is (re-find #"positive integer" (ex-message e)) label))))
      (testing "a non-map opts is refused at both entry points"
        ;; the type mismatch clj-kondo sees is the refusal under test
        #_{:clj-kondo/ignore [:type-mismatch]}
        (doseq [entry-point [#(v/preview kb batch :max-results)
                             #(v/edit-with-consequences! kb batch :max-results)]]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map" (entry-point)))))
      (testing "the rostered keys still run"
        (is (map? (v/preview kb batch {:max-depth 2 :max-derivations 10
                                       :max-results 1})))
        (let [r (v/edit-with-consequences! kb batch {:max-results 1})]
          (is (contains? r :believed-added))
          ;; put the KB back — the roster test's write is not its subject
          (doseq [h (:added r)] (v/retract! kb h)))))))
