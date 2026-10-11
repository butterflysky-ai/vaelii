;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mint-candidates-test
  "The mints a moved `genlCx` edge can have made redundant are the ones stated in a
  context under its `sub` that sees it.

  `special/withdrawal-candidates` reads them off whichever of the mint family's contexts
  and `sub`'s descendants is fewer.  A `recover` moves every `genlCx` edge, and filtering
  every descendant of every edge by what it sees costs a `sees?` walk per descendant even
  when the roster names a handful of contexts.  The candidates must
  be the ones `tax/context-down` gives."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- by-definition
  "The candidates a `genlCx` record `sx` names, read off `tax/context-down` of its `sub`."
  [kb sx]
  (set (for [c (tax/context-down (reasoning/taxonomy kb) (second (:sentence sx)))
             h (reads/as-stored-mints-in (:index kb) c)]
         [h nil])))

(defn- context-edges [kb]
  (into [] (comp (keep #(p/get-sentex (:records kb) %))
                 (filter #(and (nil? (:antecedent %)) (seq? (:sentence %))
                               (= 'genlCx (first (:sentence %))))))
        (p/sentex-ids (:records kb))))

(defn- world!
  "Contexts in a random lattice under CxUniverse, an `except` on one `genlCx` edge in
  some worlds so a context's view is filtered, and a mint in some contexts: `(arg rel 1
  kind)` with a `rel` fact there mints `(kind x)`."
  [kb ^java.util.Random rnd]
  (let [ctxs (vec (repeatedly 9 #(tu/fresh-term :context 'CxMc)))
        kind (tu/fresh-term :type 'mc_t)
        rel  (tu/fresh-term :predicate 'mcRel)
        try! (fn [s c] (try (v/assert kb s c) (catch clojure.lang.ExceptionInfo _)))]
    (try! (list 'genl kind 'thing) 'CxUniverse)
    (try! (list 'arg rel 1 kind) 'CxUniverse)
    (doseq [i (range (count ctxs))]
      (try! (list 'genlCx (ctxs i) (if (zero? i) 'CxUniverse (ctxs (.nextInt rnd i)))) 'CxUniverse)
      (when (and (pos? i) (< (.nextInt rnd 3) 1))
        (try! (list 'genlCx (ctxs i) (ctxs (.nextInt rnd i))) 'CxUniverse)))
    (when (zero? (.nextInt rnd 2))
      (let [i (inc (.nextInt rnd (dec (count ctxs))))
            e (first (filter #(= (ctxs i) (second (:sentence %))) (context-edges kb)))]
        (when e (try! (list 'except (list 'sentexHandle (:id e))) (ctxs (.nextInt rnd (count ctxs)))))))
    (dotimes [_ 4]
      (try! (list rel (tu/fresh-term :individual 'Thing) (tu/fresh-term :individual 'Thing))
            (ctxs (.nextInt rnd (count ctxs)))))
    ctxs))

(deftest a-moved-context-edge-names-the-mints-context-down-reaches
  (let [rnd  (java.util.Random. 8821)
        seen (atom 0)]
    (dotimes [trial 12]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (binding [checks/*assertive-arg-types?* true
                  checks/*prune-subsumed-mints?* true]
          (world! kb rnd)
          (doseq [sx (context-edges kb)
                  :let [want (by-definition kb sx)]]
            (swap! seen + (count want))
            (is (= want (set (@#'special/withdrawal-candidates kb sx)))
                (str "trial " trial " " (:sentence sx)))))))
    (is (pos? @seen) "the worlds hold mints under some moved edge")))

(deftest a-moved-context-edge-asks-only-the-contexts-holding-a-mint
  ;; thirty contexts under CxMcTop and a mint in one of them, and an `except` on an
  ;; unrelated `genlCx` edge, so a context's view is filtered: the edge into CxMcTop asks
  ;; what that one context sees, not what every descendant does
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (binding [checks/*assertive-arg-types?* true
              checks/*prune-subsumed-mints?* true]
      (let [top  (tu/fresh-term :context 'CxMcTop)
            subs (vec (repeatedly 30 #(tu/fresh-term :context 'CxMc)))
            kind (tu/fresh-term :type 'mc_t)
            rel  (tu/fresh-term :predicate 'mcRel)]
        (v/assert kb (list 'genlCx top 'CxUniverse) 'CxUniverse)
        (doseq [c subs] (v/assert kb (list 'genlCx c top) 'CxUniverse))
        (let [[a b] (repeatedly 2 #(tu/fresh-term :context 'CxMcAside))
              e     (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)]
          (v/assert kb (list 'genlCx b a) 'CxUniverse)
          (v/assert kb (list 'except (list 'sentexHandle e)) b))
        (v/assert kb (list 'genl kind 'thing) 'CxUniverse)
        (v/assert kb (list 'arg rel 1 kind) 'CxUniverse)
        (v/assert kb (list rel 'McFred 'McMary) (first subs))
        (is (pos? (reads/stored-mint-count-global (:index kb))) "the fact mints a membership")
        (let [sx    (first (filter #(= top (second (:sentence %))) (context-edges kb)))
              asks  (atom 0)
              real  tax/sees?
              ;; read before the definition, whose `context-down` would fill the memo
              got   (with-redefs [tax/sees? (fn [& a] (swap! asks inc) (apply real a))]
                      (set (@#'special/withdrawal-candidates kb sx)))
              want  (by-definition kb sx)]
          (is (= 1 (count want)) "the edge reaches the one mint")
          (is (= want got))
          (is (<= @asks 2) (str @asks " visibility asks for one mint context")))))))

(defn- filed
  "The handles the mint family files, read by term."
  [kb]
  (let [idx (:index kb)]
    (into #{} (mapcat #(reads/as-stored-mints-about-global idx %)) (reads/as-stored-mint-terms idx))))

(defn- concluded
  "The handles a stored justification `special/mint-informant?` accepts concludes, of a
  shape the family files: what `reindex` posts."
  [kb]
  (let [recs (:records kb)]
    (into #{}
          (comp (keep #(p/get-justification recs %))
                (filter #(special/mint-informant? (:informant %)))
                (map :consequence)
                (filter #(some-> (p/get-sentex recs %) :sentence (@#'special/roster-term))))
          (p/justification-ids recs))))

(deftest the-mint-family-files-the-records-a-stored-mint-justification-concludes
  ;; After each write, the family against the stored justifications.  The record `(kind
  ;; Rex)` loses its two mint justifications one at a time while an author's statement
  ;; holds it in the store, so the family must drop it with the second; the other rows
  ;; drop a record by a withdrawal, which sweeps it, and by a declaration's retraction.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (binding [checks/*assertive-arg-types?* true
              checks/*prune-subsumed-mints?* true]
      (tu/with-terms [kind sub_kind owns keeps Rex Fido Max Bone CxZoo]
        (let [m       {:strength :monotonic}
              h       #(v/handle-of kb % CxZoo)
              steps   (atom [])
              observe (fn [label x]
                        (swap! steps conj [label (= (concluded kb) (filed kb))
                                           (contains? (filed kb) (h (list kind x)))]))]
          (v/assert kb (list 'genlCx CxZoo 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genl kind 'thing) CxZoo m)
          (v/assert kb (list 'genl sub_kind kind) CxZoo m)
          (v/assert kb (list 'arg owns 1 kind) CxZoo m)
          (v/assert kb (list 'arg keeps 1 kind) CxZoo m)
          (v/assert kb (list owns Rex Bone) CxZoo)
          (v/assert kb (list keeps Rex Bone) CxZoo)
          (observe :two-mint-justifications Rex)
          (v/assert kb (list kind Rex) CxZoo)
          (v/retract! kb (h (list owns Rex Bone)))
          (observe :one-left Rex)
          (v/retract! kb (h (list keeps Rex Bone)))
          (observe :none-left-and-stated Rex)
          (v/assert kb (list owns Fido Bone) CxZoo)
          (v/assert kb (list sub_kind Fido) CxZoo)
          (observe :withdrawn Fido)
          (v/assert kb (list owns Max Bone) CxZoo)
          (observe :minted Max)
          (v/retract! kb (h (list 'arg owns 1 kind)))
          (observe :declaration-retracted Max)
          (is (= [[:two-mint-justifications true true]
                  [:one-left true true]
                  [:none-left-and-stated true false]
                  [:withdrawn true false]
                  [:minted true true]
                  [:declaration-retracted true false]]
                 @steps)))))))

(deftest the-mint-family-files-a-respelled-record-under-its-current-spelling
  ;; `(likes (MotherFn Bob) Tom)` mints `(person K)` while a `reifiable_function` mark
  ;; spells `(MotherFn Bob)` as the constant K, and the author states `(person (MotherFn
  ;; Bob))` too, so the record is a premise the mark respells: to the constant, which the
  ;; family files under, back to the application, which it files under nothing, and to
  ;; the constant again.  The
  ;; family against the stored justifications after each step, and empty at the end.
  (doseq [mark-first? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (binding [checks/*assertive-arg-types?* true]
        (tu/with-terms [person likes MotherFn Bob Tom]
          (let [m       {:strength :monotonic}
                mark    (list 'reifiable_function MotherFn)
                fact    (list likes (list MotherFn Bob) Tom)
                stated  (list person (list MotherFn Bob))
                steps   (atom [])
                observe (fn [label] (swap! steps conj [label (= (concluded kb) (filed kb))]))]
            (v/assert kb (list 'genl person 'thing) 'CxUniverse m)
            (v/assert kb (list 'arg likes 1 person) 'CxUniverse m)
            (doseq [s (if mark-first? [mark fact stated] [stated fact mark])]
              (v/assert kb s 'CxUniverse))
            (observe :marked)
            (v/retract! kb (v/handle-of kb mark 'CxUniverse))
            (observe :unmarked)
            (v/assert kb mark 'CxUniverse)
            (observe :remarked)
            (v/retract! kb (v/handle-of kb mark 'CxUniverse))
            (v/retract! kb (v/handle-of kb fact 'CxUniverse))
            (observe :fact-retracted)
            (v/retract! kb (v/handle-of kb stated 'CxUniverse))
            (is (= [[:marked true] [:unmarked true] [:remarked true] [:fact-retracted true]] @steps)
                (if mark-first? "mark first" "mark last"))
            (is (empty? (filed kb)) "nothing is left filed once the record is gone")))))))
