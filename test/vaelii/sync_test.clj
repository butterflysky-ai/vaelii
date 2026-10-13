;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sync-test
  "`sync!` locks CxUniverse's premises to the shipped files, brings the middle contexts to
  what this engine ships, and touches nothing an author put anywhere else.

  Each test builds its KB in a private in-RAM space of this namespace's own, restored from
  the suite's starter or upper dump, so the edits a test makes to the shipped contexts
  never reach a KB another namespace holds.  A test whose subject is the author's writes
  makes them in both arrival orders, each over a KB of its own."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.sync :as sync]
            [vaelii.test-util :as tu]))

(def ^:private ships
  "The starter's content, computed once: `sync/premises` loads the starter into a
  scratch KB, which is what a test would otherwise pay for per call."
  (delay (sync/premises)))

(defn- open-kb
  [k load!]
  (doto (v/open-kb (assoc tu/starter-build-space :space [::shipped k]))
    (tu/clear-kb!)
    (load!)))

(defn- in-orders
  "Run `check` once per entry of `orders`, `{name [write …]}` with each write a fn of the
  KB, over a starter KB of its own that the entry's writes are applied to in turn."
  [k orders check]
  (doseq [[order ws] orders]
    (let [kb (open-kb [k order] tu/load-starter!)]
      (try
        (run! #(% kb) ws)
        (testing order (check kb))
        (finally (tu/clear-kb! kb))))))

(defn- in-both-orders
  "`in-orders` over `writes` as given and reversed."
  [k writes check]
  (in-orders k {"forward" writes "reversed" (reverse writes)} check))

(defn- shipped-form
  "The first shipped entry in `context` whose form satisfies `pred`."
  [context pred]
  (first (filter #(and (= context (:context %)) (pred (:form %))) @ships)))

(defn- monotonic? [form] (and (seq? form) (= 'set/monotonic (first form))))

(defn- plain-fact?
  "A default fact under a plain functor: no wrapper, no rule, no namespaced functor."
  [form]
  (and (seq? form) (symbol? (first form)) (nil? (namespace (first form)))
       (not (monotonic? form)) (not ('#{implies exceptWhen genlCx} (first form)))))

(def ^:private in-sync {:add [] :remove []})

(deftest a-kb-built-by-this-engine-is-in-sync
  (testing "the starter"
    (let [kb (open-kb :starter tu/load-starter!)]
      (try
        (is (= in-sync (sync/plan kb @ships)))
        (finally (tu/clear-kb! kb)))))
  (testing "a vocabulary KB gains none of the middle contexts it does not have"
    (let [kb (open-kb :core tu/load-core!)]
      (try
        (is (= in-sync (sync/plan kb @ships)))
        (finally (tu/clear-kb! kb))))))

(deftest an-author-premise-in-cxuniverse-is-retracted
  (let [fact '(unary_predicate shipped_authored_kind)]
    (in-both-orders :authored
                    [#(v/assert % fact 'CxUniverse)
                     #(v/assert % '(unary_predicate shipped_other_kind) 'CxUniverse)]
                    (fn [kb]
                      (is (= #{['CxUniverse fact] ['CxUniverse '(unary_predicate shipped_other_kind)]}
                             (set (map (juxt :context :form) (:remove (sync/plan kb @ships))))))
                      (is (= {:added 0 :removed 2 :refused []} (sync/sync! kb @ships)))
                      (is (nil? (v/handle-of kb fact 'CxUniverse)))
                      (is (= in-sync (sync/plan kb @ships)))))))

(deftest an-author-genlcx-edge-survives-the-sync
  (tu/with-terms [CxAuthorAbove CxAuthorBelow]
    (in-both-orders :edges
                    [#(v/assert % (list 'genlCx 'CxUniverse CxAuthorAbove) 'CxUniverse)
                     #(v/assert % (list 'genlCx CxAuthorBelow 'CxWell) CxAuthorBelow)]
                    (fn [kb]
                      (is (= in-sync (sync/plan kb @ships)))
                      (is (= {:added 0 :removed 0 :refused []} (sync/sync! kb @ships)))
                      (is (some? (v/handle-of kb (list 'genlCx 'CxUniverse CxAuthorAbove) 'CxUniverse)))
                      (is (some? (v/handle-of kb (list 'genlCx CxAuthorBelow 'CxWell) 'CxUniverse)))))))

(deftest a-lifted-copy-of-a-data-context-binding-survives-the-sync
  ;; `(binary_predicate R)` stated in a data context has a copy in CxUniverse, which is no
  ;; premise, so the lock does not reach it.
  (tu/with-terms [CxAuthorData tiedTo]
    (let [binding (list 'binary_predicate tiedTo)]
      (in-both-orders :lifted
                      [#(v/assert % (list 'genlCx CxAuthorData 'CxWell) 'CxUniverse)
                       #(v/assert % binding CxAuthorData)]
                      (fn [kb]
                        (let [copy (v/handle-of kb binding 'CxUniverse)]
                          (is (some? copy))
                          (is (false? (v/premise? kb copy)) "the copy is no premise")
                          (is (= {:added 0 :removed 0 :refused []} (sync/sync! kb @ships)))
                          (is (= copy (v/handle-of kb binding 'CxUniverse)))
                          (is (v/in? kb copy))))))))

(deftest a-sentence-removed-from-a-shipped-file-is-retracted
  (let [gone (shipped-form 'CxUniverse plain-fact?)
        less (into [] (remove #(= gone %)) @ships)]
    ;; the premise as the load stored it, and retracted and stated again after the rest
    (in-orders :removed
               {"loaded"   [#(v/assert % '(unary_predicate shipped_stale_kind) 'CxUniverse)]
                "restated" [#(v/assert % '(unary_predicate shipped_stale_kind) 'CxUniverse)
                            #(v/retract! % (v/handle-of % (:form gone) 'CxUniverse))
                            #(v/assert % (:form gone) 'CxUniverse)]}
               (fn [kb]
                 (is (= #{['CxUniverse (:form gone)] ['CxUniverse '(unary_predicate shipped_stale_kind)]}
                        (set (map (juxt :context :form) (:remove (sync/plan kb less)))))
                     "the plan retracts a premise the files no longer state")
                 (is (= {:added 0 :removed 2 :refused []} (sync/sync! kb less)))
                 (is (nil? (v/handle-of kb (:form gone) 'CxUniverse)))
                 (is (= in-sync (sync/plan kb less)))))))

(deftest a-stale-kb-is-brought-to-what-ships
  (let [;; a shipped fact the KB lost
        missing   (shipped-form 'CxUniverse plain-fact?)
        ;; a known-true one the KB holds at :default, off the forced-monotonic roster
        weakened  (let [kb (open-kb :pick tu/load-core!)]
                    (try
                      (first (filter #(and (= 'CxUniverse (:context %))
                                           (monotonic? (:form %))
                                           (let [s (second (:form %))]
                                             (and (seq? s) (symbol? (first s))
                                                  (not ('#{genlCx implies} (first s)))
                                                  (not (v/has-prop? kb :forced-monotonic (first s))))))
                                     @ships))
                      (finally (tu/clear-kb! kb))))
        wsentence (second (:form weakened))
        ;; an author's own context wired below the middle contexts
        user-fact '(unary_predicate shipped_authored_kind)]
    (tu/with-terms [CxAuthored]
      (in-both-orders :stale
                      [#(v/retract! % (v/handle-of % (:form missing) 'CxUniverse))
                       #(do (v/retract! % (v/handle-of % wsentence 'CxUniverse))
                            (v/assert % wsentence 'CxUniverse))
                       #(v/assert % (list 'genlCx CxAuthored 'CxWell) 'CxUniverse)
                       #(v/assert % user-fact CxAuthored)]
                      (fn [kb]
                        (is (= #{{:context 'CxUniverse :form (:form missing)}
                                 {:context 'CxUniverse :form (:form weakened)}}
                               (set (:add (sync/plan kb @ships)))))
                        (is (= {:added 2 :removed 0 :refused []} (sync/sync! kb @ships)))
                        (is (= :monotonic (:strength (v/sentex kb (v/handle-of kb wsentence 'CxUniverse))))
                            "a raised strength is restated")
                        (is (= in-sync (sync/plan kb @ships)))
                        (is (some? (v/handle-of kb user-fact CxAuthored))
                            "the author's context is left alone"))))))

(deftest a-lowered-strength-is-retracted-and-restated
  (let [lowered  (shipped-form 'CxUniverse plain-fact?)
        sentence (:form lowered)]
    (in-both-orders :lowered
                    [#(v/assert % sentence 'CxUniverse {:strength :monotonic})
                     #(v/assert % '(unary_predicate shipped_lowered_kind) 'CxUniverse)]
                    (fn [kb]
                      (testing "the plan retracts the known-true form and asserts the default one"
                        (is (= {:add    [{:context 'CxUniverse :form sentence}]
                                :remove #{['CxUniverse (list 'set/monotonic sentence)]
                                          ['CxUniverse '(unary_predicate shipped_lowered_kind)]}}
                               (update (sync/plan kb @ships) :remove
                                       #(into #{} (map (juxt :context :form)) %)))))
                      (testing "the sync leaves it held at :default"
                        (is (= {:added 1 :removed 2 :refused []} (sync/sync! kb @ships)))
                        (is (= :default (:strength (v/sentex kb (v/handle-of kb sentence 'CxUniverse)))))
                        (is (= in-sync (sync/plan kb @ships))))))))

(deftest an-addition-the-batch-refuses-is-set-aside-and-lands-after-it
  (let [kb      (open-kb :aside tu/load-starter!)
        ;; a `genl` edge and its reverse close a cycle, which is refused
        lost    '(genl dog mammal)
        clash   '(genl mammal dog)
        edits   (atom 0)
        edit!   v/edit!]
    (try
      (v/retract! kb (v/handle-of kb lost 'CxUniverse))
      ;; an author's edge the lost one would close a cycle with, in the exact context the
      ;; sync retracts it from: the batch asserts before it retracts, so it refuses the
      ;; shipped edge, and the edge lands once the batch has retracted the author's
      (v/assert kb clash 'CxUniverse)
      (with-redefs [v/edit! (fn [& args] (swap! edits inc) (apply edit! args))]
        (is (= {:added 1 :removed 1 :refused []} (sync/sync! kb @ships))))
      (testing "the batch refused the edge, and ran again without it"
        (is (= 2 @edits)))
      (is (some? (v/handle-of kb lost 'CxUniverse)))
      (is (nil? (v/handle-of kb clash 'CxUniverse)))
      (is (= in-sync (sync/plan kb @ships)))
      (finally (tu/clear-kb! kb)))))

(deftest an-exception-the-engine-does-not-ship-goes-with-its-rule
  (let [kb   (open-kb :except tu/load-starter!)
        rule '(implies (bird ?x) (shipped_flagged ?x))
        form (list 'exceptWhen '(shipped_exempt ?x) rule)]
    (try
      (v/assert kb form 'CxBiology)
      (let [[entry] (:remove (sync/plan kb @ships))]
        (testing "the wrapper is one entry naming both records"
          (is (= form (:form entry)))
          (is (= 2 (count (:handles entry))))))
      (is (= {:added 0 :removed 1 :refused []} (sync/sync! kb @ships)))
      (is (nil? (v/handle-of kb rule 'CxBiology)))
      (is (= in-sync (sync/plan kb @ships)))
      (finally (tu/clear-kb! kb)))))

(deftest write-back-edits-one-line-per-premise
  (let [dir   (io/file (System/getProperty "java.io.tmpdir") (str "vaelii-write-back-" (System/nanoTime)))
        core  (io/file dir "core.txt")
        other (io/file dir "other.txt")
        kb    (open-kb :write-back (fn [_]))
        u     'CxUniverse]
    (try
      (.mkdirs dir)
      (spit core (str ";; core\n(comment dog \"A dog.\")\n(genl dog mammal)\n\n"
                      "(comment bird \"A bird.\")\n(genl bird animal)\n"))
      (spit other (str "(comment cat \"A cat.\")\n(genl cat mammal)\n"
                       ";; a cat is a mammal\n(implies (and (cat ?c))\n         (mammal ?c))\n"))
      (let [report (sync/write-back!
                    kb
                    {:add    [{:context u :form '(set/monotonic (genl dog mammal))}
                              {:context u :form '(set/monotonic (folk_species dog))}
                              {:context u :form '(genl zebra mammal)}
                              {:context u :form '(genl cat feline)}]
                     :remove [{:context u :form '(genl dog mammal)}
                              {:context u :form '(implies (and (cat ?x)) (mammal ?x))}
                              {:context u :form '(genl absent mammal)}
                              {:context 'CxNowhere :form '(genl dog mammal)}]}
                    #(when (= u %) [core other]))]
        (is (= {:written 5
                :skipped [{:context 'CxNowhere :form '(genl dog mammal)}
                          {:context u :form '(genl absent mammal)}]}
               (update report :skipped #(sort-by (comp str :context) %))))
        (testing "a strength change is rewritten in place, and an addition joins its term's block"
          (is (= (str ";; core\n(comment dog \"A dog.\")\n(set/monotonic (genl dog mammal))\n"
                      "(set/monotonic (folk_species dog))\n\n"
                      "(comment bird \"A bird.\")\n(genl bird animal)\n\n(genl zebra mammal)\n")
                 (slurp core))))
        (testing "a removal matches the sentence under other variable names, and comments stay"
          (is (= "(comment cat \"A cat.\")\n(genl cat mammal)\n;; a cat is a mammal\n(genl cat feline)\n"
                 (slurp other)))))
      (finally
        (tu/clear-kb! kb)
        (run! io/delete-file (reverse (file-seq dir)))))))
