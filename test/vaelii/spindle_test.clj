;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.spindle-test
  "`sync-spindle!` makes a KB's shipped contexts state what this engine ships, and touches
  nothing an author put anywhere else.

  Each test builds its KB in a private in-RAM space of this namespace's own, restored from
  the suite's starter or core dump, so the edits a test makes to the shipped contexts —
  the whole point here — never reach a KB another namespace holds."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.spindle :as spindle]
            [vaelii.test-util :as tu]))

(def ^:private shipped
  "The starter's content, computed once: `spindle/shipped` loads the starter into a
  scratch KB, which is what a test would otherwise pay for per call."
  (delay (spindle/shipped)))

(defn- open-kb
  [k load!]
  (doto (v/open-kb (assoc tu/starter-build-space :space [::spindle k]))
    (tu/clear-kb!)
    (load!)))

(defn- shipped-form
  "The first shipped entry in `context` whose form satisfies `pred`."
  [context pred]
  (first (filter #(and (= context (:context %)) (pred (:form %))) @shipped)))

(defn- monotonic? [form] (and (seq? form) (= 'set/monotonic (first form))))

(deftest a-kb-built-by-this-engine-is-in-sync
  (testing "the starter"
    (let [kb (open-kb :starter tu/load-starter!)]
      (try
        (is (= {:add [] :remove []} (spindle/plan kb @shipped)))
        (finally (tu/clear-kb! kb)))))
  (testing "a core-only KB gains none of the layers it does not have"
    (let [kb (open-kb :core tu/load-core!)]
      (try
        (is (= {:add [] :remove []} (spindle/plan kb @shipped)))
        (finally (tu/clear-kb! kb))))))

(deftest a-stale-spindle-is-brought-to-what-ships
  (let [kb        (open-kb :stale tu/load-starter!)
        ;; a shipped fact the KB lost
        missing   (shipped-form 'CxAbstract (every-pred seq? (complement monotonic?)))
        ;; a known-true one the KB holds at :default, off the forced-monotonic roster
        weakened  (shipped-form 'CxOrganism
                                #(and (monotonic? %)
                                      (not (v/has-prop? kb :forced-monotonic (first (second %))))))
        wsentence (second (:form weakened))
        ;; an author's own context wired into the spindle, and a fact in the collector
        user-cx   'CxSpindleAuthored
        user-fact '(unary_predicate spindle_authored_kind)]
    (try
      (v/retract! kb (v/handle-of kb (:form missing) 'CxAbstract))
      (v/retract! kb (v/handle-of kb wsentence 'CxOrganism))
      (v/assert kb wsentence 'CxOrganism)
      (v/assert kb '(unary_predicate spindle_stale_kind) 'CxCore)
      (v/assert kb (list 'genlCx user-cx 'CxCore) 'CxUniverse)
      (v/assert kb (list 'genlCx 'CxUniverse user-cx) 'CxUniverse)
      (v/assert kb user-fact user-cx)
      (v/assert kb '(unary_predicate spindle_collected_kind) 'CxUniverse)
      (testing "the plan names each difference"
        (let [{:keys [add remove]} (spindle/plan kb @shipped)]
          (is (= #{{:context 'CxAbstract :form (:form missing)}
                   {:context 'CxOrganism :form (:form weakened)}}
                 (set add)))
          (testing "and a stale membership is a removal at the strength it was written at"
            ;; `unary_predicate` is on the forced-monotonic roster, which moves the class
            ;; belief reads and leaves the record as written
            (is (= #{['CxCore '(unary_predicate spindle_stale_kind)]}
                   (set (map (juxt :context :form) remove)))))))
      (testing "the sync applies it"
        (is (= {:added 2 :removed 1 :refused []} (spindle/sync-spindle! kb @shipped)))
        (is (= {:add [] :remove []} (spindle/plan kb @shipped)))
        (is (= :monotonic (:strength (v/sentex kb (v/handle-of kb wsentence 'CxOrganism)))))
        (is (nil? (v/handle-of kb '(unary_predicate spindle_stale_kind) 'CxCore))))
      (testing "and leaves the author's context and the collector's other content alone"
        (is (some? (v/handle-of kb user-fact user-cx)))
        (is (some? (v/handle-of kb '(unary_predicate spindle_collected_kind) 'CxUniverse))))
      (finally (tu/clear-kb! kb)))))

(deftest a-lowered-strength-is-retracted-and-restated
  (let [kb       (open-kb :lowered tu/load-starter!)
        ;; a default fact the KB holds known-true
        lowered  (shipped-form 'CxAbstract (every-pred seq? (comp symbol? first) (complement monotonic?)
                                                       (comp nil? namespace first)
                                                       (comp (complement '#{implies exceptWhen}) first)))
        sentence (:form lowered)]
    (try
      (v/assert kb sentence 'CxAbstract {:strength :monotonic})
      (testing "the plan retracts the known-true form and asserts the default one"
        (is (= {:add    [{:context 'CxAbstract :form sentence}]
                :remove [['CxAbstract (list 'set/monotonic sentence)]]}
               (update (spindle/plan kb @shipped) :remove
                       #(mapv (juxt :context :form) %)))))
      (testing "the sync leaves it held at :default"
        (is (= {:added 1 :removed 1 :refused []} (spindle/sync-spindle! kb @shipped)))
        (is (= :default (:strength (v/sentex kb (v/handle-of kb sentence 'CxAbstract)))))
        (is (= {:add [] :remove []} (spindle/plan kb @shipped))))
      (finally (tu/clear-kb! kb)))))

(deftest an-addition-the-batch-refuses-is-set-aside-and-lands-after-it
  (let [kb      (open-kb :aside tu/load-starter!)
        ;; a `genl` edge and its reverse close a cycle, which is refused
        lost    '(genl dog mammal)
        clash   '(genl mammal dog)
        edits   (atom 0)
        edit!   v/edit!]
    (try
      (v/retract! kb (v/handle-of kb lost 'CxOrganism))
      ;; an author's edge the lost one would close a cycle with, in the exact context the
      ;; sync retracts it from: the batch asserts before it retracts, so it refuses the
      ;; shipped edge, and the edge lands once the batch has retracted the author's
      (v/assert kb clash 'CxOrganism)
      (with-redefs [v/edit! (fn [& args] (swap! edits inc) (apply edit! args))]
        (is (= {:added 1 :removed 1 :refused []} (spindle/sync-spindle! kb @shipped))))
      (testing "the batch refused the edge, and ran again without it"
        (is (= 2 @edits)))
      (is (some? (v/handle-of kb lost 'CxOrganism)))
      (is (nil? (v/handle-of kb clash 'CxOrganism)))
      (is (= {:add [] :remove []} (spindle/plan kb @shipped)))
      (finally (tu/clear-kb! kb)))))

(deftest an-exception-the-engine-does-not-ship-goes-with-its-rule
  (let [kb   (open-kb :except tu/load-starter!)
        rule '(implies (bird ?x) (spindle_flagged ?x))
        form (list 'exceptWhen '(spindle_exempt ?x) rule)]
    (try
      (v/assert kb form 'CxBiology)
      (let [[entry] (:remove (spindle/plan kb @shipped))]
        (testing "the wrapper is one entry naming both records"
          (is (= form (:form entry)))
          (is (= 2 (count (:handles entry))))))
      (is (= {:added 0 :removed 1 :refused []} (spindle/sync-spindle! kb @shipped)))
      (is (nil? (v/handle-of kb rule 'CxBiology)))
      (is (= {:add [] :remove []} (spindle/plan kb @shipped)))
      (finally (tu/clear-kb! kb)))))
