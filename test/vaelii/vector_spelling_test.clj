;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vector-spelling-test
  "One spelling, one meaning: a top-level **vector is a conjunction** at every entry point.

  A vector is `sequential?`, so `sentex/canon` flattens `[likes Tom Ann]` to the list it
  looks like — while `query` and `prove` read a vector as a join over its members.  The
  write entry point refuses the collision (`sentence-shape-problem`), and this pins the read
  side of it, which is where the same knowledge answered two ways:

    a sentence written as a vector   `ask` / `sentexes-matching` / `handle-of` said the
                                     fact was there, `prove` / `query` joined over its
                                     three symbols and answered nothing
    a conjunction written as one     `prove` / `query` joined it, `ask` flattened it into
                                     a sentence nothing matches and answered **false**

  Neither raised.  Both directions are refused now, and the tests below are written as a
  roster of entry points rather than as one assertion each, because the defect was never in one
  entry point — it was in two entry points disagreeing, and a roster is what fails when the in the adjacent namespace
  is added on one side only."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- refusal
  "The `ex-data` of the refusal `f` throws, or `{:answered (f)}` when it answers."
  [f]
  (try {:answered (let [r (f)] (if (seq? r) (vec r) r))}
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest every-read-entry-point-refuses-a-sentence-written-as-a-vector
  ;; The fact is stored correctly, as a list.  What is asked is the vector spelling of
  ;; it — which `assert` refuses, so no KB can hold anything the spelling names, and a
  ;; entry point that answered `true` for it was answering about a sentence nobody could write.
  (tu/with-terms [likesY TomY AnnY CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (v/assert kb (list likesY TomY AnnY) CxStory)
      (let [as-list   (list likesY TomY AnnY)
            as-vector [likesY TomY AnnY]
            entry-points     {"ask?"              #(v/ask? kb as-vector CxStory)
                              "ask"               #(v/ask kb as-vector CxStory)
                              "ask-within"        #(v/ask-within kb as-vector CxStory {:max-ms 100})
                              "sentexes-matching" #(v/sentexes-matching kb as-vector CxStory)
                              "handle-of"         #(v/handle-of kb as-vector CxStory)
                              "prove"             #(v/prove kb as-vector CxStory)
                              "provable?"         #(v/provable? kb as-vector CxStory)
                              "query"             #(v/query kb as-vector CxStory)
                              "query?"            #(v/query? kb as-vector CxStory)
                              "query-plan"        #(v/query-plan kb as-vector CxStory)
                              "prove-within"      #(v/prove-within kb as-vector CxStory {:max-ms 100})}]
        (testing "the fact is stored, and the list spelling reaches it at every entry point"
          (is (some? (v/handle-of kb as-list CxStory)))
          (is (v/ask? kb as-list CxStory))
          (is (= 1 (count (v/sentexes-matching kb as-list CxStory))))
          (is (seq (v/prove kb as-list CxStory)))
          (is (seq (v/query kb as-list CxStory))))
        (testing "and every entry point refuses the vector spelling of it, with one :type"
          (is (= (into {} (map (fn [[nm _]] [nm :shape])) entry-points)
                 (into {} (map (fn [[nm f]] [nm (:type (refusal f))])) entry-points))))
        (testing "the refusal names the spelling it refused and the list to write"
          (let [d (refusal #(v/ask? kb as-vector CxStory))
                m (ex-message (try (v/ask? kb as-vector CxStory)
                                   (catch clojure.lang.ExceptionInfo e e)))]
            (is (= as-vector (:goal d)))
            (is (.contains ^String m (pr-str as-list))
                "the list spelling is in the message, not left to be guessed")))
        (testing "the write entry point refuses the same spelling, so no entry point takes it"
          (is (= :shape (:type (refusal #(v/assert kb as-vector CxStory))))))))))

(deftest a-conjunction-is-refused-by-the-entry-points-that-cannot-join
  ;; The other direction, and the sharper one: `[(bird ?x) (nests ?x)]` is a documented
  ;; goal — for `query` and `prove`.  Handed to `ask` it was canonicalized into a
  ;; sentence with two compound arguments, which nothing matches, and came back `false`:
  ;; a wrong answer in the form a caller is least likely to question.
  (tu/with-terms [birdY nestsY RobinY CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (v/assert kb (list birdY RobinY) CxStory)
      (v/assert kb (list nestsY RobinY) CxStory)
      (let [conj-goal [(list birdY '?x) (list nestsY '?x)]]
        (testing "the entry points that join answer it"
          (is (seq (v/prove kb conj-goal CxStory)))
          (is (seq (v/query kb conj-goal CxStory)))
          (is (= 2 (count (v/query-plan kb conj-goal CxStory)))))
        (testing "and the entry points that cannot join refuse it rather than answering false"
          (doseq [[nm f] {"ask?"              #(v/ask? kb conj-goal CxStory)
                          "ask"               #(v/ask kb conj-goal CxStory)
                          "ask-within"        #(v/ask-within kb conj-goal CxStory {:max-ms 100})
                          "sentexes-matching" #(v/sentexes-matching kb conj-goal CxStory)
                          "handle-of"         #(v/handle-of kb conj-goal CxStory)}]
            (is (= :shape (:type (refusal f))) nm)))
        (testing "and the refusal sends the caller to the entry points that do join"
          (let [m (ex-message (try (v/ask? kb conj-goal CxStory)
                                   (catch clojure.lang.ExceptionInfo e e)))]
            (is (re-find #"`query`" m))
            (is (not (re-find #"Write the sentence as a list" m))
                "a real conjunction is not a sentence somebody mis-spelled")))))))

(deftest a-vector-of-sentences-is-still-what-a-conjunction-means
  ;; The rule is about the *top level*: the guards must not reach a rule's antecedent
  ;; vector, a conjunctive goal's own members, or the empty conjunction.
  (tu/with-terms [birdY fliesY nestsY RobinY CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (v/assert-rule kb [(list birdY '?x)] (list fliesY '?x) CxStory {:direction :forward})
      (v/assert kb (list birdY RobinY) CxStory)
      (v/assert kb (list nestsY RobinY) CxStory)
      (is (seq (v/sentexes-matching kb (list fliesY RobinY) CxStory))
          "the rule was stored with its antecedent vector and fired")
      (is (= [{}] (vec (v/prove kb [] CxStory)))
          "the empty conjunction still proves trivially")
      (is (= 1 (count (v/prove kb [(list birdY '?x) (list nestsY '?x)] CxStory)))
          "a one-solution join over two conjuncts")
      (testing "a conjunct that is not a sentence is what the join entry point refuses"
        (let [d (refusal #(v/prove kb [(list birdY '?x) nestsY] CxStory))]
          (is (= :shape (:type d)))
          (is (= nestsY (:conjunct d)) "and it names the conjunct, not just the goal")))
      (testing "and `nil` is a conjunct like any other, not the absence of one"
        ;; The guard tests *whether* a bad conjunct exists rather than reading the value
        ;; of the first one, because `nil` is a value it could find.  Read the other way,
        ;; a nil member and no bad member are one answer, and the goal below joins a
        ;; conjunct that matches with one that can never match — answering nothing at
        ;; all, which is the number nobody can check rather than a refusal.
        (doseq [[nm goal] {"alone"            [nil]
                           "beside a match"   [(list birdY '?x) nil]
                           "before a match"   [nil (list birdY '?x)]}]
          (let [d (refusal #(v/prove kb goal CxStory))]
            (is (= :shape (:type d)) nm)
            (is (nil? (:conjunct d)) (str nm " — and it names the nil conjunct"))
            (is (contains? d :conjunct)
                (str nm " — :conjunct is present and nil, not missing")))
          (is (= :shape (:type (refusal #(v/query kb goal CxStory)))) nm))
        (is (seq (v/prove kb [(list birdY '?x)] CxStory))
            "and the same goal without the nil still answers")))))

(deftest handle-of-refuses-a-sentence-or-a-context-that-is-not-one
  ;; `handle-of`'s nil means "not stored", and a caller reads it as a fact about the KB —
  ;; `koinii.deref` reads it as a peer that is out of sync.  A number, a map or a string as
  ;; the sentence, or a nil, a number or a variable as the context, asks nothing a store
  ;; could hold, so each is refused by `:shape` rather than answered as an absence.
  (tu/with-terms [usesDb ProdY PostgresY CxAva]
    (tu/with-cleared-kb [kb tu/fresh]
      (let [s (list usesDb ProdY PostgresY)
            h (v/assert kb s CxAva)]
        (testing "control: the stored sentence is found, and an absent one is nil"
          (is (= h (v/handle-of kb s CxAva)))
          (is (nil? (v/handle-of kb (list usesDb PostgresY ProdY) CxAva))))
        (testing "a sentence that is not a list is refused"
          (doseq [[nm bad] {"a number" 42, "a map" {:a 1}, "a string" "x", "nil" nil}]
            (let [d (refusal #(v/handle-of kb bad CxAva))]
              (is (= :shape (:type d)) nm)
              (is (= bad (:sentence d)) nm))))
        (testing "a context that is not a symbol, or is a variable, is refused"
          (doseq [[nm bad] {"nil" nil, "a number" 42, "the wildcard" '?ctx, "a variable" '?c}]
            (let [d (refusal #(v/handle-of kb s bad))]
              (is (= :shape (:type d)) nm)
              (is (= bad (:context d)) nm))))
        (testing "the context an (ist Ctx S) sentence names is the one held to it"
          (is (= h (v/handle-of kb (list 'ist CxAva s) nil))
              "ist wins over the argument, so a nil argument is not the context read")
          (is (= :shape (:type (refusal #(v/handle-of kb (list 'ist '?c s) CxAva)))))
          (is (= :shape (:type (refusal #(v/handle-of kb (list 'ist CxAva 42) CxAva))))))))))
