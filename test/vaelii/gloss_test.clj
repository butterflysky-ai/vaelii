;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.gloss-test
  "The composed gloss: English out of the KB's own comments, and the places it refuses to
  write prose rather than guess."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.gloss :as gloss]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; ---- the comment is the template -----------------------------------------

(deftest a-comment-reads-as-a-signature-and-a-clause
  (let [t (gloss/template
           "(eats ?animal ?food) means that ?animal takes ?food as nourishment. Both are individuals.")]
    (is (= ["?animal" "?food"] (:params t)))
    (is (= "?animal takes ?food as nourishment" (:text t))))
  (testing "a clause stops at its first sentence, so a comment's asides stay out"
    (is (= "?interval1 begins exactly where ?interval2 ends"
           (:text (gloss/template
                   "(metBy ?interval1 ?interval2) means that ?interval1 begins exactly where ?interval2 ends. The converse of meets.")))))
  (testing "a sentence opening with a parameter is a boundary too, not mid-clause"
    (is (= "?person was born in ?year"
           (:text (gloss/template
                   "(birthYearOf ?person ?year) means that ?person was born in ?year. ?year is a plain number.")))))
  (testing "an imported vocabulary spells the same signature with a colon and plain words"
    (let [t (gloss/template "(eats Animal Food): Animal eats Food.")]
      (is (= ["Animal" "Food"] (:params t)))
      (is (= "Animal eats Food" (:text t)))))
  (testing "a function is documented in the shape too, without the `that`"
    (let [t (gloss/template "(QuantityFn ?magnitude ?unit) means the measure of ?magnitude ?unit. So …")]
      (is (= ["?magnitude" "?unit"] (:params t)))
      (is (= "the measure of ?magnitude ?unit" (:text t)))))
  (testing "a comment with no signature is a description — a type's noun phrase"
    (let [t (gloss/template "A physical part of an organism (a wing, a heart).")]
      (is (empty? (:params t)))
      (is (str/starts-with? (:text t) "A physical part"))))
  (testing "a signature naming a compound argument is read as a description, not parsed"
    ;; substituting into `(list …)` would need to know it is one argument, not three
    (let [t (gloss/template
             "(totalDuration (list ?i1 ?i2 …) ?duration) means that ?duration is the sum of the lengths.")]
      (is (empty? (:params t)))
      (is (str/starts-with? (:text t) "?duration is the sum")))))

(tu/deftest-kb a-documented-sentence-composes-from-its-own-vocabulary
  (testing "a relation substitutes its arguments into its predicate's signature"
    (is (= "Every dog is an animal." (:text (gloss/text kb '(genl dog animal)))))
    (is (= :composed (:source (gloss/text kb '(genl dog animal))))))
  (testing "a parameter is a variable, and `?` is not a word character — the boundary
           has to be written out or the substitution silently matches nothing"
    (is (= "Muffet takes kibble as nourishment." (:text (gloss/text kb '(eats Muffet kibble))))))
  (testing "a type membership reads as one, with the type's comment as the apposition"
    (let [{:keys [text source]} (gloss/text kb '(bird Pingu))]
      (is (str/starts-with? text "Pingu is a bird — "))
      (is (= :composed source))))
  (testing "the formal sentence is never the gloss's job to replace — it returns text only"
    (is (= #{:text :source} (set (keys (gloss/text kb '(genl dog animal))))))))

(tu/deftest-kb an-undocumented-term-is-named-not-described
  (tu/with-terms [wobbles Zork]
    (let [{:keys [text source]} (gloss/text kb (list wobbles Zork))]
      (is (= :named source) "nothing was composed, and the result says so")
      (is (str/includes? text (name Zork)) "the term is named")
      (is (str/includes? text (name wobbles))))))

(tu/deftest-kb a-clause-that-never-names-its-parameters-does-not-swallow-them
  ;; `(disjoint TypeA TypeB): the two types have no common instance` names neither
  ;; argument, so substituting yields a true sentence about nothing in particular —
  ;; fluent, and having silently lost what it was about
  (let [{:keys [text source]} (gloss/text kb '(disjoint dog cat))]
    (is (= :partial source) "half a name is not a composition")
    (is (str/includes? text "dog") "the arguments are said")
    (is (str/includes? text "cat"))
    (is (str/includes? text "no common instance") "and the clause still describes them")))

(tu/deftest-kb the-comments-own-grammar-is-finished-not-rewritten
  (testing "an article the comment wrote agrees with the argument substituted after it"
    ;; "every SubType is a SuperType" + animal
    (is (str/includes? (:text (gloss/text kb '(genl dog animal))) "is an animal")))
  (testing "an article before a common-noun parameter goes when the noun becomes a name"
    ;; a clause written about a kind — "the ?animal glides" — applied to an individual,
    ;; where "the Zork glides" is the comment's grammar meeting an argument it did not
    ;; anticipate
    (tu/with-terms [glides Zork]
      (v/assert kb (list 'comment glides (str "(" glides " ?animal) means that the ?animal glides."))
                'CxUniverse)
      (let [t (:text (gloss/text kb (list glides Zork)))]
        (is (str/includes? t (str Zork " glides")))
        (is (not (str/includes? t (str "the " Zork))))))))

(tu/deftest-kb a-term-commented-in-two-contexts-reads-the-same-either-order
  ;; A term carries a believed `comment` in more than one context routinely — an
  ;; imported vocabulary's beside ours, a theory's beside the upper ontology's — and the
  ;; gloss composes from one of them.  Reading whichever the retrieval yielded first
  ;; makes the prose a reader is shown a fact about the order the KB was loaded in, which
  ;; nothing on the page could explain.
  (doseq [flip [false true]]
    (tu/with-terms [wobbles Zork CxFirst CxSecond]
      (v/assert kb (list 'genlCx CxFirst 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxSecond 'CxUniverse) 'CxUniverse)
      (let [comments [[(list 'comment wobbles
                             (str "(" wobbles " ?thing) means that ?thing sways.")) CxFirst]
                      [(list 'comment wobbles
                             (str "(" wobbles " ?thing) means that ?thing tilts.")) CxSecond]]
            ;; the pick is content-least over the sentence and its context, so the
            ;; expected verb is read off the same key rather than assumed
            least    (first (sort-by (fn [[s c]] (pr-str [s (str c)])) comments))
            [word other] (if (= least (first comments)) ["sways" "tilts"] ["tilts" "sways"])
            what     (str "the " (if flip "second" "first") " comment asserted first")]
        (doseq [[s c] (if flip (reverse comments) comments)] (v/assert kb s c))
        (let [{:keys [text source]} (gloss/text kb (list wobbles Zork))]
          (is (= :composed source) what)
          (is (str/includes? text word) (str what ": the content-least comment composed it"))
          (is (not (str/includes? text other)) what))))))

(tu/deftest-kb a-leading-term-keeps-its-own-spelling
  ;; upper-casing `siblingOf` into `SiblingOf` does not tidy a sentence, it renames a
  ;; predicate into something that is indistinguishable from an individual
  (let [t (:text (gloss/text kb '(symmetric siblingOf)))]
    (is (str/starts-with? t "siblingOf"))
    (is (not (str/starts-with? t "SiblingOf")))))

(tu/deftest-kb a-rule-reads-as-the-conditional-it-is
  (let [{:keys [text]} (gloss/text kb '(implies (and (bird ?x)) (flies ?x)))]
    (is (str/starts-with? text "If "))
    (is (str/includes? text ", then "))
    (testing "and its literals carry no appositions — a conditional dragging a dashed
             definition behind every term is not a sentence"
      (is (not (str/includes? text "—")))))
  (testing "a joined rule keeps the variables that join it"
    (let [t (:text (gloss/text kb '(implies (and (parentOf ?x ?y) (parentOf ?y ?z))
                                            (grandparentOf ?x ?z))))]
      (is (str/includes? t "x"))
      (is (str/includes? t "y"))
      (is (str/includes? t "z")))))

(tu/deftest-kb a-negation-says-so-without-rewriting-the-claim
  (let [{:keys [text]} (gloss/text kb '(not (flies Pingu)))]
    (is (str/includes? text "not true that"))
    (is (str/includes? text "Pingu"))))

;; ---- the guarantee -------------------------------------------------------

(tu/deftest-kb the-shipped-schema-glosses-without-a-model
  ;; the measurement the prompt asks for, asserted rather than reported: if this ever
  ;; falls, a comment lost its signature and the read path started needing a model
  (let [all (for [c (v/contexts kb), s (v/sentexes-in-context kb c {:believed? true})] s)
        by  (frequencies (map (comp :source #(gloss/readable kb %)) all))
        n   (count all)
        got (+ (:composed by 0) (:partial by 0))]
    (is (pos? n))
    (is (> (/ got n) 0.95)
        (str "only " got " of " n " shipped sentexes gloss from the KB's own words: " by))))

(tu/deftest-kb the-ordinary-path-cannot-reach-a-model
  ;; structural, not behavioural: `gloss` takes no provider, so a sentence over
  ;; documented vocabulary costs zero model calls by construction rather than by luck
  (is (= 2 (count (first (:arglists (meta #'gloss/gloss)))))))
