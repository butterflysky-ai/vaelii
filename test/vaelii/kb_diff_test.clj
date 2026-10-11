;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kb-diff-test
  "`kb-diff`: what two KBs disagree about, as content.

  The claim that makes it worth having is the one about **handles**.  Two KBs holding
  identical knowledge share not a single handle — handles are allocated in assertion
  order, so a reload renumbers everything — and a diff keyed on one would report a KB
  loaded from its own export as wholly changed.  The round-trip test here is that claim:
  export a KB as text, load it back into a second KB, and the two diff empty.

  The four buckets are then the four ways two KBs can differ about one sentence: it is
  new, it is gone, it holds in a different context, or it is stored in both and believed
  in only one.  A defeated default is the last of those, and it is the one a comparison
  of stored records alone would miss entirely."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.cli :as cli]
            [vaelii.impl.memory :as mem]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── two KBs, and temp directories ─────────────────────────────────────

(defn- side
  "One side of a comparison, on a space nothing else names."
  [tag]
  (v/open-kb {:backend :memory :space [::kb-diff tag] :recover? false}))

(defn- with-sides*
  "Run `(f a b)` on two independent in-RAM KBs, cleared afterwards."
  [f]
  (let [a (side :a), b (side :b)]
    (try (v/clear! a) (v/clear! b) (f a b)
         (finally (v/clear! a) (v/clear! b)))))

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-diff-" nm "-")
                                      (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- sentences [rows] (mapv :sentence rows))

;;; ── the four buckets ──────────────────────────────────────────────────

(deftest an-add-a-retract-a-defeated-default-and-a-move-land-in-four-buckets
  (with-sides*
    (fn [a b]
      (tu/with-terms [dog likes_cake Muffet Spot Rex Bess Tom CxOne CxTwo]
        (doseq [k [a b]]
          (v/assert k (list 'genlCx CxOne 'CxUniverse) 'CxUniverse)
          (v/assert k (list 'genlCx CxTwo 'CxUniverse) 'CxUniverse)
          (v/assert k (list dog Muffet) CxOne)
          ;; stored in both; defeated in `b` alone, below
          (v/assert k (list likes_cake Tom) CxOne))
        ;; an add: in b and not in a
        (v/assert b (list dog Rex) CxOne)
        ;; a retract: in a and not in b
        (v/assert a (list dog Spot) CxOne)
        ;; a move: the same sentence, a different context
        (v/assert a (list dog Bess) CxOne)
        (v/assert b (list dog Bess) CxTwo)
        ;; a defeated default: a known-true rival in `b` puts the default OUT there
        (v/assert b (list 'not (list likes_cake Tom)) CxOne {:strength :monotonic})
        (let [d (v/kb-diff a b)]
          (testing "what b has and a does not"
            (is (contains? (set (sentences (:added d))) (list dog Rex))))
          (testing "what a has and b does not"
            (is (= [(list dog Spot)] (sentences (:removed d)))))
          (testing "the same sentence, in another context, is a move and not a pair"
            (is (= [{:sentence (list dog Bess) :from CxOne :to CxTwo
                     :strength :default :premise? true}]
                   (:moved d)))
            (is (not (contains? (set (sentences (:added d))) (list dog Bess))))
            (is (not (contains? (set (sentences (:removed d))) (list dog Bess)))))
          (testing "stored in both, believed in one: the bucket a record comparison misses"
            (is (= [{:sentence (list likes_cake Tom) :context CxOne :strength :default
                     :premise? true :believed-in-a true :believed-in-b false}]
                   (:belief-changed d)))))))))

(deftest a-kb-differs-from-itself-in-nothing
  (with-sides*
    (fn [a _b]
      (tu/with-terms [dog Muffet CxSelf]
        (v/assert a (list 'genlCx CxSelf 'CxUniverse) 'CxUniverse)
        (v/assert a (list dog Muffet) CxSelf)
        (is (= {:added [] :removed [] :moved [] :belief-changed []}
               (v/kb-diff a a)))))))

(deftest the-two-directions-are-mirror-images
  (with-sides*
    (fn [a b]
      (tu/with-terms [dog Muffet Rex CxDir]
        (doseq [k [a b]]
          (v/assert k (list 'genlCx CxDir 'CxUniverse) 'CxUniverse)
          (v/assert k (list dog Muffet) CxDir))
        (v/assert b (list dog Rex) CxDir)
        (let [ab (v/kb-diff a b)
              ba (v/kb-diff b a)]
          (is (= (:added ab) (:removed ba)))
          (is (= (:removed ab) (:added ba))))))))

;;; ── derived sentexes, told apart by :premise? ─────────────────────────

(deftest a-conclusion-that-stopped-following-is-a-difference-and-says-it-is-derived
  ;; A derived sentex is not a premise anybody wrote, and comparing only premises would
  ;; call two KBs identical when one of them concludes something the other does not.
  (with-sides*
    (fn [a b]
      (tu/with-terms [bird flies Tweety CxDer]
        (doseq [k [a b]]
          (v/assert k (list 'genlCx CxDer 'CxUniverse) 'CxUniverse)
          (v/assert k (list 'set/forwardRule
                            (list 'implies (list bird '?b) (list flies '?b)))
                    CxDer)
          (v/assert k (list bird Tweety) CxDer))
        ;; only `a` has the fact that makes the rule fire a second time
        (tu/with-terms [Opus]
          (v/assert a (list bird Opus) CxDer)
          (let [d    (v/kb-diff a b)
                rows (:removed d)
                by   (group-by :premise? rows)]
            (testing "the premise somebody asserted"
              (is (= [(list bird Opus)] (sentences (get by true)))))
            (testing "and the conclusion that followed from it, marked as derived"
              (is (= [(list flies Opus)] (sentences (get by false)))))))))))

;;; ── the round trip: identical knowledge, no shared handle ─────────────

(deftest a-kb-and-its-own-text-export-diff-empty
  (let [dir (temp-dir "roundtrip")]
    (try
      (rm-rf! dir)
      (with-sides*
        (fn [a _b]
          (tu/with-terms [bird penguin flies Tweety Opus CxRt]
            (v/assert a (list 'genlCx CxRt 'CxUniverse) 'CxUniverse)
            (v/assert a (list bird Tweety) CxRt {:strength :monotonic})
            (v/assert a (list bird Opus) CxRt)
            (v/assert a (list penguin Opus) CxRt)
            (v/assert-rule a [(list bird '?b)] (list flies '?b) CxRt)
            (v/export-text! a (.getPath dir))
            (let [d (v/kb-diff a (.getPath dir))]
              (testing "a string side is read as a text KB, and the two hold the same knowledge"
                (is (= {:added [] :removed [] :moved [] :belief-changed []} d)))))))
      (finally (rm-rf! dir)))))

(defn- ram-spaces
  "Every space the memory backend's registries hold."
  []
  (set (concat (keys @@#'mem/record-spaces) (keys @@#'mem/index-spaces))))

(deftest a-path-side-is-released-and-a-passed-kb-stays-open
  (let [dir (temp-dir "release"), bad (temp-dir "release-bad")]
    (try
      (rm-rf! dir)
      (spit (str (.getPath bad) "/CxBad.txt") "(dog\n")
      (with-sides*
        (fn [a _b]
          (tu/with-terms [dog Muffet CxRel]
            (v/assert a (list 'genlCx CxRel 'CxUniverse) 'CxUniverse)
            (v/assert a (list dog Muffet) CxRel)
            (v/export-text! a (.getPath dir))
            (let [before (ram-spaces)]
              (dotimes [_ 3] (v/kb-diff a (.getPath dir)))
              (v/kb-diff (.getPath dir) (.getPath dir))
              (is (thrown? clojure.lang.ExceptionInfo (v/kb-diff a (.getPath bad))))
              (is (= before (ram-spaces))
                  "a side read from a path, loaded or refused, leaves no space behind")
              (is (some? (v/handle-of a (list dog Muffet) CxRel))
                  "and the KB the caller passed is still open and readable")))))
      (finally (run! rm-rf! [dir bad])))))

;;; ── the same comparison from a shell line ─────────────────────────────

(deftest the-cli-diffs-two-text-exports
  (let [da (temp-dir "cli-a"), db (temp-dir "cli-b")]
    (try
      (run! rm-rf! [da db])
      (with-sides*
        (fn [a b]
          (tu/with-terms [dog Muffet Spot Rex CxCli]
            (doseq [k [a b]]
              (v/assert k (list 'genlCx CxCli 'CxUniverse) 'CxUniverse)
              (v/assert k (list dog Muffet) CxCli))
            (v/assert a (list dog Spot) CxCli)
            (v/assert b (list dog Rex) CxCli)
            (v/export-text! a (.getPath da))
            (v/export-text! b (.getPath db))
            ;; the shell hands `dispatch` data, and the KB the run opened is not either
            ;; side — both are read from disk, which is what makes `diff` a command about
            ;; two exports rather than about the KB in hand
            (let [d (cli/dispatch (v/open-kb {:backend :memory :space [::kb-diff :cli]})
                                  "diff" [(.getPath da) (.getPath db)] {})]
              (is (= [(list dog Rex)] (sentences (:added d))))
              (is (= [(list dog Spot)] (sentences (:removed d))))))))
      (finally (run! rm-rf! [da db])))))

(deftest the-cli-knows-diff-and-describe-and-says-what-they-take
  (testing "both are commands the driver dispatches"
    (is (contains? (set cli/commands) "diff"))
    (is (contains? (set cli/commands) "describe")))
  (testing "and `--help` lists them with their operands"
    (let [u (cli/usage)]
      (is (re-find #"diff\s+<a> <b>" u))
      (is (re-find #"describe <term>" u))
      (is (re-find #"--context" u))
      (is (re-find #"--nearest" u)))))

;;; ── what is deliberately not compared ─────────────────────────────────

(deftest provenance-and-handles-are-not-differences
  ;; Two KBs told the same knowledge by different creators, at different handles, hold the
  ;; same knowledge.  Saying otherwise would make every reload a diff and the read useless.
  (with-sides*
    (fn [a b]
      (tu/with-terms [dog Muffet Filler CxProv]
        (doseq [k [a b]]
          (v/assert k (list 'genlCx CxProv 'CxUniverse) 'CxUniverse))
        ;; `b` mints a handle for something `a` never had, then loses it — so the shared
        ;; content lands at different handles on the two sides
        (let [h (v/assert b (list dog Filler) CxProv)]
          (v/retract! b h))
        (binding [v/*creator* "ann"] (v/assert a (list dog Muffet) CxProv))
        (binding [v/*creator* "bob"] (v/assert b (list dog Muffet) CxProv))
        (is (not= (v/handle-of a (list dog Muffet) CxProv)
                  (v/handle-of b (list dog Muffet) CxProv))
            "the same sentence at two different handles")
        (is (= {:added [] :removed [] :moved [] :belief-changed []} (v/kb-diff a b))
            "and no difference, because neither the handle nor the creator is content")))))
