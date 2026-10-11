;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.membership-handles-test
  "A clash's membership lookup names a surviving exact membership without walking the
  term's other types up.

  `checks/membership-handles-led` leads from the term's postings and tests each type it
  holds with `genl?`, but `handle-namings` names the postings saying `(t x)` itself
  whenever one survives the filters, so the walks decided nothing then.
  `disjoint-problems` asks it of a term's asserted types, and a reader's re-read of its
  nogoods on a large KB spent most of its time in those walks.  Every answer must be the
  one the `matches-visible` reference (`res/*lead-side*` `:scoped`) gives, including
  when every exact posting is filtered out and the entailing ones are named."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private membership-handles @#'checks/membership-handles)

(defn- try! [kb s cx]
  (try (v/assert kb s cx) (catch clojure.lang.ExceptionInfo _ nil)))

(defn- random-world!
  "A hierarchy of ten types, two contexts, individuals holding one to four types each,
  some of them stated in both contexts, `except`s in the lower context hiding some of the
  memberships, and a merge of two individuals the lower context sees.  Answers what the
  lookup is asked over."
  [kb ^java.util.Random rnd]
  (let [base  (tu/tmp-ctx)
        sub   (tu/tmp-ctx)
        types (vec (repeatedly 10 #(tu/fresh-term :type 'kind_t)))
        inds  (vec (repeatedly 6 #(tu/fresh-term :individual 'Ind)))
        pick  (fn [v] (v (.nextInt rnd (count v))))
        cx    #(if (zero? (.nextInt rnd 3)) sub base)
        held  (atom [])]
    (v/assert kb (list 'genlCx sub base) 'CxUniverse)
    (doseq [i (range 1 (count types)), _ (range (inc (.nextInt rnd 2)))]
      (try! kb (list 'genl (types i) (types (.nextInt rnd i))) base))
    (doseq [x inds, _ (range (inc (.nextInt rnd 4)))]
      (let [t (pick types)]
        (doseq [c (if (zero? (.nextInt rnd 4)) [base sub] [(cx)])]
          (when-let [h (try! kb (list t x) c)]
            (swap! held conj h)))))
    (doseq [h @held :when (zero? (.nextInt rnd 3))]
      (try! kb (list 'except (list 'sentexHandle h)) sub))
    (try! kb (list 'sameAs (inds 0) (inds 1)) sub)
    {:types types :inds inds :ctxs [base sub '?c]}))

(defn- postings
  "The stored memberships of `x` saying `(t x)` and the ones stating another type."
  [kb t x]
  (let [ss (keep #(p/get-sentex (:records kb) %) (reads/as-stored-with-arg-global (:index kb) 1 x))]
    (group-by #(= (list t x) (:sentence %)) ss)))

(deftest the-lookup-names-what-the-matches-visible-reference-names
  (let [rnd   (java.util.Random. 2718)
        arms  (atom {})]
    (dotimes [trial 10]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [{:keys [types inds ctxs]} (random-world! kb rnd)
              tax (reasoning/taxonomy kb)]
          (doseq [x inds, t types, c ctxs]
            (let [led   (vec (membership-handles kb t x c))
                  ref   (vec (binding [res/*lead-side* :scoped] (membership-handles kb t x c)))
                  {exact true other false} (postings kb t x)
                  said? (fn [h] (= (list t x) (:sentence (p/get-sentex (:records kb) h))))
                  below (some #(and (not= t (first (:sentence %)))
                                    (tax/genl? tax (first (:sentence %)) t c))
                              other)]
              (is (= ref led) (str "trial " trial " " (list t x) " at " c))
              (cond
                (and (seq exact) (seq led) (not-any? said? led))
                (swap! arms update :exact-filtered-entailed-named (fnil inc 0))
                (and (seq led) (every? said? led) below)
                (swap! arms update :exact-named-over-entailed (fnil inc 0))))))))
    (is (pos? (:exact-filtered-entailed-named @arms 0))
        "an exact posting is filtered out and the entailing ones are named")
    (is (pos? (:exact-named-over-entailed @arms 0))
        "an exact match is named where an entailing one survives beside it")))

(deftest an-exact-membership-walks-no-other-type-up
  ;; `x` holds `t` and ten types under chains of their own, so a walk from each of them
  ;; up to `t` is a miss that climbs the chain
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [cx    (tu/tmp-ctx)
          t     (tu/fresh-term :type 'held_t)
          x     (tu/fresh-term :individual 'Ind)
          k     10]
      (dotimes [_ k]
        (let [chain (vec (repeatedly 6 #(tu/fresh-term :type 'chain_t)))]
          (doseq [i (range 1 (count chain))]
            (v/assert kb (list 'genl (chain (dec i)) (chain i)) cx))
          (v/assert kb (list (chain 0) x) cx)))
      (let [h     (v/assert kb (list t x) cx)
            walks (atom 0)
            real  tax/genl?]
        (with-redefs [tax/genl? (fn [& args] (swap! walks inc) (apply real args))]
          (is (= [h] (vec (membership-handles kb t x cx))) "the exact membership is named"))
        (is (zero? @walks) (str @walks " genl? walks beside a surviving exact membership"))))))

(deftest an-exact-membership-is-read-by-its-own-path
  ;; `x` holds `t` and a hundred facts at argument 1: the exact membership is read under
  ;; every context by its path, and the postings, every fact holding `x`, are not read
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [cx   (tu/tmp-ctx)
          t    (tu/fresh-term :type 'held_t)
          x    (tu/fresh-term :individual 'Ind)
          pred (tu/fresh-term :predicate 'relOf)]
      (dotimes [_ 100]
        (v/assert kb (list pred x (tu/fresh-term :individual 'Other)) cx))
      (let [h     (v/assert kb (list t x) cx)
            reads (atom 0)
            real  reads/as-stored-with-arg-global]
        (with-redefs [reads/as-stored-with-arg-global (fn [& args] (swap! reads inc) (apply real args))]
          (is (= [h] (vec (membership-handles kb t x cx))) "the exact membership is named"))
        (is (zero? @reads) (str @reads " reads of the term's postings"))))))
