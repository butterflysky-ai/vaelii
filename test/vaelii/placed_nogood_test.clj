;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.placed-nogood-test
  "A nogood places its conclusions as a firing does: `(contradicts …)` and the `defeat` of
  a unique weakest member at the maximal common descendants of its members and grounds,
  justified by them (`chain/place-nogood!`).  A `defeat` is a meta-sentex only the engine
  derives, kept in a roster by the handle it names (docs/glossary.md, `defeat`).

  Every test states its lattice in a comment, since the answer is a function of it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [clojure.walk]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- refusal-type
  "The `:type` `assert` throws for `sentence` in `context`, or nil when it stores it."
  [kb sentence context]
  (try (v/assert kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb assert-refuses-defeat-in-every-literal
  (tu/with-terms [cat dog Rex CxA]
    (let [h (v/assert kb (list cat Rex) CxA)
          d (list 'defeat (list 'sentexHandle h))]
      (testing "a fact, its negation, a rule's consequent and antecedent, an exceptWhen query"
        (is (= [:derived-only :derived-only :derived-only :derived-only :derived-only]
               (mapv #(refusal-type kb % CxA)
                     [d
                      (list 'not d)
                      (list 'implies (list dog '?x) (list 'defeat '?x))
                      (list 'implies (list 'defeat '?x) (list dog '?x))
                      (list 'exceptWhen (list 'defeat '?x)
                            (list 'implies (list cat '?x) (list dog '?x)))]))))
      (testing "check predicts the refusal"
        (is (= :derived-only (:type (first (v/check kb d CxA))))))
      (testing "the index holds no defeat, and a defeat pattern is still matchable"
        (is (not (reads/stores-any? (:index kb) 'defeat)))
        (is (empty? (v/sentexes-matching kb '(defeat ?h) '?ctx)))))))

(defn- resolved
  "`form` with each `(sentexHandle h)` replaced by `[sentence context]` of `h`."
  [kb form]
  (if (and (seq? form) (= 'sentexHandle (first form)))
    (let [s (v/sentex kb (second form))] [(:sentence s) (:context s)])
    (if (seq? form) (map #(resolved kb %) form) form)))

(defn- placed
  "The stored `contradicts` and `defeat` sentexes, as `[resolved-sentence context]`."
  [kb]
  (into #{} (for [f '[contradicts defeat]
                  s (v/sentexes-with-functor kb f)]
              [(resolved kb (:sentence s)) (:context s)])))

(defn- sole
  "The one element of `xs`, which must hold exactly one."
  [xs]
  (is (= 1 (count xs)))
  (first xs))

(defn- place!
  "Place the nogood over `members` and `grounds`, and settle, as a write does."
  [kb members grounds]
  (let [hs (chain/place-nogood! kb members grounds)]
    (settle/settle kb)
    hs))

(defn- lattice!
  "CxA and CxB under CxUniverse, CxD under both."
  [kb CxA CxB CxD]
  (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
  (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx CxD c) 'CxUniverse)))

(tu/deftest-kb a-nogood-is-placed-at-the-common-descendant-of-its-members-and-grounds
  ;;   CxUniverse  (excludesType dog cat), a ground no nogood family reads
  ;;     ├─ CxA    (cat Rex) default
  ;;     └─ CxB    (dog Rex) monotonic
  ;;          CxD under both
  (tu/with-terms [cat dog Rex excludesType CxA CxB CxD]
    (lattice! kb CxA CxB CxD)
    (let [l (v/assert kb (list cat Rex) CxA)
          w (v/assert kb (list dog Rex) CxB {:strength :monotonic})
          g (v/assert kb (list excludesType dog cat) 'CxUniverse)
          L [(list cat Rex) CxA]
          W [(list dog Rex) CxB]]
      (place! kb #{l w} #{g})
      (testing "a contradicts naming the members in content order and the defeat of the loser"
        (is (= #{[(list 'contradicts L W) CxD] [(list 'defeat L) CxD]} (placed kb)))
        (is (every? #(v/in? kb (:id %)) (concat (v/sentexes-with-functor kb 'contradicts)
                                                (v/sentexes-with-functor kb 'defeat)))))
      (testing "a second detection, members in another order, stores nothing new"
        (let [before (v/sentex-count kb)]
          (is (empty? (place! kb [w l] [g])))
          (is (= before (v/sentex-count kb)))
          (is (= 1 (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= 1 (count (:support (v/why kb (:id (sole (v/sentexes-with-functor kb 'contradicts))))))))))
      (testing "why names the members, the ground and the genlCx edges CxD sees them over"
        (let [d     (:id (sole (v/sentexes-with-functor kb 'defeat)))
              antes (into #{} (comp (mapcat :because) (map :handle)) (:support (v/why kb d)))]
          (is (= [chain/nogood-informant] (mapv :informant (:support (v/why kb d)))))
          (is (= #{l w g} (into #{} (remove #(= 'genlCx (first (:sentence (v/sentex kb %))))) antes)))
          (is (every? (into #{} (comp (map #(:sentence (v/sentex kb %))) (filter #(= 'genlCx (first %))))
                            antes)
                      [(list 'genlCx CxD CxA) (list 'genlCx CxD CxB)]))))
      (testing "the defeat is in the index by its target"
        (is (= #{l} (reads/as-stored-named-global (:index kb) 'defeat)))))))

(tu/deftest-kb a-dilemma-and-a-conflict-place-a-contradicts-and-no-defeat
  (tu/with-terms [cat dog Rex Tom excludesType CxA]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (let [g  (v/assert kb (list excludesType dog cat) 'CxUniverse)
          l1 (v/assert kb (list cat Rex) CxA)
          l2 (v/assert kb (list dog Rex) CxA)
          m1 (v/assert kb (list cat Tom) CxA {:strength :monotonic})
          m2 (v/assert kb (list dog Tom) CxA {:strength :monotonic})]
      (place! kb #{l1 l2} #{g})
      (place! kb #{m1 m2} #{g})
      (is (= 2 (count (v/sentexes-with-functor kb 'contradicts))))
      (is (empty? (v/sentexes-with-functor kb 'defeat))))))

(defn- retracting-takes-it-out
  "Place the nogood of `a-nogood-is-placed-…`, retract the handle `pick` chooses, and
  answer what stays placed."
  [pick]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog Rex excludesType CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [hs {:l (v/assert kb (list cat Rex) CxA)
                :w (v/assert kb (list dog Rex) CxB {:strength :monotonic})
                :g (v/assert kb (list excludesType dog cat) 'CxUniverse)}]
        (place! kb #{(:l hs) (:w hs)} #{(:g hs)})
        (v/retract! kb (pick hs))
        [(placed kb) (reads/as-stored-named-global (:index kb) 'defeat)]))))

(tu/deftest-kb retracting-a-member-or-a-ground-takes-the-placed-sentexes-out
  (doseq [k [:l :w :g]]
    (is (= [#{} #{}] (retracting-takes-it-out k)) (str "retracting " k))))

(defn- placed-after
  "The placed sentexes once `ops` run in order on a fresh KB: each asserts one sentence of
  the nogood of `a-nogood-is-placed-…` over a `disjoint` ground, or the edge `(genlCx CxB
  CxA)`; the nogood is placed once its two members and its ground are stored.  The
  `disjoint` ground makes the nogood the membership family's, whose detection the edge
  reaches (`chain/place-memberships!`)."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog Rex CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [hs (reduce (fn [hs op]
                         (let [hs (assoc hs op
                                         (case op
                                           :l    (v/assert kb (list cat Rex) CxA)
                                           :w    (v/assert kb (list dog Rex) CxB {:strength :monotonic})
                                           :g    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
                                           :edge (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)))]
                           (when (and (not= :edge op) (every? hs [:l :w :g]))
                             (place! kb #{(:l hs) (:w hs)} #{(:g hs)}))
                           hs))
                       {} ops)]
        (assert (every? hs [:l :w :g :edge]))
        ;; the generated names differ per run, so the placement is read by role
        (let [names {cat 'cat dog 'dog Rex 'Rex CxA 'CxA CxB 'CxB CxD 'CxD}]
          (clojure.walk/postwalk #(get names % %) (placed kb)))))))

(tu/deftest-kb a-context-edge-arriving-after-the-nogood-places-it-as-arriving-first-does
  ;; (genlCx CxB CxA) makes CxB a common descendant of both members, above CxD
  (let [first-edge (placed-after [:edge :l :w :g])
        last-edge  (placed-after [:l :w :g :edge])]
    (is (= #{[(list 'contradicts [(list 'cat 'Rex) 'CxA] [(list 'dog 'Rex) 'CxB]) 'CxB]
             [(list 'defeat [(list 'cat 'Rex) 'CxA]) 'CxB]}
           first-edge))
    (is (= first-edge last-edge))))

(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(tu/deftest-kb every-arrival-order-of-the-members-the-ground-and-the-edge-places-the-same
  (is (= 1 (count (into #{} (map placed-after) (permutations [:l :w :g :edge]))))))

(defn- negation-placed-after
  "The placed sentexes and the counts of placed sentexes and their justifications once
  `ops` run in order on a fresh KB, over a negation pair and this lattice:

  ```
  CxUniverse
   ├─ CxA  (pp Rex)              :p
   └─ CxB  (not (pp Rex))        :n
       ├─ CxM                    :edge (genlCx CxM CxA)
       │   └─ CxL                :l    (genlCx CxL CxA)
       └─ CxS                    :s    (genlCx CxS CxA)
  ```

  With every op run the pair is placed at CxM and CxS: the edge retires the placement at
  CxL below its lower end and leaves the one at CxS, outside it."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pp Rex CxA CxB CxM CxL CxS]
      (doseq [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxM CxB] [CxL CxM] [CxS CxB]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (doseq [op ops]
        (case op
          :p    (v/assert kb (list pp Rex) CxA)
          :n    (v/assert kb (list 'not (list pp Rex)) CxB {:strength :monotonic})
          :l    (v/assert kb (list 'genlCx CxL CxA) 'CxUniverse)
          :s    (v/assert kb (list 'genlCx CxS CxA) 'CxUniverse)
          :edge (v/assert kb (list 'genlCx CxM CxA) 'CxUniverse)))
      (let [names {pp 'pp Rex 'Rex CxA 'CxA CxB 'CxB CxM 'CxM CxL 'CxL CxS 'CxS}
            sxs   (mapcat #(v/sentexes-with-functor kb %) '[contradicts defeat])]
        [(clojure.walk/postwalk #(get names % %) (placed kb))
         (count sxs)
         (count (mapcat #(v/supporting-justifications kb (:id %)) sxs))]))))

(tu/deftest-kb a-context-edge-re-places-a-negation-pair-alike-in-every-arrival-order
  (let [readings (into #{} (map negation-placed-after) (permutations [:p :n :l :s :edge]))]
    (is (= #{[#{[(list 'contradicts [(list 'not (list 'pp 'Rex)) 'CxB] [(list 'pp 'Rex) 'CxA]) 'CxM]
                [(list 'defeat [(list 'pp 'Rex) 'CxA]) 'CxM]
                [(list 'contradicts [(list 'not (list 'pp 'Rex)) 'CxB] [(list 'pp 'Rex) 'CxA]) 'CxS]
                [(list 'defeat [(list 'pp 'Rex) 'CxA]) 'CxS]}
              4 4]}
           readings))))

;; ---- the read walk -----------------------------------------------------------

(defn- self-hiding!
  "The lattice of design's self-hiding example, the nogood placed in CxD:

  ```
  CxUniverse     (excludesType dog cat)
   └─ CxA        (cat Rex)  :default      L
       └─ CxD    (dog Rex)  :monotonic    W
  ```

  Returns `{:l :w :g :d :c}`, the members, the ground, the defeat and the contradicts."
  [kb {:syms [cat dog Rex excludesType CxA CxD]}]
  (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
  (let [l (v/assert kb (list cat Rex) CxA)
        w (v/assert kb (list dog Rex) CxD {:strength :monotonic})
        g (v/assert kb (list excludesType dog cat) 'CxUniverse)]
    (place! kb #{l w} #{g})
    {:l l :w w :g g
     :d (:id (sole (filter #(= (list 'defeat (list 'sentexHandle l)) (:sentence %))
                           (v/sentexes-with-functor kb 'defeat))))
     :c (:id (sole (v/sentexes-with-functor kb 'contradicts)))}))

(tu/deftest-kb a-placed-defeat-hides-its-target-below-the-placement-and-not-above
  (tu/with-terms [cat dog Rex excludesType CxA CxD]
    (let [{:keys [l d c]} (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType
                                            'CxA CxA 'CxD CxD})]
      (testing "CxD does not believe the loser, and CxA does"
        (is (not (v/believed? kb l CxD)))
        (is (not (v/ask? kb (list cat Rex) CxD)))
        (is (v/believed? kb l CxA))
        (is (v/ask? kb (list cat Rex) CxA)))
      (testing "the defeat and the contradicts rest on the loser and stay believed at CxD"
        (is (v/believed? kb d CxD))
        (is (v/believed? kb c CxD)))
      (testing "the loser stays IN in the network"
        (is (jtms/in? (reasoning/tms kb) l)))
      (testing "the settle that placed it ran one pass"
        (is (= 1 (:passes @(reasoning/settle-stats kb))))))))

(defn- exemption-row
  "Self-hiding's nogood, with CxR below CxD asserting `(except H)` for the handle `pick`
  chooses: `[L believed at CxR, L believed at CxD, contradicts believed at CxR]`."
  [pick]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog Rex excludesType CxA CxD CxR]
      (let [hs (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType
                                 'CxA CxA 'CxD CxD})]
        (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
        (v/assert kb (list 'except (list 'sentexHandle (pick hs))) CxR {:strength :monotonic})
        [(v/believed? kb (:l hs) CxR) (v/believed? kb (:l hs) CxD) (v/believed? kb (:c hs) CxR)]))))

(tu/deftest-kb the-exemption-table-at-a-context-below-the-placement
  (testing "excepting the winner, the ground or the defeat brings the loser back at CxR alone"
    (is (= [true false false] (exemption-row :w)))
    (is (= [true false false] (exemption-row :g)))
    (is (= [true false true] (exemption-row :d))))
  (testing "excepting the loser hides it and the nogood at CxR"
    (is (= [false false false] (exemption-row :l)))))

(tu/deftest-kb a-defeat-hides-at-read-time-and-sweeps-nothing
  ;; design.md section A under the ruling: the rule in CxA places M there, the rule in CxD
  ;; places P at CxD, and both stay IN in the network
  (tu/with-terms [cat dog Rex excludesType meows purrs CxA CxD]
    (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list meows '?x))) CxA)
    (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list purrs '?x))) CxD)
    (let [{:keys [l w]} (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType
                                          'CxA CxA 'CxD CxD})
          tms (reasoning/tms kb)
          m   (v/handle-of kb (list meows Rex) CxA)
          p   (v/handle-of kb (list purrs Rex) CxD)]
      (testing "P stays IN in the network and is not believed at CxD"
        (is (jtms/in? tms p))
        (is (not (v/ask? kb (list purrs Rex) CxD))))
      (testing "M is believed at CxA and not at CxD"
        (is (v/ask? kb (list meows Rex) CxA))
        (is (not (v/ask? kb (list meows Rex) CxD))))
      (testing "retracting the winner changes no label but the placed sentexes'"
        (let [labels #(mapv (fn [h] (jtms/in? tms h)) [l m p])]
          (is (= [true true true] (labels)))
          (v/retract! kb w)
          (is (= [true true true] (labels)))
          (is (empty? (placed kb)))
          (is (v/ask? kb (list purrs Rex) CxD)))))))

(tu/deftest-kb an-except-reaching-a-member-re-reads-the-class-at-that-reader
  ;; design.md section C:
  ;;   CxD   W = (dog Rex) :monotonic through X, :default through Y; L = (cat Rex) :default
  ;;    └─ CxR  (except X)
  (tu/with-terms [cat dog Rex excludesType pX pY purrs CxD CxR]
    (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule (list 'implies (list pX '?x) (list dog '?x))) CxD
              {:strength :monotonic})
    (v/assert kb (list 'set/forwardRule (list 'implies (list pY '?x) (list dog '?x))) CxD)
    (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list purrs '?x))) CxD)
    (let [x (v/assert kb (list pX Rex) CxD {:strength :monotonic})
          _ (v/assert kb (list pY Rex) CxD)
          l (v/assert kb (list cat Rex) CxD)
          w (v/handle-of kb (list dog Rex) CxD)
          g (v/assert kb (list excludesType dog cat) 'CxUniverse)
          purring #(into #{} (map (juxt :sentence :context)) (v/sentexes-with-functor kb purrs))]
      (is (= :monotonic (v/defeat-class kb w)))
      (place! kb #{l w} #{g})
      (let [before (purring)]
        (v/assert kb (list 'except (list 'sentexHandle x)) CxR {:strength :monotonic})
        (testing "CxR reads W as :default, the nogood as a dilemma, and believes L"
          (is (v/believed? kb l CxR))
          (is (not (v/believed? kb l CxD))))
        (testing "a firing from L is stored as it was before the except"
          (is (= before (purring)))
          (is (seq before)))))))

(defn- swept-after
  "`[placed fired]` once `ops` run in order on a fresh KB after `(pp Rex)` is stored in CxA:
  the stored `contradicts` and `defeat` sentexes and the stored `(rr Rex)`, by role.

  ```
  CxUniverse
   ├─ CxA   P = (pp Rex) :default
   └─ CxB   (not (pp Rex)) :monotonic          :neg
            rule (pp ?x) ⇒ (rr ?x)             :fire
        CxD under both: (except P)             :except
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pp rr Rex CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [p (v/assert kb (list pp Rex) CxA)]
        (doseq [op ops]
          (case op
            :neg    (v/assert kb (list 'not (list pp Rex)) CxB {:strength :monotonic})
            :fire   (v/assert kb (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))) CxB)
            :except (v/assert kb (list 'except (list 'sentexHandle p)) CxD {:strength :monotonic})))
        (let [names {pp 'pp rr 'rr Rex 'Rex CxA 'CxA CxB 'CxB CxD 'CxD}]
          (clojure.walk/postwalk #(get names % %)
                                 [(placed kb)
                                  (into #{} (map (juxt :sentence :context)) (v/sentexes-with-functor kb rr))]))))))

(tu/deftest-kb a-premise-except-sweeps-a-nogood-s-placement-as-it-sweeps-a-firing-s
  (testing "with no except, the pair and the firing are placed in CxD"
    (is (= [#{[(list 'contradicts [(list 'not (list 'pp 'Rex)) 'CxB] [(list 'pp 'Rex) 'CxA]) 'CxD]
              [(list 'defeat [(list 'pp 'Rex) 'CxA]) 'CxD]}
            #{[(list 'rr 'Rex) 'CxD]}]
           (swept-after [:neg :fire]))))
  (testing "an except of the member in CxD stores neither, in every arrival order"
    (is (= #{[#{} #{}]} (into #{} (map swept-after) (permutations [:neg :fire :except]))))))

(defn- closure-swept-after
  "`[with-except after-retract]` once `ops` run in order on a fresh KB after `P = (pp Rex)`
  is stored in CxA, the except asserted by `:except` and retracted last: each the kinds
  of sentex IN in the network at CxD, among `contradicts`, `defeat` and `(rr Rex)`.

  ```
  CxUniverse
   ├─ CxA   P = (pp Rex)   rule (pp ?x) ⇒ (qq ?x)          :rule
   └─ CxB   (not (qq Rex)) :monotonic                       :neg
            rule (qq ?x) ⇒ (rr ?x)                          :fire
        CxD under both: (except P)                          :except
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pp qq rr Rex CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [p   (v/assert kb (list pp Rex) CxA)
            e   (volatile! nil)
            tms (reasoning/tms kb)
            at  (fn [] (into #{} (for [f ['contradicts 'defeat rr]
                                       s (v/sentexes-with-functor kb f)
                                       :when (and (= CxD (:context s)) (jtms/in? tms (:id s)))]
                                   (if (= rr f) 'rr f))))]
        (doseq [op ops]
          (case op
            :rule   (v/assert kb (list 'set/forwardRule (list 'implies (list pp '?x) (list qq '?x))) CxA)
            :neg    (v/assert kb (list 'not (list qq Rex)) CxB {:strength :monotonic})
            :fire   (v/assert kb (list 'set/forwardRule (list 'implies (list qq '?x) (list rr '?x))) CxB)
            :except (vreset! e (v/assert kb (list 'except (list 'sentexHandle p)) CxD {:strength :monotonic}))))
        (let [with (at)]
          (v/retract! kb @e)
          [with (at)])))))

(tu/deftest-kb an-except-sweeps-what-rests-on-its-target-and-retracting-it-restores-it
  (is (= #{[#{} #{'contradicts 'defeat 'rr}]}
         (into #{} (map closure-swept-after) (permutations [:rule :neg :fire :except])))
      "nothing resting on P stays at CxD in any order, and every placement comes back"))

(defn- grounded-reading
  "Two decided nogoods, one defeating the other's dependency: nogood N1 grounded on G, and
  nogood N2 with G its unique weakest member.
  `ops` asserts the sentences in order, each nogood placed once its sentences are stored.
  Answers `[G believed, (kitten Rex) believed]` at CxA.

  ```
  CxA  G = (subKind kitten cat) :default    H = (fixedKind kitten) :monotonic
       (dog Rex) :monotonic                 (kitten Rex) :default
  N2 = {G, H}, ground (excludesFact subKind fixedKind)
  N1 = {(dog Rex), (kitten Rex)}, grounds G and (excludesType dog cat)
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog kitten Rex subKind fixed_kind excludesType excludesFact CxA]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (let [g1 (v/assert kb (list excludesType dog cat) 'CxUniverse)
            g2 (v/assert kb (list excludesFact subKind fixed_kind) 'CxUniverse)
            hs (reduce (fn [hs op]
                         (let [hs (assoc hs op
                                         (case op
                                           :G  (v/assert kb (list subKind kitten cat) CxA)
                                           :H  (v/assert kb (list fixed_kind kitten) CxA {:strength :monotonic})
                                           :M1 (v/assert kb (list dog Rex) CxA {:strength :monotonic})
                                           :M2 (v/assert kb (list kitten Rex) CxA)))]
                           (when (and (#{:G :H} op) (every? hs [:G :H]))
                             (place! kb #{(:G hs) (:H hs)} #{g2}))
                           (when (and (#{:G :M1 :M2} op) (every? hs [:G :M1 :M2]))
                             (place! kb #{(:M1 hs) (:M2 hs)} #{(:G hs) g1}))
                           hs))
                       {} ops)]
        [(v/believed? kb (:G hs) CxA) (v/believed? kb (:M2 hs) CxA)]))))

(tu/deftest-kb a-defeat-resting-on-a-defeated-ground-gives-one-reading-in-every-order
  ;; A depth-two shape: N2 defeats N1's ground, N1 does not reach N2, and N1's defeat is
  ;; not in force.  The mutual case, each nogood's loser a dependency of the other through
  ;; a rule-derived ground, is `a-defeat-dependency-cycle-is-broken-in-content-order`.
  (is (= #{[false true]} (into #{} (map grounded-reading) (permutations [:G :H :M1 :M2])))))

(tu/deftest-kb why-not-names-the-placed-defeat
  ;;   CxD   (cat Rex) :default and (dog Rex) :monotonic, the nogood placed in CxD
  (tu/with-terms [cat dog Rex excludesType CxD]
    (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
    (let [l (v/assert kb (list cat Rex) CxD)
          w (v/assert kb (list dog Rex) CxD {:strength :monotonic})
          g (v/assert kb (list excludesType dog cat) 'CxUniverse)]
      (place! kb #{l w} #{g})
      (let [d (:id (sole (v/sentexes-with-functor kb 'defeat)))
            r (v/why-not kb l)]
        (is (= :defeated (:reason r)))
        (is (= [d] (:defeats r)))
        (is (= [w] (mapv :handle (:contradicted-by r))))))))

(tu/deftest-kb a-placed-defeat-requeues-the-guards-watching-its-target
  ;; `(unknown (cat Rex))` holds at CxD once the defeat hides L there
  (tu/with-terms [cat dog Rex excludesType barks CxA CxD]
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list dog '?x) (list 'unknown (list cat '?x)))
                             (list barks '?x)))
              CxD)
    (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType 'CxA CxA 'CxD CxD})
    (is (v/ask? kb (list barks Rex) CxD))))

(tu/deftest-kb an-except-moving-a-defeat-s-force-requeues-the-guards-watching-its-target
  ;;   CxA  (cat Rex) default        CxD under CxA  (not (cat Rex)) monotonic
  ;;   CxR under CxD  (pp ?x) & (unknown (cat ?x)) => (rr ?x),  (pp Rex)
  ;; The pair's defeat hides (cat Rex) at CxR, so (rr Rex) is concluded there.  An except
  ;; of the denial in CxR takes the defeat out of force there, which moves the target's
  ;; belief with no relabel of it, and the guard is decided again.
  (tu/with-terms [cat pp rr Rex CxA CxD CxR]
    (doseq [[c up] [[CxA 'CxUniverse] [CxD CxA] [CxR CxD]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse))
    (let [l (v/assert kb (list cat Rex) CxA)
          w (v/assert kb (list 'not (list cat Rex)) CxD {:strength :monotonic})]
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list pp '?x) (list 'unknown (list cat '?x)))
                               (list rr '?x)))
                CxR)
      (v/assert kb (list pp Rex) CxR)
      (is (v/ask? kb (list rr Rex) CxR) "the defeat hides the target, so the guard holds")
      (let [e (v/assert kb (list 'except (list 'sentexHandle w)) CxR)]
        (is (v/believed? kb l CxR) "the except takes the defeat out of force at CxR")
        (is (not (v/ask? kb (list rr Rex) CxR)) "and the guard is decided again")
        (v/retract! kb e)
        (is (v/ask? kb (list rr Rex) CxR) "retracting the except restores the conclusion")))))

(defn- guarded-rule
  "The rule `pp ⇒ rr` guarded by `(cat ?x)`, as an `(unknown …)` antecedent (`:unknown`)
  or as an `exceptWhen` exception (`:except`)."
  [arm pp cat rr]
  (case arm
    :unknown (list 'set/forwardRule
                   (list 'implies (list 'and (list pp '?x) (list 'unknown (list cat '?x)))
                         (list rr '?x)))
    :except  (list 'exceptWhen (list cat '?x)
                   (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))))))

(defn- guard-through-a-defeated-edge
  "`[rr believed? (cat Rex) believed?]` at CxA after the writes `ops`, in order.

  ```
  CxA  (disjoint dog cat) M   (poodle Rex) M   (pp Rex)
       E = (genl poodle dog) :default          L = (cat Rex) :default     (:edge, :cat)
       (not (genl poodle dog)) M                                         (:neg)
       the guarded rule pp ⇒ rr, guarded by (cat ?x)                     (:rule)
  ```

  The membership nogood {(poodle Rex), L} climbs E and places D_M, the defeat of L, resting
  on E.  The negation pair on E places D_E, the defeat of E.  D_E takes D_M out of force,
  so L is believed and the guard holds."
  [arm ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog poodle pp rr Rex CxA]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) CxA {:strength :monotonic})
      (v/assert kb (list poodle Rex) CxA {:strength :monotonic})
      (v/assert kb (list pp Rex) CxA)
      (let [l (reduce (fn [l op]
                        (case op
                          :edge (do (v/assert kb (list 'genl poodle dog) CxA) l)
                          :neg  (do (v/assert kb (list 'not (list 'genl poodle dog)) CxA
                                              {:strength :monotonic})
                                    l)
                          :cat  (v/assert kb (list cat Rex) CxA)
                          :rule (do (v/assert kb (guarded-rule arm pp cat rr) CxA) l)))
                      nil ops)]
        [(v/ask? kb (list rr Rex) CxA) (v/believed? kb l CxA)]))))

(tu/deftest-kb a-defeat-taking-another-defeat-out-of-force-requeues-the-guards-watching-its-target
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (is (= #{[false true]}
             (into #{} (map #(guard-through-a-defeated-edge arm %))
                   (permutations [:edge :neg :cat :rule])))))))

(tu/deftest-kb an-except-lowering-a-nogood-member-s-class-requeues-the-guards-watching-the-loser
  ;;   CxD  (disjoint dog cat) M   X = (xx Rex) M   Y = (yy Rex) :default
  ;;        (xx ?a) => (dog ?a) M   (yy ?a) => (dog ?a) M   L = (cat Rex) :default
  ;;        W = (dog Rex): :monotonic through X, :default through Y; D defeats L, rests on W
  ;;   CxR under CxD   the guarded rule pp => rr,  (pp Rex)
  ;; An except of X in CxR leaves W :default there, so the nogood is a dilemma at CxR and L
  ;; is believed there (design section C).  D rests on X only through W.
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [cat dog xx yy pp rr Rex CxD CxR]
          (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
          (v/assert kb (list 'disjoint dog cat) CxD {:strength :monotonic})
          (doseq [p [xx yy]]
            (v/assert kb (list 'set/forwardRule (list 'implies (list p '?a) (list dog '?a))) CxD
                      {:strength :monotonic}))
          (let [x (v/assert kb (list xx Rex) CxD {:strength :monotonic})
                _ (v/assert kb (list yy Rex) CxD)
                l (v/assert kb (list cat Rex) CxD)]
            (v/assert kb (guarded-rule arm pp cat rr) CxR)
            (v/assert kb (list pp Rex) CxR)
            (is (= [false true] [(v/believed? kb l CxR) (v/ask? kb (list rr Rex) CxR)])
                "D hides L at CxR, so the guard does not hold")
            (let [e (v/assert kb (list 'except (list 'sentexHandle x)) CxR)]
              (is (= [true false] [(v/believed? kb l CxR) (v/ask? kb (list rr Rex) CxR)])
                  "the except leaves D out of force at CxR, and the guard is decided again")
              (v/retract! kb e)
              (is (= [false true] [(v/believed? kb l CxR) (v/ask? kb (list rr Rex) CxR)])
                  "retracting the except gives the firing back"))))))))

(defn- guard-through-a-lowering-except
  "`[rr at CxD, rr at CxR, rr at CxR once the except is retracted]` after the writes `ops`,
  in order, with the members' side stated in `wctx` (`:a` or `:d`), and the except naming
  X (`target` `:x`) or the disjointness (`:ground`).

  ```
  CxA                (disjoint dog cat) M   Y = (yy Rex) :default
                     (xx ?a) => (dog ?a) M   (yy ?a) => (dog ?a) M
                     X = (xx Rex) M                                         (:x)
                     W = (dog Rex): :monotonic through X, :default through Y
   └─ CxD            L = (cat Rex) :default; D defeats L, resting on W      (:cat)
                     (pp Rex)                                               (:pp)
                     the guarded rule pp => rr, guarded by (cat ?x)        (:g)
       └─ CxR        (except X)                                             (:except)
  ```

  With `wctx` `:d` every CxA line is stated in CxD.  At CxD, D hides L, so the firing
  F = (rr Rex) is placed at CxD.  At CxR the except leaves W :default, the nogood is a
  dilemma there, L is believed, and the guard holds (design ruling 23).  An except of the
  disjointness hides D's ground at CxR, with the same reading."
  [arm wctx target ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog xx yy pp rr Rex CxA CxD CxR]
      (let [w ({:a CxA :d CxD} wctx)]
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
        (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
        (let [g (v/assert kb (list 'disjoint dog cat) w {:strength :monotonic})
              _ (doseq [p [xx yy]]
                  (v/assert kb (list 'set/forwardRule (list 'implies (list p '?a) (list dog '?a))) w
                            {:strength :monotonic}))
              _ (v/assert kb (list yy Rex) w)
              [_ e] (reduce (fn [[x e] op]
                              (case op
                                :x      [(v/assert kb (list xx Rex) w {:strength :monotonic}) e]
                                :pp     (do (v/assert kb (list pp Rex) CxD) [x e])
                                :g      (do (v/assert kb (guarded-rule arm pp cat rr) CxD
                                                      {:strength :monotonic})
                                            [x e])
                                :cat    (do (v/assert kb (list cat Rex) CxD) [x e])
                                :except [x (v/assert kb (list 'except (list 'sentexHandle ({:x x :ground g} target)))
                                                     CxR)]))
                            [nil nil] ops)
              read  [(v/ask? kb (list rr Rex) CxD) (v/ask? kb (list rr Rex) CxR)]]
          (v/retract! kb e)
          (conj read (v/ask? kb (list rr Rex) CxR)))))))

(def ^:private lowering-except-orders
  ;; every order of the four writes, the except right after X and last
  (into [] (comp (mapcat (fn [ops] (let [[pre post] (split-with #(not= :x %) ops)]
                                     [(concat ops [:except]) (concat pre [:x :except] (rest post))])))
                 (distinct))
        (permutations [:x :pp :g :cat])))

(defn- lowering-except-readings [target orders]
  (doseq [arm [:unknown :except], wctx [:a :d]]
    (testing [arm wctx]
      (is (= #{[true false true]}
             (into #{} (map #(guard-through-a-lowering-except arm wctx target %)) orders))))))

(tu/deftest-kb ^:slow a-guard-holding-below-through-a-lowering-except-places-its-defeat-at-the-except
  (lowering-except-readings :x lowering-except-orders))

(tu/deftest-kb sampled-orders-place-a-guard-defeat-at-a-lowering-except
  ;; The sampled twin: every seventh order, the except last and right after X among them.
  (lowering-except-readings :x (take-nth 7 lowering-except-orders)))

(tu/deftest-kb a-guard-holding-below-through-an-except-of-the-ground-places-its-defeat-at-the-except
  (lowering-except-readings :ground (take-nth 7 lowering-except-orders)))

(defn- guard-through-a-ground-defeated-below
  "`[rr at CxD, rr at CxR, rr at CxR once the denial is retracted]` after the writes
  `ops`, in order.

  ```
  CxD          (disjoint dog cat) M   (poodle Rex) M   (pp Rex)
               E = (genl poodle dog) :default                              (:edge)
               L = (cat Rex) :default; D_M defeats L, resting on E         (:cat)
               the guarded rule pp => rr, guarded by (cat ?x)             (:rule)
   └─ CxR      (not (genl poodle dog)) M; D_E defeats E at CxR             (:neg)
  ```

  At CxD, D_M hides L, so the firing F = (rr Rex) is placed at CxD.  At CxR, D_E hides E,
  D_M rests on E and is out of force there, L is believed, and the guard holds."
  [arm ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog poodle pp rr Rex CxD CxR]
      (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) CxD {:strength :monotonic})
      (v/assert kb (list poodle Rex) CxD {:strength :monotonic})
      (v/assert kb (list pp Rex) CxD)
      (let [n    (reduce (fn [n op]
                           (case op
                             :edge (do (v/assert kb (list 'genl poodle dog) CxD) n)
                             :neg  (v/assert kb (list 'not (list 'genl poodle dog)) CxR
                                             {:strength :monotonic})
                             :cat  (do (v/assert kb (list cat Rex) CxD) n)
                             :rule (do (v/assert kb (guarded-rule arm pp cat rr) CxD) n)))
                         nil ops)
            read [(v/ask? kb (list rr Rex) CxD) (v/ask? kb (list rr Rex) CxR)]]
        (v/retract! kb n)
        (conj read (v/ask? kb (list rr Rex) CxR))))))

(tu/deftest-kb a-guard-holding-below-through-a-defeat-of-the-ground-places-its-defeat-at-that-defeat
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (is (= #{[true false true]}
             (into #{} (map #(guard-through-a-ground-defeated-below arm %))
                   (permutations [:edge :neg :cat :rule])))))))

(defn- breed-cycle
  "The reading of the defeat-dependency cycle after the writes `ops`, in order:
  `[L1 L2 G1 G2]` believed at CxA, each asked alone, then L1 and L2 hidden at CxA in one
  read asking L1 first, and in one read asking L2 first.  When `ops` holds `:ex`, `:r`
  and `:s` are the same three readings at CxR and CxS.

  ```
  CxA  (disjoint dog cat) M   (disjoint bird fish) M   (poodle Rex) M   (sparrow Tweety) M
       (dog_breed poodle) M   (bird_breed sparrow) M
       L1 = (cat Rex) :default                                                  (:l1)
       L2 = (fish Tweety) :default                                              (:l2)
       R1 = (fish ?x) & (dog_breed ?t) => (genl ?t dog)                         (:r1)
       R2 = (cat ?x) & (bird_breed ?t) => (genl ?t bird)                        (:r2)
  CxR under CxA   (except G), G the ground of the defeat whose loser is first,
                  written at its position or once G is stored                   (:ex)
  CxS under CxA, beside CxR
  G1 = (genl poodle dog) from R1 over L2;  G2 = (genl sparrow bird) from R2 over L1
  D1 defeats L1 and rests on G1;  D2 defeats L2 and rests on G2
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog fish bird poodle sparrow dog_breed bird_breed Rex Tweety CxA CxR CxS]
      (doseq [[c up] [[CxA 'CxUniverse] [CxR CxA] [CxS CxA]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (doseq [s [(list 'disjoint dog cat) (list 'disjoint bird fish) (list poodle Rex)
                 (list sparrow Tweety) (list dog_breed poodle) (list bird_breed sparrow)]]
        (v/assert kb s CxA {:strength :monotonic}))
      (let [first (if (neg? (nm/compare-form [(list cat Rex) CxA] [(list fish Tweety) CxA])) :l1 :l2)
            rule  (fn [lit breed sup]
                    (list 'set/forwardRule
                          (list 'implies (list 'and (list lit '?x) (list breed '?t)) (list 'genl '?t sup))))
            g1s   (list 'genl poodle dog)
            g2s   (list 'genl sparrow bird)
            write (fn [op]
                    (case op
                      :l1 (v/assert kb (list cat Rex) CxA)
                      :l2 (v/assert kb (list fish Tweety) CxA)
                      :r1 (v/assert kb (rule fish dog_breed dog) CxA {:strength :monotonic})
                      :r2 (v/assert kb (rule cat bird_breed bird) CxA {:strength :monotonic})
                      :ex nil))
            except (fn [hs]
                     (let [g (v/handle-of kb (if (= :l1 first) g1s g2s) CxA)]
                       (if (and g (contains? hs :ex) (nil? (:ex hs)))
                         (assoc hs :ex (v/assert kb (list 'except (list 'sentexHandle g)) CxR))
                         hs)))
            hs    (reduce (fn [hs op] (except (assoc hs op (write op)))) {} ops)
            l1    (:l1 hs) l2 (:l2 hs)
            g1    (v/handle-of kb g1s CxA)
            g2    (v/handle-of kb g2s CxA)
            read  (fn [ctx hs] (let [hid (exc/defeat-hidden-fn kb ctx false)] (mapv #(boolean (hid %)) hs)))
            at    (fn [ctx] {:alone (mapv #(v/believed? kb % ctx) [l1 l2 g1 g2])
                             :l1-l2 (read ctx [l1 l2])
                             :l2-l1 (vec (rseq (read ctx [l2 l1])))})]
        (cond-> (assoc (at CxA) :first first)
          (:ex hs) (assoc :r (at CxR) :s (at CxS)))))))

(tu/deftest-kb a-defeat-dependency-cycle-is-broken-in-content-order
  ;; Each defeat rests, through a rule-derived :default type edge, on the other's loser
  ;; (design.md ruling 18).  The defeat whose loser is first in content order is in force:
  ;; its loser and the edge resting on it are hidden, and the other loser is believed.
  (let [readings (into #{} (map breed-cycle) (permutations [:l1 :l2 :r1 :r2]))
        {:keys [first]} (clojure.core/first readings)
        hidden   (if (= :l1 first) [true false] [false true])]
    (is (= #{{:first first
              :alone (if (= :l1 first) [false true true false] [true false false true])
              :l1-l2 hidden
              :l2-l1 hidden}}
           readings))))

(defn- excepted-cycle-readings
  "The except at CxR hides the first defeat's ground there, so that defeat is out of force
  at CxR for a reason outside the cycle, while the second defeat's ground and verdict
  stand: CxR reads the second in force.  CxA and CxS see no except and read ruling 18's
  answer."
  [orders]
  (let [readings (into #{} (map breed-cycle) orders)
        {:keys [first]} (clojure.core/first readings)
        ruling   (if (= :l1 first)
                   {:alone [false true true false] :l1-l2 [true false] :l2-l1 [true false]}
                   {:alone [true false false true] :l1-l2 [false true] :l2-l1 [false true]})
        excepted (if (= :l1 first)
                   {:alone [true false false true] :l1-l2 [false true] :l2-l1 [false true]}
                   {:alone [false true true false] :l1-l2 [true false] :l2-l1 [true false]})]
    (is (= #{(assoc ruling :first first :r excepted :s ruling)} readings))))

(tu/deftest-kb ^:slow a-cycle-whose-first-defeat-is-out-of-force-at-a-reader-puts-the-second-in-force-there
  (excepted-cycle-readings (permutations [:l1 :l2 :r1 :r2 :ex])))

(tu/deftest-kb sampled-orders-put-the-second-defeat-of-a-cycle-in-force-where-the-first-is-excepted
  ;; The sampled twin: every twelfth of the 120 orders.
  (excepted-cycle-readings (take-nth 12 (permutations [:l1 :l2 :r1 :r2 :ex]))))

(defn- ground-cycle
  "`{:first … :read [W G L]}`: which of G and L is first in content order, and W, G and L
  believed at L's context, after the writes `ops`, in order.  The ground G of the
  membership nogood over W and L is derived by a rule guarded by L (`:guard` and `:own`,
  with `arm` `:unknown` or `:except`), or by a rule over L (`:self`).

  ```
  CxA  (disjoint dog cat) M   W = (poodle Rex) M   (dog_breed poodle) M        (:w, :breed)
       :guard  (dog_breed ?t) & (poodle ?x) => (genl ?t dog), guarded by (cat ?x)  (:rule)
       :self   (dog_breed ?t) & (cat ?x) => (genl ?t dog)                          (:rule)
  CxB under CxA   L = (cat Rex) :default, in CxA under :own                        (:l)
  G = (genl poodle dog).  D defeats L at L's context and rests on G; under :guard and
  :own the guard defeat of G at L's context rests on L, and under :self G rests on L.
  ```"
  [shape arm ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog poodle dog_breed Rex CxA CxB]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) CxA {:strength :monotonic})
      (let [conc (list 'genl '?t dog)
            lctx (if (= :own shape) CxA CxB)
            rule (case [(if (= :own shape) :guard shape) arm]
                   [:self nil]       (list 'set/forwardRule
                                           (list 'implies (list 'and (list dog_breed '?t) (list cat '?x)) conc))
                   [:guard :unknown] (list 'set/forwardRule
                                           (list 'implies (list 'and (list dog_breed '?t) (list poodle '?x)
                                                                (list 'unknown (list cat '?x)))
                                                 conc))
                   [:guard :except]  (list 'exceptWhen (list cat '?x)
                                           (list 'set/forwardRule
                                                 (list 'implies (list 'and (list dog_breed '?t) (list poodle '?x))
                                                       conc))))
            hs   (into {} (map (fn [op]
                                 [op (case op
                                       :w     (v/assert kb (list poodle Rex) CxA {:strength :monotonic})
                                       :breed (v/assert kb (list dog_breed poodle) CxA {:strength :monotonic})
                                       :rule  (v/assert kb rule CxA {:strength :monotonic})
                                       :l     (v/assert kb (list cat Rex) lctx))]))
                       ops)
            g    (v/handle-of kb (list 'genl poodle dog) CxA)]
        {:first (if (neg? (nm/compare-form [(list 'genl poodle dog) CxA] [(list cat Rex) lctx])) :g :l)
         :read  (mapv #(boolean (and % (v/believed? kb % lctx))) [(:w hs) g (:l hs)])}))))

(tu/deftest-kb a-guard-defeat-and-a-nogood-defeat-resting-on-each-other-are-broken-in-content-order
  ;; The guard defeat of G rests on its blocker L, and the defeat of L rests on G.  The one
  ;; whose target is first in content order is in force at CxB, and the other is not.
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (let [readings (into #{} (map #(ground-cycle :guard arm %)) (permutations [:w :breed :rule :l]))
            first    (:first (clojure.core/first readings))]
        (is (= #{{:first first :read (if (= :g first) [true false true] [true true false])}}
               readings))))))

(tu/deftest-kb a-guard-at-the-firings-own-placement-and-a-nogood-defeat-resting-on-each-other-are-broken-in-content-order
  ;; L is stated where G is placed, so the guard holds at G's own placement.  L is
  ;; `:default`, so G is stored with a guard defeat at CxA resting on L (design ruling
  ;; 25), and the walk breaks the cycle in content order in every arrival order, as it
  ;; does for the two-context shape.
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (let [readings (into #{} (map #(ground-cycle :own arm %)) (permutations [:w :breed :rule :l]))
            first    (:first (clojure.core/first readings))]
        (is (= #{{:first first :read (if (= :g first) [true false true] [true true false])}}
               readings))))))

(tu/deftest-kb a-defeat-resting-on-its-own-target-through-a-ground-is-in-force
  ;; G rests on L, so the defeat of L rests on L through G as well as directly.  The cycle
  ;; holds one defeat, which is first in content order, so it is in force at CxB: L is
  ;; hidden there, and G with it.
  (is (= #{{:read [true false false]}}
         (into #{} (map #(dissoc (ground-cycle :self nil %) :first)) (permutations [:w :breed :rule :l])))))
