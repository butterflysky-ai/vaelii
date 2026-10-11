;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.negation
  "The negation family: a stored `(not B)` and a stored `B` whose contexts have a common
  descendant, placed there as a nogood (`chain/place-negations!`).  The bodies stored in
  both polarities and their members are an index family (`reads/as-stored-opposed-…`).
  See docs/nmtms.md, \"A nogood placed as a conclusion\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- body-of
  "The body a fact sentence keys its polarity under: `s` with one leading `not` removed."
  [s]
  (if (sx/negation? s) (second s) s))

(defn- polarity-handles
  "`[neg pos]`, the handles of body `b`'s stored denials and of its stored positive facts,
  each a set, while `b` is stored in both polarities; two empty sets when it is not.  The
  members are the index family's, split by the `[:false b]` leaves."
  [kb b]
  (let [idx (:index kb)
        ms  (reads/as-stored-opposed-members-global idx b)]
    (if (empty? ms)
      [#{} #{}]
      (let [neg (into #{} (filter #(contains? ms %))
                      (reads/as-stored-at-path idx [:false (sx/canon b) '?c]))]
        [neg (into #{} (remove neg) ms)]))))

(defn bodies-of
  "The bodies stored in both polarities among the bodies of the facts of the handles
  `hs`: a record read per handle and a membership read per body."
  [kb hs]
  (let [recs (:records kb)
        idx  (:index kb)]
    (into #{} (filter #(reads/stored-opposed? idx %))
          (into #{} (comp (keep #(p/get-sentex recs %))
                          (filter #(nil? (:antecedent %)))
                          (map (comp body-of :sentence))
                          (filter seq?))
                hs))))

(defn pairs
  "Each `[n p]` pair of a stored `(not B)` and a stored `B` over the bodies `bs`, read off
  the index."
  [kb bs]
  (for [b bs
        :let [[neg pos] (polarity-handles kb b)]
        n neg
        q pos]
    [n q]))

;; ---- the placements that left, and the rows respelled -----------------------
;; A `(contradicts …)` placement can leave the store while its pair stands: a `genlCx`
;; edge it rests on left with it, and that edge's move reaches no member.  A row moved to
;; another spelling in place (`kb/respell-sentex!`) can join a pair with no relabel.
;; `::moved` queues the pair's body, and the settle places it at its common descendants
;; as they stand (`take-moved!`).

(defn- note-placement-left!
  "Queue the body of the negation pair a `(contradicts …)` sentex `sx` leaving the store
  placed."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)) (= 3 (count s)))
      (let [bs (bodies-of kb (keep sx/handle-id (rest s)))]
        (when (seq bs)
          (swap! (reasoning/nogood-candidates kb) update ::moved (fnil into #{}) bs))))))

(defn note-respelled!
  "Queue the body of the fact `sx` when it is stored in both polarities: `sx` was just
  moved to its spelling in place (`kb/respell-sentex!`), which relabels nothing."
  [kb sx]
  (let [bs (bodies-of kb [(:id sx)])]
    (when (seq bs)
      (swap! (reasoning/nogood-candidates kb) update ::moved (fnil into #{}) bs))))

(defn take-moved!
  "The bodies `note-placement-left!` and `note-respelled!` queued since the last call,
  and the queue emptied."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old #{})))

(defn moved?
  "Has the index queued a body whose pairs the settle places again (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(def family
  "The negation family's entry in `decide/registry`: it keeps no candidate rows, and its
  write hook queues a placement that left (`note-placement-left!`).  A pair is placed as a
  conclusion (`chain/place-negations!`)."
  {:note! (fn [kb _ sx stored?]
            (when-not stored? (note-placement-left! kb sx)))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :Q7 :label "Negation placement queue" :kind :queue :keyed-by :literal
  :holds-content? false
  :reads [:records :index]
  :retired-by {:removed :K :settle-pass :Q :recover :R :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates ::moved]]
  :note "the bodies of the negation pairs whose `contradicts` placement left the store or whose row was respelled in place, which `take-moved!` drains once a pass"})
