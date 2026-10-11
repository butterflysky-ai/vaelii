;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.inherited
  "The inherited family's rows of the candidate index: the clashes the settle's detector
  found (`discovery/discover-inherited!`), each with its vantages, where each is placed.
  See docs/nmtms.md, \"The inherited-clash memo\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the inherited clashes --------------------------------------------------
;;
;; A stored claim against a known-true claim argument preservation reaches at its tuple or
;; at its converse's (`inherit/clashing-claim`, `inherit/converse-claim`), or a stored
;; membership against one of a separated type (`inherit/separated-claims`), is found by the
;; settle's detector (`discovery/discover-inherited!`) with the most general contexts that
;; read it whole, and placed there (`chain/place-inherited!`).  `:inherited` keeps what the
;; detector found, `{:by-set {members ngmap} :members #{h}}`, for the reports.

(defn install-inherited!
  "Keep the nogood maps `ngs` a discovery found under `:inherited`: one entry per member
  set, its vantages the union of every map's and its `:sentence` and `:inherited` the
  least map's by content.  Journals only the members that entered or left, so a clash
  found again moves no candidate.  Returns the member sets the index held before and does
  not hold now."
  [kb ngs]
  (let [by-set  (into {}
                      (map (fn [[ms es]]
                             (let [e (if (next es)
                                       (nm/min-by-content-key
                                        (juxt #(nm/print-key (:sentence %))
                                              #(nm/print-key (:inherited %)))
                                        compare es)
                                       (first es))]
                               [ms {:nogood   ms
                                    :sentence (:sentence e)
                                    :inherited (:inherited e)
                                    :vantages (into #{} (mapcat :vantages) es)}])))
                      (group-by :nogood ngs))
        members (into #{} cat (keys by-set))
        [old _] (swap-vals! (reasoning/nogood-candidates kb)
                            (fn [c]
                              (let [was (:members (:inherited c) #{})
                                    c   (journal/note c (-> #{} (into (remove was) members)
                                                            (into (remove members) was)))]
                                (if (seq by-set)
                                  (assoc c :inherited {:by-set by-set :members members})
                                  (dissoc c :inherited)))))]
    (into [] (remove #(contains? by-set %)) (keys (:by-set (:inherited old))))))

(defn inherited-clashes
  "The inherited clashes, `{members {:nogood :sentence :inherited :vantages}}`."
  [kb]
  (:by-set (:inherited @(reasoning/nogood-candidates kb))))

(def family
  "The inherited family's entry in `decide/registry`.  Its rows are installed by the
  settle's detector, not noted at the store.  Each nogood of it is placed as a conclusion
  (`chain/place-inherited!`)."
  {:handles   (fn [_ c] (:members (:inherited c)))
   :holds?    (fn [_ c h] (contains? (:members (:inherited c)) h))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N7 :label "Inherited clashes" :kind :index :keyed-by :value :reads [:D3]
  :holds-content? false
  :retired-by {:inherited :W :recover :R :image-install :R}
  :computed :settle :imaged? :state :at [[:nogood-candidates :inherited]]
  :note "the inherited clashes and their vantages, installed again by every settle's detector"})
