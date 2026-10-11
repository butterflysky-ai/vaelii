;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.projection
  "Relation algebras of nine relations, each a pair of coordinates on two independent axes
  of the one-dimensional point algebra: the cardinal directions (`vaelii.impl.orientation`)
  and the relative frame (`vaelii.impl.relative`). `algebra` derives universe, identity,
  composition and converse from one projection table. See docs/space.md and docs/qcn.md."
  (:require [clojure.set :as set]))

(def point-compose
  "The one-dimensional point algebra: `[a b]` → the relations possible between x and z
  when a relates x to y and b relates y to z."
  {[:lt :lt] #{:lt}, [:lt :eq] #{:lt}, [:lt :gt] #{:lt :eq :gt}
   [:eq :lt] #{:lt}, [:eq :eq] #{:eq}, [:eq :gt] #{:gt}
   [:gt :lt] #{:lt :eq :gt}, [:gt :eq] #{:gt}, [:gt :gt] #{:gt}})

(def point-converse
  "The one-dimensional point algebra's converse: reading a relation backwards flips it."
  {:lt :gt, :eq :eq, :gt :lt})

(def ^:private all-axis-pairs
  "The nine `[x y]` combinations a total projection must cover."
  (set (for [x [:lt :eq :gt] y [:lt :eq :gt]] [x y])))

(defn algebra
  "The `vaelii.impl.qcn` relation algebra `{:universe :identity :compose :converse}` of
  `relation->axes`, a map of base relation → its `[axis-1 axis-2]` projection. The
  identity is the relation projecting to `[:eq :eq]`. Throws `:bad-algebra` unless the
  projection is a bijection onto the nine axis pairs."
  [relation->axes]
  (let [axes->relation (set/map-invert relation->axes)
        covered        (set (vals relation->axes))]
    ;; a repeated pair still covers all nine, and `map-invert` drops one of its two relations
    (when-not (and (= all-axis-pairs covered)
                   (= (count relation->axes) (count all-axis-pairs)))
      (throw (ex-info (str "a two-axis projection must cover all nine [x y] pairs exactly"
                           " once, got " (count relation->axes) " relations over "
                           (count covered) " distinct pairs")
                      {:type :bad-algebra
                       :relations (count relation->axes)
                       :missing (vec (sort (set/difference all-axis-pairs covered)))
                       :repeated (vec (sort (keys (into {} (remove (fn [[_ n]] (= 1 n)))
                                                        (frequencies (vals relation->axes))))))})))
    {:universe (set (keys relation->axes))
     :identity #{(axes->relation [:eq :eq])}
     :compose
     (fn [s1 s2]
       (into #{}
             (for [r1 s1 r2 s2
                   :let [[a1 a2] (relation->axes r1)
                         [b1 b2] (relation->axes r2)]
                   c1 (point-compose [a1 b1])
                   c2 (point-compose [a2 b2])]
               (axes->relation [c1 c2]))))
     :converse
     (fn [rels]
       (into #{}
             (map (fn [r]
                    (let [[x y] (relation->axes r)]
                      (axes->relation [(point-converse x) (point-converse y)]))))
             rels))}))
