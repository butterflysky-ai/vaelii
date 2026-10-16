;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
;;
;; Print the believed genl edges of the shipped ontology as JSON, for
;; scripts/ontology-graph.py. Loads the upper ontology (or, with `middle`, the starter)
;; into an in-memory KB and reads the taxonomy through the public API, so every edge is
;; one the engine installed: a stated genl, a cover roster part or an intersection
;; conjunct. Each row is [sub super minimal?], where minimal? marks a super in
;; `min-genls`, the transitive reduction.
;;
;;   lein run -m clojure.main scripts/ontology-edges.clj [middle] [predicates]
;;
;; `predicates` adds the genl components outside `thing`, which relate predicates.
(require '[cheshire.core :as json]
         '[vaelii.core :as v]
         '[vaelii.host.core-context :as core-context]
         '[vaelii.host.starter :as starter])

(let [args  (set *command-line-args*)
      kb    (v/open-kb {})
      _     (if (args "middle") (starter/load-into kb) (core-context/load-into kb))
      nodes (if (args "predicates") (v/types kb) (v/specs kb 'thing))
      rows  (for [t     (sort-by str nodes)
                  :let  [minimal (v/min-genls kb t)]
                  super (sort-by str (v/direct-genls kb t))
                  :when (contains? nodes super)]
              [(str t) (str super) (contains? minimal super)])]
  (println (json/generate-string {:edges rows}))
  (shutdown-agents))
