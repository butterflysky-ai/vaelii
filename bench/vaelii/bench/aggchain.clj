;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.aggchain
  "What a forward rule over an **aggregate** antecedent costs at load time: loading *n*
  facts on a counted predicate re-joins the rule *n* times over *n* groupings
  (docs/aggregate.md, \"What it costs\").

    no rule             the floor: the same facts with nothing counting them
    rule first          the real cost — the rule is standing as the facts arrive
    deferred chaining   the same, asserted `{:chain? false}` with one `forward-chain`
                        at the end — which does **not** help, and the reason it does
                        not is the point of the table
    one edit            the whole load as a single `edit` batch: one settle, so one
                        drain of the re-check queue
    rule last           the facts first, then the rule: one join over a finished
                        extent, so the reductions are done exactly once

  The shape is a chain of *n* nodes under `(transitive ancestorOf)`, which is what makes
  every node's ancestor set a different size and every count real work.

  Run: `lein bench-aggchain`"
  (:require [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]))

(defn- fresh-kb
  "A KB with the upper layer in CxUniverse and nothing else.  The in-memory stores are
  shared per space number, so `clear!` is what makes each row independent."
  []
  (let [kb (v/open-kb {:backend :memory :space 30 :recover? false})]
    (v/clear! kb)
    (core-context/load-into kb)
    kb))

(defn- ms [f] (let [t (System/nanoTime)] (f) (/ (- (System/nanoTime) t) 1e6)))

(def ^:private rule
  '(implies (and (node ?x) (agg/count ?n ?a (ancestorOf ?a ?x)))
             (ancestorCount ?x ?n)))

(defn- scenario
  "Load a chain of `n` nodes and return the milliseconds it took.  `when-rule` is
  `:none`, `:first` (standing before the facts arrive) or `:last` (asserted over the
  finished extent); `mode` is `:assert`, `:defer` (`{:chain? false}` + one
  `forward-chain`) or `:edit` (the whole load as one batch)."
  [n when-rule mode]
  (let [kb   (fresh-kb)
        ctx  'CxUniverse
        node #(symbol (str "Node" % "Individual"))
        opts (when (= :defer mode) {:chain? false})
        eds  (for [i (range 1 n)] [(list 'ancestorOf (node (dec i)) (node i)) ctx])]
    (v/assert kb '(transitive ancestorOf) ctx {:strength :monotonic})
    (doseq [i (range n)] (v/assert kb (list 'node (node i)) ctx))
    (when (= :first when-rule) (v/assert kb rule ctx))
    (cond-> (if (= :edit mode)
              (ms #(v/edit! kb {:add (vec eds)}))
              (ms #(doseq [[s c] eds] (v/assert kb s c opts))))
      (= :defer mode)     (+ (ms #(v/forward-chain kb {})))
      (= :last when-rule) (+ (ms #(v/assert kb rule ctx))))))

(defn- best
  "The fastest of two timed runs after a warm one — the discipline every bench here
  uses."
  [f]
  (f)
  (min (f) (f)))

(defn -main [& args]
  (let [sizes (if (seq args) (map #(Long/parseLong %) args) [10 20 40])]
    (println "vaelii aggregate forward-chaining load cost")
    (println "wall-clock, fastest of two after a warm run — read the ratios, not the values.\n")
    (println "  nodes | no rule | rule first | deferred chaining | one edit | rule last")
    (println "  -------------------------------------------------------------------------")
    (doseq [n sizes]
      (println (format "  %5d | %7.1f | %10.1f | %17.1f | %8.1f | %9.1f"
                       n
                       (best #(scenario n :none  :assert))
                       (best #(scenario n :first :assert))
                       (best #(scenario n :first :defer))
                       (best #(scenario n :first :edit))
                       (best #(scenario n :last  :assert)))))
    (println)
    (println "  Reading:")
    (println "  - the shape is quadratic, and on purpose rather than by accident: every")
    (println "    arriving (ancestorOf a b) re-joins the rule over every node, and each")
    (println "    of those groupings re-reads its whole ancestor set.")
    (println "  - `{:chain? false}` buys NOTHING, which is the useful finding. The")
    (println "    re-join is not the assert's forward chain — it is queued in the re-check")
    (println "    index and drained by SETTLE, and settle runs per assert whether or not")
    (println "    chaining did. Deferring the half that was never the cost changes nothing.")
    (println "  - one `edit` lands exactly on `rule last` — the floor, where the")
    (println "    reductions happen once over a finished extent. One settle, one drain of")
    (println "    the queue, one join. The ratio climbs with n rather than being a")
    (println "    constant, which is the point: the per-assert path is quadratic and the")
    (println "    batch is not. Actionable advice for a bulk load: batch it.")
    (println "  - the standing fix is an incremental aggregate — a count maintained on")
    (println "    assert rather than recomputed — which needs the rule-consequent case")
    (println "    that is deliberately out of scope today (docs/aggregate.md, \"Scope\").")
    (shutdown-agents)))
