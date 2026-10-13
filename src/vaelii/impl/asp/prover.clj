;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.prover
  "A query-time prover for `(bravely S)` and `(cautiously S)` — brave/cautious reading
  of the dilemmas the asking context reads, answered as a read and never committed.

  ## What it answers

  `(cautiously S)` holds when `S` is in **every** optimal labeling of the dilemmas the
  asking context reads; `(bravely S)` when `S` is in **some**.  Over a coexisting `P`/`¬P` dilemma the
  engine declines to arbitrate (docs/exceptions.md), both sides are IN, and an ordinary
  `ask` reports both — so it cannot tell the *forced* belief from the *arbitrary* one.  A
  brave/cautious read can: in a Nixon diamond `(bravely (pacifist N))` holds and
  `(cautiously (pacifist N))` does not, because the other labeling gives it up.

  This is the read-path delivery of the forced/arbitrary signal.  The only prior route to
  it, `do/labeling`, **commits** — it re-asserts the kept side at `:monotonic` and defeats
  the loser everywhere (docs/labeling.md).  This prover commits nothing: it reads
  `label/classify-datum` — the solve-free `label/classify-local`, refined by a backend's
  `classify-program` only past its caps — all pure reads over settled belief, so a query
  answers and leaves belief, `contradictions` and `last-program` exactly as they were.

  ## Opting in

  Registered like the other optional reasoners — `(add-reasoner kb :brave-cautious)` — so
  the ASP stack stays off a KB's load path until a caller asks (docs/asp.md).  **It reads
  the solve-free JTMS bracket** (`label/classify-local`) with or without a backend, which
  enumerates the dilemmas' optimal resolutions from the dependency graph and classifies
  each datum by which resolutions keep it — `:true` in every, `:supportable` in some,
  `:false` in none.  Exact for a datum whose
  clusters it enumerates: the one cluster its support touches, or several whose product of
  resolutions stays within `VAELII_CLASSIFY_MAX_JOINT_OPTIMA`.  A datum past that cap, or
  one touching a cluster too large to enumerate, degrades to `:supportable`; a backend
  refines a member of such a cluster when no member of it derives from another, where a
  `Program` is exact (docs/labeling.md).

  ## Where it stops

  **Ground `S` only.**  `(bravely (pacifist N))` is answered; an open `(bravely (pacifist
  ?x))` is not applicable and no prover answers it, rather than enumerating the contested
  atoms — the same restraint `different` takes.

  **A query, not a fact and not an antecedent.**  `bravely`/`cautiously` are not
  assertible (`wff/brave-cautious-problems`): a stored one would be a computed value with
  no way to keep it current, the reason the aggregates and `unknown` are refused too.  As a
  rule antecedent the answer carries no support (it is not a `SupportingProver`), so the
  forward join drops it and it derives nothing — a read, not something belief rests on.
  Threading its support (the dilemma's contested handles) so a rule could rest on it is the
  open design point, deferred until a use asks for it."
  (:require
   [vaelii.impl.asp.label :as label]
   [vaelii.impl.except :as exc]
   [vaelii.impl.kb :as kb]
   [vaelii.impl.resolution :as res]
   [vaelii.impl.sentex :as sx]
   [vaelii.impl.taxonomy :as tax]
   [vaelii.impl.types.prover :as prover-types]
   [vaelii.impl.types.reasoning :as reasoning]))

(defn- modal-goal? [goal]
  (and (sequential? goal)
       (contains? #{'bravely 'cautiously} (first goal))
       (= 2 (count goal))
       (sx/ground-term? (second goal))))

(defn- visible-handles
  "The handles of `s` stored in `context`'s `genlCx` ancestor set that `context` believes
  (`res/believed-at?`) and sees (`exc/hidden-fn`): what a ground `ask` of `s` reads at
  `ask`'s level (what is stored, no rule expansion).  Empty at a variable context."
  [kb s context]
  (when-not (sx/variable? context)
    (let [hidden? (or (exc/hidden-fn kb context) (constantly false))]
      (into [] (comp (keep #(kb/find-sentex-handle kb s %))
                     (filter #(and (res/believed-at? kb % context) (not (hidden? %)))))
            (tax/context-up (reasoning/taxonomy kb) context)))))

(defn- class-at
  "The class of `s` at `context`: the strongest (`:true` over `:supportable` over
  `:false`) of its visible handles' classes (`label/classify-datum` at `context`), since
  `s` holds in a labeling when one of them does.  A handle no dilemma the context reads
  classifies is believed in every labeling, so it reads `:true`.  Nil when no handle is
  visible."
  [kb s context]
  (let [cs (into #{} (map #(or (label/classify-datum kb % context) :true))
                 (visible-handles kb s context))]
    (some cs [:true :supportable :false])))

(defn- holds?
  "Does `(<modal> s)` hold in `context`?"
  [kb modal s context]
  (case (class-at kb s context)
    :true        true                            ; every resolution: brave & cautious
    :supportable (= modal 'bravely)              ; some only: brave, not cautious
    false))                                      ; no resolution, or not believed

(defrecord BraveCautiousProver []
  prover-types/Prover
  (applicable?  [_ _ goal _] (modal-goal? goal))
  (est-bindings [_ _ _ _] 1)          ; a ground modal check: it holds or it does not
  (cost         [_ _ _ _] :compute)   ; a backend solve (brave + cautious), or the solve-free bracket
  ;; Authoritative for its shape: `bravely`/`cautiously` are not assertible and no rule
  ;; concludes one, so the superset claim holds against an empty field — as it does for
  ;; `different` — and `sole-prover` guards it like any other claimant regardless.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [[modal s] goal]
      (if (holds? kb modal s context) [{}] []))))

(defn brave-cautious-prover
  "The `(bravely S)` / `(cautiously S)` prover, for `add-prover` — or, the ordinary way in,
  `(add-reasoner kb :brave-cautious)`."
  []
  (->BraveCautiousProver))
