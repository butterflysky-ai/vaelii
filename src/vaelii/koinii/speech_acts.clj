;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.speech-acts
  "Koinii speech-acts: the small vocabulary of moves agents make, as
  sentexes in the KB.  A move is not an out-of-band message but knowledge — queryable,
  retractable, auditable like any other fact — and the FORM of the move carries the
  layer's headline property (koinii design D1 / D5).

  Two kinds of move, one split (`koinii.md`, *Reply is an assertion*):

  - **Origination** (`asserts`, `queries`) — a plain assertion in the acting agent's
    own context.  The claim, or the query node, plus its provenance IS the act: nothing
    wraps it, because provenance already records who spoke (first-writer-wins).  So an
    assertion in koinii is just an assertion — `assert-claim` mints no `asserts` edge.
    A query is minted as a node (`pose-query`), because a question must be told apart
    from a claim.
  - **Response** (`answers`, `disputes`, `endorses`, `justifies`) — a META-SENTEX on
    the target sentex, naming it by handle `(sentexHandle H)`, asserted in the
    RESPONDER's own context and stamped with the responder as creator.  Each response
    predicate is declared `target_following_predicate` in `CxSpeechActs`, so retracting a
    target sweeps its replies with it (`core/retract-following-metas!`).  Two facts
    force this: the cascade needs BOTH the meta-sentex AND the mark (an unmarked meta
    orphans harmlessly), and first-writer-wins forces each act to be its own object —
    two endorsers are two sentexes with two creators, never one re-assert.

  `retracts` is the engine's `retract!` on a handle.  The error acts
  (`notUnderstood`, `refuse`) name the received edge, in the refusing agent's context,
  and are deliberately unmarked.  This layer only REPRESENTS the moves; adjudication is
  a separate layer.

  Additive, like the sibling koinii modules: requires only the public core API and koinii
  `identity` — nothing under `vaelii.impl`, and nothing in core loads it.  Every write goes
  through the provenance-stamping `assert` path, never `bulk-assert-facts!`."
  (:require [vaelii.core :as v]
            [vaelii.koinii.identity :as id]))

;; ---- loading the vocabulary ----------------------------------------------

(defn load-speech-acts
  "Load the CxSpeechActs vocabulary into `kb` from resources/kb/koinii/CxSpeechActs.txt.
  Koinii KB files are not auto-discovered (the starter walks only upper/ and middle/),
  so this explicit loader is how the context comes into being.  Requires the upper
  ontology already loaded (CxSpeechActs wires `(genlCx CxSpeechActs CxUniverse)`).
  Returns kb."
  [kb]
  (id/load-seed-context kb 'CxSpeechActs))

;; ---- per-agent context placement (koinii design D8) ----------------------

(defn speaker-context
  "Create/lift `agent`'s per-agent context (`id/context-for`): under `channel` so the
  channel sees the agent's moves — `(genlCx channel CxAtlas)` — and under CxSpeechActs so
  the agent speaks the act vocabulary and the rules over it fire.  Both edges are
  monotonic topology.  Returns the agent context symbol.

  This is the identity substrate acts land in: 'who' comes from the edge's own context
  and provenance, never from the target it names."
  [kb channel agent]
  (id/place-agent-context #(v/assert kb %1 %2 %3) channel agent 'CxSpeechActs))

;; ---- origination: the claim / query node plus provenance IS the act ------

(defn assert-claim
  "The `asserts` move: originate a claim.  A bare assertion of `claim` in `agent`'s own
  context, stamped `agent` as creator — NO `asserts` wrapper, because provenance already
  records who asserted (first-writer-wins), so wrapping would only duplicate it.  A
  second agent re-asserting the same sentence in the same context writes no new
  provenance, which is exactly why an endorsement must be its own object.  Returns the
  claim's handle."
  ([kb agent claim] (assert-claim kb agent claim (id/context-for agent)))
  ([kb agent claim ctx]
   ;; a cooperative agent may write another agent's context (first-writer-wins reads the
   ;; provenance, not the destination) — but never the admin registry
   (id/check-registry-write! agent ctx)
   (v/assert kb claim ctx {:creator agent})))

(defn pose-query
  "The `queries` move: originate a query NODE `(queries agent question)` in `agent`'s own
  context, stamped `agent` as creator — the node a responder later answers by handle.
  Minted (unlike `assert-claim`) because a question must be told apart from a claim.
  Returns the query node's handle."
  ([kb agent question] (pose-query kb agent question (id/context-for agent)))
  ([kb agent question ctx]
   (id/check-registry-write! agent ctx)
   (v/assert kb (list 'queries agent question) ctx {:creator agent})))

;; ---- response acts: meta-sentexes on the target, stamped by the responder -

(defn endorse
  "The `endorses` response act: `agent` stands behind the claim at `target-handle`.  A
  meta-sentex `(endorses agent (sentexHandle target-handle))` in `agent`'s own context,
  creator `agent`.  target_following_predicate, so it is swept when the target is
  retracted.  Two endorsers of one claim yield two distinct sentexes with two creators —
  the case a bare re-assert would collapse to one.  Returns the endorsement's handle."
  [kb agent target-handle]
  (v/assert kb (list 'endorses agent (v/sentex-handle target-handle))
            (id/context-for agent) {:creator agent}))

(defn answer
  "The `answers` response act: `agent` answers the query at `target-handle` with
  `content`.  A meta-sentex `(answers agent content (sentexHandle target-handle))` in
  `agent`'s own context, creator `agent`.  target_following_predicate.  The answerer's
  identity is read off THIS sentex (its context + provenance), not off the query.
  Returns the answer's handle."
  [kb agent content target-handle]
  (v/assert kb (list 'answers agent content (v/sentex-handle target-handle))
            (id/context-for agent) {:creator agent}))

(defn justify
  "The `justifies` response act: `agent` offers `ground` as a reason for the claim at
  `target-handle`.  A meta-sentex `(justifies agent ground (sentexHandle target-handle))`
  in `agent`'s own context, creator `agent`.  target_following_predicate.  Returns the
  justification's handle."
  [kb agent ground target-handle]
  (v/assert kb (list 'justifies agent ground (v/sentex-handle target-handle))
            (id/context-for agent) {:creator agent}))

(defn dispute
  "The `disputes` response act: `agent` challenges the claim at `target-handle`.  Does
  two writes in `agent`'s own context, both stamped creator `agent`:

  1. the REBUTTING claim — the negation of the target's sentence — so the pair surfaces
     in `(v/contradictions kb)` (both sides believed at their defeat class);
  2. a `disputes` meta-sentex naming the target by handle — target_following_predicate, so
     retracting the target sweeps the dispute edge.

  Represents the challenge only; adjudication is a separate layer.  Returns the dispute
  edge's handle (write 2).

  **A handle that names no record is refused** (`:koinii/no-such-handle`), as `deref`'s
  `marker` refuses one.  Write 1 is built from the target's own sentence, so a missing
  target would store the literal `(not nil)` and a `disputes` edge on nothing — a
  challenge to a claim that does not exist, indistinguishable in the KB from one that
  does."
  [kb agent target-handle]
  (let [ctx (id/context-for agent)
        sx  (v/sentex kb target-handle)]
    (when (nil? sx)
      (throw (ex-info (str "koinii: cannot dispute handle " (pr-str target-handle)
                           " — it names no record in this KB")
                      {:type :koinii/no-such-handle :handle target-handle})))
    (v/assert kb (list 'not (v/sentence-of sx)) ctx {:creator agent})
    (v/assert kb (list 'disputes agent (v/sentex-handle target-handle)) ctx {:creator agent})))

;; ---- retraction: the engine operation named as a move --------------------

(defn retract-move
  "The `retracts` move: the engine's `retract!` on `handle`.  It is this very teardown
  that the target_following_predicate response acts cascade with — retract a target and
  its answers / endorses / disputes / justifies edges go with it.  Returns retract!'s
  counts."
  [kb handle]
  (v/retract! kb handle))

;; ---- error acts: name the received edge, in the refuser's context, unmarked

(defn not-understood
  "The `notUnderstood` error act: `agent` could not parse the received edge at
  `received-handle`.  A meta-sentex `(notUnderstood agent (sentexHandle received-handle))`
  in `agent`'s own context, creator `agent`.  Deliberately NOT target_following_predicate:
  a parse failure is a fact about the exchange and outlives what provoked it.  Returns
  its handle."
  [kb agent received-handle]
  (v/assert kb (list 'notUnderstood agent (v/sentex-handle received-handle))
            (id/context-for agent) {:creator agent}))

(defn refuse
  "The `refuse` error act: `agent` will not act on the received edge at `received-handle`.
  Same shape and placement as `not-understood`, also unmarked.  Returns its handle."
  [kb agent received-handle]
  (v/assert kb (list 'refuse agent (v/sentex-handle received-handle))
            (id/context-for agent) {:creator agent}))

;; ---- reads: recover the conversation as data -----------------------------

(defn answers-to
  "Every believed answer naming the query `query-handle`, seen from `context` (default
  ?ctx — match anywhere): the sentex maps `(answers ?agent ?content (sentexHandle
  query-handle))`.  Pair each with `responder-of` for who answered and its `:context`
  for where from — 'what answered A's question, and who said it' is this read."
  ([kb query-handle] (answers-to kb query-handle '?ctx))
  ([kb query-handle context]
   (v/sentexes-matching kb (list 'answers '?agent '?content (v/sentex-handle query-handle))
                        context)))

(defn endorsements-of
  "Every believed endorsement naming `target-handle`, seen from `context` (default ?ctx):
  the sentex maps `(endorses ?agent (sentexHandle target-handle))`.  Distinct endorsers
  are distinct sentexes; read each one's creator with `responder-of`."
  ([kb target-handle] (endorsements-of kb target-handle '?ctx))
  ([kb target-handle context]
   (v/sentexes-matching kb (list 'endorses '?agent (v/sentex-handle target-handle))
                        context)))

(defn responder-of
  "The agent credited (via provenance `:creator`) with the response sentex `handle`, or
  nil — 'who made this move', read off the move itself."
  [kb handle]
  (:creator (v/provenance kb handle)))
