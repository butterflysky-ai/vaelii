# Aggregation: a reduction over a query's solutions

- **Covers:** the five reduction operators
  (`agg/count`/`agg/sum`/`agg/min`/`agg/max`/`agg/avg`) as query operators, grouping by
  binding discipline, and how a firing resting on a count is maintained.
- **Not here:** the `unknown`/`thereExists` family this extends → [naf.md](naf.md); the
  rule-level exception whose re-check and stratification machinery this reuses →
  [exceptions.md](exceptions.md).
- **Assumes:** context, belief, `genl`, justification → [glossary.md](glossary.md).

Counting, summing and averaging are **query operators**, the third member of the
`unknown` / `thereExists` family. Nothing here is stored, and the engine machinery is
the family's.

## The five

```clojure
(agg/count ?n ?v Body)   ; ?n = how many distinct ?v satisfy Body
(agg/sum   ?n ?v Body)   ; ?n = the sum of the distinct numeric ?v
(agg/min   ?n ?v Body)
(agg/max   ?n ?v Body)
(agg/avg   ?n ?v Body)
```

One shape, one prover (`provers/AggregateProver`), one `wff` arm. `?v` is **projected
out**, as a `thereExists` binder is, so `?n` is the only binding produced and no solution
mentions `?v` outside the aggregate.

```clojure
;; (scoreOf Team 3) (scoreOf Team 1) (scoreOf Team 4) (scoreOf Team 1) (scoreOf Team 5)

(v/ask kb '(agg/count ?n ?v (scoreOf Team ?v)) 'CxWell)   ; => ({?n 4})
(v/ask kb '(agg/sum   ?n ?v (scoreOf Team ?v)) 'CxWell)   ; => ({?n 13})
(v/ask kb '(agg/avg   ?n ?v (scoreOf Team ?v)) 'CxWell)   ; => ({?n 3.25})
```

The reductions run over the four **distinct** values, not the five solutions. An
aggregate yields exactly one answer or none, never a stream.

## Bind or check

A variable `?n` takes the computed value; a **bound** `?n` is compared against it, so
`(agg/count 2 ?v (scoreOf Team ?v))` is a test. `EvaluateProver` makes the same pair. The
check arm is what re-verifies a *firing* against the count it rested on (maintenance,
below). Numbers compare with `==`, so a long and a double naming one value agree.

## Grouping: the binding discipline is GROUP BY

`free-vars` subtracts **both** of the aggregate's own slots: `?v` because it is
projected out, `?n` because it is the operator's output.

| form | `free-vars` |
|------|-------------|
| `(agg/count ?n ?v (ancestorOf ?v Tom))` | `{}` — closed |
| `(agg/count ?n ?v (ancestorOf ?v ?x))` | `{?x}` |
| `(agg/sum 3 ?v (mass ?v Tom))` | `{}` |

In a rule, whether the rest of the rule names a remaining variable decides its role:

- A variable the rule also mentions **outside** the aggregate is the **group**. A
  generator antecedent must bind it before the aggregate runs, the contract `unknown` has
  ([naf.md](naf.md)), refused with the same `:naf-not-closed`.
- A variable mentioned **only** inside the aggregate is **local to the census**, and the
  body's join binds it. `?c` in `(agg/sum ?n ?a (and (childOf Bob ?c) (ageOf ?c ?a)))` is
  the join between the two conjuncts, and the rule sums the ages of Bob's children. A
  local variable outside `sentex/census-bound-vars` (what a generator conjunct matches
  plus what a computed conjunct writes) is refused `:naf-not-closed`, because the join
  runs generators first and never reaches a conjunct that only reads it.

```clojure
(implies (and (node ?x)
              (agg/count ?n ?a (ancestorOf ?a ?x)))
         (ancestorCount ?x ?n))
```

`?x` is bound by the generator, so the aggregate runs **once per `?x`** and yields one `?n`
each, which is the grouped count. An aggregate is a deferred literal
(`sentex/deferred-predicates`), so canonical antecedent order and the planner both pin it
after its binders, whichever order it is written in.

The reduction variable is **local**, like a `thereExists` binder: `?a` appearing outside
its own aggregate literal is refused `:quantifier-not-local`, since `range-problems`
reads occurrences and cannot see the hole. The reduction slot must hold a **variable**:
`(agg/count ?n Ada Body)` reduces over nothing and no prover claims it, so a rule carrying
one would store and never fire, and is refused `:not-well-formed`.

**A conjunctive body is joined.** `provers/aggregate-values` runs the body through
`provers/conjunction-solutions`, the evaluator `unknown`, `thereExists` and `exceptWhen`
read, so one witness satisfies every conjunct
([why](defenses.md#a-conjunction-under-a-quantifier-is-joined-never-read-flat)):

```clojure
;; (childOf Bob Kid1) (childOf Bob Kid2) (childOf Bob Kid3)
;; (asleep Kid1) (asleep Kid2) (asleep Stranger)

(v/ask kb '(agg/count ?n ?c (and (childOf Bob ?c) (asleep ?c))) 'CxWell)   ; => ({?n 2})
```

A **disjunctive** body is refused (`:not-well-formed`): a count over a union is not the
sum of two counts, since a witness satisfying both alternatives would be counted twice.
Name the extent with a rule, whose antecedent may disjoin
([canonicalization.md](canonicalization.md)), and aggregate over the conclusion.

A bare **goal** has no rule around it, so every variable of its body is local, and
`AggregateProver` claims it when the census binds them all. A goal whose census cannot
bind one (a variable only a computed conjunct reads) answers empty instead of being
refused: a goal is asked once, while a rule is stored and re-run.

## Comparing the count

```clojure
(implies (and (person ?x)
              (agg/count ?n ?c (childOf ?x ?c))
              (lessThan 2 ?n))
         (large_family ?x))
```

`?n` is bound per **placement context** (below), so it does not exist during the join,
and `(lessThan 2 ?n)` is a computed literal with no fact to wait on.
`rules/post-join-literals` therefore moves every aggregate, and every deferred literal
reading what one writes (transitively), into the placement phase:

```clojure
(and (person ?x)                          ; joined
     (agg/count ?n ?c (childOf ?x ?c))    ; placement: binds ?n
     (evaluate ?d (+ ?n 1))               ; placement: reads ?n, binds ?d
     (lessThan 3 ?d))                     ; placement: reads ?d
```

**They run in written order**, and a computed literal reads only what is written before
it, the rule an `evaluate` chain follows too. The uphill writing is refused
(`:naf-not-closed`) rather than reordered: the forward chainer could reorder the
placement phase and the backward one cannot, so reordering would make the two disagree
about one rule.

The re-check re-runs the **whole** list, so a firing licensed by `(lessThan 2 ?n)` at a
count of 3 is withdrawn at a count of 1. Each literal keeps the context it would have had
in the join: the aggregate runs in the placement context, the comparison in the wildcard.

**A literal that answers two ways answers nothing.** Which of several solutions the
registry yields first depends on how the facts were stored, so taking the first would
place a different fact per arrival order. `chain/post-join-bindings` declines a literal
whose solutions disagree, as `provers/table-read` declines a unit declaring two
conversion factors: nothing is concluded, and a `:post-join-ambiguous` entry naming the
literal and its solutions goes into `violations`. It realizes at most two solutions, so
the check costs one extra pull off a lazy seq. The built-in computations answer once or
not at all, so only a registered prover reaches it.

**What counts as bound** is a generator's variables plus what the deferred literals
write: an aggregate's `?n`, an `evaluate`'s output. A deferred literal reading a
variable nothing in the rule writes is refused at assert time (`:naf-not-closed`). The
join would otherwise throw on the unbound input mid-fixpoint, after the rule is stored.

## Evaluated over the registry, which expands no rule

The body runs through the **registry** for the reason `unknown`'s does: a count reached
from inside a relabel loop must not launch an open-ended backward search. Nothing in the
registry backchains, so the restriction holds by construction.

A **forward-derived** fact is counted, since it is stored and believed by the time the
query runs. So is a relation held in the cached closures (`genl`, a `(transitive
ancestorOf)` walked by `TransitivePredicateProver`). A level-6 body cannot see a relation
reachable **only** by backward chaining: a `set/backwardRule`'s conclusions.

`cost` is `:compute`: a reduction must exhaust the body before it has any answer, so a
`{:max-cost :lookup}` budget drops the prover. `completeness` is `100`: an aggregate is
not assertible, so nothing else holds a claim about one and nothing is unioned in.

## Distinctness is by the equality closure

Count and sum run over *distinct* `?v`, and distinctness reads the equality closure's
representative, so two names for one thing are one value:

```clojure
(knows Ada Alan) (knows Ada Turing)     ; (agg/count ?n ?v (knows Ada ?v)) => 2
(sameAs Alan Turing)                    ;                                      => 1
```

The closure is **read from the asking context**, the scoping `different` puts on the same
partition ([equality.md](equality.md)). A `(sameAs Alan Turing)` stated in a context
collapses the two there and nowhere else; the context above it still counts two.

## The empty body

**Count is 0 and sum is 0**, the identity of each reduction. **Min, max and avg over
nothing yield no binding**: not nil, not zero.

## Numbers, measures, and what is neither

A non-numeric value under `sum` / `min` / `max` / `avg` is an **error, not a skip**:
dropping the non-numbers would answer a different question. It yields nothing and is
recorded in the violations ledger (`(violations kb)`, `:violation :aggregate`). `count`
never reads the values and is unaffected.

The error goes to the ledger rather than a throw because an aggregate is reached from
inside a fixpoint that must not abort. It is filed **once** per distinct error: a count
is recomputed on every query, re-check and settle pass, and filing each would fill the
ledger (capped at its newest 1000 entries) with copies of one defect.

**The reduction runs over sorted values.** Floating-point addition is not associative,
and the values arrive in solution order, which depends on how the facts were stored. Six
readings that sum to `8.0` sorted sum to `7.7`, `8.2` and `8.6` in three arrival orders,
so without the sort the same KB asserted in another order would report another total,
against order independence ([nmtms.md](nmtms.md)). The sort buys determinism, not
exactness.

**Measures are numeric.** `agg/sum` over `(QuantityFn 5 Meter)` normalizes each value
through `provers/normalize-quantity`, adds in base units, and renders the result with
`render-quantity` from the same `conversionFactor` table. Which base unit an inconsistent
table renders in is [quantity.md](quantity.md)'s.

* `:sum` and `:avg` are linear in the `[lo hi]` bounds, so an interval in gives a
  `QuantityIntervalFn` out.
* `:min` and `:max` need a **total** order, and measure bounds give only a partial one.
  They answer for point measures (`lo = hi`) and refuse a genuine interval.
* A **dimension mismatch** is refused. Metres plus seconds is not a sum.

## Not assertible, and nothing is stored

A `wff` arm refuses all five as stored facts, as it refuses `unknown` and `different`. A
stored count would be a **stale** fact: a count is a function of what is believed now,
and truth maintenance has no way to invalidate one.

Asking an aggregate leaves the sentex and justification sets identical. A count is
recomputed and never cached, as `unknown` is.

The naming checks read the operator as a **frame**: the body is checked as a goal, not
read as an argument of a three-place `agg/count` ([naming.md](naming.md)).

## Maintenance, when the aggregate is a rule antecedent

A rule that fired because the count was 2 must not stay fired when the count becomes 3.
The mechanism is `exceptWhen`'s, with one addition.

**The trigger.** The rule is posted in the re-check index
(`[:exception-index <predicate>]`) under the predicate of every conjunct of its aggregate
bodies (`rules/watched-literals`), since a fact arriving on any one changes which
witnesses the join finds. `rules/recheck-predicates` unions those with the `unknown`
antecedents' predicates: both conditions read belief rather than a fact the
justification names.

**The withdrawal.** `chain/post-join-withdrawn?`, reached through `rule-firing-blocked?`
from `justification-excepted?`, re-runs the post-join literals in the conclusion's
context under the firing's **stored bindings**. `?n` is already bound there, so each runs
in check mode, and a mismatch blocks the firing as an exception does. The antecedents
cannot express this: the facts the join matched are still stored and believed when
another fact changes the census.

**The addition: a count that rises.** A count going 1 ⇒ 2 licenses a firing that never
existed, so no blocked justification is released and the blocked set does not move.
`settle` re-joins a queued aggregate rule whether or not anything blocked
(`rules/arrival-releasable?`, which a nested `unknown` shares;
[exceptions.md](exceptions.md#re-chaining-what-was-released-not-what-was-touched)).

**Belief, not storage.** A defeated fact is stored and not believed, so it drops out of
the census. `special/recheck-on-sentence` posts an arriving `(not S)` under `S`'s
predicate (`sentex/underlying-body`), so the defeat reaches the rule.

**An equality moves a census** with no fact arriving, leaving or relabelling: a merge
retires a spelling. `special/recheck-equality-edge` is the trigger, and an aggregate rule
takes its blanket arm ([exceptions.md](exceptions.md#five-channels-a-declaration-or-a-fact-reaches-an-exception-through-sideways)).
`chain/settled-bindings` rewrites the firing's stored bindings to the representatives,
since the registry reads a retired spelling's census as zero.

The counted fact asserted, retracted, defeated and un-defeated, and an equality asserted
or retracted, each move the conclusions both ways. The four edges of a chain loaded in all
24 orders give one set of counts.

## What it costs

A rule joining on a count is **re-joined**, not only re-checked, whenever a counted fact
arrives. A chain of *n* nodes under `(transitive ancestorOf)`, with the grouping rule
above (`lein bench-aggchain`, ms):

| nodes | no rule | rule first | deferred chaining | one `edit!` | rule last |
|---|---|---|---|---|---|
| 10 | 1.7 | 21.3 | 20.2 | 5.1 | 4.4 |
| 20 | 1.6 | 45.8 | 48.6 | 7.9 | 6.8 |
| 40 | 4.3 | 160.0 | 170.7 | 17.6 | 15.4 |

The per-assert path is quadratic: every arriving `(ancestorOf a b)` re-joins the rule over
every node, and each grouping re-reads its whole ancestor set.

- **`{:chain? false}` changes nothing.** The re-join is queued in the re-check index and
  drained by **settle**, which runs per assert whether or not chaining did.
- **One `edit!` lands on `rule last`**: one settle, one drain, one join over the finished
  extent. The ratio to `rule first` is 4x at n=10 and 9x at n=40. A bulk load against an
  aggregate rule should be batched, and the batch reaches the identical counts.

## Stratification

An aggregate over a relation that depends on the aggregate is unstratified, as negation
as failure is: a fact changes the count, which can withdraw the conclusion, so arrival
order would pick the answer. The aggregate bodies' predicates, one per conjunct, join the
`unknown` antecedents' as **negative edges** in the rule dependency graph, and
`checks/check-stratified` refuses a cycle through them at assert time
(`:type :not-stratified`, with the cycle).

## Where it plugs in

| site | what it contributes |
|------|---------------------|
| `provers/default-provers` | one `AggregateProver` beside `->UnknownProver` / `->ThereExistsProver` |
| `provers/conjunction-solutions` | the joined evaluator the census body runs through |
| `wff/naf-problems` | the five, through `special/entries` |
| `sentex/deferred-predicates` | the five, so canonical order and the planner pin them after their binders |
| `sentex/free-vars` | one arm subtracting both slots |
| `sentex/deferred-input-vars` / `-output-vars` | what a computed literal reads and what it writes |
| `sentex/census-bound-vars` | what a census body binds for itself, read by the assert-time check and by the prover's applicability |
| `sentex/check-naf-closed` | group closure, binder locality, the reduction-slot and census refusals |
| `naming/literals` | one frame arm, so the body is checked as a goal |
| `rules/recheck-predicates` | the aggregate bodies' predicates, one per conjunct |
| `rules/post-join-literals` | the antecedents the join withholds for the placement phase |
| `checks/check-stratified` | the same predicates as negative edges |
| `chain` | withhold from the join; bind per placement; the withdrawal arm |
| `settle` | re-join a queued aggregate rule whether or not anything blocked |
| `kb/upper/core.txt` | five `(comment …)` + `(ternary_predicate …)` declarations |

## Where the census is taken

Which facts are in the census depends on the context, and placement is computed from
the matched facts after the join. So the aggregate is withheld from the join, as
`unknown` is, and evaluated per **placement context** in `chain/place-conseq`. The
bindings it produces are the ones every check there reads, so an exception or a NAF
literal mentioning `?n` sees the count this placement rests on: `(unknown (banned ?n))`
over a count works.

**It counts where the conclusion lands, and does not decide where that is.** An aggregate
matches nothing, so it contributes no handle to placement; the rule's other antecedents
decide it. One rule gives each context its own count:

```clojure
;; Left and Right under Root; the rule in Root
(person Ann)@Left  (person Ann)@Right
(childOf Ann C1)@Left  (childOf Ann C2)@Left  (childOf Ann C3)@Right
;; => (childCount Ann 2)@Left  and  (childCount Ann 1)@Right
```

The same fact read the other way: grouped on something only a *general* context holds,
the count is taken there, where the children's facts are invisible. `(person Ann)@Root`
with every `childOf` below it concludes `(childCount Ann 0)@Root`. Bind the grouping
variable from a fact in the context you mean to count.

Backward chaining (`prove` and the node engine) evaluates the aggregate in the goal's
context and forward chaining in the conclusion's placement context; both are the context
the conclusion is about, the answer [exceptions.md](exceptions.md) gives to the same
question. Tests pin the two chainers' agreement on the comparison-on-a-count shape.

## Scope

**In:** the five operators as one prover, the `wff` refusal, the `core.txt`
declarations, the closure and stratification checks, the re-check maintenance.

**Out:**

* **Aggregates as rule consequents**, deriving and storing an aggregate fact. That puts a
  computed value under truth maintenance, which has no invalidation for it.
* **Incremental / maintained aggregates**, a count updated on assert rather than
  recomputed. It rests on the consequent case above.
* **`GROUP BY` as a construct.** Grouping comes from the binding discipline; syntax for
  it would be a second way to say the same thing.

An aggregate **inside an `unknown`** works and is tested: `(unknown (agg/count 9 ?v
Body))` holds exactly while the count is not 9, because `unknown` runs its argument
through the level-6 list the aggregate is registered in.
