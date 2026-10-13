# Arriving from another system

- **Covers:** which orientation page to read if you already think in Cyc, answer set
  programming, defeasible logic, Prolog or Datalog, or a production rule engine — and the handful of facts
  that hold whatever you arrived from.
- **Not here:** the engine. Every line below routes to the page that owns it, and the map
  for a reader with no prior is [README.md](README.md).
- **Assumes:** nothing. The vocabulary is [glossary.md](glossary.md) and the model is the
  [README](../README.md).

## Pick your arrival

| coming from | the page | the first thing that will surprise you |
|---|---|---|
| OpenCyc or ResearchCyc | [from-cyc.md](from-cyc.md) | there is no everything-context to assert into; scope is a property of the read |
| answer set programming | [from-asp.md](from-asp.md) | there is no grounding step, and belief is a single labeling rather than a set of models |
| defeasible logic (SPINdle, Deimos) | [from-defeasible-logic.md](from-defeasible-logic.md) | a tie between two defaults is believed on both sides, and superiority is written as an `exceptWhen` |
| Prolog or Datalog | [from-prolog.md](from-prolog.md) | `Foo` is an individual and `?x` is the variable — capitalization means nearly the opposite |
| CLIPS, Jess or Drools | [from-production-rules.md](from-production-rules.md) | a rule concludes a sentence; there is no right-hand side to act in |

## What holds whatever you arrived from

- **A sentence is not knowledge until it has a context.** The unit is a *sentex* —
  sentence plus context — every sentex is in exactly one, and a read sees up the `genlCx`
  ancestor set from wherever it asks → [contexts.md](contexts.md)
- **A symbol's role is read off its spelling**, and `assert` refuses a sentence that
  breaks the convention: `parentOf` a predicate, `Fido` an individual, `physical_object` a
  type, `CxUniverse` a context → [naming.md](naming.md)
- **A rule is a sentex too** — same structure, same handle, same truth maintenance,
  additionally indexed by its antecedent and consequent predicates. So it is retractable,
  believable and askable-about, which is not true of a rule kept in a separate program →
  [inference.md](inference.md)
- **A stored sentex is not a believed one.** Belief is computed from current state by a
  truth maintenance system, never accumulated, and matching, the taxonomy closures and the
  cached relations all follow it → [nmtms.md](nmtms.md)
- **Content is asserted defeasible unless you say otherwise.** `:default` is the default
  and is what most common-sense knowledge wants; `:monotonic` is known-true and never
  defeasible. Two classes, and there is no third → [nmtms.md](nmtms.md)
- **Reading is a stack, not a function.** Eight named levels sit between a raw index read
  and full backchaining, and `query`, `prove`, `ask` and `sentexes-matching` enter it at
  different heights → [levels.md](levels.md), [api.md](api.md)

Five properties hold across all of it, and the [README](../README.md)'s model section
states them: order independence, locality, context scoping, belief filtering, and separated
state. They are worth reading before the page for your own arrival, because most of the
surprises below are one of the five showing through.

## What these pages are not

They are **one-way orientation, not a compatibility claim**. A shared name usually covers
a different semantics, and each page's third column is where that is said. Nothing here
promises a program from the other system will run, or that a translation preserves what it
meant.

They are also not an import route. **No reader for a foreign format ships in this
repository** — a bridge is a plugin that declares itself in one edn resource on the
classpath, and reading a corpus in is a separate task from writing for this engine →
[foreign.md](foreign.md), [kbs.md](kbs.md).
