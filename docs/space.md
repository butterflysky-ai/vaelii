# Qualitative spatial reasoning — topology, direction and distance

- **Covers:** the four spatial relation algebras — RCC-8 topology, cardinal
  direction, relative direction, qualitative distance — and each one's base and
  derived predicates.
- **Not here:** the generic path-consistency engine and entailment/support machinery
  all four share → [qcn.md](qcn.md); the temporal algebras (Allen's intervals, the
  point algebra) → [time.md](time.md).
- **Assumes:** base relation, relation algebra, constraint network →
  [glossary.md](glossary.md).

Four relation algebras over the constraint-network engine in [qcn.md](qcn.md), each with a
prover that reads a KB into a network and reads answers back out:

| Namespace | Question |
|-----------|----------|
| `vaelii.impl.space`       | **RCC-8 topology** — do two regions touch, overlap, nest? |
| `vaelii.impl.orientation` | **cardinal direction** — which way is one place from another? |
| `vaelii.impl.relative`    | **relative direction** — which way from a point of view? |
| `vaelii.impl.distance`    | **qualitative distance** — how far apart? |

They share no predicate, and no network ever sees another's facts. Topology, orientation
and distance are the three standard questions of qualitative spatial reasoning; relative
direction is orientation asked from inside the scene rather than off a map.

## RCC-8 (`vaelii.impl.space`)

The eight base relations are jointly exhaustive and pairwise disjoint, so exactly one
holds of any two regions:

| Keyword | RCC-8 | Stored predicate | Meaning |
|---------|-------|------------------|---------|
| `:dc`    | DC    | `spatiallyDisconnected`          | share no point |
| `:ec`    | EC    | `externallyConnected`            | touch, share no interior |
| `:po`    | PO    | `partiallyOverlapping`           | share a part, each has one outside the other |
| `:eq`    | EQ    | `spatiallyEqual`                 | the same extent — the algebra's identity |
| `:tpp`   | TPP   | `tangentialProperPart`           | inside, touching the boundary |
| `:ntpp`  | NTPP  | `nonTangentialProperPart`        | strictly inside |
| `:tppi`  | TPPi  | `tangentialProperPartInverse`    | the converse of TPP |
| `:ntppi` | NTPPi | `nonTangentialProperPartInverse` | the converse of NTPP |

`rcc8-composition` is the canonical Randell–Cui–Cohn table, and `compose` lifts it to
relation *sets* by union — a disjunction on either side admits every combination.

Six **derived** predicates each name a disjunction of base relations:

| Predicate | RCC-8 | Denotation |
|-----------|-------|------------|
| `regionConnectedTo`  | C  | everything but DC |
| `partOfRegion`       | P  | TPP, NTPP, EQ |
| `properPartOfRegion` | PP | TPP, NTPP |
| `hasRegionPart`      | Pi | TPPi, NTPPi, EQ |
| `regionOverlaps`     | O  | PO, TPP, NTPP, TPPi, NTPPi, EQ |
| `regionDiscreteFrom` | DR | DC, EC |

`qcn-kb/network` reads the KB in and the prover answers goals by entailment, both as
[qcn.md](qcn.md) describes. So `(nonTangentialProperPart A B)` and
`(nonTangentialProperPart B C)` entail `(nonTangentialProperPart A C)` — the table pins
the pair to `#{:ntpp}` — and with it the weaker `(partOfRegion A C)`,
`(properPartOfRegion A C)`, `(regionOverlaps A C)` and `(regionConnectedTo A C)`, whose
denotations are supersets. On the diagonal, `(partOfRegion ?x ?x)` answers every region
and `(properPartOfRegion ?x ?x)` none.

`core/possible-relations kb :rcc8 ctx a b` exposes the network directly — the base
relations still allowed between two regions, a singleton when path consistency pinned
one, the whole universe when nothing is known, `#{}` when the network is unsatisfiable.
`core/qualitative-network kb :rcc8 ctx` hands back the whole tightened network with its
node list and `:consistent?` verdict.

## Cardinal direction (`vaelii.impl.orientation`)

Cardinal direction says which way one place lies from another, on the map's own axes. Its
nine base relations are jointly exhaustive and pairwise disjoint, and each is a pair of
**independent one-dimensional point relations** — east-west on x, north-south on y, each
`:lt` / `:eq` / `:gt`:

| Keyword | Projection | Stored predicate | | Keyword | Projection | Stored predicate |
|---------|-----------|------------------|-|---------|-----------|------------------|
| `:n`  | `[:eq :gt]` | `northOf`     | | `:s`  | `[:eq :lt]` | `southOf`     |
| `:ne` | `[:gt :gt]` | `northeastOf` | | `:sw` | `[:lt :lt]` | `southwestOf` |
| `:e`  | `[:gt :eq]` | `eastOf`      | | `:w`  | `[:lt :eq]` | `westOf`      |
| `:se` | `[:gt :lt]` | `southeastOf` | | `:nw` | `[:lt :gt]` | `northwestOf` |
| `:eq` | `[:eq :eq]` | `sameLocationAs` | | | | |

**There is no 9×9 table**: `vaelii.impl.projection` *computes* composition by composing
each axis separately through the three-relation point algebra and taking the product of
the two results. North-then-east is `:eq;:gt` = `:gt` on x and `:gt;:eq` = `:gt` on y,
which reads back as northeast. The nine directions are exactly the nine `[x y]`
combinations, so every pair the axes compose to names a direction and composition is
never empty ([qcn.md](qcn.md) gives the bijection check). The two disagreeing point
compositions (`:lt;:gt` and `:gt;:lt`) lose information: north-then-south leaves
`#{:n :eq :s}`, and two opposite diagonals lose both axes at once and compose to all nine.

Four **derived** predicates each constrain one axis and leave the other open:

| Predicate | Denotation |
|-----------|-----------|
| `northwardOf` | N, NE, NW |
| `southwardOf` | S, SE, SW |
| `eastwardOf`  | E, NE, SE |
| `westwardOf`  | W, NW, SW |

None contains `:eq`, so none holds of a place and itself — where `partOfRegion` does.
The converse falls out of the projection too: flip both axes, so `converse(:ne) = :sw`
and `:eq` is its own converse.

Every read is the same one, taken with `:cardinal` in place of `:rcc8` —
`core/qualitative-network`, `core/possible-relations`, `core/qualitative-scenario`. So
`(northeastOf A B)` and `(northeastOf B D)`
entail `(northeastOf A D)`, and with it the weaker `(northwardOf A D)` and
`(eastwardOf A D)`; asserting `(northwardOf A B)` and `(eastwardOf A B)` intersects two
single-axis constraints into `#{:ne}` and entails the `(northeastOf A B)` neither one
states.

## Relative direction (`vaelii.impl.relative`)

The compass says where a place is on the map. Relative direction says where a thing is
from where you stand: the mouse on the lion's left, the crow in front of the fox.

### The frame of reference is the context

Relative direction is **ternary** in the literature: A is left of B *from viewpoint C*.
A constraint network is strictly binary — a constraint is a set of relations on a *pair* —
so a ternary calculus does not fit the engine, and the usual fixes (reify the viewpoint
into the relation name, or build a ternary network) either explode the vocabulary or
replace the engine.

Neither is needed, because **a context already is a frame of reference**. A network is
built per context out of the facts visible there, so `(leftOf Mouse Lion)` asserted in
`CxLionMouse` is a claim in that context's frame and in no other. Two
contexts looking at the same individuals from opposite sides state opposite facts,
each context's network answers its own way, and neither contaminates the other. Nothing
declares a viewpoint, because the context is the viewpoint; where a frame has to be argued
about rather than assumed, the frame is a context and the argument is `genlCx`.

So the calculus is binary, it composes as the cardinal directions do, and it runs on the
shared glue in [qcn.md](qcn.md) unchanged.

A context that sees *both* of two incompatible frames inherits both facts, and its network
goes inconsistent: merging two frames without translating between them is an error, and
the network reports it rather than averaging it away.

### The nine relations

The nine are jointly exhaustive and pairwise disjoint, and each is a pair of **independent
one-dimensional point relations** — left-right and front-back, coordinates growing
rightwards and frontwards, each `:lt` / `:eq` / `:gt`:

| Keyword | Projection | Stored predicate | | Keyword | Projection | Stored predicate |
|---------|-----------|------------------|-|---------|-----------|------------------|
| `:left`       | `[:lt :eq]` | `leftOf`        | | `:right`        | `[:gt :eq]` | `rightOf`        |
| `:front`      | `[:eq :gt]` | `inFrontOf`     | | `:behind`       | `[:eq :lt]` | `behind`         |
| `:front-left` | `[:lt :gt]` | `frontLeftOf`   | | `:front-right`  | `[:gt :gt]` | `frontRightOf`   |
| `:behind-left`| `[:lt :lt]` | `behindLeftOf`  | | `:behind-right` | `[:gt :lt]` | `behindRightOf`  |
| `:eq`         | `[:eq :eq]` | `sameRelativePositionAs` | | | | |

Composition and converse are computed by the same projection as the compass's. Left then
in-front is `:lt;:eq` = `:lt` on one axis and `:eq;:gt` = `:gt` on the other, which reads
back as front-left. The converse flips both axes, so `converse(:front-left) =
:behind-right` and `:eq` is its own converse.

Four **derived** predicates each constrain one axis and leave the other open:

| Predicate | Denotation |
|-----------|-----------|
| `leftwardOf`  | left, front-left, behind-left |
| `rightwardOf` | right, front-right, behind-right |
| `frontwardOf` | front, front-left, front-right |
| `rearwardOf`  | behind, behind-left, behind-right |

None contains `:eq`, so none holds of a thing and itself. A derived predicate is what
survives a chain that disagrees on one axis: `(frontLeftOf A B)` with `(behindLeftOf B D)`
pins the left-right axis and loses the front-back one, leaving three relations, no base
one entailed, and `(leftwardOf A D)` entailed.

`sameRelativePositionAs` is a third spelling of coincidence beside the compass's
`sameLocationAs` and the distance chain's `coLocatedWith`. A predicate belongs to exactly
one calculus, each network reads only its own vocabulary, and the three are three different
claims: same compass position, same offset in a frame, zero distance apart.

The same reads again under `:relative`, and each takes the context whose frame it asks
about.

## Qualitative distance (`vaelii.impl.distance`)

Distance is the only one of the four algebras whose relations are an **ordered chain**:
seven classes, each denoting a half-open interval `(lo, hi]` of the non-negative
reals, tiling `[0, ∞)` so that exactly one holds of any two things.

| Keyword | Interval | Stored predicate |
|---------|----------|------------------|
| `:co`         | `(-∞, 0]`      | `coLocatedWith` |
| `:very-close` | `(0, 1]`       | `veryCloseTo` |
| `:close`      | `(1, 10]`      | `closeTo` |
| `:near`       | `(10, 100]`    | `nearTo` |
| `:moderate`   | `(100, 1000]`  | `moderatelyFarFrom` |
| `:far`        | `(1000, 10000]`| `farFrom` |
| `:very-far`   | `(10000, ∞)`   | `veryFarFrom` |

The bounds are the **one** transcribed thing in the namespace, and they are a *scale*
rather than a unit: multiplying every finite bound by one factor changes no entry of the
composition table (`distance_test/scaling-the-bounds-leaves-the-composition-table-unchanged`),
so the numbers fix the ratio between neighbouring classes, not a length in metres. `:co`
runs from `-∞` so that, distance being non-negative, it denotes exactly zero, which makes
it the algebra's identity with no special case in the arithmetic. `:very-far` is unbounded
above because no finite bound is known for the last class.

**Composition is computed from the bounds by the triangle inequality**, not transcribed.
If `d(A,B) ∈ (l1, h1]` and `d(B,C) ∈ (l2, h2]` then

```
max(l1 - h2, l2 - h1)  <  d(A,C)  <=  h1 + h2
```

and the composed set is every class whose own interval meets that range. That range is
exactly the set of distances the geometry admits, so composition is **exact**, no looser
than the truth and no tighter (`distance_test/the-composition-table-matches-the-triangle-inequality`
checks every cell against sampled real distances). A different chain of bounds gives a
different table that is exact for those bounds.

**Distance is symmetric**, so the converse of every class set is itself and `converse` is
the identity function, where the converse of each of the other five algebras is not the
identity. The symmetry lives in the algebra and
deliberately *not* in a `(symmetric P)` declaration: that metadata would hand these
predicates to the generic symmetric-relation prover as well, where the entailment prover
means to claim them alone.

Three **derived** predicates name a range of the chain:

| Predicate | Denotation |
|-----------|-----------|
| `withinNearDistanceOf`  | co-located, very close, close, near |
| `beyondFarDistanceFrom` | far, very far |
| `atSomeDistanceFrom`    | everything but co-located |

`atSomeDistanceFrom` is the complement of the identity, so it holds of no thing and
itself.

### How weakly this composes

Two mid-range classes usually compose to several — `close ∘ close` is
`{co, very-close, close, near}` — because a class is an interval and the triangle
inequality relates intervals loosely. Only a chain through the zero class pins a distance
down: `(coLocatedWith A B)` with `(closeTo B D)` entails `(closeTo A D)` exactly, and
nothing else does short of several facts about one pair intersecting.

So the use of the calculus is **refutation and consistency-checking** rather than pinpoint
entailment. Two things very close to a third *cannot* be very far from each other, and
asserting that they are makes the context's network unsatisfiable and reportable. A
derived range is what usually survives: the same very-close chain entails
`(withinNearDistanceOf A D)` while entailing no class at all.

Exactness is per **pair** of classes: composing a *result* onward loses the correlation
between the two legs that produced it, so this is the one algebra here whose composition
does not associate — `(moderate∘close)∘close` and `moderate∘(close∘close)` differ, both
over-approximating the truth (`distance_test/composition-is-computed-from-the-bounds`).
Path consistency needs composition to *contain* the truth rather than to associate, so
`qcn_algebra_test` leaves associativity out of the laws it holds ([qcn.md](qcn.md)).

The same reads again under `:distance`, and a `core/possible-relations` set with several
members is the normal case on a chain this coarse rather than a sign of a thin KB.
`distance/classify` maps a real number onto its class for anyone bridging to a measured
length.

## The vocabulary

All fifty predicates — fourteen RCC-8, thirteen cardinal, thirteen relative, ten distance —
are declared `binary_predicate` in `resources/kb/upper/CxSpace.txt`, each with its own
`comment` sentex, in one **upper** context rather than the vocabulary head because all four
calculi are *about* space: CxCore holds only the grammar they are stated in
(`binary_predicate`, `comment`), which every domain shares. So the vocabulary is separable —
a KB built from CxCore plus the layers it wants carries regions only if it reasons
about them (the starter, which loads every upper context it finds, takes them). Regions,
places, and the things a frame or a distance is about are all **ordinary individuals**:
every argument position is declared `(arg … spatial)`, the type a location in some
space — physical or mathematical — makes something an instance of. None of the four
calculi needs time, so they relate regions of a plane, squares of an abstract board or a
line such as y=x as readily as fields and rooms. `tangible` sits under `spatial`, so every
animal, made thing and substance qualifies without a further declaration, while a region or
a frame of reference, which occupies space without being made of anything, is declared
`spatial` directly. The context keeps two spaces apart, as it keeps two frames of
reference apart: a prover's network is built per context, so facts about an abstract
plane and facts about the world, stated in two contexts neither of which sees the other,
never meet. A spatial relation between two predicates is refused `:arg-type` under the
constraint-only reading. Under the entailing reading, the default, it is stored, and the
predicate's `:monotonic` memberships defeat the `spatial` memberships it entails
([argtypes.md](argtypes.md#an-argument-constraint-only-adds-support)). `space_test/the-four-calculi-share-no-predicate-and-type-every-argument-spatial`
pins the fifty declarations and their argument types.

Each prover is **opt-in**: `vaelii.core/add-reasoner` registers it by name (`:rcc8`,
`:cardinal`, `:relative`, `:distance`), and until then a KB stores and retrieves the facts
of that calculus as ordinary facts ([qcn.md](qcn.md)). The vocabulary ships either way.
