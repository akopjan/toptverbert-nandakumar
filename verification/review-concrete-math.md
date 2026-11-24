# Mathematical review of the concrete `d > 17` reduction

Reviewed completion sources: `ConcreteComparisonTarget.lean`,
`ConcreteComparison.lean`, `ConcreteReduction.lean`, and
`RelativeComparison.lean`, all under `AkopyanResearch/Completion/`.
Definitions were also checked in `Solution.lean`,
`AkopyanResearch/QuadraticArrangement.lean`,
`AkopyanResearch/SafeQuadraticRealization.lean`, and the new matching/join modules.

This is an independent review of mathematical statements and proof structure.
It does not substitute for the build and axiom-audit logs, and no duplicate
compilation was run for this review.

**Finding:** no weakening of the requested conclusion or mismatch of the
simplex, support, row-action, or face domains was found. The resulting theorem
is an exact **conditional reduction**. The proposition
`AkopyanResearch.ConcreteComparison.RequiredRelativeLifting` remains unproved.
Neither this review nor the new reduction proves the unconditional case
`d > 17`.

## 1. Source, target, and final dimension

`MassSimplex` and `JoinMassCoordinates.Mass (Fin 15)` are the same subtype:
nonnegative real color weights whose sum is one. `FaceSimplex S` additionally
requires weights outside the finite color set `S` to vanish. Nonempty faces
are not empty types; only the boundary of a singleton face is empty.

The chosen section always uses `rowMap 14` and `pairPath 14` on one fixed
fifteen-color coordinate join. Labels outside a face can be extended
arbitrarily: `fromMass_congr_of_support` makes their values irrelevant at
zero mass. Thus `sectionMap_natural` is genuine equality on faces. It does
not compare incompatible iterated-join stages indexed by the face cardinality.

`almostSix_ninety_of_relative_lifting` concludes an almost-six embedding of
the simplex with **90 vertices**, hence dimension 89, into `Fin 16 → ℝ`.
The realization theorem gives a globally continuous ambient map; the reduction
uses its restriction-continuity, as required by the original
`IsAlmostSixEmbedding`. The definitions `coordinateSimplex (Fin 90)` and
`simplex 90`, and respectively `SixDisjointSupports` and `DisjointSupports`,
are definitionally the same conditions. No weaker disjointness predicate is
substituted.

The final theorem uses `17 < d`, which for natural numbers is `18 ≤ d`.
It has exactly the original geometric conclusion: a continuous map on all
Hausdorff-metric convex bodies in Euclidean `d`-space, with `d - 1` real
coordinates, and an absolutely continuous probability measure, excluding
equal values on every convex six-partition of the unit ball with equal
measure. No blocking-set or partition-specific hypothesis was added to this
conclusion. `convex_partition_counterexample_ge_18` in `Solution.lean` obtains the
blocking markers from the already proved `exists_isBlocking_5d`.

## 2. Enumeration relations and pair stabilizers

The target imposes the exact single-row relation
`F (σ * τ) = permSphere τ⁻¹ (F σ)` pointwise in the colors. This prevents the
720 enumerations of one matching from becoming 720 independent sphere
factors. For a one-color face there is only one intrinsic single factor.

The original theorem `stabilizer_PairState_iff` in `PairUniversalSource.lean`
states that the stabilizer of a vertex `(σ, b)` is the identity together with
`(1, tau0)` for phase `false`, or `(1, tau1)` for phase `true`. Consequently
a family containing both phases has trivial stabilizer. A pure family has
a two-element stabilizer, but `Relations.pure` fixes its entire path to
infinity, which is fixed by the full pair group. No additional fixed-point
restriction is imposed on a non-pure pair path.

Mathematically, single orbits correspond to six-matching wordsets, and
non-pure pair orbits correspond to unordered pairs sharing exactly four
words. The choices are the order of the four common words, the order of
each residual pair, and exchange of the two matchings: `4!·2!·2!·2 = 192`,
the order of `PairGroup`. Pure families represent coincident wordsets and
are correctly removed by the constant-infinity condition. This supports
the intended product homotopy-fiber interpretation of `Space S`. A separate
Lean homeomorphism expressing that interpretation was outside this initial
review. It has since been proved in `TargetFiberModel.homotopyFiberHomeomorph`;
the current model review is [final-model-review.md](final-model-review.md).

## 3. The actual comparison map

`matchingSphere` evaluates the actual quadratic table on six matching words,
subtracts the mean separately in the two real coordinates, applies the
original isometry `iso10`, and normalizes. `matchingVector_ne_zero` uses
avoidance of the corresponding matching kernel; normalization is not
assumed to be defined. Its continuity and inverse row-action convention are
proved. Face lifting merely restricts the word before evaluation, so the
comparison is strictly natural.

For a pair, `pair_rows_common` gives equality of the four common raw rows.
After centering, the first four entries differ by a constant in each
coordinate. `MatchingPairCollapse` proves that this difference is orthogonal
to `Comm6`; therefore the common projections agree. The two normalizations
multiply that projection by nonnegative real scalars. The original collapse
is infinity for these configurations, so constant-infinity
paths satisfy the target's start condition. No extra pair-collapse
assumption is hidden in `comparisonMap`.

## 4. What the relative hypothesis says

`RelativeLifting.extend` receives both a boundary table `g` and a prescribed
boundary homotopy `eta` from its comparison image to the chosen section.
It must produce an extension `G` of `g` and an extension `H` of `eta`, with
both endpoints retained. In `step`, the boundary equality for `H` is passed
to `extendStep sk.eta`; it is not discarded. `base` legitimately uses empty
singleton boundaries and obtains a homotopy to the specified section.

The finite induction reaches all fifteen colors. Its extraction of a safe
table uses the fourteen-color face obtained by deleting a zero-mass color,
so zero-mass independence is proved for every such color. Safety is obtained
from the actual `QuadComplement` condition on each six-word matching.

This hypothesis does **not** assert extension of every boundary map into
`QuadComplement`. A boundary homotopy into the concrete target must first be
given. Thus the erroneous universal-connectivity implication of the old
`ComparisonTarget.extend_high` interface is not reintroduced.

## 5. Remaining obligation and audit boundary

The missing term is a proof of `RequiredRelativeLifting` for the concrete
comparison and chosen section. The expected route still needs a proof of
the low-dimensional comparison connectivity, including the action of the
actual comparison on single and minimal-pair linking classes, and a relative
lifting argument preserving the given boundary homotopy. Finite rank bounds,
continuous collapse maps, and the existence of the chosen section do not
alone establish these statements.

`RequiredRelativeLifting` is an explicitly named proposition, not a new axiom
or an automatic instance. However, placing it in a theorem's argument list
does not solve it. The two theorems in `ConcreteReduction.lean` retain that
argument, so they cannot be presented as unconditional proofs of `d > 17`.

The original `Challenge.lean` still has its two statement-template `sorry`
placeholders. It is not imported by the inspected proof closure. A claim
that every file in the archive contains no `sorry` would therefore be
inaccurate; the solver dependency closure and its axiom audit are the
relevant proof checks. That challenge's Theorem B has the bound `36 ≤ d`;
passing its comparator does not certify the stronger `d > 17` assertion.
