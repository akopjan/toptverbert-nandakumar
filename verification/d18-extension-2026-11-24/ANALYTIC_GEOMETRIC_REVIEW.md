# Analytic and convex-geometric review of the dimension-eighteen extension

Date: 2026-11-24. Scope: the passage from a continuous compatible safe quadratic
table to an actual almost-six embedding of the 89-simplex, and the passage from
that embedding to the convex-body theorem for every natural number `d > 17`.

**Result:** no missing mathematical input, dimension mismatch, restricted
continuity domain, or weakened partition predicate was found in these two
passages. This is a targeted review of the definitions, formulas and critical
proof branches. It is not a separate line-by-line review of every geometric
parametrization in `Solution.lean`. The independent statement check and complete
final-theorem kernel/axiom audit are separate verification tasks.

## 1. The statement represented by the types

In `Solution.lean`, `simplex n` is the subset of `Fin n → ℝ` defined by
nonnegative coordinates summing to one. Thus `simplex 90` is the ordinary
89-dimensional simplex. `DisjointSupports` asserts coordinatewise disjointness
for each distinct pair among all six points. `IsAlmostSixEmbedding` consists of
`ContinuousOn` on this actual simplex and separation of every such six-tuple;
it contains no additional safety predicate or restricted collection of faces.

`Ambient d` is `EuclideanSpace ℝ (Fin d)`. `Body d` is Mathlib's
`ConvexBody (Ambient d)`, with its Hausdorff topology: its elements are nonempty
compact convex sets. `IsSixPartition C` requires exact union equal to the closed
unit ball, nonempty interior of each of the six parts, and pairwise disjoint
interiors. The final functional is continuous on **all** `Body d`, not only the
bodies occurring in a particular partition.

Evidence: `Solution.lean`, definitions `simplex`, `DisjointSupports`,
`IsAlmostSixEmbedding`, `Ambient`, `Body`, `unitBall`, `IsSixPartition` and
`IsBlocking` near the beginning of the file; the exact final statement in
`AkopyanResearch/Completion/DimensionEighteen.lean`.

## 2. Safe quadratic table to the actual simplex map

The input is a function
`H : MassSimplex → TableWords → Fin 2 → ℝ`, where `MassSimplex` is the standard
simplex on fifteen coordinates and `TableWords = Fin 15 → Fin 6`. Its continuity,
quadraticity, compatibility at zero masses and separation for every matching
`Fin 15 → Equiv.Perm (Fin 6)` are separate explicit hypotheses.

`exists_safe_factored_quadratic_coefficients` in `SafeQuadraticBridge.lean`
extracts the actual canonical coefficients. Compatibility makes a coefficient vanish when
its required mass factor vanishes. The proof does **not** divide this
coefficient by a possibly zero mass. `BoundaryRegularization` uses the
continuous function `a / max δ p`, for a proved `δ > 0`, to approximate a
boundary-vanishing coefficient by `p * b`. `FiniteRegularization` obtains a
uniform positive margin for the finitely many matching tests on the compact
mass simplex. The approximation preserves all their nonvanishing conditions.

`SafeQuadraticRealization` then produces linear and two-color coefficients.
Its evaluation formula subtracts only the word-independent constant feature,
which preserves separation. `QuadraticRealization` extends the coefficients
to all of `Fin 15 → ℝ` using the explicit continuous simplex retraction
`simplexRetractionMap`; its denominator is `max 1 (positiveMass z) ≥ 1`, and
the retraction fixes every point of the simplex.

The map `quadraticMapNinety` uses the bijection `Fin 15 × Fin 6 ≃ Fin 90`.
Its target has fourteen color-mass coordinates and two quadratic height
coordinates, hence exactly sixteen coordinates. Equal images imply equality
of the first fourteen masses; the sum-to-one condition gives equality of the
fifteenth. For each color, `equal_mass_disjoint_matrix` proves that six
nonnegative, pairwise support-disjoint rows with their common mass form a
scaled permutation matrix. Its zero-mass branch proves that all entries are
zero and chooses any permutation. Thus no positive-mass assumption is omitted.
The matching separation hypothesis now applies to the two height coordinates.

The resulting theorem supplies a function on the full space
`(Fin 90 → ℝ) → (Fin 16 → ℝ)` which is globally continuous; its separation
statement is exactly the support-disjointness statement on the standard
simplex. `AkopyanSixfold.almostSix_ninety_of_relative_lifting` in
`ConcreteReduction.lean` merely packages this as `IsAlmostSixEmbedding`.

Evidence: `BoundaryRegularization.lean`, `FiniteRegularization.lean`,
`SafeQuadraticBridge.lean`, `SafeQuadraticRealization.lean`, and
`QuadraticRealization.lean`, especially `simplexRetraction_mem`,
`simplexRetraction_eq_self`, `equal_mass_disjoint_matrix`,
`quadraticHeight_no_common_value` and `quadraticMapNinety_isAlmostSix`.

## 3. Dimension padding and genuine geometric blocking

`join_almostSixEmbedding` constructs the ordinary weighted join and verifies
continuity at zero weights with `continuousOn_perspective`. Joining with the
five-vertex simplex mapped to `ℝ⁰` adds five vertices and one target coordinate.
The latter factor is almost-six because six nonempty disjoint supports cannot
fit into five vertices; this is proved by a finite pigeonhole argument.

Starting with ninety vertices and target dimension sixteen, `d - 18` padding
steps give `90 + 5(d - 18) = 5d` vertices and
`16 + (d - 18) = d - 2` target coordinates. The reindexing lemmas transport the
actual simplex and support conditions.

`exists_isBlocking_5d` proves existence of the required markers, rather than
assuming them. Its definition of `IsBlocking` also covers partitions with
degenerate parts; this is necessary for the compactness argument. The proof
chooses an actual configuration of `5d` points in the open unit ball outside
two finite unions of differentiable images of smaller-dimensional parameter
spaces. The two bounds, with `m = 5d`, are:

| Branch | Upper bound for parameter dimension | Ambient configuration dimension |
| --- | ---: | ---: |
| Rank at most four | `4d + 17 + m(d - 1)` | `md` |
| Rank five | `5d - 1 + m(d - 1)` | `md` |

The first strict inequality is exactly `17 < d`; the second has a margin of
one. The finite configurations, differentiability and dimension estimates are
proved in `Solution.lean`. `volume_image_eq_zero_of_card_lt` reduces the null
image assertion to Mathlib's actual Haar-measure theorem for differentiable
maps and null sets. Nonempty openness of the configurations inside the ball
gives positive measure, so a configuration outside both exceptional sets
exists.

For any central partition missed by the markers, the actual separating normals
are constructed by geometric Hahn–Banach. The proof splits according to
linear independence of five normal row sums. In the rank-five branch,
`rank5_triangle_dependent` and `exists_treeParam` lead to
`mem_range_maxRankMap_of_tree`. In the other branch,
`separating_normals_in_rref4_span` and `mem_range_planeDagMap_of_dag` give the
other exceptional parametrization. Both contradict the choice of markers.
The lower-rank coverage explicitly treats parts with empty interior: if a part
is inactive, at most ten pairs of active parts remain, and their projective
normal directions use at most thirty parameters, within the proved bound of
thirty-three. No polyhedral-partition hypothesis is added.

Evidence: `Solution.lean`, `join_almostSixEmbedding`,
`emptyFive_almostSixEmbedding`, `iterated_padding_from`,
`card_maxRankParamIdx`, `card_planeDagParamIdx`, and the complete proof of
`exists_isBlocking_5d`.

## 4. Continuity, positive probability and the obstruction

For a marker `p a : Ambient d` and body `C : Body d`, the weight is the actual
inward distance `w(C,a) = infDist (p a) Cᶜ`. The complement is proved nonempty
when `d > 0`; `inwardDist_pos_iff` identifies positive weight with membership
in the interior. `inwardDist_le` proves the Hausdorff Lipschitz estimate using
convex separation, and `continuous_inwardDist` follows.

Let `s(C)` be the sum of these nonnegative weights. The functional consists of
`s(C)` and `s(C) * g(w(C)/s(C))`, with zero in the latter coordinates when
`s(C) = 0`. This has `1 + (d - 2) = d - 1` coordinates. The perspective
continuity proof uses boundedness of `g` on the compact simplex to handle
`s(C) → 0`; it therefore proves continuity on every body, including bodies
containing no marker in their interior.

Blaschke compactness is applied to bodies contained in the unit ball.
`exists_eta_of_isBlocking` encodes coverage, interior disjointness and absence
of markers as closed conditions. It obtains `0 < η < 1` such that every
partition whose pieces meet the closed `η`-ball is hit in some interior.
Allowing degenerate parts in `IsBlocking` makes its use at the compact limit
valid.

The chosen measure is explicitly
`μ = (volume S)⁻¹ • volume.restrict S`, where `S` is the closed `η`-ball.
`normalized_ball_measure_props` proves `0 < volume S < ∞`,
`μ(univ) = μ(S) = μ(unitBall d) = 1`, and `μ ≪ volume`. Consequently a fair
piece has measure `1/6`; the obstruction does not rely on zero mass or an
infinite normalization. `fair_meets_eta_ball` shows that every fair piece
meets `S`.

If all six functional values were equal, their first coordinates would give
a common value of `s`. If it were zero, uniform blocking would contradict
vanishing of every marker weight. Otherwise the normalized weight vectors
would be six points of the simplex with pairwise disjoint supports, because
the interiors of the bodies are disjoint. Equality of the remaining
coordinates would contradict the almost-six property of `g`.

Evidence: `Solution.lean`, `continuousOn_perspective`, `inwardDist_pos_iff`,
`continuous_inwardDist`, `blaschke_isCompact_subsets_unitBall`,
`exists_eta_of_isBlocking`, `normalized_ball_measure_props`,
`convex_partition_of_embedding_and_blocking` and
`convex_partition_counterexample_ge_18`.

## 5. Dependency boundary and verification

The older theorem `AkopyanSixfold.convex_partition_counterexample_ge_18` is a valid
conditional helper with the actual ninety-vertex embedding as an argument.
The new `AkopyanSixfold.convex_partition_counterexample_gt_17` in
`DimensionEighteen.lean` supplies it through
`ConcreteComparisonLifting.requiredRelativeLifting`; no marker,
measure, safe table or almost-six embedding is added as a new assumption of
the final theorem. The unconditional proof of that topological lifting
theorem is outside this review's scope and is checked by the other review
and kernel gates.

`AnalyticGeometricAudit.lean` prints the transitive axiom dependencies of nine
public results covering regularization, actual realization, joins, blocking,
compactness, the margin and the final geometric transfer. The output is
recorded in `ANALYTIC_GEOMETRIC_AXIOMS.txt`. This supplements, rather than
replaces, the full owner-level and final-theorem audits.

The corrected diagnostic, beginning with the required `module` header,
completed successfully under Lean 4.35.0. Each of the nine results depends
only on `propext`, `Classical.choice` and `Quot.sound`; none depends on
`sorryAx` or a newly introduced axiom.

Publication note: the old conditional helper's docstring says that the
ninety-vertex embedding "remains open". That historical wording should be
updated now that the unconditional theorem is supplied in
`Completion/DimensionEighteen.lean`; it does not alter the helper's proof or
its explicit type.
