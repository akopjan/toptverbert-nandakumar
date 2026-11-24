# Final statement and reduction review

This is a source-level review of the closed result and its interpretation.
It supplements the recorded Lean checks; it is not a new kernel execution
or external human peer review.

## Closed declaration and actual spaces

`AkopyanSixfold.convex_partition_counterexample_gt_17` in
`AkopyanResearch/Completion/DimensionEighteen.lean` has exactly the explicit
arguments `d : ℕ` and `hd : 17 < d`. Its proof applies the supplied geometric
reduction with the proved
`AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting`.
The helper with a lifting argument remains an internal intermediate
theorem; that argument is discharged in the exported declaration.

The original `Solution.lean` defines `Ambient d` as Mathlib's Euclidean
space, `Body d` as `ConvexBody (Ambient d)`, and `unitBall d` as the closed
unit ball. Its six-partition condition requires exact coverage and
nonempty, pairwise disjoint interiors. The almost-six predicate requires
continuity on the standard simplex and separation of six points with
pairwise disjoint barycentric supports. It imposes no injectivity condition
on individual faces.

The separately compiled Mathlib-only semantic reference captures these
standard topologies and measure structures before importing the proof.
The final B18 declaration directly inhabits its independently specified
type. The original A also transports to a continuous map from the actual
simplex subtype to Euclidean six-space. The recorded nonvacuity witnesses
are genuine six distinct simplex vertices and a concrete matching.

## Dimension and boundary conditions

For a nonempty `S : Finset (Fin 15)`, the face dimension is `S.card - 1`,
which is at most fourteen. The actual comparison cylinder and its top are
eight-connected. Relative homology vanishing in degrees nine through
fourteen supplies six successive genuine relative Hurewicz steps.
`MappingCylinderFaceLifting.extend` then applies the resulting
fourteen-connectivity to that same face dimension.

Its conclusion preserves both the boundary map and the complete prescribed
boundary homotopy as literal equalities. Its two endpoint identities also
hold on the whole face. The zero-dimensional case is included. The
completion does not replace the arrangement spaces with predicates that
already assert the desired connectivity or lifting property.

## Geometry and positive measure

The unchanged `Solution.lean` proves `exists_isBlocking_5d` for every
`d ≥ 18`. Its definition of blocking includes central partitions with
degenerate parts. This is needed when taking Hausdorff limits in the
compactness argument for `exists_eta_of_isBlocking`; the final partition
statement still requires nonempty interiors.

The private proof `normalized_ball_measure_props` explicitly constructs
the normalized restriction of volume to a smaller positive-radius closed
ball. Its local equalities are `mu univ = 1`, `mu S = 1` and
`mu (unitBall d) = 1`. Thus the final obstruction is not obtained by giving
the partitioned unit ball measure zero. The exported statement does not
request this additional normalization, but the chosen witness satisfies it.

The functional in `convex_partition_of_embedding_and_blocking` is defined
on every `Body d`. Its first coordinate is the sum of nonnegative inward
distances to the markers. The other coordinates are the corresponding
perspective of the almost-six map. Boundedness on the compact simplex
proves continuity when this sum is zero. Equal functional values therefore
lead either to the blocking contradiction at total weight zero, or to six
normalized points with disjoint supports and equal images at positive
total weight. These are exactly the two branches of the supplied proof.

The new ninety-vertex map has target dimension sixteen. Joining with the
constant map on five vertices adds five vertices and one target coordinate;
after `d - 18` steps the counts are `5 * d` and `d - 2`, as required by the
geometric transfer. No additional embedding or measure hypothesis remains
in the closed B18 theorem.

## Scope of the publication claim

This review confirms the interpretation of the formal statements and the
listed source-level reductions. It does not establish bibliographic
priority, a complete human author list, project licensing authority, or
Palomar registration. Those distinctions are preserved in the release
documentation and the submission handoff.
