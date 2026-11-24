# Statement and relative-lifting review

## Scope and verification state

This is a semantic source review of the independent publication statement and
of the exact boundary lifting construction. The generic compression,
rectification, cubical lifting, face homeomorphism, and face lifting modules
have each compiled with Lean 4.35.0. At the time of this review, the concrete
comparison connectivity, its lifting wrapper, and the final
`DimensionEighteen` theorem still await the remaining integrated dependency
checks. This review does not replace the final kernel, axiom, or comparator
gates.

## The statement

`Challenge.lean` and `DimensionEighteen.lean` give the same complete signature
for `AkopyanSixfold.convex_partition_counterexample_gt_17`. The only theorem
parameters are `(d : ℕ)` and `(hd : 17 < d)`. There is no assumption of an
almost embedding, a safe table, a blocking configuration, a homology
calculation, or a relative lifting theorem. Those are supplied by the proof
chain and are not additional premises of the published statement.

The seven interface definitions in `Challenge` are unchanged from both the
archived original specification and the unchanged `Solution.lean`. In
particular:

- `Ambient d` is `EuclideanSpace ℝ (Fin d)`.
- `Body d` is Mathlib's `ConvexBody (Ambient d)`: a nonempty compact convex
  subset. Mathlib's `Analysis/Convex/Body.lean` gives this type the Hausdorff
  metric, with `dist K L = Metric.hausdorffDist K L`. No replacement topology
  for bodies or Euclidean ambient spaces was found in the project sources.
- `Phi : Body d → (Fin (d - 1) → ℝ)` is required to be continuous. The finite
  product target represents exactly `d - 1` continuous real functionals.
- `mu : Measure (Ambient d)` satisfies `IsProbabilityMeasure mu`, meaning
  `mu Set.univ = 1`, and `mu.AbsolutelyContinuous volume`, meaning that every
  volume-null set is `mu`-null. The standard Euclidean `volume` is used.
- `IsSixPartition C` requires the union of the six bodies to be the closed
  unit ball, every interior to be nonempty, and distinct interiors to be
  disjoint. Boundary overlap is permitted, as for a usual convex partition.
- Equal measure is stated literally as
  `mu (C i) = mu (unitBall d) / 6`. The signature does not additionally assert
  that the measure is supported on the ball; no such assertion is made here.
- The witnesses `Phi` and `mu` are chosen before the universal quantifier over
  partitions. The conclusion `∃ i, Phi (C i) ≠ Phi (C 0)` rules out equality
  of all six vector values, and hence simultaneous equality of all the real
  functionals.

Since `d` is natural, `17 < d` includes `d = 18`. The regression suite changes
this assumption to `18 < d` and detects the signature mismatch. Theorem A and
all seven definitions remain unchanged. `Solution.lean` remains byte-for-byte
identical, and the old specification is archived as text rather than as an
additional Lean specification module.

## The zero-dimensional face

For a nonempty singleton `S`, the face dimension `S.card - 1` is zero.
`faceCube S hS` is still defined: the original face-to-ball homeomorphism is
composed with the inverse cube-to-ball homeomorphism. Neither construction
requires positive dimension. The cube `Fin 0 → I` is a singleton and its
boundary is empty. The actual `FaceBoundary S` is likewise empty, as also
proved in `RelativeFaceDiagram.boundary_isEmpty_of_card_le_one`.

The zero-dimensional compression case is explicit in
`MappingCylinderCompression.disk_top`. Path connectedness of the source
makes the actual cylinder top nonempty and path connected. Its zeroth
homotopy group is a subsingleton; the pair's component-surjectivity hypothesis
then makes the actual inclusion map on components bijective. The imported
zero-disk compression theorem applies. Thus the proof does not use a
positive-dimensional relative group at dimension zero, and does not rely on
a vacuous connectivity assertion for an empty top.

`MappingCylinderFaceLifting.extend` consequently supplies a source point and
a path to the prescribed target section on each singleton face. The empty
boundary conditions are vacuous; the two endpoint conditions remain real
requirements. This is exactly the input used by `RelativeComparison.base`.

## Exact boundary homotopies

The initial homotopy extension into the mapping cylinder makes the boundary
square strict. Relative compression preserves the boundary map. Retracting
the concatenated homotopies to the target gives the prescribed boundary path
with parameter `pause(t) = max(0, 4*t - 3)`.

`CubicalHomotopyRectification.rectify` removes this pause. On the entire
boundary of the cylinder it interpolates the side parameter from `pause(t)`
to `t`, and keeps the bottom and top maps fixed. The three closed pieces
agree on their intersections because both parameter maps fix zero and one.
`Cube.splitAtLast` identifies their union with the boundary of the
next-dimensional cube; the actual cubical homotopy extension theorem extends
the correction. This argument also applies when the original cube has
dimension zero.

The final conclusions are literal equalities:
`G a.val = g a` and `H a.val = eta a` as continuous maps `I → Y`, together
with `H x 0 = f (G x)` and `H x 1 = p x` on the whole domain. Currying gives
an actual continuous map into the compact-open path space. Transport through
`faceBoundaryCube` preserves these equalities without another change of the
time parameter. They match all four fields required by
`RelativeComparison.RelativeLifting`, so the existing face-gluing induction
receives its exact specified boundary data.

## Recorded source hashes

These hashes identify the files inspected, not a claim that every final
integration gate has passed.

Recorded UTC: 2026-11-24T08:33:25.867548+00:00

- `Challenge.lean`: `d7b36eaa7daf9c593b205f0fc3f748c0a6c8ab3ba726269947d71328c4ce4e66`
- `Solution.lean`: `41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23`
- `AkopyanResearch/Completion/DimensionEighteen.lean`: `24f45bfe59787b9308d242083be6163f7852abaec0bc2565cd90fafdaeac7ad8`
- `AkopyanResearch/Completion/MappingCylinderCompression.lean`: `5b0d8011195861e56eac080fcbc97a9d60ce65b176aaaecd603c772056c2271b`
- `AkopyanResearch/Completion/CubicalHomotopyRectification.lean`: `a7cddcfcba53e785c25db533fab0f2b91a357fb89d5712630627db92c90208eb`
- `AkopyanResearch/Completion/MappingCylinderLifting.lean`: `3a9b8aea1434b080ced2d39392413d1e744327805791e29e0228982b792ef237`
- `AkopyanResearch/Completion/FaceCubicalHomeomorph.lean`: `5267579c771cc80b307f7b0201f4fb18212bcb69cb1888877c1e854e4b55ffe8`
- `AkopyanResearch/Completion/MappingCylinderFaceLifting.lean`: `730a5b802b3446e0afe8900898556dbb02b6e46f1299f43b4878c55f3f8f31f7`
- `AkopyanResearch/Completion/ConcreteComparisonLifting.lean`: `390fdbabb29938ad3abaa649c1cf561b1fc0e91e4e8691b5fd4b1aa8eaa7d4f2`
