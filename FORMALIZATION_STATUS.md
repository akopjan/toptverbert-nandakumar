# Formalization Status

## Proved result

**The unconditional `d > 17` case is complete.** The module
`AkopyanResearch/Completion/DimensionEighteen.lean` provides the theorems
`AkopyanSixfold.almostSix_ninety` and
`AkopyanSixfold.convex_partition_counterexample_gt_17`.
The latter takes only `d : ℕ` and `hd : 17 < d`; the proposition
`RequiredRelativeLifting` is proved internally and is not an extra hypothesis.

Let `d : ℕ` satisfy `17 < d`, and let `Ambient d = EuclideanSpace ℝ (Fin d)`.
The space `Body d = ConvexBody (Ambient d)` consists of nonempty compact
convex sets endowed with the Hausdorff metric. The theorem proves the
existence of a continuous map `Phi : Body d → (Fin (d - 1) → ℝ)` and a
probability measure `mu : Measure (Ambient d)`, absolutely continuous with
respect to Lebesgue volume, such that for every convex six-partition of the
closed unit ball `C : Fin 6 → Body d`, the equalities
`mu (C i) = mu (unitBall d) / 6` for all `i` imply `Phi (C i) ≠ Phi (C 0)`
for at least one `i`.

The partition predicate requires nonempty pairwise-disjoint interiors whose
union equals the closed unit ball. Internally, the geometric proof constructs
the normalized volume of a smaller central ball and establishes
`mu (unitBall d) = 1`; the obstruction does not arise from a zero-measure
unit ball.

The original unconditional Theorem A (`AkopyanSixfold.tverberg_counterexample`,
an almost-six embedding `Δ³⁵ → ℝ⁶`) is retained. The new construction
provides an almost-six embedding `Δ⁸⁹ → ℝ¹⁶` continuous on the standard
simplex.

## Closed proof chain

### 1. Concrete spaces and comparison maps

For every nonempty color set `S`, the complement `Y_S` of the quadratic
subspace arrangement is paired with a target space `P_S` homeomorphic to the
homotopy fiber of the original pair collapse map, and a continuous comparison
map `c_S : Y_S → P_S` built from normalized single-matching tests and pair
paths. All symmetry, zero-mass degeneracy, and face-compatibility conditions
are proved.

Both spaces are 8-connected. The reduced integral homology of `Y_S` through
degree 13 and of `P_S` through degree 14 is nonzero only in degrees 9 and 12,
with coordinates indexed by six-matchings and critical pairs. The isomorphisms
are established for concrete normalized maps, including primitive integral
generators.

Key interfaces: `QuadraticSourceCoordinates.singleCoordinatesIso`,
`QuadraticSourceCoordinates.collapsedCoordinatesIso`,
`TargetPairCoordinates.homologyCoordinatesIso`.

### 2. Local comparison and relative homology

`PairEndpointHomology.collapsedInclusion_isIso` proves that the inclusion of
the collapsed locus into the local homotopy fiber induces an isomorphism on
`H₁₂`, using the path-space endpoint fibration, the relative long exact
sequence, Hurewicz naturality, and explicit coordinate charts.

Combining the single and pair coordinate isomorphisms yields
`ConcreteComparisonHomology.homology_isIso`: the comparison map `c_S` induces
homology isomorphisms through degree 13 and an epimorphism in degree 14. For
its mapping cylinder `M_S`, `H_k(M_S, Y_S) = 0` for `1 ≤ k ≤ 14`.

### 3. Relative connectivity

`SimplexSkeletonRetraction` and `SimplexSkeletonConnectivity` construct a
retraction and prove connectivity of the required simplex skeleton. Addition
of boundary face classes is proved for the universal simplicial pair and
transported to any pair with a fixed boundary normalization, yielding
injectivity of the first relative Hurewicz homomorphism.

Initial 8-connectivity and vanishing relative homology inductively yield
connectivity in degrees 9 through 14:
`ConcreteComparisonConnectivity.cylinder_pair_fourteen`.

### 4. Exact extension and ninety vertices

Relative disk compression and the homotopy extension property eliminate
boundary reparametrization. `MappingCylinderFaceLifting.extend` preserves
prescribed boundary values literally, including on 0-dimensional faces,
yielding the unconditional theorem
`ConcreteComparisonLifting.requiredRelativeLifting`.

For any subset of at most 15 colors, the face dimension is at most 14.
Relative induction therefore constructs a continuous, compatible, safe
planar quadratic table. Fourteen mass coordinates and two averaged height
coordinates produce `Δ⁸⁹ → ℝ¹⁶` (`AkopyanSixfold.almostSix_ninety`).

### 5. Convex geometry

The original `Solution.lean` contains the geometric reduction valid for all
`d ≥ 18`: central blocking markers (`exists_isBlocking_5d`), dimension bounds
for exceptional configurations of rank ≤ 4 and rank 5, Blaschke compactness,
normalized small-ball measure, and Hausdorff-continuous inward-distance
functionals. Padding from 90 vertices to `5d` vertices adds 5 vertices and 1
target coordinate per dimension step. Substituting `almostSix_ninety` yields
`AkopyanSixfold.convex_partition_counterexample_gt_17`.

Detailed exposition: [docs/DIMENSION_EIGHTEEN_PROOF.md](docs/DIMENSION_EIGHTEEN_PROOF.md).
Independent analytic and geometric review:
[verification/d18-extension-2026-11-24/ANALYTIC_GEOMETRIC_REVIEW.md](verification/d18-extension-2026-11-24/ANALYTIC_GEOMETRIC_REVIEW.md).

## Axioms and independent specification

Proof modules contain no `sorry`, custom axioms, `admit`, or `sorryAx`
dependencies. The audit permits only `propext`, `Classical.choice`, and
`Quot.sound`.

`Audit.lean` inspects all declaration kinds by owning module, including
private definitions and auxiliary lemmas, using `import all` and private
environment views in Lean 4.35, and checks public accessibility and exact
kinds for 90 key theorems and 28 definitions.

The independent `Challenge.lean` retains two template `sorry` placeholders
for Comparator. Neither `PalomarSolution` nor any module in its dependency
closure imports `Challenge`. `scripts/check-statements.py` verifies exact
reversible substitution of the proved theorems into `Challenge.lean`.

`Solution.lean` is preserved byte-for-byte
(`41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23`), and
the former B36 specification is archived at
`verification/original-specification/Challenge36.lean.txt`
(`cfd2f4648eee325094309614e72c032d7822cb1c23f09e941b86c36c667cff05`).

## Completed verifications

<!-- BEGIN CURRENT VERIFICATION STATUS -->
The full integration gate completed on **24 November 2026 at 08:56:01 UTC**.
All six stages exited with code 0: structure check, module provenance,
37 unit tests, full build, literal statement check, and fresh declaration
audit. The audit checked **16,765 declarations across 438 proof modules**
(14,244 public and 2,521 private; 12,586 theorems and 3,975 definitions).
All **472 input files** remained unchanged (`verification/d18-final-retry/results.json`).

An independent cumulative source rebuild starting from zero project build
objects completed at **09:01:10 UTC**, passing all six stages with all 472
input hashes matching the main gate (`verification/d18-clean-final/results.json`).

An immutable ZIP snapshot of the final proof sources was also extracted and
compiled from scratch with zero pre-existing project objects, passing all six
stages at **10:23:29 UTC** (`verification/d18-archive-final/`).

The separate compiled-interface comparison between `Challenge` and the proof
closure passed at **08:59:09 UTC**, matching all nine types and seven
definition bodies across 419 sources and 1,257 compiled objects
(`verification/d18-compiled-interface/results.json`).

The export of the four final theorems (`tverberg_counterexample`,
`almostSix_ninety`, `convex_partition_counterexample_gt_17`,
`requiredRelativeLifting`) and 58,974 transitive theorem dependencies
(700,996,206 bytes, SHA-256
`978d77cdeecf295f3ae79fbc5c18f5d42fb66e911dc7ce0e758925c7d543a0be`) was
accepted with exit code 0 by **Lean checker, NanoDa, and con-ron** at
**09:15:21 UTC** (`verification/d18-kernels/results.json`), and by the
Palomar-approved con-ron from Lean 4.36.0-rc1 at **09:18:19 UTC**
(`verification/d18-approved-con-ron/results.json`).

Direct object comparisons between the main, clean, and archive builds confirm
agreement of all stored declarations, types, proof bodies, and imports
(`verification/d18-clean-final/object-comparison/REPORT.md`,
`verification/d18-archive-object-comparison/`).
<!-- END CURRENT VERIFICATION STATUS -->

Toolchain: Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
All nine Git dependencies match their pinned revisions, and all 164 vendored
topology modules match their 13 provenance manifests (`python3 scripts/check-provenance.py`).

See [verification/README.md](verification/README.md),
[docs/PALOMAR_PREPARATION.md](docs/PALOMAR_PREPARATION.md),
[docs/MATHEMATICAL_CONTEXT.md](docs/MATHEMATICAL_CONTEXT.md), and
[verification/d18-publication/REPORT.md](verification/d18-publication/REPORT.md).
