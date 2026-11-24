# Changes relative to the supplied reviewed archive

Baseline comparison archive: `akopyan_toptverberg_formalization_reviewed(1).zip`,
SHA-256 `7537d4233d74c40aa3eddad5fd4912287810f6a78c6543dbf75cf2fe364e119b`.
The original `Solution.lean` is preserved byte-for-byte.

## Completed `d > 17` case

Added the unconditional theorems
`AkopyanSixfold.almostSix_ninety` and
`AkopyanSixfold.convex_partition_counterexample_gt_17`.
The previously explicit premise `ConcreteComparison.RequiredRelativeLifting`
is now proved in `ConcreteComparisonLifting.requiredRelativeLifting`.

The mathematical completion closes the following steps:

1. Constructed the fifteen-color values and null-homotopies compatible with
   symmetries, degeneracies, and faces.
2. Identified the single- and pair-coordinate spaces with products of spheres
   and path spaces, and the target space with the homotopy fiber of the
   original pair collapse map.
3. Proved the required rank bounds and critical-pair classification for the
   quadratic arrangement; its complement is 8-connected.
4. Computed the integral homology of the source and target in the required
   range. In degrees 9 and 12, concrete normalized coordinate maps are
   preserved rather than merely abstract free-group ranks.
5. Proved that the local inclusion of the collapsed subspace into the actual
   homotopy fiber induces an isomorphism on `H₁₂`.
6. Proved that the comparison map induces homology isomorphisms through
   degree 13 and a surjection in degree 14. The relative homology of its
   mapping cylinder vanishes through degree 14.
7. Proved the required simplex-skeleton connectivity, universal addition of
   boundary classes, and injectivity of the first relative Hurewicz
   homomorphism. The actual mapping-cylinder pair is 14-connected.
8. Relative compression and homotopy extension yield an exact extension on
   faces, proving the unconditional relative lifting theorem.
9. Induction over fifteen colors constructs a safe compatible planar table,
   realized as an almost-six embedding `Δ⁸⁹ → ℝ¹⁶`.
10. Substituted this map into the original geometric reduction to obtain the
    convex equipartition obstruction for every `d ≥ 18`.

Earlier conditional theorems are retained as general interfaces; the final
theorem requires no extra hypotheses from the user.

## Integration and specification

- Added `PalomarSolution.lean` as the entry point to the final result.
- `Challenge.lean` specifies the original Theorem A and the proved B18.
  All seven interface definitions are preserved; the original B36 Challenge
  is archived separately.
- `comparator.json` compares these two theorems against `PalomarSolution`.
- New proof libraries are included in Lake; all project sources carry the
  required `module` header.
- Resolved the colliding name `AkopyanResearch.homToCont` in
  `CoxeterTriangulation` and `EquivariantPinch64` by using distinct names
  `coxeterHomToCont` and `pinchHomToCont`.
- Lean and all Git dependencies are pinned; verification scripts do not
  invoke `lake update`.

## Trusted base and audit

- The audit covers all public and private declarations by module owner. It
  rejects custom axioms and any transitive axiom dependencies outside
  `propext`, `Classical.choice`, and `Quot.sound`.
- `import all` exposes actual bodies in the Lean 4.35 module system; public
  visibility of key declarations is checked separately.
- The generator synchronizes the explicit inventory of 438 proof modules,
  90 key theorems, and 28 definitions. A finite local limit of 4,000,000
  heartbeats is set for elaborating the audit list.
- The independent specification is checked via a literal reversible
  transformation. The entire local proof dependency closure and configuration
  are hashed.
- 37 infrastructure unit tests include negative cases: omitted owners,
  private axioms, violated independence, and signature mutations.
- Vendored third-party modules are checked against full inventories, SHA-256
  hashes, pinned upstream commits, and preserved licenses.
- `verify.sh` records full logs, exit codes, and input hashes. An additional
  export script checks the selected theorem bodies with the Lean checker,
  NanoDa, and con-ron.

## Semantic review and publication materials

Independent reviews checked exact simplex dimensions, standard topologies
and measures, absence of extra hypotheses, zero-mass handling, ball-measure
normalization, and exactness of boundary extension.

Updated the README, formalization status, and mathematical proof
documentation; prepared primary literature comparisons, provenance manifests,
a metadata draft, and Palomar instructions. Both standard CI and the optional
manual official workflow are pinned by commit SHA. Historical documents
predating the B18 completion are archived in `verification/history-before-d18/`.

See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact final
verification results and scope.

## Companion exposition and reproduction

Added the combined mathematical exposition `docs/PROOF_COMPANION.md`,
explanations of the target section construction and the analytic transition
from the height table, and a reproducible PDF renderer with preserved font
licenses. The verified PDF is included in `verification/d18-release/`.

Prepared `verification/d18-publication/SUBMISSION_HANDOFF.md` with exact
technical fields. The final proof sources were additionally extracted from a
clean ZIP archive and compiled from scratch with zero pre-existing project
objects, passing all six verification stages at 10:23:29 UTC with unchanged
sources.
