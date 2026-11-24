# TopTverberg — Lean 4.35.0

This project proves an unconditional obstruction to convex six-part
equipartition in every natural dimension **`d > 17`**. The concrete relative
lifting theorem needed for this bound is proved inside the project; it is
not an additional hypothesis of the final result.

## Mathematical statements

Let `d : ℕ` satisfy `17 < d`. The real vector space
`Ambient d = EuclideanSpace ℝ (Fin d)` is Euclidean `d`-space.
The space `Body d = ConvexBody (Ambient d)` consists of nonempty compact
convex subsets, with the Hausdorff metric. The set
`unitBall d : Set (Ambient d)` is the closed unit ball in `Ambient d`.

The main theorem produces a continuous map
`Phi : Body d → (Fin (d - 1) → ℝ)` and a probability measure
`mu : Measure (Ambient d)`, absolutely continuous with respect to volume.
For every family `C : Fin 6 → Body d` whose union is `unitBall d` and whose
nonempty interiors are pairwise disjoint, the equalities
`mu (C i) = mu (unitBall d) / 6` imply that some `Phi (C i)` differs from
`Phi (C 0)`. Thus the six parts cannot simultaneously have equal measure
and equal values of all `d - 1` functionals. Each functional depends on
the individual body, and `Phi` is defined on the entire space `Body d`.

The construction internally proves `mu (unitBall d) = 1`; it does not obtain
the obstruction from a zero-mass ball. This normalization is stronger than
what the exported statement explicitly requests.

| Declaration in `AkopyanSixfold` | Conclusion |
|---|---|
| `tverberg_counterexample` | An almost-six embedding `Δ³⁵ → ℝ⁶`, the original theorem A. |
| `almostSix_ninety` | An almost-six embedding `Δ⁸⁹ → ℝ¹⁶`. |
| `convex_partition_counterexample_gt_17` | The convex equipartition obstruction for every `d > 17`. |

An almost-six embedding is a continuous map of a simplex such that the
images of any six pairwise disjoint faces have empty common intersection.
The term does not require injectivity. The new declarations are in
[DimensionEighteen.lean](AkopyanResearch/Completion/DimensionEighteen.lean).

## Using and building the project

The public entry point is:

```lean
import PalomarSolution

#check AkopyanSixfold.almostSix_ninety
#check AkopyanSixfold.convex_partition_counterexample_gt_17
```

The project pins `leanprover/lean4:v4.35.0` and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All nine Git dependencies have
full commit revisions in [lake-manifest.json](lake-manifest.json).
With the pinned toolchain installed, run:

```sh
lake exe cache get
SKIP_MATHLIB_CACHE=1 bash scripts/verify.sh
```

An ordinary complete build is `lake build`. The verification script also
checks project structure, imported-source provenance, regression tests,
the literal Challenge statements and every project declaration's axiom
dependencies. It records commands, exit codes and input hashes before and
after verification. The Python checks require Python 3.11 or newer.

## Proof of the dimension-eighteen bound

The completion constructs an actual comparison map from a quadratic
subspace-arrangement complement to a specified homotopy fiber. Its integral
homology maps are identified in degrees 9 and 12 using explicit local
models, normal tubes, excision and Mayer–Vietoris. This calculates the
concrete coordinate maps, including primitive integral generators.

The mapping-cylinder pair has zero relative homology through degree 14.
A proved relative Hurewicz argument raises its connectivity to 14, and
homotopy extension preserves the prescribed boundary homotopy exactly.
This yields `ConcreteComparisonLifting.requiredRelativeLifting`.

Relative induction over fifteen colors then constructs a compatible safe
planar table. Fourteen mass coordinates and two height coordinates realize
it as `Δ⁸⁹ → ℝ¹⁶`. The original convex-geometric reduction applies in every
dimension `d ≥ 18`. The detailed chain of formalized maps and theorems is in
[DIMENSION_EIGHTEEN_PROOF.md](docs/DIMENSION_EIGHTEEN_PROOF.md).
[PROOF_MAP.md](docs/PROOF_MAP.md) links the twenty principal interfaces
to their owning files and distinguishes the publication and audit closures.

## Specification, trust and verification

Proof modules contain no `sorry` or new axioms. The complete declaration
audit permits only `propext`, `Classical.choice` and `Quot.sound`, including
dependencies of private and generated declarations. The two deliberate
`sorry` placeholders in [Challenge.lean](Challenge.lean) specify Comparator
tasks. The proof entry point and its dependency closure do not import
Challenge.

The original [Solution.lean](Solution.lean) is unchanged byte-for-byte.
Its historical comments describe the earlier state. The current Challenge
retains theorem A and seven interface definitions, and replaces the former
dimension-36 target with the proved dimension-18 result. The original
specification is archived separately.

The full build and owner audit, the separate cumulative source rebuild,
and the independent compiled-interface comparison have passed. The audit
covers 16,765 declarations from 438 proof-module owners. The interface
comparison matches nine types and seven definition bodies in separate
Challenge and proof environments. A separate
[semantic review](verification/d18-extension-2026-11-24/SEMANTIC_SCOPE_REVIEW.md)
checks compatibility with a reference compiled using Mathlib alone.

A further clean compilation extracted the final frozen proof inputs from
a source ZIP and started with no project objects. Its completed six-stage
gate is in `verification/d18-archive-final/`; the initial output-path
correction is preserved in `verification/d18-archive-build/`. No proof
source changed during that compilation.

The selected final proofs and their exported dependencies have also passed
Lean checker, NanoDa and con-ron. A supplemental replay with Palomar's
approved newer con-ron accepted the same export. Exact scopes, checker
identities and current verification results are tracked centrally in
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) and
[verification/README.md](verification/README.md). A type comparison is not
a proof-body replay. Earlier certificates for the dimension-36 result are
kept distinct from evidence for this release.

## Palomar preparation and attribution

The package includes the independent specification, `comparator.json`,
pinned CI, provenance records and an optional manual workflow calling
Palomar's official reusable verifier. The local sandboxed Comparator
attempt stopped during `bwrap` tmpfs setup; it is not recorded as a
successful comparison. Palomar acceptance or publication is not claimed.

Submission still requires confirmed human authors and maintainers, the
actual project licence, a public repository and an immutable commit.
These are publication requirements, not missing hypotheses of the theorem.
The [metadata draft](verification/d18-publication/formalization.yaml.draft)
leaves unresolved fields explicit. See the
[publication report](verification/d18-publication/REPORT.md) for the exact
remaining checks and administrative requirements.
The [submission handoff](verification/d18-publication/SUBMISSION_HANDOFF.md)
collects the ready technical fields, proposed description and intake steps.

The provenance records credit the supplied archive and imported
formalizations. The bounded literature review and limits of the established
source attribution are explained in
[MATHEMATICAL_CONTEXT.md](docs/MATHEMATICAL_CONTEXT.md).
No claim of priority is made.
Changes from the supplied archive are listed in [CHANGES.md](CHANGES.md).

## Mathematical companion

[PROOF_COMPANION.md](docs/PROOF_COMPANION.md) gives the combined mathematical
exposition, including the [chosen target section](docs/TARGET_SECTION.md),
the [table-to-simplex construction](docs/SAFE_TABLE_TO_EMBEDDING.md),
and both geometric steps. The PDF is included under
`verification/d18-release/` and also delivered separately. Its source,
renderer and [rebuilding instructions](docs/pdf/README.md) are included.
