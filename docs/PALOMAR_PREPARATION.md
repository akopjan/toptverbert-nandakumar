# Palomar Preparation: Theorem A and the Unconditional `d > 17` Bound

24 November 2026, UTC. The unconditional theorem
`AkopyanSixfold.convex_partition_counterexample_gt_17` and the supporting
almost-six embedding `Δ⁸⁹ → ℝ¹⁶` (`AkopyanSixfold.almostSix_ninety`) have
passed full Lean compilation, literal statement verification, and the
all-declaration owner audit (`2026-11-24T08:56:01Z`). The separate
compiled-interface comparison passed at `08:59:09 UTC`, the cumulative source
rebuild passed at `09:01:10 UTC`, and the clean archive build passed at
`10:23:29 UTC`. The exported proof bodies were accepted by Lean checker,
NanoDa, bundled con-ron, and the Palomar-approved con-ron (4.36.0-rc1).

## Scope of the exported declarations

| Comparator declaration | Proof module | Result |
|---|---|---|
| `AkopyanSixfold.tverberg_counterexample` | `Solution` | Almost-six embedding `Δ³⁵ → ℝ⁶`. |
| `AkopyanSixfold.convex_partition_counterexample_gt_17` | `AkopyanResearch.Completion.DimensionEighteen` | Convex six-equipartition obstruction for every natural `d` with `17 < d`. |

For natural `d > 17`, `Body d` is the space of nonempty compact convex
subsets of `ℝ^d` with the Hausdorff topology, and `unitBall d` is the closed
unit ball. The second theorem constructs a continuous map
`Phi : Body d → (Fin (d - 1) → ℝ)` and a probability measure `mu` on `ℝ^d`
absolutely continuous with respect to volume such that no partition of
`unitBall d` into six convex bodies with nonempty pairwise-disjoint interiors
can simultaneously have `mu (C i) = mu (unitBall d) / 6` for all `i` and
equal values of `Phi` on all six parts.

The result contains no extra connectivity, homology, or
`RequiredRelativeLifting` hypotheses: the required relative lifting property
is proved for the concrete comparison map in
`ConcreteComparisonLifting.requiredRelativeLifting`. See
[DIMENSION_EIGHTEEN_PROOF.md](DIMENSION_EIGHTEEN_PROOF.md),
[STATEMENT_AND_LIFTING_REVIEW.md](../verification/d18-extension-2026-11-24/STATEMENT_AND_LIFTING_REVIEW.md),
and [SEMANTIC_SCOPE_REVIEW.md](../verification/d18-extension-2026-11-24/SEMANTIC_SCOPE_REVIEW.md).

## Independent specification and reproducible environment

`Challenge.lean` states Theorems A and B18 independently and imports only
`Mathlib`. Its two template `sorry` placeholders specify the Comparator
targets and are never imported by proof modules. All seven interface
definitions match the original `Solution.lean`, which is retained
byte-for-byte. The publication entry point is `PalomarSolution.lean`, and
`comparator.json` targets `Challenge` and `PalomarSolution`.

The project pins Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with full 40-character commit
SHAs for all nine Git dependencies in `lake-manifest.json`.

## Summary of verification evidence

| Location | Purpose and status |
|---|---|
| [`verification/d18-final-retry/`](../verification/d18-final-retry/) | Main release verification **PASS** (`08:56:01 UTC`): 16,765 declarations across 438 proof-module owners, 37 regression tests, 472 unchanged input hashes. |
| [`verification/d18-clean-final/`](../verification/d18-clean-final/) | Separate cumulative source rebuild **PASS** (`09:01:10 UTC`) with identical 472 input hashes and declaration audit. |
| [`verification/d18-archive-final/`](../verification/d18-archive-final/) | Clean ZIP extraction and full build from zero project objects **PASS** (`10:23:29 UTC`). |
| [`verification/d18-compiled-interface/`](../verification/d18-compiled-interface/) | Separately compiled interface comparison **PASS** (`08:59:09 UTC`): 9 types and 7 definition bodies matched. |
| [`verification/d18-kernels/`](../verification/d18-kernels/) | External kernel replay **PASS** (`09:15:21 UTC`): Lean checker, NanoDa, and bundled con-ron accepted the 700,996,206-byte export (`978d77cd...`). |
| [`verification/d18-approved-con-ron/`](../verification/d18-approved-con-ron/) | Approved con-ron 4.36.0-rc1 replay **PASS** (`09:18:19 UTC`) on the same export. |
| [`verification/d18-publication/`](../verification/d18-publication/) | Static preflight, metadata draft, official reference snapshots, and submission handoff. |

All audited declarations depend only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## GitHub workflows and metadata

The primary `.github/workflows/verify.yml` verifies dependency pins, runs the
full verification script `scripts/verify.sh`, and invokes
`scripts/verify-comparator.sh`. The manual
`.github/workflows/palomar-preflight.yml` calls the official reusable
verifier `PalomarRegistry/PalomarSubmission@14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
See [REPORT.md](../verification/d18-publication/REPORT.md) and
[SUBMISSION_HANDOFF.md](../verification/d18-publication/SUBMISSION_HANDOFF.md)
for full details.
