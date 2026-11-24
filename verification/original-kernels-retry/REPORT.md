# Original Solution proof certificates

**Accepted:** the two original comparator theorems and their proof dependencies
were exported as proof bodies and accepted by the bundled Lean checker, NanoDa,
and con-ron. The driver returned exit **0** at `2026-11-24T05:12:58.894037+00:00`.

The checked theorems are **A** and **B for d ≥ 36**. This report does not assert
the stronger unconditional conclusion for d > 17.

## Exact theorem scope

The selected declarations are `AkopyanSixfold.tverberg_counterexample` and
`AkopyanSixfold.convex_partition_counterexample`. Their independent Challenge
statements, with proof bodies omitted, are:

```lean
-- In namespace AkopyanSixfold:
theorem tverberg_counterexample :
    ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
      IsAlmostSixEmbedding f

theorem convex_partition_counterexample (d : ℕ) (hd : 36 ≤ d) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0)
```

The seven interface definitions are printed in `declaration-audit.log`.
`IsAlmostSixEmbedding` requires continuity on the simplex and prevents six
points with pairwise disjoint barycentric supports from sharing one image.
`Body d` is the Hausdorff space of nonempty compact convex bodies in standard
Euclidean space. `IsSixPartition` requires union equal to the closed unit ball,
nonempty interiors, and pairwise disjoint interiors.

The separate successful [literal statement gate](../statement-audit-retry/REPORT.md)
was generated directly from the supplied `Challenge.lean`; exact reversal of
its five permitted edits reconstructed the original Challenge bytes. It
checks the definitions, dimensions, and hypotheses without a manually
restated interface. This proof-export run itself does not perform that
independent statement comparison.

## Observed component results

| Stage | Exit code | Seconds |
| --- | ---: | ---: |
| build | 0 | 7.770 |
| declaration-audit | 0 | 27.647 |
| export | 0 | 1049.289 |
| leanchecker | 0 | 128.524 |
| nanoda | 0 | 29.693 |
| con-ron | 0 | 20.829 |

All three checkers ran sequentially. The con-ron output was
`con-ron: accepted 51114 declarations (--verified)`.
NanoDa was configured with `unpermitted_axiom_hard_error: true`.
Every exported axiom was one of `propext`, `Classical.choice`, and `Quot.sound`.
There was no exported `sorryAx` or new axiom.

The structural export audit found both selected declarations as `thm` records
with an actual `value` field. The generated Lean audit also required genuine
private-environment theorem declarations; it did not mistake Lean 4.35's
weakened public theorem views for proof bodies.

The closure contains 39,235 theorem records, 10,823 definitions, 1,012 inductive
records, 37 opaque declarations, 4 quotient records, and 3 permitted axioms.
The exported file has **433,148,960 bytes** and SHA-256:

```text
e13da01da2ed86c54af2e33eb8277862cb7f6a8100a78d6d4043e99b205a8781
```

## Source and tool binding

- Lean: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
- Lake: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
- Mathlib v4.35.0: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- All **47 local source modules** in Solution's import closure are byte-for-byte
  identical to the supplied original archive. See `source-provenance.json`.
- Every source, recorded compiled object, toolchain/configuration input, and
  generated declaration-audit input remained unchanged during this run.
- The NDJSON SHA-256 was recomputed after the checkers; its bytes remained
  unchanged throughout the checks.
- `results.json` records the exact commands, durations, dependency graph,
  dependency pins, executable hashes, source/object hashes, and target record
  locations. `verifier-used.py` is the exact driver used for this run.

The large NDJSON is intentionally stored outside the release project at
`tools-runtime/original-kernels/selected-retry1.ndjson`; it need not be shipped
inside the source ZIP. The export can be reproduced from the pinned project
using the recorded `leanexport Solution -- ...` command. A fresh driver run
must use a new output directory and an absent export-file path.

## Limits and prior interrupted attempt

These are component checks inside the surrounding execution sandbox. They are
**not** an execution of Palomar's sandboxed Comparator, do not establish
registry acceptance, and do not independently audit every unused declaration
in the project. The final all-owner audit is a separate project-wide gate.
They also do not verify the later Completion modules: those sources lie
outside this unchanged 47-module proof closure.

An earlier attempt lost its execution session before the exporter completed;
it remains explicitly incomplete in `../original-kernels/interruption.json`.
This report relies only on the completed retry. Previously discovered Lean
imports were reused only after every corresponding source, dependency pin,
and tool executable hash matched. The proof export and all three checker
runs in this report were performed afresh and finished successfully.
