# Selected concrete-model kernel certificate

**Passed** at `2026-11-24T06:09:39.804253+00:00` with driver exit **0**.
Lean checker, NanoDa, and con-ron all accepted the selected compiled bodies and
their exported dependencies. No recorded source, compiled object, configuration,
or export byte changed during verification. This certificate records the
**131-source-module snapshot**, whose selected entry imports 130 proof modules.

## Exact selection

All names below begin with `AkopyanResearch.`. The five definitions contain
actual maps together with their inverse, continuity, and algebraic proof fields;
this selection exports their bodies, not only their type signatures.

| Declaration | Required kernel kind |
| --- | --- |
| `TargetFiberModel.homotopyFiberHomeomorph` | definition |
| `PairNormalModel.jointQuotientContinuousEquiv` | definition |
| `SingleCoordinateModel.coordinatesHomeomorph` | definition |
| `PairPathCoordinates.homeomorph` | definition |
| `TargetCollapseModel.pairTargetSphereHomeomorph` | definition |
| `PairOrbit.card_labelsOverPair` | theorem |
| `PairL2Deformation.strong_deformation_retraction` | theorem |

`DeclarationAudit.lean` imports the owning modules with `import all`, checks
actual private declaration kinds, and enforces the three permitted axioms.
`declaration-audit.log` contains the complete explicit Lean types and additional
definitions of `HomotopyFiber`, `commonEquality`, and `Balanced2`.

## Mathematical content and premises

Let `S : Finset (Fin 15)` be nonempty. Let `MatchingIndex S` be the actual
six-matchings on S, and let `CriticalPairIndex S` be the actual unordered critical
pairs. Write X for `MatchingIndex S → Target`, where the original Target is a
nine-sphere, and Y for `CriticalPairIndex S → OnePoint PairTarget`.
The continuous map `collapseCoordinates hS : X → Y` is the actual product
collapse constructed from these coordinates.

The first selected definition constructs the homeomorphism

```lean
ConcreteComparisonTarget.Space S ≃ₜ
  {p : X × C(Time, Y) //
    p.2 timeZero = collapseCoordinates hS p.1 ∧
    p.2 timeOne = fun _ => ∞}
```

Here `Time` is the closed unit interval, and `C(Time, Y)` is the continuous-map
space with its compact-open topology. This is the full homotopy-fiber space,
including both endpoint conditions. The inverse reconstructs all row and pair
symmetries and the pure-label conditions. No connectivity premise occurs in
this homeomorphism; it does not itself prove connectivity.

The single-coordinate homeomorphism identifies the original row-enumeration
relations with `MatchingIndex S → Target`. The pair-path homeomorphism identifies
an equivariant path family, with pure labels fixed at infinity, with
`CriticalPairIndex S → PathSpace`. Both directions are defined and continuous.
For a mixed labeling `ω : S → PairState` whose two associated matchings have
exactly four common words, `card_labelsOverPair` proves that the labelings over
its unordered pair have cardinality **192**. Its explicit hypotheses are
`S.Nonempty` and the four-word intersection condition.

For the same nonempty S and labeling ω with a four-word intersection,
`jointQuotientContinuousEquiv` constructs a continuous linear equivalence

```lean
(QuadSpace S ⧸ (L_M S (matchingWords (firstVertex ∘ ω)) ⊓
  L_M S (matchingWords (secondVertex ∘ ω)))) ≃L[ℝ] commonEquality
```

The subspace `commonEquality ≤ Rep10 × Rep10` requires equality of the two
six-dimensional common coordinate projections. This is the actual joint test
map and quotient kernel; no quotient identification is assumed as an input.

The compactified pair target is explicitly identified with the ordinary
thirteen-sphere:

```lean
OnePoint PairTarget ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 14)) 1
```

Finally, let Z, A, and B be real normed vector spaces. The normal pair
complement consists of triples `(z,a,b) : Z × A × B` with both `(z,a)` and
`(z,b)` nonzero. The `Balanced2` locus is defined by the two equations
`‖z‖² + ‖a‖² = 1` and `‖z‖² + ‖b‖² = 1`.
The selected bundled theorem verifies the displayed inclusion, retraction, and
homotopy: both maps are continuous, retraction after inclusion is the identity,
the homotopy is continuous, it starts at the identity and ends at inclusion
composed with retraction, and it fixes every balanced point at every time.
Thus the selected proof includes the full strong deformation, not merely an
endpoint equality.

## Observed component results

| Stage | Exit code | Seconds |
| --- | ---: | ---: |
| build | 0 | 5.552 |
| declaration-audit | 0 | 20.486 |
| export | 0 | 282.514 |
| leanchecker | 0 | 157.985 |
| nanoda | 0 | 21.958 |
| con-ron | 0 | 11.069 |

The three kernels ran sequentially. NanoDa used
`unpermitted_axiom_hard_error: true`. The export contains exactly the permitted
axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or
project axiom. The structural gate found both selected theorems as `thm`
records and all five selected definitions as `def` records, each with an
actual `value` field. The prior Lean audit independently checked their genuine
private declaration kinds and complete transitive axiom closures.

Con-ron reported **accepted 38429 declarations (--verified)**. It also recorded
its internal reordering of `Nat.mul._f` and `Nat.mul` ahead of the pinned Nat
operations they ground, then completed successfully; the exact message remains
in `con-ron.log`. Lean checker was run with `--silent`; NanoDa's log is empty,
and both actual process exits are 0.

The export contains **28,864 theorem records**, **8,690 definitions**,
**842 inductive records**, **26 opaque declarations**, **4 quotient records**,
and the **3 permitted axioms**. Its size is **255,995,168 bytes**.
The SHA-256, recomputed after every checker had finished, is:

```text
4203052facd22c02d5ecd94b0222dff8cc237d183d018649a7d329280a05ee4f
```

The large export is kept outside the source release at
`tools-runtime/actual-model-kernels/final-selected.ndjson`.

## Provenance and reproducibility

The entry was `Audit`. Lean's own import parser recorded its **130 local
source modules**; source hashes and the corresponding `.olean`, private,
and server proof objects were checked before and after export. Pinned
configuration and manifest hashes also remained unchanged. The toolchain is
Lean 4.35.0; Mathlib is fixed to
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).

`results.json` retains executable hashes, exact commands, complete explicit
types, the import graph, target record locations, and durations.
`run-selected-models.sh` records the exact seven-target selection, and
`verifier-used.py` is the unchanged driver used for this run. Exact accepted
Audit and Completion entry sources are retained as
`audit-entry-at-verification.lean.txt` and
`completion-entry-at-verification.lean.txt`, with hashes in
`entry-source-snapshots.json`, so subsequent inventory additions cannot be
confused with this historical snapshot.

From a fresh checkout with the pinned toolchain available, select a fresh
external export path:

```sh
bash verification/model-kernels/run-selected-models.sh /absolute/fresh-model-export.ndjson
```

## Limits

These component checks ran in the surrounding execution sandbox. They do not
compare this model interface against an independently specified Challenge.
They are not the official sandboxed Palomar Comparator and do not constitute
registry acceptance. In particular they do not prove the remaining
`ConcreteComparison.RequiredRelativeLifting` premise of the d > 17 theorem.

The complete 131-module project audit and staged source build are recorded
separately in `../final-extended/REPORT.md` and
`../clean-release-final/REPORT.md`. Later unrelated source additions require
their own owner/build audit and do not extend the mathematical selection of
this certificate. The already accepted original and earlier Completion kernel
certificates were not repeated.

## Final 132-module extension

After this certificate finished, the final release added
`AkopyanResearch.Completion.PairCollapsedLocus`. All **128 mathematical
source files from this certificate's import snapshot remained unchanged**;
only the Audit inventory and Completion import aggregate changed. Their exact
accepted source versions remain preserved as listed above.

`final-source-lineage.json` records the source-hash comparison with the
132-module final delivery. The new collapsed-locus theorem is covered by the
separate full Lean owner/build gates in `../final-delivery/REPORT.md` and
`../clean-delivery/REPORT.md`. It was not exported as part of this seven-target
certificate, and no old independent checks were repeated.
