# New Completion proof certificates

**Accepted:** four selected Completion theorems and their proof dependencies
were accepted by the bundled Lean checker, NanoDa, and con-ron. The driver
returned exit **0** at `2026-11-24T05:30:52.540641+00:00`. No source, compiled object,
configuration, generated audit, or export drift was observed.

The dimension-eighteen result below is **conditional** on the explicitly named
proposition `AkopyanResearch.ConcreteComparison.RequiredRelativeLifting`.
Neither this run nor the project-wide audit supplies a proof of that proposition.

## Exact selected statements

Fully qualified types with all implicit arguments displayed are retained in
`declaration-audit.log`. That log also prints the remaining lifting proposition,
its general relative extension structure, the actual concrete diagram,
comparison and chosen section, and the planar-table compatibility/safety
predicates. The readable source statements below omit only their proof bodies.

### 1. Convex-partition obstruction in every dimension greater than seventeen

Declaration: `AkopyanSixfold.convex_partition_counterexample_gt_17_of_relative_lifting`.

```lean
theorem convex_partition_counterexample_gt_17_of_relative_lifting
    (d : ℕ) (hd : 17 < d)
    (hLift : AkopyanResearch.ConcreteComparison.RequiredRelativeLifting) :
    ∃ (Phi : Body d → Fin (d - 1) → ℝ) (mu : Measure (Ambient d)),
      Continuous Phi ∧ IsProbabilityMeasure mu ∧ mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d, IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0)
```

All spaces, comparison maps and chosen sections in the lifting assumption are
constructed in the project. The remaining proposition requires extension of a
boundary map into the quadratic arrangement complement together with a
prescribed homotopy of its comparison image to that chosen section. Both the
boundary map and its homotopy must be preserved on the boundary. The premise
`hLift` is a theorem argument, not an axiom or an automatically supplied instance.

### 2. Ninety vertices and a sixteen-dimensional target from a height table

Declaration: `AkopyanSixfold.almostSix_ninety_of_continuous_table`.

```lean
theorem almostSix_ninety_of_continuous_table
    (H : AkopyanResearch.TableToEmbedding.PlanarTable)
    (hH : Continuous H)
    (hcompat : AkopyanResearch.TableRealization.Compatible H)
    (hsafe : AkopyanResearch.TableRealization.Safe 0 H) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ, IsAlmostSixEmbedding g
```

This is a construction from a continuous, compatible, safe planar height table.
It does not assert the existence of such a table. The conclusion uses exactly
the original `IsAlmostSixEmbedding` predicate, with continuity on the simplex
and separation of six points with pairwise disjoint supports.

### 3. Strict chains of flats in the actual quadratic arrangement

Declaration: `AkopyanResearch.QuadraticFlatRank.strict_flat_chain_length_bound`.

```lean
theorem strict_flat_chain_length_bound {S : Finset (Fin 15)} (hS : S.Nonempty)
    {n t : ℕ} (ht : 7 ≤ t) (c : Fin n → Finset (MatchingIndex S))
    (hc : StrictAnti (fun i => familyFlat (c i)))
    (hpos : ∀ i, 0 < scalarRank (c i)) (hmax : ∀ i, scalarRank (c i) < t) :
    n ≤ t - 6
```

Here `S` is a nonempty finite subset of `Fin 15`; each `c i` is a finite family
of six-matchings on `S`. The spaces `familyFlat (c i)` are their actual forbidden
subspace intersections, and `scalarRank` is the scalar quotient dimension.
The assumptions require strict reverse inclusion, positive ranks, and ranks
below `t`; the verified bound is `n ≤ t - 6` for `t ≥ 7`.

### 4. An actual linking nine-sphere retract

Declaration: `AkopyanResearch.exists_matching_sphere_retract`.

```lean
theorem exists_matching_sphere_retract
    (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m : Finset (S → Fin 6)) (hm : SixMatching m) :
    ∃ (s : UnitSphere (EuclideanSpace ℝ (Fin 10)) → QuadComplement S)
      (r : QuadComplement S → UnitSphere (EuclideanSpace ℝ (Fin 10))),
      Continuous s ∧ Continuous r ∧ Function.LeftInverse r s
```

Both continuous maps are constructed. The target sphere is the ordinary unit
sphere in ten-dimensional Euclidean space, and `Function.LeftInverse r s`
asserts `r (s y) = y` for every sphere point. No retraction hypothesis is assumed.

## Observed kernel results

| Stage | Exit code | Seconds |
| --- | ---: | ---: |
| build | 0 | 4.100 |
| declaration-audit | 0 | 15.103 |
| export | 0 | 281.830 |
| leanchecker | 0 | 118.654 |
| nanoda | 0 | 32.565 |
| con-ron | 0 | 25.686 |

The three checkers ran sequentially. NanoDa used
`unpermitted_axiom_hard_error: true`. The exported axioms were exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project axiom
was admitted. The structural gate found all four selected declarations as
`thm` records with actual `value` fields. The Lean declaration audit separately
checked their genuine theorem kinds using imported private proof information.

Con-ron reported `accepted 54894 declarations (--verified)`. Its log also
records the internal reordering of `Nat.mul._f` and `Nat.mul` ahead of the pinned
Nat operations they ground; it then completed successfully. This message is
preserved in `con-ron.log`.

The complete export contains 42,227 theorem records, 11,576 definitions,
1,046 inductive records, 38 opaque declarations, 4 quotient records and 3
permitted axioms. Its size is **464,409,372 bytes** and SHA-256:

```text
d554d77166f9b6b606f09bf83c19f1ecd7123290359c494871293049cb5adecc
```

The hash was recomputed after every checker had finished; the exported bytes
were unchanged.

## Reproducibility and limits

- Entry module: `Audit`; selected owning modules: `ConcreteReduction`,
  `GeneralTableBridge`, `QuadraticFlatRank`, and `QuadraticLink` under
  `AkopyanResearch.Completion`.
- The entry's **119 local source modules** and
  their recorded compiled proof objects were hashed before export and checked
  again afterward. The frozen source/configuration snapshot did not change.
- Lean and Lake came from the pinned Lean 4.35.0 toolchain. Mathlib was pinned
  to `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).
- Exact commands, tool executable hashes, source/object/configuration hashes,
  import graph, target record locations, and durations are in `results.json`.
  `verifier-used.py` is the exact driver used.
- The large NDJSON is stored outside the source release at
  `tools-runtime/actual-completion-kernels/final-selected.ndjson`.

These component checks were performed in the surrounding execution sandbox.
They do not constitute a successful sandboxed Palomar Comparator run or registry
acceptance. They check the four displayed statements with their stated premises;
they do not discharge the remaining relative lifting obligation. The separate
[full project gate](../final-project-retry/REPORT.md) covers compilation and
axiom dependencies of every project proof declaration, including unused private
declarations. The earlier [original Solution certificates](../original-kernels-retry/REPORT.md)
cover the unconditional original A and B36 theorems and were not rerun here.

## Later source extension

The subsequent 131-module revision added eleven separate mathematical modules. A source-hash
comparison with this accepted snapshot found that all **117 mathematical source files from
this import snapshot remained unchanged**. The two changed
entries are `Audit.lean` and `AkopyanResearch/Completion.lean`, whose inventories
and imports were extended. Their exact accepted versions are preserved in
`audit-entry-at-verification.lean.txt` and
`completion-entry-at-verification.lean.txt`.

`final-source-lineage.json` records the old and current entry hashes and the
unchanged-source count. This historical certificate retains its original scope;
it is not relabelled as a fresh export of the extended entries. The final
all-owner build audit and the separate new model certificate are recorded
independently for the later revision; their outcomes are not asserted here. No accepted independent proof check was repeated merely because
unrelated modules were added.

The final 132-module delivery additionally includes `PairCollapsedLocus`.
The same 117 original mathematical source files from this certificate remain
unchanged; its two entry snapshots remain the only source differences in the
recorded import closure. The refreshed `final-source-lineage.json` explicitly
binds this historical certificate to the final delivery without extending its
four selected theorem claims.
