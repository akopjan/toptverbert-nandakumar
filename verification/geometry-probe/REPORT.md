# Independent Verification of the Central Geometric Block

24 November 2026, 04:30 UTC.

**Result: Lean 4.35.0 exited with code 0.** For all four theorems listed
below, `#print axioms` reports only the standard permitted axioms
`propext`, `Classical.choice`, and `Quot.sound`.

| Declaration `AkopyanSixfold.…` | Verified statement |
|---|---|
| `blaschke_isCompact_subsets_unitBall` | Blaschke compactness of convex bodies contained in the unit ball |
| `exists_eta_of_isBlocking` | Extension of central blocking to partitions whose parts all intersect a sufficiently small central ball |
| `exists_isBlocking_5d` | Existence of `5 * d` central blocking markers for all `18 ≤ d` |
| `convex_partition_of_embedding_and_blocking` | Transfer of an almost-six embedding and blocking markers to continuous functionals and an absolutely continuous probability measure |

## Scope

`GeometryProbe.lean` is a deterministic extraction from the original
`Solution.lean` isolating the convex-geometric block and checking its four
principal theorems with `#print axioms`.

- Original `Solution.lean` SHA-256:
  `41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23`
- `GeometryProbe.lean` SHA-256:
  `82aafe2c7150ed78dececdc2f680dd0360bb9119699ab886dbee2d2f682f1c86`

## Reproduction

From the repository root with the pinned Lean 4.35.0 toolchain and Mathlib
(`56a005855ea17e0b0958f73ec801ae140b0a1679`):

```sh
lake env lean -R . verification/geometry-probe/GeometryProbe.lean
```
