# Sixfold Tverberg Counterexamples and Convex Equipartition Obstructions

We construct a counterexample to the generalized Nandakumar--Ramana Rao problem: in every dimension $d \ge 24$, there are $d - 1$ continuous functionals on convex bodies and a probability measure such that there is no convex partition of the unit ball into six parts of equal measure on which all these functionals are equalized.

We also show that the topological Tverberg conjecture fails for sixfold intersections already in $\mathbb{R}^6$: we construct a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet.

This repository formalizes Theorems A and B from [*Sixfold Tverberg counterexamples and convex equipartition obstructions*](paper/manuscript.tex) by Arseniy Akopyan in Lean 4, developed with the assistance of Aristotle and Gemini.

---

## Challenge Theorems

The challenge is specified in `Challenge.lean` and checked by the Palomar Comparator against `Solution.lean` (and audited by `Audit.lean`):

1. **Theorem A (`AkopyanSixfold.tverberg_counterexample`)**:
   There exists a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet:
   ```lean
   theorem tverberg_counterexample :
       ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
         IsAlmostSixEmbedding f
   ```

2. **Theorem B (`AkopyanSixfold.convex_partition_counterexample`)**:
   Unconditionally in every dimension $d \ge 36$, there exist $d - 1$ continuous functionals on convex bodies and an absolutely continuous probability measure such that no convex six-partition of the unit ball into six equal-measure parts equalizes all these functionals:
   ```lean
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

Additional dimension-reduction theorems in `Solution.lean`:
- `exists_isBlocking_5d`: Unconditionally proves the existence of $5d$ central blocking markers in every dimension $d \ge 18$.
- `convex_partition_counterexample_ge_18`: Proves the convex equipartition counterexample in every dimension $d \ge 18$ from `exists_isBlocking_5d` given an almost six-embedding $\Delta^{89} \to \mathbb{R}^{16}$.
- `convex_partition_counterexample_ge_18_of_quadratic_table`: Reduces the $d \ge 18$ counterexample to a safe compatible quadratic height table ($5402$ features).
- `convex_partition_counterexample_ge_24`: Reduces the $d \ge 24$ counterexample to $5d - 4$ central blocking markers using only Theorem A ($\Delta^{35} \to \mathbb{R}^6$) and join-padding.

---

## Repository Structure

- `Solution.lean` — Main proofs of Theorems A and B, joins, central blocking marker existence (`exists_isBlocking_5d` for all $d \ge 18$), Blaschke compactness, and inward-distance transfer to convex bodies.
- `RequestProject/` — Height-table reduction (`RequestProject/Solution.lean`, `RequestProject/Reduction.lean`), cellular construction (`RequestProject/Construction/`), and boundary-preserving zero-removal surgery (`RequestProject/Surgery/`) for Theorem A ($\Delta^{35} \to \mathbb{R}^6$).
- `AkopyanResearch/` — Quadratic label spaces ($5402$ features), matching combinatorics, colored chain contraction, normal bundle trivialization, quaternion belt trick, $P_{\mathrm{row}}$-equivariant degree-$64$ pinch maps, and Kuhn PL extension for the $d = 18$ ($\Delta^{89} \to \mathbb{R}^{16}$) program.
- `Challenge.lean` — Independent specification template used by `comparator.json`.
- `Audit.lean` — Kernel-level verification module checking the exact types of Theorems A and B and verifying via `Lean.collectAxioms` that they depend only on `[propext, Classical.choice, Quot.sound]`.

---

## Verification

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.35.0`
- Mathlib `v4.35.0`
- Python 3.11+ (for offline structural checks)

### Build & Check
```bash
# Run static structural checks and unit tests
python3 scripts/check_structure.py
python3 -m unittest discover -s tests -q

# Build all default targets (including Solution and Audit)
lake build

# Run Palomar comparator check
lake env comparator comparator.json
```

When verified with `comparator`, the solution is exported and replayed through the Lean default kernel:
```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```
