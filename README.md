# Sixfold Tverberg Counterexamples and Convex Equipartition Obstructions

We construct a counterexample to the generalized Nandakumar--Ramana Rao problem: in every dimension $d > 17$, there are $d - 1$ continuous functionals on convex bodies and a probability measure such that there is no convex partition of the unit ball into six parts of equal measure on which all these functionals are equalized.

We also show that the topological Tverberg conjecture fails for sixfold intersections already in $\mathbb{R}^6$: we construct a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet.

This repository formalizes Theorems A and B from [*Sixfold Tverberg counterexamples and convex equipartition obstructions*](paper/manuscript.tex) by Arseniy Akopyan in Lean 4, developed with the assistance of Aristotle and Gemini.

---

## Challenge Theorems

The challenge is specified in `Challenge.lean` and checked by the Palomar Comparator against `PalomarSolution.lean` (`Solution.lean` and `AkopyanResearch/Completion/DimensionEighteen.lean`):

1. **Theorem A (`AkopyanSixfold.tverberg_counterexample`)**:
   There exists a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet:
   ```lean
   theorem tverberg_counterexample :
       ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
         IsAlmostSixEmbedding f
   ```

2. **Theorem B (`AkopyanSixfold.convex_partition_counterexample_gt_17`)**:
   Unconditionally in every dimension $d > 17$, there exist $d - 1$ continuous functionals on convex bodies and an absolutely continuous probability measure such that no convex six-partition of the unit ball into six equal-measure parts equalizes all these functionals:
   ```lean
   theorem convex_partition_counterexample_gt_17 (d : ℕ) (hd : 17 < d) :
       ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
         Continuous Phi ∧
         IsProbabilityMeasure mu ∧
         mu.AbsolutelyContinuous volume ∧
         ∀ C : Fin 6 → Body d,
           IsSixPartition C →
           (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
           ∃ i, Phi (C i) ≠ Phi (C 0)
   ```

---

## Verification

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.35.0`
- Mathlib `v4.35.0`

### Build & Check
```bash
# Build the challenge and solution
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
