# Sixfold Tverberg Counterexamples and Convex Equipartition Obstructions

We construct a counterexample to the generalized Nandakumar--Ramana Rao problem: in every dimension $d > 17$, there are $d - 1$ continuous functionals on convex bodies and a probability measure such that there is no convex partition of the unit ball into six parts of equal measure on which all these functionals are equalized.

We also show that the topological Tverberg conjecture fails for sixfold intersections already in $\mathbb{R}^6$: we construct a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet.

---

## Challenge Theorems

The challenge is specified in `Challenge.lean` and checked by the Palomar Comparator against `PalomarSolution.lean` (`Solution.lean` and `AkopyanResearch/Completion/DimensionEighteen.lean`):

1. **Theorem A (`AkopyanSixfold.tverberg_counterexample`, formalizing Theorem A of the manuscript)**:
   There exists a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet:
   ```lean
   theorem tverberg_counterexample :
       ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
         IsAlmostSixEmbedding f
   ```

2. **Theorem B (`AkopyanSixfold.convex_partition_counterexample_gt_17`, adapting and strengthening Theorem B of the manuscript from $d \ge 24$ to $d > 17$)**:
   Unconditionally in every dimension $d > 17$, there exist $d - 1$ continuous functionals on convex bodies and an absolutely continuous probability measure with full mass on the unit ball such that no convex six-partition of the unit ball into six equal-measure parts equalizes all these functionals:
   ```lean
   theorem convex_partition_counterexample_gt_17 (d : ℕ) (hd : 17 < d) :
       ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
         Continuous Phi ∧
         IsProbabilityMeasure mu ∧
         mu (unitBall d) = 1 ∧
         mu.AbsolutelyContinuous volume ∧
         ∀ C : Fin 6 → Body d,
           IsSixPartition C →
           (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
           ∃ i, Phi (C i) ≠ Phi (C 0)
   ```

---

## Provenance and Authorship

- **Manuscript and Strengthened Bound**: This repository is based on the paper [*Sixfold Tverberg counterexamples and convex equipartition obstructions*](paper/manuscript.tex) by **Arseniy Akopyan**.
  - **Theorem A (`AkopyanSixfold.tverberg_counterexample`)** directly formalizes Theorem A of the manuscript ($\Delta^{35} \to \mathbb{R}^6$).
  - **Theorem B (`AkopyanSixfold.convex_partition_counterexample_gt_17`)** adapts and strengthens Theorem B of the manuscript: whereas Theorem B in [paper/manuscript.tex](paper/manuscript.tex) states the convex six-equipartition obstruction for $d \ge 24$, this Lean development proves the stronger unconditional bound $d > 17$ ($d \ge 18$) by constructing an unconditional almost six-embedding $\Delta^{89} \to \mathbb{R}^{16}$ (`AkopyanSixfold.almostSix_ninety`) and combining it with the $5d$ central blocking marker theorem (`AkopyanSixfold.exists_isBlocking_5d` for $d \ge 18$).
- **Relationship to the Earlier Lean Development**:
  1. **Initial Lean Baseline (`RequestProject/`, `Solution.lean`, and initial `AkopyanResearch/` modules)**: Developed by **Arseniy Akopyan** with AI assistance from **Aristotle** (for the Theorem A height-table surgery closure in `RequestProject/`) and **Gemini** (for join-padding, Blaschke compactness, normal rank $\le 5$, RREF/tree parametrizations, `exists_isBlocking_5d` for $d \ge 18$, the unconditional $d \ge 36$ theorem `convex_partition_counterexample`, the conditional $d \ge 18$ reduction `convex_partition_counterexample_ge_18` in `Solution.lean`, and the 43 quadratic arrangement and equivariant collapse modules in `AkopyanResearch/`). The original `Solution.lean` is preserved byte-for-byte.
  2. **Later Completion for $d > 17$ (`AkopyanResearch/Completion/`, `Submission/`, `Hatcher/`, `PalomarSolution.lean`, `Audit.lean`)**: Directed and maintained by **Arseniy Akopyan** with AI assistance from **GPT-6 Astra Pro**, extending the earlier Lean baseline and adapting ported homotopy and singular homology infrastructure from `homotopy-groups-lean` (Vasily Ilin, Tau Ceti contributors, Jiazhen Xia; Apache-2.0) and `hatcher-at` (Joël Riou, Jack McCarthy; Apache-2.0) to prove the relative lifting theorem (`ConcreteComparisonLifting.requiredRelativeLifting`), the unconditional embedding $\Delta^{89} \to \mathbb{R}^{16}$ (`almostSix_ninety`), and the unconditional $d > 17$ theorem (`convex_partition_counterexample_gt_17`).
- **Human Responsibility and License**: **Arseniy Akopyan** is the sole human author of both the manuscript and the complete Lean 4 formalization (including both the earlier development and the later $d > 17$ completion), as well as the responsible maintainer of this repository under the `Apache-2.0` license ([LICENSE](LICENSE)).

---

## Verification

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.36.0-rc2`
- Mathlib `v4.36.0-rc2` (`9d581dfff2e41de989072ea63abf3daf69311520`)

### Build & Check
```bash
# Build all targets (including PalomarSolution and Audit)
lake build

# Run Palomar comparator check
lake env comparator comparator.json
```
