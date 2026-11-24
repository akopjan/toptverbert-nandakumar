# Independent semantic scope review

Recorded 2026-11-24, 08:54 UTC. Lean 4.35.0; Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

**Result: PASS.** The original Theorem A states an almost-six embedding
\(\Delta^{35}\to\mathbb R^6\) in the usual sense. The final Theorem B states
the advertised unconditional obstruction in every natural dimension \(d>17\),
including \(d=18\). No vacuous tuple condition, restricted collection of faces,
replacement topology, dimension shift, or hidden theorem parameter was found.
No project proof source was modified for this review.

## 1. Independent type checks

The diagnostic `SemanticReference` imports **only Mathlib**. It defines the
expected A, height-extension and B statements with Mathlib's standard real,
finite-product, Euclidean, convex-body and measure instances. This module was
compiled before the checking module imported `Solution` and
`Completion.DimensionEighteen`. Thus an instance introduced by the proof
project cannot silently alter the reference propositions.

Lean accepted the following checks:

| Check | Result |
| --- | --- |
| Original `AkopyanSixfold.tverberg_counterexample` inhabits the frozen A proposition | PASS |
| The direct `Tverberg6R` height-extension bridge inhabits that same proposition | PASS |
| `Tverberg6R.heightExtension` inhabits the frozen, assumption-free height-extension proposition | PASS |
| Final `convex_partition_counterexample_gt_17 d hd` inhabits the frozen B proposition | PASS |
| A gives an actual continuous map from the standard simplex subtype into `EuclideanSpace ℝ (Fin 6)` | PASS |

All five diagnostic proofs depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The reference compilation and the checking compilation both
returned exit code 0. The Euclidean-target check uses Mathlib's explicit
`PiLp.homeomorph`, rather than identifying the finite-product and Euclidean
metric spaces by assertion.

## 2. Theorem A and the original bridge

In `Challenge.lean`, `Solution.lean`, and `RequestProject/Reduction.lean`, the
source simplex consists of nonnegative functions `Fin 36 → ℝ` whose coordinate
sum is one. It has 36 vertices and dimension 35. The target is the ordinary
finite real product `Fin 6 → ℝ`. The parameter values therefore satisfy the
usual Tverberg threshold \((6-1)(6+1)=35\); the domain is not a smaller simplex.

`ContinuousOn` is required on the entire simplex. This is precisely continuity
of the restricted map on that simplex, as also checked by the diagnostic's
continuous-map formulation. The behavior of the chosen ambient function off
the simplex does not change the topological assertion.

`DisjointSupports` quantifies over every pair of distinct indices in `Fin 6`
and every vertex coordinate. It requires at least one of the two coordinates
to vanish. On the nonnegative simplex, these are exactly disjoint supports,
or equivalently disjoint vertex sets of the minimal containing faces. There
is no rainbow-face, equal-mass, positive-color, or full-support restriction in
the theorem. The conclusion `∃ i, f (x i) ≠ f (x 0)` is exactly the failure of
all six image values to coincide. The choice of index zero as a reference
does not weaken that condition.

Nonvacuity was checked explicitly: six different coordinate unit vectors
belong to this simplex and satisfy its disjoint-support predicate. The
height-table matching predicate also has an explicit witness, namely
`m j p = j`.

The bridge uses the bijection `Fin 6 × Fin 6 ≃ Fin 36`. Its test map has five
color-mass coordinates and one averaged-height coordinate. If six test images
coincide, the sum-to-one identity supplies equality of the sixth mass as well.
For a positive common color mass, disjointness and the six available labels
force one occupied label per point, giving a permutation. For a zero mass,
the proof chooses arbitrary distinct labels, and boundary compatibility makes
the table independent of that choice. Thus safety applies to an actual
matching for every six-tuple covered by the theorem. The continuity argument
handles the zero-mass cases explicitly.

`heightExtension` obtains its witness from `exists_height`; it is not an
additional hypothesis of A. The inspected original source chain introduces
no replacement topological, metric, or measurable-space instance. Its sole
declared project instance found by this scan is
`Fintype Mtch := Fintype.ofFinite _`, which enumerates the actual matching
subtype.

## 3. Theorem B18

The final theorem has only the parameters `(d : ℕ)` and `(hd : 17 < d)`.
It assumes no almost embedding, blocking configuration, safe table, homology
calculation, or lifting property.

`Ambient d` is Mathlib's Euclidean space of dimension `d`. `Body d` consists
of nonempty compact convex subsets, with the Hausdorff topology. The continuous
map `Phi : Body d → (Fin (d - 1) → ℝ)` is defined on all those bodies. Its
witness and the absolutely continuous probability measure are chosen before
the universal quantifier over partitions.

The six-partition predicate requires exact union equal to the closed unit
ball, nonempty interior of every part, and pairwise disjoint interiors. It
imposes no polyhedral or central-partition restriction. Equal mass is stated
as `mu (C i) = mu (unitBall d) / 6`. Although the exported statement does not
add a support condition on the measure, its proof constructs normalized
Lebesgue measure on a smaller positive-radius ball and proves internally that
`mu (unitBall d) = 1`. It does not exploit zero mass of the unit ball.

## 4. Published status and proof correctness

The located primary literature does not identify the specific
\(\Delta^{35}\to\mathbb R^6\) result as an already published theorem.
Avvakumov, Mabillard, Skopenkov and Wagner's
[codimension-two paper](https://arxiv.org/abs/1511.03501), published in
*Israel Journal of Mathematics* 245 (2021), gives the standard counterexamples
for \(d\ge2r+1\), hence \(d\ge13\) when \(r=6\). Avvakumov, Karasev and
Skopenkov's [stronger-counterexamples paper](https://arxiv.org/abs/1908.08731),
published in *Combinatorica* 43 (2023), gives an improved simplex-size formula.
These located guarantees are not a published provenance for A.

This scoped literature check does not establish priority, exhaust all later
publications, or constitute external peer review. Conversely, a stronger
claim than those located in the literature is not by itself a semantic or
logical defect. The results here concern what the submitted formulas mean
and their checked type compatibility. The existing original component-kernel
record `verification/original-kernels-retry/results.json` records acceptance;
the final complete-project build, axiom inventory and exported-term kernel
checks remain separate release records.

This review did not re-prove every surgery, degree-counting, or convex-geometric
lemma in the original project. It found no mismatch between the advertised
mathematical statements and the actual exported interfaces.

## 5. Reproducible evidence and source identity

The exact invocation used was:

```text
python /workspace/scratch/9db1b532943d/alternate-method/semantic-scope/run_check.py
```

The working directory was `/workspace/scratch/9db1b532943d`. The runner obtains
the project's `LEAN_PATH` through `lake env printenv LEAN_PATH`, resolves its
paths, and prepends the separate diagnostic directory. It invokes the pinned
Lean binary with `-j 1 -o` for the Mathlib-only reference first and the checking
module second. The complete runner, including its exact subprocess arguments,
is preserved as `SEMANTIC_SCOPE_RUNNER.py.txt`. The diagnostic sources retain
their module headers in `SEMANTIC_SCOPE_REFERENCE.lean.txt` and
`SEMANTIC_SCOPE_CHECK.lean.txt`; the corresponding logs and
`SEMANTIC_SCOPE_RESULTS.json` record the successful checks. They are stored as
text so they do not alter the proof project's module inventory.

Current inspected source SHA-256 hashes:

| Source | SHA-256 |
| --- | --- |
| `Challenge.lean` | `d7b36eaa7daf9c593b205f0fc3f748c0a6c8ab3ba726269947d71328c4ce4e66` |
| `Solution.lean` | `41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23` |
| `RequestProject/Reduction.lean` | `b403a35928c808eb7fa9fda4a8fb890755bf99b037b8adea2d26bd91327c4794` |
| `RequestProject/Solution.lean` | `21a44423bd69b613010d1b935e054ddcc6883aaaaeef80f0ae0fa56699465930` |
| `RequestProject/Construction/Assembly.lean` | `fd2390ca67f8ac59fc3893e69f923984648d0cc2c3d8054787ffd22adb6d563a` |
| `AkopyanResearch/Completion/DimensionEighteen.lean` | `24f45bfe59787b9308d242083be6163f7852abaec0bc2565cd90fafdaeac7ad8` |
| `PalomarSolution.lean` | `98bcca73c13415a014c1cb394eb8530f8e82993ca7b123fc42752ce0c560744e` |
