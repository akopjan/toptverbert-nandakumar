module

public import Mathlib
public import RequestProject.Solution
public import AkopyanResearch.SafeQuadraticRealization

@[expose] public section

/-!
# Sixfold Tverberg Counterexample and Convex Equipartition Obstruction (`Solution.lean`)

Arseniy Akopyan

Matches `Challenge.lean` via `comparator.json` without importing `Challenge.lean`:
* `AkopyanSixfold.tverberg_counterexample` (Theorem A):
  An almost six-embedding `Δ³⁵ → ℝ⁶`, proved via the height-table construction
  `Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension`.
* `AkopyanSixfold.convex_partition_counterexample` (Theorem B):
  Unconditionally in every dimension `d ≥ 36`, proves the existence of `5 * d`
  central blocking markers (`exists_isBlocking_5d`, via separating normals, rank-four
  RREF reduction, rank-five tree parametrization, and measure-zero arguments),
  derives `eta` via Blaschke compactness (`blaschke_isCompact_subsets_unitBall` /
  `exists_eta_of_isBlocking`, Lemma 5.2), constructs an unconditional almost six-embedding
  `Δ^(5d-1) → ℝ^(d-2)` by a fivefold join of Theorem A and join-padding
  (`fivefold_tverberg_join` / `padded_tverberg_ge_36`), and transfers it via
  `inwardDist` to `d - 1` continuous body functionals `Phi` and an absolutely
  continuous probability measure `mu` without equalizing convex six-partitions.
* Additional results in `Solution.lean`:
  `join_almostSixEmbedding`, `tverberg_counterexample_ge_six` (`d ≥ 6`), `fivefold_tverberg_join`
  (`Δ¹⁷⁹ → ℝ³⁴`), `padded_tverberg_ge_36` (`d ≥ 36`), `twofold_seven_color_join`
  (`Δ⁴¹ → ℝ⁷` implies `Δ⁸³ → ℝ¹⁵`), `convex_partition_of_embedding_and_blocking`,
  `convex_partition_counterexample_ge_24` (`d ≥ 24`, `5 * d - 4` central blocking markers),
  `convex_partition_counterexample_ge_36` (`d ≥ 36`, `5 * d` central blocking markers without `[AKS]`),
  and `convex_partition_counterexample_ge_18` (`d ≥ 18`, conditional only on `Δ⁸⁹ → ℝ¹⁶`,
  with `5 * d` central blocking markers proved unconditionally via `exists_isBlocking_5d`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Topology

namespace AkopyanSixfold

/-- The simplex on `n` vertices (dimension `n - 1`). -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1}

/-- The six points have pairwise disjoint barycentric supports. -/
def DisjointSupports {n : ℕ} (x : Fin 6 → (Fin n → ℝ)) : Prop :=
  ∀ i j, i ≠ j → ∀ v, x i v = 0 ∨ x j v = 0

/-- An almost six-embedding of the `(n - 1)`-simplex into `ℝ^d`:
continuity is required on the simplex, and no six points with pairwise disjoint
barycentric supports share the same image. -/
def IsAlmostSixEmbedding {n d : ℕ}
    (f : (Fin n → ℝ) → (Fin d → ℝ)) : Prop :=
  ContinuousOn f (simplex n) ∧
  ∀ x : Fin 6 → (Fin n → ℝ),
    (∀ i, x i ∈ simplex n) →
    DisjointSupports x →
    ∃ i, f (x i) ≠ f (x 0)

/-- **Theorem A**: Counterexample to the topological Tverberg conjecture for sixfold
intersections in `ℝ⁶` (`36` vertices, target dimension `6`). -/
theorem tverberg_counterexample :
    ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨f, hf_cont, hf_disj⟩ :=
    Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension
  exact ⟨f, hf_cont, hf_disj⟩

/-- Standard Euclidean space `ℝ^d`. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Nonempty compact convex bodies in `ℝ^d` endowed with the Hausdorff metric. -/
abbrev Body (d : ℕ) := ConvexBody (Ambient d)

/-- The closed unit ball in `ℝ^d`. -/
def unitBall (d : ℕ) : Set (Ambient d) :=
  Metric.closedBall (0 : Ambient d) 1

/-- A convex six-partition of the unit ball: six convex bodies with nonempty,
pairwise disjoint interiors whose union equals `unitBall d`. -/
def IsSixPartition {d : ℕ} (C : Fin 6 → Body d) : Prop :=
  unitBall d = (⋃ i, (C i : Set (Ambient d))) ∧
  (∀ i, (interior (C i : Set (Ambient d))).Nonempty) ∧
  ∀ i j, i ≠ j →
    Disjoint (interior (C i : Set (Ambient d)))
             (interior (C j : Set (Ambient d)))

/-- `p` blocks central six-partitions if every six-partition of `unitBall d`
(possibly with degenerate parts) whose parts all contain the origin `0` has some
marker `p a` in the interior of some part. -/
def IsBlocking {d m : ℕ} (p : Fin m → Ambient d) : Prop :=
  ∀ C : Fin 6 → Body d,
    unitBall d = (⋃ i, (C i : Set (Ambient d))) →
    (∀ i j, i ≠ j →
      Disjoint (interior (C i : Set (Ambient d)))
               (interior (C j : Set (Ambient d)))) →
    (∀ i, (0 : Ambient d) ∈ (C i : Set (Ambient d))) →
    ∃ i a, p a ∈ interior (C i : Set (Ambient d))

/-! ### Helper 1: Perspective continuity, binary joins, and join-padding -/

private lemma continuousOn_perspective {X : Type*} [TopologicalSpace X]
    {S : Set X} {n q : ℕ}
    {w : X → Fin n → ℝ}
    (hw_cont : ∀ v, ContinuousOn (fun x => w x v) S)
    (hw_nonneg : ∀ x ∈ S, ∀ v, 0 ≤ w x v)
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : ContinuousOn g (simplex n))
    (j : Fin q) :
    ContinuousOn
      (fun x =>
        let s := ∑ v, w x v
        if s = 0 then 0 else s * g (fun v => w x v / s) j)
      S := by
  let s : X → ℝ := fun x => ∑ v, w x v
  have hs_cont : ContinuousOn s S :=
    continuousOn_finsetSum _ fun v _ => hw_cont v
  have hs_nonneg : ∀ x ∈ S, 0 ≤ s x :=
    fun x hx => Finset.sum_nonneg fun v _ => hw_nonneg x hx v
  have h_simplex : ∀ x ∈ S, s x ≠ 0 → (fun v => w x v / s x) ∈ simplex n := by
    intro x hx hsx
    refine ⟨fun v => div_nonneg (hw_nonneg x hx v) (hs_nonneg x hx), ?_⟩
    rw [← Finset.sum_div]
    exact div_self hsx
  have hcompact : IsCompact (simplex n) := isCompact_stdSimplex ℝ (Fin n)
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn hg
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hbound : ∀ y ∈ simplex n, |g y j| ≤ M := fun y hy =>
    (norm_le_pi_norm (g y) j).trans ((hM₀ y hy).trans (le_max_left M₀ 0))
  intro x₀ hx₀
  by_cases hs₀ : s x₀ = 0
  · change Filter.Tendsto
      (fun x => if s x = 0 then (0 : ℝ) else s x * g (fun v => w x v / s x) j)
      (𝓝[S] x₀) (𝓝 (if s x₀ = 0 then (0 : ℝ) else s x₀ * g (fun v => w x₀ v / s x₀) j))
    simp only [hs₀, ↓reduceIte]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (g := fun x => M * |s x|)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      by_cases hsx : s x = 0
      · simp [hsx]
      · simp only [hsx, ↓reduceIte, Real.norm_eq_abs, abs_mul]
        have hle := hbound _ (h_simplex x hx hsx)
        calc
          |s x| * |g (fun v => w x v / s x) j| ≤ |s x| * M := by gcongr
          _ = M * |s x| := mul_comm _ _
    · have htend : Filter.Tendsto (fun x => M * |s x|) (𝓝[S] x₀) (𝓝 (M * |s x₀|)) :=
        (continuous_const.continuousWithinAt.mul
          (continuous_abs.continuousAt.comp_continuousWithinAt (hs_cont x₀ hx₀))).tendsto
      simpa [hs₀] using htend
  · let yMap : X → Fin n → ℝ := fun x v => w x v / s x
    have hyMap_tend : Filter.Tendsto yMap (𝓝[S] x₀) (𝓝 (yMap x₀)) :=
      tendsto_pi_nhds.mpr fun v =>
        ((hw_cont v x₀ hx₀).div (hs_cont x₀ hx₀) hs₀).tendsto
    have hsnz : {x : X | s x ≠ 0} ∈ 𝓝[S] x₀ :=
      (hs_cont x₀ hx₀).tendsto (isOpen_ne.mem_nhds hs₀)
    have h_maps : Filter.Tendsto yMap (𝓝[S] x₀) (𝓝[simplex n] (yMap x₀)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hyMap_tend, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hsnz] with x hx hsx
      exact h_simplex x hx hsx
    have hg_at : ContinuousWithinAt (fun y => g y j) (simplex n) (yMap x₀) :=
      (continuous_apply j).continuousAt.comp_continuousWithinAt
        (hg (yMap x₀) (h_simplex x₀ hx₀ hs₀))
    have h_prod : ContinuousWithinAt (fun x => s x * g (yMap x) j) S x₀ :=
      (hs_cont x₀ hx₀).mul (hg_at.tendsto.comp h_maps)
    refine h_prod.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hsnz] with x hx
      simp [s, hx, yMap]
    · simp [s, hs₀, yMap]

/-- The binary join `g₁ * g₂ : Δ^(m+n-1) → ℝ^(p+q+1)` of two almost six-embeddings is an
almost six-embedding. -/
theorem join_almostSixEmbedding {m n p q : ℕ}
    {g₁ : (Fin m → ℝ) → (Fin p → ℝ)} {g₂ : (Fin n → ℝ) → (Fin q → ℝ)}
    (hg₁ : IsAlmostSixEmbedding g₁) (hg₂ : IsAlmostSixEmbedding g₂) :
    ∃ f : (Fin (m + n) → ℝ) → (Fin (p + q + 1) → ℝ),
      IsAlmostSixEmbedding f := by
  let w₁ : (Fin (m + n) → ℝ) → Fin m → ℝ := fun x v => x (Fin.castAdd n v)
  let w₂ : (Fin (m + n) → ℝ) → Fin n → ℝ := fun x w => x (Fin.natAdd m w)
  let t : (Fin (m + n) → ℝ) → ℝ := fun x => ∑ v : Fin m, w₁ x v
  let s : (Fin (m + n) → ℝ) → ℝ := fun x => ∑ w : Fin n, w₂ x w
  let f : (Fin (m + n) → ℝ) → (Fin (p + q + 1) → ℝ) := fun x k =>
    if _hk0 : k = 0 then t x
    else if hkp : k.1 - 1 < p then
      if t x = 0 then 0 else t x * g₁ (fun v => w₁ x v / t x) ⟨k.1 - 1, hkp⟩
    else
      if s x = 0 then 0 else s x * g₂ (fun w => w₂ x w / s x) ⟨k.1 - 1 - p, by have := k.isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · refine continuousOn_pi.mpr fun k => ?_
    by_cases hk0 : k = 0
    · have hfun : (fun x => f x k) = t := funext fun x => by simp [f, hk0]
      rw [hfun]
      exact (continuous_finsetSum Finset.univ fun v _ =>
        continuous_apply (Fin.castAdd n v)).continuousOn
    · by_cases hkp : k.1 - 1 < p
      · have hfun :
            (fun x => f x k) = fun x =>
              let t' := ∑ v, w₁ x v
              if t' = 0 then 0 else t' * g₁ (fun v => w₁ x v / t') ⟨k.1 - 1, hkp⟩ :=
          funext fun x => by simp [f, hk0, hkp, t]
        rw [hfun]
        exact continuousOn_perspective (fun v => (continuous_apply _).continuousOn)
          (fun _ hx v => hx.1 _) hg₁.1 ⟨k.1 - 1, hkp⟩
      · have hfun :
            (fun x => f x k) = fun x =>
              let s' := ∑ w, w₂ x w
              if s' = 0 then 0 else s' * g₂ (fun w => w₂ x w / s') ⟨k.1 - 1 - p, by have := k.isLt; omega⟩ :=
          funext fun x => by simp [f, hk0, hkp, s]
        rw [hfun]
        exact continuousOn_perspective (fun w => (continuous_apply _).continuousOn)
          (fun _ hx w => hx.1 _) hg₂.1 ⟨k.1 - 1 - p, by have := k.isLt; omega⟩
  · intro x hx hdisj
    by_contra h_all
    push Not at h_all
    have ht_eq : ∀ i, t (x i) = t (x 0) := fun i => by
      have h0 := congrFun (h_all i) 0
      simpa [f] using h0
    have hts_sum : ∀ i, t (x i) + s (x i) = 1 := fun i => by
      have hsum := (hx i).2
      rw [Fin.sum_univ_add] at hsum
      exact hsum
    have hs_eq : ∀ i, s (x i) = s (x 0) := fun i => by
      linarith [hts_sum i, hts_sum 0, ht_eq i]
    by_cases ht0 : t (x 0) = 0
    · have hs0 : s (x 0) = 1 := by linarith [hts_sum 0, ht0]
      have hsi_ne : ∀ i, s (x i) ≠ 0 := fun i => by
        rw [hs_eq i, hs0]
        norm_num
      have hsi_nonneg : ∀ i, 0 ≤ s (x i) := fun i =>
        Finset.sum_nonneg fun w _ => (hx i).1 _
      let y : Fin 6 → Fin n → ℝ := fun i w => w₂ (x i) w / s (x i)
      have hy_mem : ∀ i, y i ∈ simplex n := fun i =>
        ⟨fun w => div_nonneg ((hx i).1 _) (hsi_nonneg i),
          by rw [← Finset.sum_div]; exact div_self (hsi_ne i)⟩
      have hy_disj : DisjointSupports y := fun i j hij w => by
        rcases hdisj i j hij (Fin.natAdd m w) with hi0 | hj0
        · left; simp [y, w₂, hi0]
        · right; simp [y, w₂, hj0]
      obtain ⟨i, hi_ne⟩ := hg₂.2 y hy_mem hy_disj
      apply hi_ne
      funext j
      let k : Fin (p + q + 1) := ⟨1 + p + j.1, by omega⟩
      have hk0 : k ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp [k] at hv
      have hkp : ¬ k.1 - 1 < p := by simp [k]; omega
      have hksub : (⟨k.1 - 1 - p, by have := k.isLt; omega⟩ : Fin q) = j := by
        ext; simp [k]; omega
      have hcon := congrFun (h_all i) k
      simp only [f, hk0, ↓reduceDIte, hkp, hs_eq i, hs0, one_ne_zero, ↓reduceIte, hksub] at hcon
      simpa [y, hs_eq i, hs0] using hcon
    · have hti_ne : ∀ i, t (x i) ≠ 0 := fun i => (ht_eq i).symm ▸ ht0
      have hti_nonneg : ∀ i, 0 ≤ t (x i) := fun i =>
        Finset.sum_nonneg fun v _ => (hx i).1 _
      let y : Fin 6 → Fin m → ℝ := fun i v => w₁ (x i) v / t (x i)
      have hy_mem : ∀ i, y i ∈ simplex m := fun i =>
        ⟨fun v => div_nonneg ((hx i).1 _) (hti_nonneg i),
          by rw [← Finset.sum_div]; exact div_self (hti_ne i)⟩
      have hy_disj : DisjointSupports y := fun i j hij v => by
        rcases hdisj i j hij (Fin.castAdd n v) with hi0 | hj0
        · left; simp [y, w₁, hi0]
        · right; simp [y, w₁, hj0]
      obtain ⟨i, hi_ne⟩ := hg₁.2 y hy_mem hy_disj
      apply hi_ne
      funext j
      let k : Fin (p + q + 1) := ⟨1 + j.1, by omega⟩
      have hk0 : k ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp [k] at hv
      have hkp : k.1 - 1 < p := by simp [k]
      have hksub : (⟨k.1 - 1, hkp⟩ : Fin p) = j := by
        ext; simp [k]
      have hcon := congrFun (h_all i) k
      simp only [f, hk0, ↓reduceDIte, hkp, ht_eq i, ht0, ↓reduceIte, hksub] at hcon
      exact mul_left_cancel₀ ht0 (by simpa [y, ht_eq i] using hcon)

private lemma emptyFive_almostSixEmbedding :
    IsAlmostSixEmbedding (fun (_ : Fin 5 → ℝ) => (Fin.elim0 : Fin 0 → ℝ)) := by
  refine ⟨continuousOn_const, fun x hx hdisj => ?_⟩
  exfalso
  have hex : ∀ i : Fin 6, ∃ v : Fin 5, x i v ≠ 0 := fun i => by
    by_contra hzero
    push Not at hzero
    have hsum0 : (∑ v : Fin 5, x i v) = 0 := Finset.sum_eq_zero fun v _ => hzero v
    linarith [(hx i).2]
  choose v hv using hex
  obtain ⟨i, j, hij, hvij⟩ := Fintype.exists_ne_map_eq_of_card_lt v (by simp)
  rcases hdisj i j hij (v i) with hi0 | hj0
  · exact hv i hi0
  · rw [hvij] at hj0
    exact hv j hj0

/-- Join-padding preserves almost six-embeddings (adding 5 vertices and 1 target coordinate). -/
private lemma padding_almostSixEmbedding {n q : ℕ}
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : IsAlmostSixEmbedding g) :
    ∃ f : (Fin (n + 5) → ℝ) → (Fin (q + 1) → ℝ),
      IsAlmostSixEmbedding f := by
  simpa using join_almostSixEmbedding hg emptyFive_almostSixEmbedding

private lemma reindex_almostSixEmbedding {n m q r : ℕ} (hn : n = m) (hq : q = r)
    {g : (Fin n → ℝ) → (Fin q → ℝ)} (hg : IsAlmostSixEmbedding g) :
    ∃ f : (Fin m → ℝ) → (Fin r → ℝ), IsAlmostSixEmbedding f := by
  let castDom : (Fin m → ℝ) → (Fin n → ℝ) := fun x v => x (Fin.cast hn v)
  let f : (Fin m → ℝ) → (Fin r → ℝ) := fun x j => g (castDom x) (Fin.cast hq.symm j)
  have hcastDom_mem : ∀ x ∈ simplex m, castDom x ∈ simplex n := fun x hx => by
    refine ⟨fun v => hx.1 _, ?_⟩
    calc
      ∑ v : Fin n, x (Fin.cast hn v) = ∑ w : Fin m, x w :=
        Fintype.sum_equiv (finCongr hn) (fun v => x (Fin.cast hn v)) x (fun _ => rfl)
      _ = 1 := hx.2
  refine ⟨f, ?_, ?_⟩
  · have hcast_cont : Continuous castDom := continuous_pi fun v => continuous_apply _
    have hg_comp : ContinuousOn (fun x => g (castDom x)) (simplex m) :=
      hg.1.comp hcast_cont.continuousOn hcastDom_mem
    refine continuousOn_pi.mpr fun j => ?_
    exact (continuous_apply (Fin.cast hq.symm j)).continuousOn.comp hg_comp (fun _ _ => Set.mem_univ _)
  · intro x hx hdisj
    have hdisj' : DisjointSupports (fun i => castDom (x i)) :=
      fun i j hij v => hdisj i j hij (Fin.cast hn v)
    obtain ⟨i, hi⟩ := hg.2 (fun i => castDom (x i)) (fun i => hcastDom_mem (x i) (hx i)) hdisj'
    refine ⟨i, fun heq => hi ?_⟩
    funext j
    have hcon := congrFun heq (Fin.cast hq j)
    simpa [f] using hcon

private lemma iterated_padding_from {n₀ q₀ : ℕ} (k : ℕ)
    {g₀ : (Fin n₀ → ℝ) → (Fin q₀ → ℝ)} (hg₀ : IsAlmostSixEmbedding g₀) :
    ∃ f : (Fin (n₀ + 5 * k) → ℝ) → (Fin (q₀ + k) → ℝ),
      IsAlmostSixEmbedding f := by
  induction k with
  | zero =>
    simpa using ⟨g₀, hg₀⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨f, hf⟩ := padding_almostSixEmbedding hg
    exact reindex_almostSixEmbedding (by omega : n₀ + 5 * k + 5 = n₀ + 5 * (k + 1))
      (by omega : q₀ + k + 1 = q₀ + (k + 1)) hf

/-- **Best unconditional Tverberg counterexample for `r = 6`**: in every dimension `d ≥ 6`,
there is an almost six-embedding `Δ^(5d+5) → ℝ^d` (`5d + 6` vertices). -/
theorem tverberg_counterexample_ge_six (d : ℕ) (hd : 6 ≤ d) :
    ∃ f : (Fin (5 * d + 6) → ℝ) → (Fin d → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨g₀, hg₀⟩ := tverberg_counterexample
  obtain ⟨g, hg⟩ := iterated_padding_from (d - 6) hg₀
  exact reindex_almostSixEmbedding (by omega : 36 + 5 * (d - 6) = 5 * d + 6)
    (by omega : 6 + (d - 6) = d) hg

/-- **Fivefold join of Theorem A (no `[AKS]` needed)**: an unconditional almost six-embedding
`Δ¹⁷⁹ → ℝ³⁴` (`180 = 5 * 36` vertices, `34 = 36 - 2` target coordinates). -/
theorem fivefold_tverberg_join :
    ∃ f : (Fin 180 → ℝ) → (Fin 34 → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨f₁, hf₁⟩ := tverberg_counterexample
  obtain ⟨f₂, hf₂⟩ := join_almostSixEmbedding hf₁ hf₁
  obtain ⟨f₃, hf₃⟩ := join_almostSixEmbedding hf₂ hf₁
  obtain ⟨f₄, hf₄⟩ := join_almostSixEmbedding hf₃ hf₁
  exact join_almostSixEmbedding hf₄ hf₁

/-- **Padded fivefold join (`d ≥ 36`, no `[AKS]`)**: for every `d ≥ 36`, there exists an
unconditional almost six-embedding `Δ^(5d-1) → ℝ^(d-2)` (`5d` vertices). -/
theorem padded_tverberg_ge_36 (d : ℕ) (hd : 36 ≤ d) :
    ∃ g : (Fin (5 * d) → ℝ) → (Fin (d - 2) → ℝ),
      IsAlmostSixEmbedding g := by
  obtain ⟨g₀, hg₀⟩ := fivefold_tverberg_join
  obtain ⟨g, hg⟩ := iterated_padding_from (d - 36) hg₀
  exact reindex_almostSixEmbedding (by omega : 180 + 5 * (d - 36) = 5 * d)
    (by omega : 34 + (d - 36) = d - 2) hg

/-- **General `(k + 1)`-fold binary join of Theorem A**: for every `k : ℕ`, there is an
unconditional almost six-embedding `Δ^(36 * (k + 1) - 1) → ℝ^(7 * (k + 1) - 1)`. -/
theorem kfold_tverberg_join (k : ℕ) :
    ∃ f : (Fin (36 * (k + 1)) → ℝ) → (Fin (7 * (k + 1) - 1) → ℝ),
      IsAlmostSixEmbedding f := by
  induction k with
  | zero => exact tverberg_counterexample
  | succ k ih =>
    obtain ⟨f₁, hf₁⟩ := ih
    obtain ⟨f₀, hf₀⟩ := tverberg_counterexample
    obtain ⟨f, hf⟩ := join_almostSixEmbedding hf₁ hf₀
    exact reindex_almostSixEmbedding (by omega : 36 * (k + 1) + 36 = 36 * (k + 1 + 1))
      (by omega : (7 * (k + 1) - 1) + 6 + 1 = 7 * (k + 1 + 1) - 1) hf

/-- **Padded `41`-fold join (`d ≥ 288`, no `[AKS]`)**: for every `d ≥ 288`, there exists an
unconditional almost six-embedding `Δ^(5d+35) → ℝ^(d-2)` (`5d + 36` vertices). -/
theorem padded_tverberg_ge_288 (d : ℕ) (hd : 288 ≤ d) :
    ∃ g : (Fin (5 * d + 36) → ℝ) → (Fin (d - 2) → ℝ),
      IsAlmostSixEmbedding g := by
  obtain ⟨g₀, hg₀⟩ := kfold_tverberg_join 40
  obtain ⟨g, hg⟩ := iterated_padding_from (d - 288) hg₀
  exact reindex_almostSixEmbedding (by omega : 36 * (40 + 1) + 5 * (d - 288) = 5 * d + 36)
    (by omega : (7 * (40 + 1) - 1) + (d - 288) = d - 2) hg

/-- **Twofold seven-color join**: given an almost six-embedding `f₇ : Δ⁴¹ → ℝ⁷`
(Section 2.3 of the research report), its self-join gives an almost six-embedding
`Δ⁸³ → ℝ¹⁵` (`84` vertices). -/
theorem twofold_seven_color_join
    {f₇ : (Fin 42 → ℝ) → (Fin 7 → ℝ)} (hf₇ : IsAlmostSixEmbedding f₇) :
    ∃ f : (Fin 84 → ℝ) → (Fin 15 → ℝ),
      IsAlmostSixEmbedding f := by
  simpa using join_almostSixEmbedding hf₇ hf₇

/-! ### Helper 2: Hausdorff-continuous inward distance (Lemma 5.3) -/

/-- Inward distance of a point `p` to the boundary/complement of a convex body `C`. -/
def inwardDist {d : ℕ} (p : Ambient d) (C : Body d) : ℝ :=
  Metric.infDist p (C : Set (Ambient d))ᶜ

private lemma body_compl_nonempty {d : ℕ} (hd : 0 < d) (C : Body d) :
    (C : Set (Ambient d))ᶜ.Nonempty := by
  obtain ⟨R, hR⟩ := C.isCompact.isBounded.subset_closedBall (0 : Ambient d)
  let e0 : Ambient d := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ)
  have he0 : ‖e0‖ = 1 :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).norm_eq_one ⟨0, hd⟩
  let x₀ : Ambient d := (max R 0 + 1) • e0
  refine ⟨x₀, fun hx₀ => ?_⟩
  have hle : dist x₀ 0 ≤ R := hR hx₀
  have hx₀_norm : ‖x₀‖ = max R 0 + 1 := by
    rw [norm_smul, he0, mul_one, Real.norm_of_nonneg (by positivity)]
  rw [dist_zero_right, hx₀_norm] at hle
  linarith [le_max_left R 0]

private lemma inwardDist_pos_iff {d : ℕ} (hd : 0 < d) (p : Ambient d) (C : Body d) :
    0 < inwardDist p C ↔ p ∈ interior (C : Set (Ambient d)) := by
  have hne : (C : Set (Ambient d))ᶜ.Nonempty := body_compl_nonempty hd C
  unfold inwardDist
  rw [← Metric.infDist_pos_iff_notMem_closure hne]
  rw [interior_eq_compl_closure_compl]
  simp

private lemma inwardDist_le {d : ℕ} (hd : 0 < d) (p : Ambient d) (C D : Body d) :
    inwardDist p D ≤ inwardDist p C + dist C D := by
  have hneC : (C : Set (Ambient d))ᶜ.Nonempty := body_compl_nonempty hd C
  suffices h : inwardDist p D - dist C D ≤ inwardDist p C by linarith
  refine (Metric.le_infDist hneC).2 fun y hyC => ?_
  have hy_compl : y ∉ (C : Set (Ambient d)) := hyC
  obtain ⟨f, s, hfC, hfy⟩ :=
    geometric_hahn_banach_closed_point C.convex C.isClosed hy_compl
  let v : Ambient d := (InnerProductSpace.toDual ℝ (Ambient d)).symm f
  have hv_ne : v ≠ 0 := by
    intro hv0
    obtain ⟨x₀, hx₀⟩ := C.nonempty
    have hf_zero : f = 0 := by
      have hmap := congrArg (InnerProductSpace.toDual ℝ (Ambient d)) hv0
      simpa [v] using hmap
    have h1 := hfC x₀ hx₀
    simp only [hf_zero, zero_apply] at h1 hfy
    linarith
  let u : Ambient d := (‖v‖)⁻¹ • v
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv_ne)]
  have hu_sep : ∀ x ∈ (C : Set (Ambient d)), ⟪u, x⟫_ℝ < ⟪u, y⟫_ℝ := by
    intro x hx
    have hnorm_pos : 0 < (‖v‖)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hv_ne)
    have hfx_lt_fy : f x < f y := (hfC x hx).trans hfy
    have hvx : ⟪v, x⟫_ℝ = f x := InnerProductSpace.toDual_symm_apply
    have hvy : ⟪v, y⟫_ℝ = f y := InnerProductSpace.toDual_symm_apply
    calc
      ⟪u, x⟫_ℝ = (‖v‖)⁻¹ * ⟪v, x⟫_ℝ := by simp [u, real_inner_smul_left]
      _ = (‖v‖)⁻¹ * f x := by rw [hvx]
      _ < (‖v‖)⁻¹ * f y := mul_lt_mul_of_pos_left hfx_lt_fy hnorm_pos
      _ = (‖v‖)⁻¹ * ⟪v, y⟫_ℝ := by rw [hvy]
      _ = ⟪u, y⟫_ℝ := by simp [u, real_inner_smul_left]
  suffices hdelta : ∀ δ : ℝ, 0 < δ → inwardDist p D ≤ dist p y + (dist C D + δ) by
    have h_le : inwardDist p D - dist C D ≤ dist p y := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      linarith [hdelta δ hδ]
    exact h_le
  intro δ hδ
  let z : Ambient d := y + (dist C D + δ) • u
  have hzD : z ∈ (D : Set (Ambient d))ᶜ := by
    intro hz_mem
    have hhaus : Metric.hausdorffDist (C : Set (Ambient d)) (D : Set (Ambient d)) < dist C D + δ := by
      rw [ConvexBody.hausdorffDist_coe]
      linarith
    obtain ⟨x, hxC, hxz⟩ :=
      Metric.exists_dist_lt_of_hausdorffDist_lt' hz_mem hhaus ConvexBody.hausdorffEDist_ne_top
    have h_upper : ⟪u, z - x⟫_ℝ < dist C D + δ := by
      have hcs : ⟪u, z - x⟫_ℝ ≤ ‖u‖ * ‖z - x‖ := real_inner_le_norm u (z - x)
      rw [hu_norm, one_mul, ← dist_eq_norm, dist_comm] at hcs
      exact hcs.trans_lt hxz
    have h_lower : dist C D + δ < ⟪u, z - x⟫_ℝ := by
      have hzx_eq : z - x = (y - x) + (dist C D + δ) • u := by
        simp [z]; abel
      have hu_self : ⟪u, u⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, hu_norm, one_pow]
      rw [hzx_eq, inner_add_right, inner_smul_right, hu_self, mul_one, inner_sub_right]
      linarith [hu_sep x hxC]
    linarith
  have hdist_yz : dist y z = dist C D + δ := by
    rw [dist_eq_norm, show y - z = -((dist C D + δ) • u) by simp [z], norm_neg, norm_smul,
      hu_norm, mul_one, Real.norm_of_nonneg (add_nonneg dist_nonneg hδ.le)]
  have hinf : inwardDist p D ≤ dist p z := Metric.infDist_le_dist_of_mem hzD
  exact hinf.trans ((dist_triangle p y z).trans (by rw [hdist_yz]))

private lemma continuous_inwardDist {d : ℕ} (hd : 0 < d) (p : Ambient d) :
    Continuous (inwardDist p : Body d → ℝ) :=
  (LipschitzWith.of_le_add fun C D => by
    rw [dist_comm]
    exact inwardDist_le hd p D C).continuous

/-! ### Helper 2.5: Blaschke selection theorem and central-avoidance margin (Lemma 5.2) -/

private def bodyToNC {d : ℕ} (C : Body d) : TopologicalSpace.NonemptyCompacts (Ambient d) :=
  ⟨⟨(C : Set (Ambient d)), C.isCompact⟩, C.nonempty⟩

private lemma isometry_bodyToNC {d : ℕ} : Isometry (bodyToNC (d := d)) :=
  Isometry.of_dist_eq fun C D => by
    change Metric.hausdorffDist (C : Set (Ambient d)) D = dist C D
    exact ConvexBody.hausdorffDist_coe C D

private lemma continuous_infDist_body {d : ℕ} (x : Ambient d) :
    Continuous (fun C : Body d => Metric.infDist x (C : Set (Ambient d))) :=
  (LipschitzWith.of_le_add fun C D => by
    have h := Metric.infDist_le_infDist_add_hausdorffDist (x := x)
      (s := (D : Set (Ambient d))) (t := (C : Set (Ambient d))) ConvexBody.hausdorffEDist_ne_top
    rw [ConvexBody.hausdorffDist_coe, dist_comm D C] at h
    exact h).continuous

private lemma convex_iff_infDist_ineq {d : ℕ}
    (K : TopologicalSpace.NonemptyCompacts (Ambient d)) :
    Convex ℝ (K : Set (Ambient d)) ↔
      ∀ (x y : Ambient d) (a b : ℝ),
        0 ≤ a → 0 ≤ b → a + b = 1 →
        Metric.infDist (a • x + b • y) (K : Set (Ambient d)) ≤
          a * Metric.infDist x (K : Set (Ambient d)) +
          b * Metric.infDist y (K : Set (Ambient d)) := by
  constructor
  · intro hK x y a b ha hb hab
    obtain ⟨u, hu, hux⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    obtain ⟨v, hv, hvy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty y
    have hmem : a • u + b • v ∈ (K : Set (Ambient d)) :=
      convex_iff_add_mem.mp hK hu hv ha hb hab
    have hdiff : (a • x + b • y) - (a • u + b • v) = a • (x - u) + b • (y - v) := by
      simp only [smul_sub]
      abel
    calc
      Metric.infDist (a • x + b • y) (K : Set (Ambient d))
        ≤ dist (a • x + b • y) (a • u + b • v) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖a • (x - u) + b • (y - v)‖ := by rw [dist_eq_norm, hdiff]
      _ ≤ ‖a • (x - u)‖ + ‖b • (y - v)‖ := norm_add_le _ _
      _ = a * ‖x - u‖ + b * ‖y - v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ = a * Metric.infDist x (K : Set (Ambient d)) + b * Metric.infDist y (K : Set (Ambient d)) := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← hux, ← hvy]
  · intro hineq
    refine convex_iff_add_mem.mpr fun x hx y hy a b ha hb hab => ?_
    have hx0 : Metric.infDist x (K : Set (Ambient d)) = 0 := Metric.infDist_zero_of_mem hx
    have hy0 : Metric.infDist y (K : Set (Ambient d)) = 0 := Metric.infDist_zero_of_mem hy
    have hle : Metric.infDist (a • x + b • y) (K : Set (Ambient d)) ≤ 0 := by
      have h := hineq x y a b ha hb hab
      rw [hx0, hy0, mul_zero, mul_zero, add_zero] at h
      exact h
    have hzero : Metric.infDist (a • x + b • y) (K : Set (Ambient d)) = 0 :=
      le_antisymm hle Metric.infDist_nonneg
    exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).2 hzero

private lemma isClosed_range_bodyToNC {d : ℕ} :
    IsClosed (Set.range (bodyToNC (d := d))) := by
  let S : Set (TopologicalSpace.NonemptyCompacts (Ambient d)) :=
    ⋂ (x : Ambient d) (y : Ambient d)
      (c : {p : ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1}),
      {K | Metric.infDist (c.1.1 • x + c.1.2 • y) (K : Set (Ambient d)) ≤
        c.1.1 * Metric.infDist x (K : Set (Ambient d)) +
        c.1.2 * Metric.infDist y (K : Set (Ambient d))}
  have hS_closed : IsClosed S := by
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun c => ?_
    refine isClosed_le
      (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const (c.1.1 • x + c.1.2 • y)).continuous
      (((continuous_const.mul
          (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const x).continuous)).add
        (continuous_const.mul
          (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const y).continuous))
  have h_eq : Set.range (bodyToNC (d := d)) = S := by
    ext K
    constructor
    · rintro ⟨C, rfl⟩
      simp only [S, Set.mem_iInter, Set.mem_ofPred_eq]
      intro x y c
      exact (convex_iff_infDist_ineq (bodyToNC C)).mp C.convex x y c.1.1 c.1.2 c.2.1 c.2.2.1 c.2.2.2
    · intro hK
      have hconv : Convex ℝ (K : Set (Ambient d)) := by
        refine (convex_iff_infDist_ineq K).mpr fun x y a b ha hb hab => ?_
        simp only [S, Set.mem_iInter, Set.mem_ofPred_eq] at hK
        exact hK x y ⟨(a, b), ha, hb, hab⟩
      refine ⟨⟨(K : Set (Ambient d)), hconv, K.isCompact, K.nonempty⟩, ?_⟩
      ext
      rfl
  rw [h_eq]
  exact hS_closed

private lemma isClosedEmbedding_bodyToNC {d : ℕ} :
    Topology.IsClosedEmbedding (bodyToNC (d := d)) where
  __ := isometry_bodyToNC.isEmbedding
  isClosed_range := isClosed_range_bodyToNC

/-- **Blaschke Selection Theorem**: compact convex bodies contained in the closed unit ball
form a compact subset of `ConvexBody (Ambient d)` with the Hausdorff metric. -/
theorem blaschke_isCompact_subsets_unitBall (d : ℕ) :
    IsCompact {C : Body d | (C : Set (Ambient d)) ⊆ unitBall d} := by
  have hK :
      IsCompact {K : TopologicalSpace.NonemptyCompacts (Ambient d) | (K : Set (Ambient d)) ⊆ unitBall d} :=
    TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact
      (isCompact_closedBall (0 : Ambient d) 1)
  have hpre :
      {C : Body d | (C : Set (Ambient d)) ⊆ unitBall d} =
        bodyToNC ⁻¹' {K : TopologicalSpace.NonemptyCompacts (Ambient d) | (K : Set (Ambient d)) ⊆ unitBall d} := by
    ext C
    rfl
  rw [hpre]
  exact isClosedEmbedding_bodyToNC.isCompact_preimage hK

/-- **Central-avoidance margin (Lemma 5.2)**: if `p` blocks all central six-partitions of
`unitBall d`, there exists `eta ∈ (0, 1)` such that every six-partition whose parts all meet
`eta • unitBall d` contains some marker `p a` in the interior of some part. -/
theorem exists_eta_of_isBlocking {d m : ℕ} (hd : 0 < d)
    {p : Fin m → Ambient d} (hp : IsBlocking p) :
    ∃ eta : ℝ,
      0 < eta ∧ eta < 1 ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, ∃ x ∈ (C i : Set (Ambient d)), ‖x‖ ≤ eta) →
        ∃ i a, p a ∈ interior (C i : Set (Ambient d)) := by
  let Q : Set (Fin 6 → Body d) :=
    Set.pi Set.univ fun _ : Fin 6 => {C : Body d | (C : Set (Ambient d)) ⊆ unitBall d}
  have hQ_compact : IsCompact Q :=
    isCompact_univ_pi fun _ => blaschke_isCompact_subsets_unitBall d
  let Cov : Set (Fin 6 → Body d) :=
    ⋂ x ∈ unitBall d,
      {C : Fin 6 → Body d | (∏ i : Fin 6, Metric.infDist x (C i : Set (Ambient d))) = 0}
  let Disj : Set (Fin 6 → Body d) :=
    ⋂ (i : Fin 6) (j : Fin 6) (_ : i ≠ j) (x : Ambient d),
      {C : Fin 6 → Body d | inwardDist x (C i) * inwardDist x (C j) = 0}
  let NoMark : Set (Fin 6 → Body d) :=
    ⋂ (i : Fin 6) (a : Fin m),
      {C : Fin 6 → Body d | inwardDist (p a) (C i) = 0}
  have hCov_closed : IsClosed Cov := by
    refine isClosed_biInter fun x _ => isClosed_eq ?_ continuous_const
    exact continuous_finsetProd Finset.univ fun i _ =>
      (continuous_infDist_body x).comp (continuous_apply i)
  have hDisj_closed : IsClosed Disj := by
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun x => isClosed_eq ?_ continuous_const
    exact ((continuous_inwardDist hd x).comp (continuous_apply i)).mul
      ((continuous_inwardDist hd x).comp (continuous_apply j))
  have hNoMark_closed : IsClosed NoMark := by
    refine isClosed_iInter fun i => isClosed_iInter fun a => isClosed_eq ?_ continuous_const
    exact (continuous_inwardDist hd (p a)).comp (continuous_apply i)
  let S_bad : Set (Fin 6 → Body d) := Q ∩ (Cov ∩ Disj ∩ NoMark)
  have hS_compact : IsCompact S_bad :=
    hQ_compact.inter_right ((hCov_closed.inter hDisj_closed).inter hNoMark_closed)
  have hCov_iff : ∀ C : Fin 6 → Body d,
      C ∈ Cov ↔ unitBall d ⊆ (⋃ i, (C i : Set (Ambient d))) := fun C => by
    simp only [Cov, Set.mem_iInter, Set.mem_ofPred_eq, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and]
    refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · obtain ⟨i, hi⟩ := h x hx
      exact Set.mem_iUnion.mpr ⟨i, ((C i).isClosed.mem_iff_infDist_zero (C i).nonempty).2 hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h hx)
      exact ⟨i, Metric.infDist_zero_of_mem hi⟩
  have hDisj_iff : ∀ C : Fin 6 → Body d,
      C ∈ Disj ↔
        ∀ i j, i ≠ j →
          Disjoint (interior (C i : Set (Ambient d)))
                   (interior (C j : Set (Ambient d))) := fun C => by
    simp only [Disj, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h i j hij => Set.disjoint_left.mpr fun x hxi hxj => ?_, fun h i j hij x => ?_⟩
    · have hi_pos : 0 < inwardDist x (C i) := (inwardDist_pos_iff hd x (C i)).mpr hxi
      have hj_pos : 0 < inwardDist x (C j) := (inwardDist_pos_iff hd x (C j)).mpr hxj
      have h0 : inwardDist x (C i) * inwardDist x (C j) = 0 := h i j hij x
      linarith [mul_pos hi_pos hj_pos]
    · by_cases hxi : x ∈ interior (C i : Set (Ambient d))
      · have hxj : x ∉ interior (C j : Set (Ambient d)) := Set.disjoint_left.mp (h i j hij) hxi
        have hwj : inwardDist x (C j) = 0 := by
          have hnot := (inwardDist_pos_iff hd x (C j)).not.mpr hxj
          exact le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
        simp [hwj]
      · have hwi : inwardDist x (C i) = 0 := by
          have hnot := (inwardDist_pos_iff hd x (C i)).not.mpr hxi
          exact le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
        simp [hwi]
  have hNoMark_iff : ∀ C : Fin 6 → Body d,
      C ∈ NoMark ↔ ∀ i a, p a ∉ interior (C i : Set (Ambient d)) := fun C => by
    simp only [NoMark, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h i a ha => ?_, fun h i a => ?_⟩
    · have hpos : 0 < inwardDist (p a) (C i) := (inwardDist_pos_iff hd (p a) (C i)).mpr ha
      linarith [h i a]
    · have hnot := (inwardDist_pos_iff hd (p a) (C i)).not.mpr (h i a)
      exact le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
  let F : (Fin 6 → Body d) → ℝ := fun C =>
    ∑ i : Fin 6, Metric.infDist (0 : Ambient d) (C i : Set (Ambient d))
  have hF_cont : Continuous F :=
    continuous_finsetSum Finset.univ fun i _ =>
      (continuous_infDist_body (0 : Ambient d)).comp (continuous_apply i)
  have h_not_mem_Sbad : ∀ C : Fin 6 → Body d, IsSixPartition C →
      (∃ i a, p a ∈ interior (C i : Set (Ambient d))) ∨ C ∈ S_bad := by
    intro C hC
    by_cases hm : ∃ i a, p a ∈ interior (C i : Set (Ambient d))
    · exact Or.inl hm
    · right
      push Not at hm
      refine ⟨fun i _ => ?_, ⟨(hCov_iff C).mpr (by rw [hC.1]), (hDisj_iff C).mpr hC.2.2⟩,
        (hNoMark_iff C).mpr hm⟩
      rw [hC.1]
      exact Set.subset_iUnion (fun j => (C j : Set (Ambient d))) i
  by_cases hS_ne : S_bad.Nonempty
  · obtain ⟨C₀, hC₀_mem, hC₀_min⟩ := hS_compact.exists_isMinOn hS_ne hF_cont.continuousOn
    have hF_pos : 0 < F C₀ := by
      by_contra hle
      have hnonpos : F C₀ ≤ 0 := not_lt.mp hle
      have hzero : F C₀ = 0 :=
        le_antisymm hnonpos (Finset.sum_nonneg fun i _ => Metric.infDist_nonneg)
      have hzero_mem : ∀ i : Fin 6, (0 : Ambient d) ∈ (C₀ i : Set (Ambient d)) := fun i => by
        have hi0 : Metric.infDist (0 : Ambient d) (C₀ i : Set (Ambient d)) = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Metric.infDist_nonneg) |>.mp hzero i
            (Finset.mem_univ i)
        exact ((C₀ i).isClosed.mem_iff_infDist_zero (C₀ i).nonempty).2 hi0
      rcases hC₀_mem with ⟨hQ₀, ⟨hCov₀, hDisj₀⟩, hNoMark₀⟩
      have h_eq : unitBall d = (⋃ i, (C₀ i : Set (Ambient d))) :=
        subset_antisymm ((hCov_iff C₀).mp hCov₀) (Set.iUnion_subset fun i => hQ₀ i (Set.mem_univ i))
      obtain ⟨i, a, ha⟩ := hp C₀ h_eq ((hDisj_iff C₀).mp hDisj₀) hzero_mem
      exact (hNoMark_iff C₀).mp hNoMark₀ i a ha
    let eta : ℝ := min (1 / 2) (F C₀ / 12)
    have heta0 : 0 < eta := lt_min (by norm_num) (by linarith)
    have heta1 : eta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨eta, heta0, heta1, fun C hC hmeet => ?_⟩
    rcases h_not_mem_Sbad C hC with hm | hC_bad
    · exact hm
    · exfalso
      have hmin : F C₀ ≤ F C := hC₀_min hC_bad
      have hFC_le : F C ≤ 6 * eta := by
        have hterm : ∀ i : Fin 6, Metric.infDist (0 : Ambient d) (C i : Set (Ambient d)) ≤ eta := by
          intro i
          obtain ⟨x, hxC, hxnorm⟩ := hmeet i
          calc
            Metric.infDist (0 : Ambient d) (C i : Set (Ambient d)) ≤ dist (0 : Ambient d) x :=
              Metric.infDist_le_dist_of_mem hxC
            _ = ‖x‖ := by rw [dist_zero_left]
            _ ≤ eta := hxnorm
        calc
          F C = ∑ i : Fin 6, Metric.infDist (0 : Ambient d) (C i : Set (Ambient d)) := rfl
          _ ≤ ∑ _i : Fin 6, eta := Finset.sum_le_sum fun i _ => hterm i
          _ = 6 * eta := by simp [nsmul_eq_mul]
      have heta_bound : eta ≤ F C₀ / 12 := min_le_right _ _
      linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, fun C hC _ => ?_⟩
    rcases h_not_mem_Sbad C hC with hm | hC_bad
    · exact hm
    · exact False.elim (hS_ne ⟨C, hC_bad⟩)

/-! ### Helper 3: Fair partitions under concentrated measures & Lebesgue restriction -/

private lemma fair_meets_eta_ball {d : ℕ} {eta : ℝ} (heta : eta < 1)
    {mu : Measure (Ambient d)}
    (_hpos : 0 < mu (unitBall d)) (htop : mu (unitBall d) < ⊤)
    (hconc : 5 * mu (unitBall d) < 6 * mu (Metric.closedBall (0 : Ambient d) eta))
    {C : Fin 6 → Body d} (hC : IsSixPartition C)
    (hfair : ∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) :
    ∀ i, ((C i : Set (Ambient d)) ∩ Metric.closedBall (0 : Ambient d) eta).Nonempty := by
  intro i
  by_contra h_empty
  have h_disj : Disjoint (C i : Set (Ambient d)) (Metric.closedBall (0 : Ambient d) eta) :=
    Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h_empty)
  have h_sub_C : (C i : Set (Ambient d)) ⊆ unitBall d := by
    rw [hC.1]
    exact Set.subset_iUnion (fun j => (C j : Set (Ambient d))) i
  have h_sub_eta : Metric.closedBall (0 : Ambient d) eta ⊆ unitBall d :=
    Metric.closedBall_subset_closedBall heta.le
  have h_union_le :
      mu (C i : Set (Ambient d)) + mu (Metric.closedBall (0 : Ambient d) eta) ≤
        mu (unitBall d) := by
    rw [← measure_union h_disj Metric.isClosed_closedBall.measurableSet]
    exact measure_mono (Set.union_subset h_sub_C h_sub_eta)
  rw [hfair i] at h_union_le
  have hB_ne_top : mu (unitBall d) ≠ ⊤ := htop.ne
  have hE_ne_top : mu (Metric.closedBall (0 : Ambient d) eta) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono h_sub_eta) htop).ne
  have hconc_real :
      5 * (mu (unitBall d)).toReal < 6 * (mu (Metric.closedBall (0 : Ambient d) eta)).toReal := by
    have h6E_ne_top : (6 : ENNReal) * mu (Metric.closedBall (0 : Ambient d) eta) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hE_ne_top
    have h5B_ne_top : (5 : ENNReal) * mu (unitBall d) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hB_ne_top
    have hlt := (ENNReal.toReal_lt_toReal h5B_ne_top h6E_ne_top).mpr hconc
    simpa [ENNReal.toReal_mul] using hlt
  have hsum_real :
      (mu (unitBall d)).toReal / 6 + (mu (Metric.closedBall (0 : Ambient d) eta)).toReal ≤
        (mu (unitBall d)).toReal := by
    have h_div_ne_top : mu (unitBall d) / 6 ≠ ⊤ :=
      ENNReal.div_ne_top hB_ne_top (by norm_num)
    have hle := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨h_div_ne_top, hE_ne_top⟩)
      hB_ne_top).mpr h_union_le
    simpa [ENNReal.toReal_add h_div_ne_top hE_ne_top, ENNReal.toReal_div] using hle
  linarith

private lemma normalized_ball_measure_props {d : ℕ} {eta : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    let S : Set (Ambient d) := Metric.closedBall (0 : Ambient d) eta
    let mu : Measure (Ambient d) := (volume S)⁻¹ • volume.restrict S
    IsProbabilityMeasure mu ∧
    mu.AbsolutelyContinuous (volume : Measure (Ambient d)) ∧
    0 < mu (unitBall d) ∧
    mu (unitBall d) < ⊤ ∧
    5 * mu (unitBall d) < 6 * mu S := by
  intro S mu
  have hS_pos : 0 < volume S :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self heta0⟩)
      (measure_mono Metric.ball_subset_closedBall)
  have hS_top : volume S < ⊤ := (isCompact_closedBall (0 : Ambient d) eta).measure_lt_top
  have hS_ne_zero : volume S ≠ 0 := hS_pos.ne'
  have hS_ne_top : volume S ≠ ⊤ := hS_top.ne
  have hmu_univ : mu Set.univ = 1 := by
    simp [mu, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hS_ne_zero hS_ne_top]
  have hmu_prob : IsProbabilityMeasure mu := ⟨hmu_univ⟩
  have hmu_ac : mu.AbsolutelyContinuous volume := fun s hs => by
    have h0 : volume.restrict S s = 0 :=
      nonpos_iff_eq_zero.mp ((Measure.restrict_le_self s).trans hs.le)
    simp [mu, Measure.smul_apply, h0]
  have hmu_S : mu S = 1 := by
    simp [mu, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self,
      ENNReal.inv_mul_cancel hS_ne_zero hS_ne_top]
  have hS_sub_ball : S ⊆ unitBall d := Metric.closedBall_subset_closedBall heta1.le
  have hmu_ball : mu (unitBall d) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hmu_univ]
      exact measure_mono (Set.subset_univ _)
    · rw [← hmu_S]
      exact measure_mono hS_sub_ball
  refine ⟨hmu_prob, hmu_ac, ?_, ?_, ?_⟩
  · simp [hmu_ball]
  · simp [hmu_ball]
  · rw [hmu_ball, hmu_S]
    norm_num

/-- **General convex equipartition transfer**: given any almost six-embedding
`g : Δ^(m-1) → ℝ^(d-2)` and `m` central blocking markers `p` (`IsBlocking p`) in dimension `d ≥ 2`,
uses `exists_eta_of_isBlocking` (Lemma 5.2 / Blaschke compactness) to obtain `eta ∈ (0, 1)`,
constructs `d - 1` continuous functionals `Phi` and an absolutely continuous probability
measure `mu` (working uniformly for every `eta`-concentrated absolutely continuous measure)
such that no fair convex six-partition equalizes `Phi`. -/
theorem convex_partition_of_embedding_and_blocking {d m : ℕ} (hd : 2 ≤ d)
    {g : (Fin m → ℝ) → (Fin (d - 2) → ℝ)} (hg : IsAlmostSixEmbedding g)
    {p : Fin m → Ambient d} (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  have hd_pos : 0 < d := by omega
  obtain ⟨eta, heta0, heta1, heta_block⟩ := exists_eta_of_isBlocking hd_pos hp
  let w : Body d → Fin m → ℝ := fun C a => inwardDist (p a) C
  let s : Body d → ℝ := fun C => ∑ a, w C a
  let Phi : Body d → (Fin (d - 1) → ℝ) := fun C k =>
    if _hk : k.1 = 0 then s C
    else
      if s C = 0 then 0
      else s C * g (fun a => w C a / s C) ⟨k.1 - 1, by have := k.isLt; omega⟩
  have hw_nonneg : ∀ C a, 0 ≤ w C a := fun _ _ => Metric.infDist_nonneg
  have hs_nonneg : ∀ C, 0 ≤ s C := fun C => Finset.sum_nonneg fun a _ => hw_nonneg C a
  have hs_cont : Continuous s :=
    continuous_finsetSum _ fun a _ => continuous_inwardDist hd_pos (p a)
  have h_simplex_of_pos : ∀ C, s C ≠ 0 → (fun a => w C a / s C) ∈ simplex m := by
    intro C hsC
    refine ⟨fun a => div_nonneg (hw_nonneg C a) (hs_nonneg C), ?_⟩
    rw [← Finset.sum_div]
    exact div_self hsC
  have hPhi_cont : Continuous Phi := by
    refine continuous_pi fun k => ?_
    by_cases hk : k.1 = 0
    · simpa [Phi, hk] using hs_cont
    · have hfun :
          (fun C : Body d => Phi C k) = fun C =>
            let s' := ∑ a, w C a
            if s' = 0 then 0 else s' * g (fun a => w C a / s') ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
        funext fun C => by simp [Phi, hk, s]
      rw [hfun]
      exact continuousOn_univ.mp <| continuousOn_perspective
        (fun a => (continuous_inwardDist hd_pos (p a)).continuousOn)
        (fun C _ a => hw_nonneg C a) hg.1 ⟨k.1 - 1, by have := k.isLt; omega⟩
  have hPhi_obstruct :
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, ((C i : Set (Ambient d)) ∩ Metric.closedBall (0 : Ambient d) eta).Nonempty) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
    intro C hC hmeet
    by_contra h_all
    push Not at h_all
    have hs_eq : ∀ i, s (C i) = s (C 0) := fun i => by
      have h0 := congrFun (h_all i) ⟨0, by omega⟩
      simpa [Phi] using h0
    by_cases hs0 : s (C 0) = 0
    · have hno_int : ∀ i a, p a ∉ interior (C i : Set (Ambient d)) := fun i a hmem => by
        have hpos_w : 0 < w (C i) a := (inwardDist_pos_iff hd_pos (p a) (C i)).mpr hmem
        have hsum0 : s (C i) = 0 := (hs_eq i).trans hs0
        have hw0 : w (C i) a = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hw_nonneg (C i) b) |>.mp hsum0 a
            (Finset.mem_univ a)
        linarith
      obtain ⟨i, a, ha⟩ := heta_block C hC fun i => by
        obtain ⟨y, hyC, hyeta⟩ := hmeet i
        exact ⟨y, hyC, by simpa [Metric.mem_closedBall, dist_zero_right] using hyeta⟩
      exact hno_int i a ha
    · have hsi_ne : ∀ i, s (C i) ≠ 0 := fun i => (hs_eq i).symm ▸ hs0
      let x : Fin 6 → Fin m → ℝ := fun i a => w (C i) a / s (C i)
      have hx_mem : ∀ i, x i ∈ simplex m :=
        fun i => h_simplex_of_pos (C i) (hsi_ne i)
      have hx_disj : DisjointSupports x := by
        intro i j hij a
        by_contra h_both
        push Not at h_both
        have hwi : 0 < w (C i) a := by
          have hle := hw_nonneg (C i) a
          by_contra hle0
          have heq0 : w (C i) a = 0 := le_antisymm (not_lt.mp hle0) hle
          exact h_both.1 (by simp [x, heq0])
        have hwj : 0 < w (C j) a := by
          have hle := hw_nonneg (C j) a
          by_contra hle0
          have heq0 : w (C j) a = 0 := le_antisymm (not_lt.mp hle0) hle
          exact h_both.2 (by simp [x, heq0])
        have hi_int : p a ∈ interior (C i : Set (Ambient d)) :=
          (inwardDist_pos_iff hd_pos (p a) (C i)).mp hwi
        have hj_int : p a ∈ interior (C j : Set (Ambient d)) :=
          (inwardDist_pos_iff hd_pos (p a) (C j)).mp hwj
        exact Set.disjoint_left.mp (hC.2.2 i j hij) hi_int hj_int
      obtain ⟨i, hi_ne⟩ := hg.2 x hx_mem hx_disj
      apply hi_ne
      funext j
      let k : Fin (d - 1) := ⟨j.1 + 1, by have := j.isLt; omega⟩
      have hk0 : k.1 ≠ 0 := by simp [k]
      have hcon := congrFun (h_all i) k
      simp only [Phi, hk0, ↓reduceDIte, hs_eq i, hs0, ↓reduceIte, k] at hcon
      have hksub : (⟨j.1 + 1 - 1, by have := j.isLt; omega⟩ : Fin (d - 2)) = j := by
        ext; simp
      rw [hksub] at hcon
      have hmul : s (C 0) * g (x i) j = s (C 0) * g (x 0) j := by
        simpa [x, hs_eq i] using hcon
      exact mul_left_cancel₀ hs0 hmul
  have h_unif :
      ∀ mu : Measure (Ambient d),
        mu.AbsolutelyContinuous (volume : Measure (Ambient d)) →
        0 < mu (unitBall d) →
        mu (unitBall d) < ⊤ →
        5 * mu (unitBall d) < 6 * mu (Metric.closedBall (0 : Ambient d) eta) →
        ∀ C : Fin 6 → Body d,
          IsSixPartition C →
          (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
          ∃ i, Phi (C i) ≠ Phi (C 0) := by
    intro mu _ hpos htop hconc C hC hfair
    exact hPhi_obstruct C hC (fair_meets_eta_ball heta1 hpos htop hconc hC hfair)
  obtain ⟨hprob, hac, hpos, htop, hconc⟩ :=
    normalized_ball_measure_props (d := d) heta0 heta1
  exact ⟨Phi, _, hPhi_cont, hprob, hac,
    fun C hC hfair => h_unif _ hac hpos htop hconc C hC hfair⟩

/-! ### Helper 4: Central separating normals, Lemma 4.2, RREF, and generic blocking points -/

private def nonEmptyIntParts {d : ℕ} (C : Fin 6 → Body d) : Finset (Fin 6) := by
  classical exact Finset.univ.filter fun i => (interior (C i : Set (Ambient d))).Nonempty

private lemma mem_nonEmptyIntParts {d : ℕ} (C : Fin 6 → Body d) {i : Fin 6} :
    i ∈ nonEmptyIntParts C ↔ (interior (C i : Set (Ambient d))).Nonempty := by
  classical
  simp [nonEmptyIntParts]

private lemma open_subset_biUnion_closed_empty_interior {E : Type*} [TopologicalSpace E]
    {ι : Type*} [DecidableEq ι] (T : Finset ι) {f : ι → Set E}
    (hclosed : ∀ i ∈ T, IsClosed (f i))
    (hempty : ∀ i ∈ T, interior (f i) = ∅)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ ⋃ i ∈ T, f i) : U = ∅ := by
  induction T using Finset.induction_on generalizing U with
  | empty =>
    simpa only [Finset.notMem_empty, Set.iUnion_false, Set.iUnion_empty, Set.subset_empty_iff]
      using hsub
  | @insert i₀ T' _ ih =>
    have hclosed_T' : ∀ i ∈ T', IsClosed (f i) :=
      fun i hi => hclosed i (Finset.mem_insert_of_mem hi)
    have hempty_T' : ∀ i ∈ T', interior (f i) = ∅ :=
      fun i hi => hempty i (Finset.mem_insert_of_mem hi)
    have hU_sdiff : IsOpen (U \ f i₀) :=
      hU.sdiff (hclosed i₀ (Finset.mem_insert_self i₀ T'))
    have hsub_sdiff : U \ f i₀ ⊆ ⋃ i ∈ T', f i := by
      rintro x ⟨hxU, hxnot⟩
      have hx' := hsub hxU
      simp only [Set.mem_iUnion, Finset.mem_insert] at hx' ⊢
      rcases hx' with ⟨i, rfl | hi', hxi⟩
      · exact False.elim (hxnot hxi)
      · exact ⟨i, hi', hxi⟩
    have hdiff_empty : U \ f i₀ = ∅ := ih hclosed_T' hempty_T' hU_sdiff hsub_sdiff
    have hU_sub : U ⊆ f i₀ := Set.sdiff_eq_empty.mp hdiff_empty
    have hU_sub_int : U ⊆ interior (f i₀) := interior_maximal hU_sub hU
    rw [hempty i₀ (Finset.mem_insert_self i₀ T'), Set.subset_empty_iff] at hU_sub_int
    exact hU_sub_int

private lemma unitBall_subset_biUnion_nonempty_interior {d : ℕ}
    (C : Fin 6 → Body d) (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d)))) :
    unitBall d ⊆ ⋃ i ∈ nonEmptyIntParts C, (C i : Set (Ambient d)) := by
  classical
  let S := nonEmptyIntParts C
  let U : Set (Ambient d) :=
    Metric.ball (0 : Ambient d) 1 \ ⋃ i ∈ S, (C i : Set (Ambient d))
  have hS_closed : IsClosed (⋃ i ∈ S, (C i : Set (Ambient d))) :=
    isClosed_biUnion_finset fun i _ => (C i).isClosed
  have hU_open : IsOpen U := Metric.isOpen_ball.sdiff hS_closed
  let T : Finset (Fin 6) := Finset.univ \ S
  have hU_sub : U ⊆ ⋃ i ∈ T, (C i : Set (Ambient d)) := by
    rintro x ⟨hx_ball, hx_notS⟩
    have hx_unit : x ∈ unitBall d := Metric.ball_subset_closedBall hx_ball
    rw [hcov, Set.mem_iUnion] at hx_unit
    obtain ⟨i, hxi⟩ := hx_unit
    have hi_notS : i ∉ S := fun hiS =>
      hx_notS (Set.mem_iUnion₂.mpr ⟨i, hiS, hxi⟩)
    have hiT : i ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi_notS⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hiT, hxi⟩
  have hU_empty : U = ∅ :=
    open_subset_biUnion_closed_empty_interior T
      (fun i _ => (C i).isClosed)
      (fun i hi => by
        have hi_notS : i ∉ S := (Finset.mem_sdiff.mp hi).2
        rw [mem_nonEmptyIntParts] at hi_notS
        exact Set.not_nonempty_iff_eq_empty.mp hi_notS)
      hU_open hU_sub
  have hball_sub : Metric.ball (0 : Ambient d) 1 ⊆ ⋃ i ∈ S, (C i : Set (Ambient d)) :=
    Set.sdiff_eq_empty.mp hU_empty
  have hcl := closure_mono hball_sub
  rw [closure_ball (0 : Ambient d) one_ne_zero, hS_closed.closure_eq] at hcl
  exact hcl

private lemma exists_central_separating_normals {d : ℕ}
    (C : Fin 6 → Body d)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (interior (C i : Set (Ambient d)))
               (interior (C j : Set (Ambient d))))
    (h0 : ∀ i, (0 : Ambient d) ∈ (C i : Set (Ambient d))) :
    ∃ n : Fin 6 → Fin 6 → Ambient d,
      (∀ i, n i i = 0) ∧
      (∀ i j, n j i = - n i j) ∧
      (∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0) ∧
      (∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
        n i j ≠ 0 ∧
        (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
        (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ) ∧
        (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0) ∧
        (∀ x ∈ interior (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ < 0)) := by
  let S := nonEmptyIntParts C
  have h_pair_lt : ∀ i j : Fin 6, i ∈ S → j ∈ S → i < j →
      ∃ v : Ambient d, v ≠ 0 ∧
        (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪v, y⟫_ℝ) ∧
        (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪v, y⟫_ℝ) ∧
        (∀ x ∈ (C j : Set (Ambient d)), ⟪v, x⟫_ℝ ≤ 0) ∧
        (∀ x ∈ interior (C j : Set (Ambient d)), ⟪v, x⟫_ℝ < 0) := by
    intro i j hiS hjS hij
    have hi_ne : (interior (C i : Set (Ambient d))).Nonempty := (mem_nonEmptyIntParts C).mp hiS
    have hj_ne : (interior (C j : Set (Ambient d))).Nonempty := (mem_nonEmptyIntParts C).mp hjS
    obtain ⟨f, u, hf_lt, hf_gt⟩ := geometric_hahn_banach_open_open
      (C j).convex.interior isOpen_interior (C i).convex.interior isOpen_interior
      (hdisj j i hij.ne')
    let v : Ambient d := (InnerProductSpace.toDual ℝ (Ambient d)).symm f
    have hv_eq : ∀ z, ⟪v, z⟫_ℝ = f z := fun z => InnerProductSpace.toDual_symm_apply
    have hCi_cl : closure (interior (C i : Set (Ambient d))) = (C i : Set (Ambient d)) :=
      ((C i).convex.closure_interior_eq_closure_of_nonempty_interior hi_ne).trans
        (C i).isClosed.closure_eq
    have hCj_cl : closure (interior (C j : Set (Ambient d))) = (C j : Set (Ambient d)) :=
      ((C j).convex.closure_interior_eq_closure_of_nonempty_interior hj_ne).trans
        (C j).isClosed.closure_eq
    have h_le_Ci : ∀ y ∈ (C i : Set (Ambient d)), u ≤ f y := by
      have hsub : interior (C i : Set (Ambient d)) ⊆ {y | u ≤ f y} :=
        fun y hy => (hf_gt y hy).le
      have hclosed : IsClosed {y : Ambient d | u ≤ f y} :=
        isClosed_le continuous_const f.continuous
      intro y hy
      rw [← hCi_cl] at hy
      exact hclosed.closure_subset_iff.mpr hsub hy
    have h_le_Cj : ∀ x ∈ (C j : Set (Ambient d)), f x ≤ u := by
      have hsub : interior (C j : Set (Ambient d)) ⊆ {x | f x ≤ u} :=
        fun x hx => (hf_lt x hx).le
      have hclosed : IsClosed {x : Ambient d | f x ≤ u} :=
        isClosed_le f.continuous continuous_const
      intro x hx
      rw [← hCj_cl] at hx
      exact hclosed.closure_subset_iff.mpr hsub hx
    have hu0 : u = 0 := by
      have h0i := h_le_Ci 0 (h0 i)
      have h0j := h_le_Cj 0 (h0 j)
      rw [map_zero] at h0i h0j
      linarith
    subst hu0
    obtain ⟨y₀, hy₀⟩ := hi_ne
    have hv_ne : v ≠ 0 := by
      intro hv0
      have := hf_gt y₀ hy₀
      rw [← hv_eq, hv0, inner_zero_left] at this
      exact lt_irrefl 0 this
    refine ⟨v, hv_ne, ?_, ?_, ?_, ?_⟩
    · intro y hy; rw [hv_eq]; exact h_le_Ci y hy
    · intro y hy; rw [hv_eq]; exact hf_gt y hy
    · intro x hx; rw [hv_eq]; exact h_le_Cj x hx
    · intro x hx; rw [hv_eq]; exact hf_lt x hx
  classical
  let n_lt : Fin 6 → Fin 6 → Ambient d := fun i j =>
    if h : i ∈ S ∧ j ∈ S ∧ i < j then
      Classical.choose (h_pair_lt i j h.1 h.2.1 h.2.2)
    else 0
  let n : Fin 6 → Fin 6 → Ambient d := fun i j =>
    if i < j then n_lt i j else if j < i then - n_lt j i else 0
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [n]
  · intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hnot : ¬ (j < i) := hij.not_gt
      simp [n, hij, hnot]
    · simp [n]
    · have hnot : ¬ (i < j) := hij.not_gt
      simp [n, hij, hnot]
  · intro i j hij
    have hn_lt : ∀ a b, a ∉ S ∨ b ∉ S → n_lt a b = 0 := fun a b hab => by
      dsimp [n_lt]
      split_ifs with h
      · exact absurd h.1 (hab.elim id fun hb' => absurd h.2.1 hb')
      · rfl
    rcases lt_trichotomy i j with hij' | rfl | hij'
    · simp [n, hij', hn_lt i j hij]
    · simp [n]
    · have hji : ¬ (i < j) := hij'.not_gt
      simp [n, hij', hji, hn_lt j i hij.symm]
  · intro i hiS j hjS hij_ne
    rcases lt_or_gt_of_ne hij_ne with hij | hij
    · have hspec := Classical.choose_spec (h_pair_lt i j hiS hjS hij)
      have hn_eq : n i j = n_lt i j := by simp [n, hij]
      have hn_lt_eq : n_lt i j = Classical.choose (h_pair_lt i j hiS hjS hij) := by
        dsimp [n_lt]
        split_ifs with h'
        · rfl
        · exact False.elim (h' ⟨hiS, hjS, hij⟩)
      simpa [hn_eq, hn_lt_eq] using hspec
    · have hspec := Classical.choose_spec (h_pair_lt j i hjS hiS hij)
      have hn_eq : n i j = - n_lt j i := by simp [n, hij, hij.not_gt]
      have hn_lt_eq : n_lt j i = Classical.choose (h_pair_lt j i hjS hiS hij) := by
        dsimp [n_lt]
        split_ifs with h'
        · rfl
        · exact False.elim (h' ⟨hjS, hiS, hij⟩)
      rw [hn_eq, hn_lt_eq]
      rcases hspec with ⟨hv_ne, hCj, hCj_int, hCi, hCi_int⟩
      refine ⟨neg_ne_zero.mpr hv_ne, ?_, ?_, ?_, ?_⟩
      · intro y hy; rw [inner_neg_left]; linarith [hCi y hy]
      · intro y hy; rw [inner_neg_left]; linarith [hCi_int y hy]
      · intro x hx; rw [inner_neg_left]; linarith [hCj x hx]
      · intro x hx; rw [inner_neg_left]; linarith [hCj_int x hx]

private lemma skeleton_in_separating_hyperplanes {d : ℕ}
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hsym : ∀ i j, n j i = - n i j)
    {x : Ambient d} (hx_ball : x ∈ Metric.ball (0 : Ambient d) 1)
    (hx_not_int : ∀ i : Fin 6, x ∉ interior (C i : Set (Ambient d))) :
    ∃ i ∈ nonEmptyIntParts C, ∃ j ∈ nonEmptyIntParts C, i < j ∧ ⟪n i j, x⟫_ℝ = 0 := by
  classical
  let S := nonEmptyIntParts C
  have hS_cov := unitBall_subset_biUnion_nonempty_interior C hcov
  have hx_S : x ∈ ⋃ i ∈ S, (C i : Set (Ambient d)) :=
    hS_cov (Metric.ball_subset_closedBall hx_ball)
  rw [Set.mem_iUnion₂] at hx_S
  obtain ⟨i, hiS, hxi⟩ := hx_S
  have hex_j : ∃ j ∈ S, j ≠ i ∧ ⟪n i j, x⟫_ℝ = 0 := by
    by_contra h_none
    push Not at h_none
    have hpos_j : ∀ j ∈ S.erase i, 0 < ⟪n i j, x⟫_ℝ := by
      intro j hj
      have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hle : 0 ≤ ⟪n i j, x⟫_ℝ := (hsep i hiS j hjS hji.symm).1 x hxi
      exact lt_of_le_of_ne hle (Ne.symm (h_none j hjS hji))
    let U : Set (Ambient d) :=
      Metric.ball (0 : Ambient d) 1 ∩ ⋂ j ∈ S.erase i, {y : Ambient d | 0 < ⟪n i j, y⟫_ℝ}
    have hU_open : IsOpen U :=
      Metric.isOpen_ball.inter <| isOpen_biInter_finset fun j _ =>
        isOpen_lt continuous_const (continuous_const.inner continuous_id)
    have hxU : x ∈ U := ⟨hx_ball, Set.mem_iInter₂.mpr hpos_j⟩
    have hU_sub : U ⊆ (C i : Set (Ambient d)) := by
      intro y hyU
      have hy_S : y ∈ ⋃ k ∈ S, (C k : Set (Ambient d)) :=
        hS_cov (Metric.ball_subset_closedBall hyU.1)
      rw [Set.mem_iUnion₂] at hy_S
      obtain ⟨k, hkS, hyk⟩ := hy_S
      by_cases hki : k = i
      · exact hki ▸ hyk
      · have hk_er : k ∈ S.erase i := Finset.mem_erase.mpr ⟨hki, hkS⟩
        have hpos : 0 < ⟪n i k, y⟫_ℝ := Set.mem_iInter₂.mp hyU.2 k hk_er
        have hle : ⟪n i k, y⟫_ℝ ≤ 0 := (hsep i hiS k hkS (Ne.symm hki)).2 y hyk
        exact False.elim (not_lt_of_ge hle hpos)
    exact hx_not_int i (interior_maximal hU_sub hU_open hxU)
  obtain ⟨j, hjS, hji, hzero⟩ := hex_j
  rcases lt_or_gt_of_ne hji with hij | hij
  · refine ⟨j, hjS, i, hiS, hij, ?_⟩
    rw [hsym, inner_neg_left, hzero, neg_zero]
  · exact ⟨i, hiS, j, hjS, hij, hzero⟩

/-- **Lemma 4.2 (Normal rank ≤ 5)**: for separating normals `n` of a central six-partition,
the vectors `a i = ∑ j, n i j` annihilate the same vectors as all `n i j`. -/
private lemma central_partition_normal_rank {d : ℕ}
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ))
    (hsym : ∀ i j, n j i = - n i j)
    {v : Ambient d}
    (hv : ∀ i : Fin 6, ⟪∑ j : Fin 6, n i j, v⟫_ℝ = 0) :
    ∀ i j : Fin 6, ⟪n i j, v⟫_ℝ = 0 := by
  classical
  let S := nonEmptyIntParts C
  have hS_cov := unitBall_subset_biUnion_nonempty_interior C hcov
  let Sv : Finset (Fin 6) := S.filter fun i => ∀ j ∈ S, 0 ≤ ⟪n i j, v⟫_ℝ
  have hSv_zero : ∀ i ∈ Sv, ∀ j : Fin 6, ⟪n i j, v⟫_ℝ = 0 := by
    intro i hiSv
    have hiS : i ∈ S := (Finset.mem_filter.mp hiSv).1
    have hnonneg_S : ∀ j ∈ S, 0 ≤ ⟪n i j, v⟫_ℝ := (Finset.mem_filter.mp hiSv).2
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 6)), 0 ≤ ⟪n i j, v⟫_ℝ := by
      intro j _
      by_cases hjS : j ∈ S
      · exact hnonneg_S j hjS
      · simp [hnotS i j (Or.inr hjS)]
    have hsum0 : ∑ j : Fin 6, ⟪n i j, v⟫_ℝ = 0 := by
      simpa only [sum_inner] using hv i
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 j (Finset.mem_univ j)
  have hzero_diag : ∀ i : Fin 6, n i i = 0 := fun i => by
    have hadd : n i i + n i i = 0 := by
      conv_lhs => rhs; rw [hsym i i]
      exact add_neg_cancel _
    have h2 : (2 : ℝ) • n i i = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hSv_ne : Sv.Nonempty := by
    let α : ℝ := (‖v‖ + 1)⁻¹
    have hα_pos : 0 < α := inv_pos.mpr (by positivity)
    let w : Ambient d := α • v
    have hw_ball : w ∈ unitBall d := by
      change dist (α • v) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hα_pos.le]
      dsimp [α]
      rw [inv_mul_le_one₀ (by positivity)]
      linarith
    have hw_S : w ∈ ⋃ i ∈ S, (C i : Set (Ambient d)) := hS_cov hw_ball
    rw [Set.mem_iUnion₂] at hw_S
    obtain ⟨i, hiS, hwi⟩ := hw_S
    refine ⟨i, Finset.mem_filter.mpr ⟨hiS, fun j hjS => ?_⟩⟩
    by_cases hij : i = j
    · subst hij
      rw [hzero_diag i, inner_zero_left]
    · have hnonneg_w : 0 ≤ ⟪n i j, w⟫_ℝ := (hsep i hiS j hjS hij).1 w hwi
      dsimp [w] at hnonneg_w
      rw [real_inner_smul_right] at hnonneg_w
      exact nonneg_of_mul_nonneg_right hnonneg_w hα_pos
  have hS_sub_Sv : S ⊆ Sv := by
    by_contra hnot_sub
    obtain ⟨k, hkS, hk_not_Sv⟩ := Finset.not_subset.mp hnot_sub
    have hk_ne : (interior (C k : Set (Ambient d))).Nonempty := (mem_nonEmptyIntParts C).mp hkS
    obtain ⟨x, hx_int⟩ := hk_ne
    have hex_neg : ∀ i ∈ S \ Sv, ∃ j ∈ S, ⟪n i j, v⟫_ℝ < 0 := by
      intro i hi
      obtain ⟨hiS, hi_not_Sv⟩ := Finset.mem_sdiff.mp hi
      have hnot : ¬ ∀ j ∈ S, 0 ≤ ⟪n i j, v⟫_ℝ := fun h =>
        hi_not_Sv (Finset.mem_filter.mpr ⟨hiS, h⟩)
      push Not at hnot
      exact hnot
    choose jOf hjOf_mem hjOf_neg using hex_neg
    let t : ℝ :=
      1 + ∑ i ∈ S \ Sv,
        if hi : i ∈ S \ Sv then |⟪n i (jOf i hi), x⟫_ℝ| / (-⟪n i (jOf i hi), v⟫_ℝ) else 0
    have hterm_nonneg : ∀ i ∈ S \ Sv,
        0 ≤ (if hi : i ∈ S \ Sv then |⟪n i (jOf i hi), x⟫_ℝ| / (-⟪n i (jOf i hi), v⟫_ℝ) else 0) := by
      intro i hi
      simp only [hi, ↓reduceDIte]
      exact div_nonneg (abs_nonneg _) (by linarith [hjOf_neg i hi])
    have ht_pos : 0 < t := by
      have hsum_nn := Finset.sum_nonneg hterm_nonneg
      dsimp [t]
      linarith
    let y : Ambient d := x + t • v
    let β : ℝ := (‖y‖ + 1)⁻¹
    have hβ_pos : 0 < β := inv_pos.mpr (by positivity)
    let z : Ambient d := β • y
    have hz_ball : z ∈ unitBall d := by
      change dist (β • y) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hβ_pos.le]
      dsimp [β]
      rw [inv_mul_le_one₀ (by positivity)]
      linarith
    have hz_S : z ∈ ⋃ m ∈ S, (C m : Set (Ambient d)) := hS_cov hz_ball
    rw [Set.mem_iUnion₂] at hz_S
    obtain ⟨m, hmS, hzm⟩ := hz_S
    have hy_nonneg : ∀ j ∈ S, m ≠ j → 0 ≤ ⟪n m j, y⟫_ℝ := by
      intro j hjS hmj
      have hzw : 0 ≤ ⟪n m j, z⟫_ℝ := (hsep m hmS j hjS hmj).1 z hzm
      dsimp [z] at hzw
      rw [real_inner_smul_right] at hzw
      exact nonneg_of_mul_nonneg_right hzw hβ_pos
    by_cases hmSv : m ∈ Sv
    · have hmk_ne : m ≠ k := fun h => hk_not_Sv (h ▸ hmSv)
      have hy_mk : 0 ≤ ⟪n m k, y⟫_ℝ := hy_nonneg k hkS hmk_ne
      have hv_mk : ⟪n m k, v⟫_ℝ = 0 := hSv_zero m hmSv k
      have hx_km : 0 < ⟪n k m, x⟫_ℝ := (hsep k hkS m hmS hmk_ne.symm).2 x hx_int
      have hx_mk : ⟪n m k, x⟫_ℝ < 0 := by
        rw [hsym k m, inner_neg_left]
        linarith
      dsimp [y] at hy_mk
      rw [inner_add_right, real_inner_smul_right, hv_mk, mul_zero, add_zero] at hy_mk
      linarith
    · have hm_sdiff : m ∈ S \ Sv := Finset.mem_sdiff.mpr ⟨hmS, hmSv⟩
      let j : Fin 6 := jOf m hm_sdiff
      have hjS : j ∈ S := hjOf_mem m hm_sdiff
      have hv_mj : ⟪n m j, v⟫_ℝ < 0 := hjOf_neg m hm_sdiff
      have hmj_ne : m ≠ j := by
        intro hmj
        have hm0 : ⟪n m m, v⟫_ℝ = 0 := by rw [hzero_diag m, inner_zero_left]
        rw [← hmj, hm0] at hv_mj
        exact lt_irrefl 0 hv_mj
      have hy_mj : 0 ≤ ⟪n m j, y⟫_ℝ := hy_nonneg j hjS hmj_ne
      have hsingle :
          |⟪n m j, x⟫_ℝ| / (-⟪n m j, v⟫_ℝ) ≤
            ∑ i ∈ S \ Sv,
              if hi : i ∈ S \ Sv then |⟪n i (jOf i hi), x⟫_ℝ| / (-⟪n i (jOf i hi), v⟫_ℝ) else 0 := by
        have hle := Finset.single_le_sum hterm_nonneg hm_sdiff
        simpa [hm_sdiff, j] using hle
      have hb_pos : 0 < -⟪n m j, v⟫_ℝ := by linarith
      have ht_gt : |⟪n m j, x⟫_ℝ| / (-⟪n m j, v⟫_ℝ) < t := by
        dsimp [t]
        linarith
      have hmul_gt : |⟪n m j, x⟫_ℝ| < t * (-⟪n m j, v⟫_ℝ) :=
        (div_lt_iff₀ hb_pos).mp ht_gt
      have h_le_abs : ⟪n m j, x⟫_ℝ ≤ |⟪n m j, x⟫_ℝ| := le_abs_self _
      dsimp [y] at hy_mj
      rw [inner_add_right, real_inner_smul_right] at hy_mj
      linarith
  intro i j
  by_cases hiS : i ∈ S
  · exact hSv_zero i (hS_sub_Sv hiS) j
  · simp [hnotS i j (Or.inl hiS)]

/-- Gaussian elimination to Reduced Row Echelon Form (RREF) for any tuple of `k ≤ d` vectors. -/
private lemma exists_rref {d : ℕ} (k : ℕ) (hk : k ≤ d) (A : Fin k → Ambient d) :
    ∃ (I : Fin k → Fin d) (u : Fin k → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin k, u r (I s) = if r = s then 1 else 0) ∧
      (∀ t : Fin k, A t ∈ Submodule.span ℝ (Set.range u)) := by
  induction k with
  | zero =>
    exact ⟨finZeroElim, finZeroElim, Function.injective_of_subsingleton _,
      fun r => r.elim0, fun t => t.elim0⟩
  | succ k ih =>
    let A' : Fin k → Ambient d := fun t => A t.castSucc
    obtain ⟨I', u', hI'_inj, hu'_rref, hA'_span⟩ := ih (by omega : k ≤ d) A'
    let w : Ambient d := A (Fin.last k)
    let w' : Ambient d := w - ∑ r : Fin k, (w (I' r)) • u' r
    have hw'_piv : ∀ s : Fin k, w' (I' s) = 0 := fun s => by
      have h1 : (∑ r : Fin k, (w (I' r)) • u' r) (I' s) =
          ∑ r : Fin k, w (I' r) * u' r (I' s) := by
        simp [Finset.sum_apply, smul_eq_mul]
      change w (I' s) - (∑ r : Fin k, (w (I' r)) • u' r) (I' s) = 0
      rw [h1]
      have h2 : ∑ r : Fin k, w (I' r) * u' r (I' s) = w (I' s) := by
        simp [hu'_rref]
      linarith
    have hex_step : ∃ (j₀ : Fin d) (u_new : Ambient d),
        (∀ s : Fin k, I' s ≠ j₀) ∧
        u_new j₀ = 1 ∧
        (∀ s : Fin k, u_new (I' s) = 0) ∧
        w' ∈ Submodule.span ℝ ({u_new} : Set (Ambient d)) := by
      by_cases hw'0 : w' = 0
      · have hnot_sub : ¬ Finset.univ ⊆ Finset.univ.image I' := by
          intro hsub
          have hcard := Finset.card_le_card hsub
          have hcard_img : (Finset.univ.image I').card ≤ k :=
            Finset.card_image_le.trans (by simp)
          rw [Finset.card_univ, Fintype.card_fin] at hcard
          omega
        obtain ⟨j₀, _, hj₀_not⟩ := Finset.not_subset.mp hnot_sub
        have hj₀_ne : ∀ s : Fin k, I' s ≠ j₀ := fun s h =>
          hj₀_not (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, h⟩)
        let u_new : Ambient d := EuclideanSpace.single j₀ (1 : ℝ)
        refine ⟨j₀, u_new, hj₀_ne, ?_, ?_, ?_⟩
        · simp [u_new, EuclideanSpace.single]
        · intro s
          simp [u_new, EuclideanSpace.single, (hj₀_ne s).symm]
        · rw [hw'0]
          exact Submodule.zero_mem _
      · have hex_j : ∃ j₀ : Fin d, w' j₀ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hw'0 (PiLp.ext hall)
        obtain ⟨j₀, hj₀_ne0⟩ := hex_j
        have hj₀_ne : ∀ s : Fin k, I' s ≠ j₀ := fun s h => by
          rw [← h] at hj₀_ne0
          exact hj₀_ne0 (hw'_piv s)
        let u_new : Ambient d := (w' j₀)⁻¹ • w'
        refine ⟨j₀, u_new, hj₀_ne, ?_, ?_, ?_⟩
        · change (w' j₀)⁻¹ * w' j₀ = 1
          exact inv_mul_cancel₀ hj₀_ne0
        · intro s
          change (w' j₀)⁻¹ * w' (I' s) = 0
          rw [hw'_piv s, mul_zero]
        · have hw'_eq : w' = (w' j₀) • u_new := by
            dsimp [u_new]
            rw [smul_smul, mul_inv_cancel₀ hj₀_ne0, one_smul]
          rw [hw'_eq]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u_new))
    obtain ⟨j₀, u_new, hj₀_ne, hu_new_j0, hu_new_piv, hw'_span⟩ := hex_step
    let I : Fin (k + 1) → Fin d := Fin.snoc I' j₀
    let u : Fin (k + 1) → Ambient d :=
      Fin.snoc (fun r : Fin k => u' r - (u' r j₀) • u_new) u_new
    refine ⟨I, u, ?_, ?_, ?_⟩
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · have hab' : I' a' = I' b' := by simpa [I] using hab
        exact congrArg Fin.castSucc (hI'_inj hab')
      · have hab' : I' a' = j₀ := by simpa [I] using hab
        exact False.elim (hj₀_ne a' hab')
      · have hab' : j₀ = I' b' := by simpa [I] using hab
        exact False.elim (hj₀_ne b' hab'.symm)
      · rfl
    · intro r s
      refine Fin.lastCases ?_ (fun r' => ?_) r <;>
        refine Fin.lastCases ?_ (fun s' => ?_) s
      · simp [I, u, hu_new_j0]
      · have hne : Fin.last k ≠ s'.castSucc := (Fin.castSucc_lt_last s').ne'
        change u (Fin.last k) (I s'.castSucc) = if Fin.last k = s'.castSucc then 1 else 0
        simp [hne, I, u, hu_new_piv s']
      · have hne : r'.castSucc ≠ Fin.last k := (Fin.castSucc_lt_last r').ne
        change u r'.castSucc (I (Fin.last k)) = if r'.castSucc = Fin.last k then 1 else 0
        simp [hne, I, u, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hu_new_j0]
      · simp only [Fin.castSucc_inj]
        have hstep : (u' r' - (u' r' j₀) • u_new) (I' s') = if r' = s' then 1 else 0 := by
          change (u' r' (I' s')) - (u' r' j₀) * u_new (I' s') = if r' = s' then 1 else 0
          rw [hu_new_piv s', mul_zero, sub_zero, hu'_rref r' s']
        simpa [I, u] using hstep
    · have hu_new_mem : u_new ∈ Submodule.span ℝ (Set.range u) :=
        Submodule.subset_span ⟨Fin.last k, by simp [u]⟩
      have hu'_mem : ∀ r : Fin k, u' r ∈ Submodule.span ℝ (Set.range u) := fun r => by
        have hmem : u r.castSucc ∈ Submodule.span ℝ (Set.range u) :=
          Submodule.subset_span ⟨r.castSucc, rfl⟩
        have heq : u' r = u r.castSucc + (u' r j₀) • u_new := by
          simp [u]
        rw [heq]
        exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ hu_new_mem)
      have hspan_le : Submodule.span ℝ (Set.range u') ≤ Submodule.span ℝ (Set.range u) :=
        Submodule.span_le.mpr (by rintro x ⟨r, rfl⟩; exact hu'_mem r)
      have hw'_mem : w' ∈ Submodule.span ℝ (Set.range u) := by
        have hle : Submodule.span ℝ ({u_new} : Set (Ambient d)) ≤ Submodule.span ℝ (Set.range u) :=
          Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu_new_mem)
        exact hle hw'_span
      intro t
      refine Fin.lastCases ?_ (fun t' => ?_) t
      · have hw_eq : A (Fin.last k) = w' + ∑ r : Fin k, (w (I' r)) • u' r := by
          dsimp [w', w]
          abel
        rw [hw_eq]
        refine Submodule.add_mem _ hw'_mem (Submodule.sum_mem _ fun r _ => ?_)
        exact Submodule.smul_mem _ _ (hu'_mem r)
      · exact hspan_le (hA'_span t')

/-- Pairwise separating normals of a central six-partition lie in the RREF span of
the 5 row vectors `a₁, ..., a₅`. -/
private lemma separating_normals_in_rref_span {d : ℕ} (hd : 5 ≤ d)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (interior (C i : Set (Ambient d)))
               (interior (C j : Set (Ambient d))))
    (h0 : ∀ i, (0 : Ambient d) ∈ (C i : Set (Ambient d))) :
    ∃ (n : Fin 6 → Fin 6 → Ambient d) (I : Fin 5 → Fin d) (u : Fin 5 → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin 5, u r (I s) = if r = s then 1 else 0) ∧
      (∀ i, n i i = 0) ∧
      (∀ i j, n j i = - n i j) ∧
      (∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0) ∧
      (∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j → n i j ≠ 0) ∧
      (∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
        (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
        (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0)) ∧
      (∀ k l : Fin 6, ∀ j : Fin d,
        n k l j = ∑ r : Fin 5, n k l (I r) * u r j) := by
  obtain ⟨n, hnii, hnsym, hnnotS, hnsep⟩ := exists_central_separating_normals C hdisj h0
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  have ha_sum0 : ∑ i : Fin 6, a i = 0 := by
    have hneg : ∑ i : Fin 6, a i = - ∑ i : Fin 6, a i := by
      calc ∑ i : Fin 6, a i
          = ∑ i : Fin 6, ∑ j : Fin 6, n i j := rfl
        _ = ∑ j : Fin 6, ∑ i : Fin 6, n i j := Finset.sum_comm
        _ = ∑ j : Fin 6, ∑ i : Fin 6, (- n j i) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hnsym j i]
        _ = - ∑ j : Fin 6, ∑ i : Fin 6, n j i := by
          simp [Finset.sum_neg_distrib]
    have hadd : (∑ i : Fin 6, a i) + (∑ i : Fin 6, a i) = 0 := by
      conv_lhs => rhs; rw [hneg]
      exact add_neg_cancel _
    have h2 : (2 : ℝ) • (∑ i : Fin 6, a i) = 0 := by rwa [two_smul]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  let A : Fin 5 → Ambient d := fun t => a t.succ
  obtain ⟨I, u, hI_inj, hu_rref, hA_span⟩ := exists_rref 5 hd A
  have ha_span : ∀ i : Fin 6, a i ∈ Submodule.span ℝ (Set.range u) := fun i => by
    refine Fin.cases ?_ (fun t => hA_span t) i
    have ha0 : a 0 = - ∑ t : Fin 5, A t := by
      have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
        simpa only [← Fin.sum_univ_succ] using ha_sum0
      exact eq_neg_of_add_eq_zero_left hsplit
    rw [ha0]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun t _ => hA_span t)
  have hinner_single : ∀ (w : Ambient d) (j : Fin d),
      ⟪w, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = w j := fun w j => by
    rw [EuclideanSpace.inner_single_right, one_mul]
    simp
  have hspan_perp : ∀ {v : Ambient d},
      (∀ r : Fin 5, ⟪u r, v⟫_ℝ = 0) →
      ∀ i : Fin 6, ⟪a i, v⟫_ℝ = 0 := by
    intro v hv i
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (ha_span i)
    · rintro _ ⟨r, rfl⟩; exact hv r
    · simp
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx; rw [real_inner_smul_left, hx, mul_zero]
  have hcoef : ∀ k l : Fin 6, ∀ j : Fin d,
      n k l j = ∑ r : Fin 5, n k l (I r) * u r j := by
    intro k l j
    let v : Ambient d :=
      EuclideanSpace.single j (1 : ℝ) -
        ∑ r : Fin 5, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)
    have hv_u : ∀ s : Fin 5, ⟪u s, v⟫_ℝ = 0 := fun s => by
      dsimp [v]
      rw [inner_sub_right, inner_sum, hinner_single]
      have hsum : (∑ r : Fin 5, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) = u s j := by
        calc ∑ r : Fin 5, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ
            = ∑ r : Fin 5, u r j * u s (I r) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [real_inner_smul_right, hinner_single]
          _ = ∑ r : Fin 5, u r j * (if s = r then 1 else 0) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hu_rref s r]
          _ = u s j := by simp
      rw [hsum, sub_self]
    have hv_n : ⟪n k l, v⟫_ℝ = 0 :=
      central_partition_normal_rank C hcov n hnnotS
        (fun i hiS j hjS hij =>
          ⟨(hnsep i hiS j hjS hij).2.1, (hnsep i hiS j hjS hij).2.2.1⟩)
        hnsym (hspan_perp hv_u) k l
    dsimp [v] at hv_n
    rw [inner_sub_right, inner_sum, hinner_single] at hv_n
    have hsum_n :
        (∑ r : Fin 5, ⟪n k l, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) =
          ∑ r : Fin 5, n k l (I r) * u r j := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [real_inner_smul_right, hinner_single, mul_comm]
    linarith [hv_n, hsum_n]
  refine ⟨n, I, u, hI_inj, hu_rref, hnii, hnsym, hnnotS,
    (fun i hiS j hjS hij => (hnsep i hiS j hjS hij).1),
    (fun i hiS j hjS hij => ⟨(hnsep i hiS j hjS hij).2.1, (hnsep i hiS j hjS hij).2.2.2.1⟩),
    hcoef⟩

private abbrev Pairs (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

private abbrev Pairs6 := Pairs 6

private lemma card_pairs6 : Fintype.card Pairs6 = 15 := by decide

private abbrev RrefParamIdx {d m k : ℕ}
    (I : Fin k → Fin d) (rDom : Pairs6 → Fin k) (σ : Fin m → Pairs6) :=
  (Fin k × {j : Fin d // ∀ r, I r ≠ j}) ⊕
  ((e : Pairs6) × {r : Fin k // r ≠ rDom e}) ⊕
  ((a : Fin m) × {j : Fin d // j ≠ I (rDom (σ a))})

private structure RrefConfig (d m k : ℕ) where
  I : {I : Fin k → Fin d // Function.Injective I}
  rDom : Pairs6 → Fin k
  σ : Fin m → Pairs6

private instance (d m k : ℕ) : Finite (RrefConfig d m k) :=
  Finite.of_injective
    (fun c : RrefConfig d m k => (c.I, c.rDom, c.σ))
    (fun c₁ c₂ h => by
      cases c₁; cases c₂
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl)

private def evalPoints {d m : ℕ} (z : Fin (m * d) → ℝ) : Fin m → Ambient d :=
  fun a => (EuclideanSpace.equiv (Fin d) ℝ).symm fun j => z (finProdFinEquiv (a, j))

private lemma continuous_evalPoints {d m : ℕ} :
    Continuous (evalPoints (d := d) (m := m)) := by
  refine continuous_pi fun a => ?_
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp <|
    continuous_pi fun j => continuous_apply (finProdFinEquiv (a, j))

private def rrefParamU {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (r : Fin k) (j : Fin d) : ℝ :=
  if _h : c.I.1 r = j then 1
  else if h' : ∃ s : Fin k, c.I.1 s = j then 0
  else y (Sum.inl (r, ⟨j, fun s hs => h' ⟨s, hs⟩⟩))

private def rrefParamC {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (e : Pairs6) (r : Fin k) : ℝ :=
  if h : r = c.rDom e then 1
  else y (Sum.inr (Sum.inl ⟨e, ⟨r, h⟩⟩))

private def rrefParamN {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (e : Pairs6) (j : Fin d) : ℝ :=
  ∑ r : Fin k, rrefParamC c y e r * rrefParamU c y r j

private def rrefParamP0 {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) (a : Fin m) (j : Fin d) : ℝ :=
  if h : j = c.I.1 (c.rDom (c.σ a)) then 0
  else y (Sum.inr (Sum.inr ⟨a, ⟨j, h⟩⟩))

private def rrefParamMap {d m k : ℕ} (c : RrefConfig d m k)
    (y : RrefParamIdx c.I.1 c.rDom c.σ → ℝ) : Fin (m * d) → ℝ :=
  fun x =>
    let p := finProdFinEquiv.symm x
    if p.2 = c.I.1 (c.rDom (c.σ p.1)) then
      - ∑ j : Fin d, rrefParamN c y (c.σ p.1) j * rrefParamP0 c y p.1 j
    else
      rrefParamP0 c y p.1 p.2

private lemma differentiable_rrefParamMap {d m k : ℕ} (c : RrefConfig d m k) :
    Differentiable ℝ (rrefParamMap c) := by
  have hu : ∀ r j, Differentiable ℝ fun y => rrefParamU c y r j := fun r j => by
    dsimp [rrefParamU]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_const 0
    · exact differentiable_apply _
  have hc : ∀ e r, Differentiable ℝ fun y => rrefParamC c y e r := fun e r => by
    dsimp [rrefParamC]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_apply _
  have hn : ∀ e j, Differentiable ℝ fun y => rrefParamN c y e j := fun e j =>
    Differentiable.fun_sum fun r _ => (hc e r).mul (hu r j)
  have hp0 : ∀ a j, Differentiable ℝ fun y => rrefParamP0 c y a j := fun a j => by
    dsimp [rrefParamP0]
    split_ifs
    · exact differentiable_const 0
    · exact differentiable_apply _
  refine differentiable_pi.mpr fun x => ?_
  dsimp [rrefParamMap]
  split_ifs
  · exact (Differentiable.fun_sum fun j _ => (hn _ j).mul (hp0 _ j)).neg
  · exact hp0 _ _

private lemma card_rrefParamIdx {d m k : ℕ}
    (c : RrefConfig d m k) :
    Fintype.card (RrefParamIdx c.I.1 c.rDom c.σ) =
      k * (d - k) + 15 * (k - 1) + m * (d - 1) := by
  have h1 : Fintype.card {j : Fin d // ∀ r : Fin k, c.I.1 r ≠ j} = d - k := by
    let sRest : Finset (Fin d) := Finset.univ \ Finset.univ.image c.I.1
    have heq : {j : Fin d // ∀ r : Fin k, c.I.1 r ≠ j} ≃ {j : Fin d // j ∈ sRest} :=
      Equiv.subtypeEquivRight fun j => by
        simp [sRest, Finset.mem_sdiff, Finset.mem_image]
    rw [Fintype.card_congr heq, Fintype.card_coe]
    have hsub : Finset.univ.image c.I.1 ⊆ (Finset.univ : Finset (Fin d)) :=
      Finset.subset_univ _
    dsimp [sRest]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ c.I.2, Finset.card_univ, Fintype.card_fin]
  have h2 : ∀ e : Pairs6, Fintype.card {r : Fin k // r ≠ c.rDom e} = k - 1 := fun e => by
    have heq : {r : Fin k // r ≠ c.rDom e} ≃
        {r : Fin k // r ∈ Finset.univ.erase (c.rDom e)} :=
      Equiv.subtypeEquivRight fun r => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  have h3 : ∀ a : Fin m, Fintype.card {j : Fin d // j ≠ c.I.1 (c.rDom (c.σ a))} = d - 1 :=
    fun a => by
    have heq : {j : Fin d // j ≠ c.I.1 (c.rDom (c.σ a))} ≃
        {j : Fin d // j ∈ Finset.univ.erase (c.I.1 (c.rDom (c.σ a)))} :=
      Equiv.subtypeEquivRight fun j => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  simp only [RrefParamIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
    Fintype.card_fin, h1, h2, h3, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_pairs6]
  ring

private lemma volume_image_eq_zero_of_card_lt {N : ℕ} (hN : 0 < N)
    {γ : Type*} [Fintype γ] (hcard : Fintype.card γ < N)
    {U : Set (γ → ℝ)} {Ψ : (γ → ℝ) → (Fin N → ℝ)} (hΨ : DifferentiableOn ℝ Ψ U) :
    (volume : Measure (Fin N → ℝ)) (Ψ '' U) = 0 := by
  let k0 : Fin N := ⟨0, hN⟩
  let H₀ : Submodule ℝ (Fin N → ℝ) := LinearMap.ker (LinearMap.proj k0)
  have hH₀_ne_top : H₀ ≠ ⊤ := by
    intro htop
    have hmem : Pi.single (M := fun _ : Fin N => ℝ) k0 (1 : ℝ) ∈ H₀ := htop ▸ Submodule.mem_top
    have h0 : (Pi.single (M := fun _ : Fin N => ℝ) k0 (1 : ℝ)) k0 = 0 := hmem
    simp at h0
  have hH₀_vol : (volume : Measure (Fin N → ℝ)) (H₀ : Set (Fin N → ℝ)) = 0 :=
    Measure.addHaar_submodule volume H₀ hH₀_ne_top
  let e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ
  let ι : γ → Fin N := fun g => ⟨(e g).1 + 1, by have := (e g).isLt; omega⟩
  let L : (Fin N → ℝ) → (γ → ℝ) := fun z g => z (ι g)
  have hL_diff : Differentiable ℝ L := differentiable_pi.mpr fun g => differentiable_apply (ι g)
  let M : (γ → ℝ) → (Fin N → ℝ) := fun y k =>
    if hk : k.1 = 0 then 0
    else if hlt : k.1 - 1 < Fintype.card γ then y (e.symm ⟨k.1 - 1, hlt⟩)
    else 0
  have hM_mem : ∀ y, M y ∈ (H₀ : Set (Fin N → ℝ)) := fun y => by
    change M y k0 = 0
    simp [M, k0]
  have hLM : ∀ y, L (M y) = y := fun y => by
    funext g
    dsimp [L, M]
    have hlt : (ι g).1 - 1 < Fintype.card γ := by simp [ι]
    simp only [↓reduceDIte, hlt]
    have heq : (⟨(ι g).1 - 1, hlt⟩ : Fin (Fintype.card γ)) = e g := by
      ext; simp [ι]
    rw [heq, e.symm_apply_apply]
  let s : Set (Fin N → ℝ) := (H₀ : Set (Fin N → ℝ)) ∩ L ⁻¹' U
  have hs_vol : (volume : Measure (Fin N → ℝ)) s = 0 :=
    measure_mono_null Set.inter_subset_left hH₀_vol
  have hsub : Ψ '' U ⊆ (Ψ ∘ L) '' s := by
    rintro _ ⟨y, hyU, rfl⟩
    refine ⟨M y, ⟨hM_mem y, ?_⟩, ?_⟩
    · simpa [Set.mem_preimage, hLM y] using hyU
    · simp [Function.comp_apply, hLM y]
  have hcomp_diff : DifferentiableOn ℝ (Ψ ∘ L) s :=
    hΨ.comp hL_diff.differentiableOn fun _ hz => hz.2
  have himg_zero : (volume : Measure (Fin N → ℝ)) ((Ψ ∘ L) '' s) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (volume : Measure (Fin N → ℝ)) hcomp_diff hs_vol
  exact measure_mono_null hsub himg_zero

private lemma volume_range_eq_zero_of_card_lt {N : ℕ} (hN : 0 < N)
    {γ : Type*} [Fintype γ] (hcard : Fintype.card γ < N)
    {Ψ : (γ → ℝ) → (Fin N → ℝ)} (hΨ : Differentiable ℝ Ψ) :
    (volume : Measure (Fin N → ℝ)) (Set.range Ψ) = 0 := by
  rw [← Set.image_univ]
  exact volume_image_eq_zero_of_card_lt hN hcard hΨ.differentiableOn

private lemma mem_range_rrefParamMap_of_span {d m k : ℕ} (hk : 1 ≤ k)
    (z : Fin (m * d) → ℝ)
    (hz_ball : ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j)
    (hnne : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j → n i j ≠ 0)
    (hnsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hno_int : ∀ (k₁ : Fin 6) (a : Fin m), evalPoints z a ∉ interior (C k₁ : Set (Ambient d)))
    (I : Fin k → Fin d) (u : Fin k → Ambient d)
    (hI_inj : Function.Injective I)
    (hu_rref : ∀ r s : Fin k, u r (I s) = if r = s then 1 else 0)
    (hcoef : ∀ k₁ l : Fin 6, ∀ j : Fin d, n k₁ l j = ∑ r : Fin k, n k₁ l (I r) * u r j) :
    ∃ c : RrefConfig d m k, z ∈ Set.range (rrefParamMap c) := by
  classical
  let p : Fin m → Ambient d := evalPoints z
  let S := nonEmptyIntParts C
  have hex_rDom : ∀ e : Pairs6, ∃ r : Fin k,
      e.1.1 ∈ S → e.1.2 ∈ S → n e.1.1 e.1.2 (I r) ≠ 0 := by
    intro e
    by_cases hmem : e.1.1 ∈ S ∧ e.1.2 ∈ S
    · have hne0 : n e.1.1 e.1.2 ≠ 0 := hnne e.1.1 hmem.1 e.1.2 hmem.2 e.2.ne
      by_contra hall
      push Not at hall
      have hzero : n e.1.1 e.1.2 = 0 := by
        apply PiLp.ext
        intro j
        rw [hcoef e.1.1 e.1.2 j]
        have hsum0 : (∑ r : Fin k, n e.1.1 e.1.2 (I r) * u r j) = 0 :=
          Finset.sum_eq_zero fun r _ => by rw [(hall r).2.2, zero_mul]
        exact hsum0
      exact hne0 hzero
    · exact ⟨⟨0, hk⟩, fun h1 h2 => False.elim (hmem ⟨h1, h2⟩)⟩
  choose rDom hrDom_spec using hex_rDom
  have hex_sig : ∀ a : Fin m,
      ∃ e : Pairs6, e.1.1 ∈ S ∧ e.1.2 ∈ S ∧ ⟪n e.1.1 e.1.2, p a⟫_ℝ = 0 := by
    intro a
    obtain ⟨i, hiS, j, hjS, hij, hzero⟩ :=
      skeleton_in_separating_hyperplanes C hcov n hnsep hnsym (hz_ball a)
        (fun q hq => hno_int q a hq)
    exact ⟨⟨(i, j), hij⟩, hiS, hjS, hzero⟩
  choose σ hσ1 hσ2 hσ_zero using hex_sig
  let cfg : RrefConfig d m k := ⟨⟨I, hI_inj⟩, rDom, σ⟩
  let cCoef : Pairs6 → Fin k → ℝ := fun e r =>
    if e.1.1 ∈ S ∧ e.1.2 ∈ S then
      (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 (I r)
    else if r = rDom e then 1 else 0
  have hc_dom : ∀ e : Pairs6, cCoef e (rDom e) = 1 := fun e => by
    dsimp [cCoef]
    by_cases h : e.1.1 ∈ S ∧ e.1.2 ∈ S
    · simp [h, inv_mul_cancel₀ (hrDom_spec e h.1 h.2)]
    · simp [h]
  let y : RrefParamIdx cfg.I.1 cfg.rDom cfg.σ → ℝ
    | Sum.inl (r, j) => u r j.1
    | Sum.inr (Sum.inl ⟨e, r⟩) => cCoef e r.1
    | Sum.inr (Sum.inr ⟨a, j⟩) => p a j.1
  have hy_U : ∀ r j, rrefParamU cfg y r j = u r j := fun r j => by
    dsimp [rrefParamU, cfg]
    split_ifs with h1 h2
    · rw [← h1, hu_rref r r]; simp
    · obtain ⟨s, hs⟩ := h2
      have hrs : r ≠ s := fun h => h1 (h ▸ hs)
      rw [← hs, hu_rref r s]; simp [hrs]
    · rfl
  have hy_C : ∀ e r, rrefParamC cfg y e r = cCoef e r := fun e r => by
    dsimp [rrefParamC, cfg]
    split_ifs with h
    · rw [h, hc_dom e]
    · rfl
  have hy_N_perp : ∀ a : Fin m, ∑ j : Fin d, rrefParamN cfg y (σ a) j * p a j = 0 := fun a => by
    let e := σ a
    have h1 : e.1.1 ∈ S := hσ1 a
    have h2 : e.1.2 ∈ S := hσ2 a
    have hN_eq : ∀ j : Fin d, rrefParamN cfg y e j =
        (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 j := fun j => by
      dsimp [rrefParamN]
      have hc_eq : ∀ r : Fin k, rrefParamC cfg y e r =
          (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * n e.1.1 e.1.2 (I r) := fun r => by
        rw [hy_C e r]
        dsimp [cCoef]
        simp only [h1, h2, and_self, ↓reduceIte]
      simp_rw [hc_eq, hy_U]
      rw [hcoef e.1.1 e.1.2 j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hN_mul : ∀ j : Fin d, rrefParamN cfg y (σ a) j * p a j =
        (n e.1.1 e.1.2 (I (rDom e)))⁻¹ * (n e.1.1 e.1.2 j * p a j) := fun j => by
      rw [show σ a = e from rfl, hN_eq j, mul_assoc]
    simp_rw [hN_mul]
    rw [← Finset.mul_sum]
    have hdot : ∑ j : Fin d, n e.1.1 e.1.2 j * p a j = 0 := by
      simpa only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
        conj_trivial, mul_comm] using hσ_zero a
    rw [hdot, mul_zero]
  have hy_N_piv : ∀ e : Pairs6, rrefParamN cfg y e (I (rDom e)) = 1 := fun e => by
    dsimp [rrefParamN]
    simp_rw [hy_C, hy_U, hu_rref]
    rw [Finset.sum_eq_single (rDom e)]
    · simp [hc_dom e]
    · intro r _ hr; simp [hr]
    · intro hr; exact False.elim (hr (Finset.mem_univ _))
  refine ⟨cfg, y, ?_⟩
  funext x
  obtain ⟨⟨a, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  have hp_eq : p a j = z (finProdFinEquiv (a, j)) := rfl
  dsimp [rrefParamMap]
  rw [finProdFinEquiv.symm_apply_apply]
  split_ifs with hj
  · have hj_eq : j = I (rDom (σ a)) := hj
    have hp0_eq : ∀ q : Fin d, rrefParamP0 cfg y a q =
        if q = I (rDom (σ a)) then 0 else p a q := fun q => by
      dsimp [rrefParamP0, cfg]
      split_ifs <;> rfl
    simp_rw [hp0_eq]
    have hsplit : ∑ q : Fin d, rrefParamN cfg y (σ a) q * (if q = I (rDom (σ a)) then 0 else p a q) =
        (∑ q ∈ Finset.univ.erase (I (rDom (σ a))), rrefParamN cfg y (σ a) q * p a q) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (I (rDom (σ a))))]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp [(Finset.mem_erase.mp hq).1]
    have hsplit_full : ∑ q : Fin d, rrefParamN cfg y (σ a) q * p a q =
        rrefParamN cfg y (σ a) (I (rDom (σ a))) * p a (I (rDom (σ a))) +
          ∑ q ∈ Finset.univ.erase (I (rDom (σ a))), rrefParamN cfg y (σ a) q * p a q :=
      (Finset.add_sum_erase Finset.univ (fun q => rrefParamN cfg y (σ a) q * p a q)
        (Finset.mem_univ (I (rDom (σ a))))).symm
    rw [hy_N_perp a, hy_N_piv (σ a), one_mul] at hsplit_full
    have hpj : p a (I (rDom (σ a))) = p a j := by rw [← hj_eq]
    change - ∑ q : Fin d, rrefParamN cfg y (σ a) q * (if q = I (rDom (σ a)) then 0 else p a q) =
      z (finProdFinEquiv (a, j))
    rw [hsplit]
    linarith [hsplit_full, hpj, hp_eq]
  · have hj_ne : j ≠ I (rDom (σ a)) := hj
    dsimp [rrefParamP0, cfg, y]
    simp [hj_ne, hp_eq]

/-- Unconditional existence of `5 * d + 36` central blocking points in `unitBall d` (`d ≥ 5`). -/
theorem exists_isBlocking (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : Fin (5 * d + 36) → Ambient d, IsBlocking p := by
  let m := 5 * d + 36
  have hmd : 0 < m * d := by positivity
  let bad : Set (Fin (m * d) → ℝ) := ⋃ c : RrefConfig d m 5, Set.range (rrefParamMap c)
  have hbad_vol : (volume : Measure (Fin (m * d) → ℝ)) bad = 0 := by
    refine measure_iUnion_null fun c => ?_
    have hcard : Fintype.card (RrefParamIdx c.I.1 c.rDom c.σ) < m * d := by
      rw [card_rrefParamIdx c]
      have hm_prod : m * d = m * (d - 1) + m := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        ring
      rw [hm_prod]
      dsimp [m]
      omega
    exact volume_range_eq_zero_of_card_lt hmd hcard (differentiable_rrefParamMap c)
  let good : Set (Fin (m * d) → ℝ) :=
    {z | ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1}
  have hgood_open : IsOpen good := by
    have heq : good = ⋂ a : Fin m, (fun z => evalPoints z a) ⁻¹' Metric.ball (0 : Ambient d) 1 := by
      ext z; simp [good]
    rw [heq]
    refine isOpen_iInter_of_finite fun a => Metric.isOpen_ball.preimage ?_
    exact (continuous_apply a).comp continuous_evalPoints
  have hzero_good : (0 : Fin (m * d) → ℝ) ∈ good := fun a => by
    have hev : evalPoints (0 : Fin (m * d) → ℝ) a = 0 := by
      apply PiLp.ext
      intro j
      rfl
    rw [hev]
    exact Metric.mem_ball_self zero_lt_one
  have hgood_pos : 0 < (volume : Measure (Fin (m * d) → ℝ)) good :=
    hgood_open.measure_pos volume ⟨0, hzero_good⟩
  have hnot_sub : ¬ good ⊆ bad := fun hsub => by
    have hle : (volume : Measure (Fin (m * d) → ℝ)) good ≤ volume bad := measure_mono hsub
    rw [hbad_vol] at hle
    exact (lt_of_lt_of_le hgood_pos hle).ne' rfl
  obtain ⟨z, hz_good, hz_not_bad⟩ := Set.not_subset.mp hnot_sub
  refine ⟨evalPoints z, ?_⟩
  by_contra hnot_block
  dsimp [IsBlocking] at hnot_block
  push Not at hnot_block
  obtain ⟨C, hcov, hdisj, h0, hno_int⟩ := hnot_block
  obtain ⟨n, I, u, hI_inj, hu_rref, _hnii, hnsym, _hnnotS, hnne, hnsep, hcoef⟩ :=
    separating_normals_in_rref_span hd C hcov hdisj h0
  obtain ⟨c, hc⟩ := mem_range_rrefParamMap_of_span (by norm_num : 1 ≤ 5) z hz_good C hcov n
    hnsym hnne hnsep hno_int I u hI_inj hu_rref hcoef
  exact hz_not_bad (Set.mem_iUnion.mpr ⟨c, hc⟩)

private lemma separating_normals_rref_of_a_span {d k : ℕ} (hk : k ≤ d)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep_nn : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ))
    (hnsym : ∀ i j, n j i = - n i j)
    (A : Fin k → Ambient d)
    (ha_span_A : ∀ i : Fin 6, (∑ j : Fin 6, n i j) ∈ Submodule.span ℝ (Set.range A)) :
    ∃ (I : Fin k → Fin d) (u : Fin k → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin k, u r (I s) = if r = s then 1 else 0) ∧
      (∀ k₁ l : Fin 6, ∀ j : Fin d,
        n k₁ l j = ∑ r : Fin k, n k₁ l (I r) * u r j) := by
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  obtain ⟨I, u, hI_inj, hu_rref, hA_span⟩ := exists_rref k hk A
  have hA_le_u : Submodule.span ℝ (Set.range A) ≤ Submodule.span ℝ (Set.range u) :=
    Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hA_span t)
  have ha_span : ∀ i : Fin 6, a i ∈ Submodule.span ℝ (Set.range u) := fun i =>
    hA_le_u (ha_span_A i)
  have hinner_single : ∀ (w : Ambient d) (j : Fin d),
      ⟪w, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = w j := fun w j => by
    rw [EuclideanSpace.inner_single_right, one_mul]
    simp
  have hspan_perp : ∀ {v : Ambient d},
      (∀ r : Fin k, ⟪u r, v⟫_ℝ = 0) →
      ∀ i : Fin 6, ⟪a i, v⟫_ℝ = 0 := by
    intro v hv i
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (ha_span i)
    · rintro _ ⟨r, rfl⟩; exact hv r
    · simp
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx; rw [real_inner_smul_left, hx, mul_zero]
  have hcoef : ∀ k₁ l : Fin 6, ∀ j : Fin d,
      n k₁ l j = ∑ r : Fin k, n k₁ l (I r) * u r j := by
    intro k₁ l j
    let v : Ambient d :=
      EuclideanSpace.single j (1 : ℝ) -
        ∑ r : Fin k, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)
    have hv_u : ∀ s : Fin k, ⟪u s, v⟫_ℝ = 0 := fun s => by
      dsimp [v]
      rw [inner_sub_right, inner_sum, hinner_single]
      have hsum : (∑ r : Fin k, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) = u s j := by
        calc ∑ r : Fin k, ⟪u s, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ
            = ∑ r : Fin k, u r j * u s (I r) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [real_inner_smul_right, hinner_single]
          _ = ∑ r : Fin k, u r j * (if s = r then 1 else 0) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hu_rref s r]
          _ = u s j := by simp
      rw [hsum, sub_self]
    have hv_n : ⟪n k₁ l, v⟫_ℝ = 0 :=
      central_partition_normal_rank C hcov n hnnotS hsep_nn hnsym (hspan_perp hv_u) k₁ l
    dsimp [v] at hv_n
    rw [inner_sub_right, inner_sum, hinner_single] at hv_n
    have hsum_n :
        (∑ r : Fin k, ⟪n k₁ l, (u r j) • EuclideanSpace.single (I r) (1 : ℝ)⟫_ℝ) =
          ∑ r : Fin k, n k₁ l (I r) * u r j := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [real_inner_smul_right, hinner_single, mul_comm]
    linarith [hv_n, hsum_n]
  exact ⟨I, u, hI_inj, hu_rref, hcoef⟩

private lemma normal_row_sum_zero {d : ℕ} (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j) :
    ∑ i : Fin 6, ∑ j : Fin 6, n i j = 0 := by
  have hneg : (∑ i : Fin 6, ∑ j : Fin 6, n i j) = - ∑ i : Fin 6, ∑ j : Fin 6, n i j := by
    calc ∑ i : Fin 6, ∑ j : Fin 6, n i j
        = ∑ j : Fin 6, ∑ i : Fin 6, n i j := Finset.sum_comm
      _ = ∑ j : Fin 6, ∑ i : Fin 6, (- n j i) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hnsym j i]
      _ = - ∑ j : Fin 6, ∑ i : Fin 6, n j i := by
        simp [Finset.sum_neg_distrib]
  have hadd : (∑ i : Fin 6, ∑ j : Fin 6, n i j) + (∑ i : Fin 6, ∑ j : Fin 6, n i j) = 0 := by
    conv_lhs => rhs; rw [hneg]
    exact add_neg_cancel _
  have h2 : (2 : ℝ) • (∑ i : Fin 6, ∑ j : Fin 6, n i j) = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma separating_normals_in_rref4_span {d : ℕ} (hd : 4 ≤ d)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep_nn : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ))
    (hnsym : ∀ i j, n j i = - n i j)
    (hnot_indep : ¬ LinearIndependent ℝ (fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)) :
    ∃ (I : Fin 4 → Fin d) (u : Fin 4 → Ambient d),
      Function.Injective I ∧
      (∀ r s : Fin 4, u r (I s) = if r = s then 1 else 0) ∧
      (∀ k₁ l : Fin 6, ∀ j : Fin d,
        n k₁ l j = ∑ r : Fin 4, n k₁ l (I r) * u r j) := by
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  have ha_sum0 : ∑ i : Fin 6, a i = 0 := normal_row_sum_zero n hnsym
  obtain ⟨c, hc_sum, t₀, hct₀⟩ := Fintype.not_linearIndependent_iff.mp hnot_indep
  let A' : Fin 4 → Ambient d := fun r => a (t₀.succAbove r).succ
  have ha_span_A' : ∀ i : Fin 6, a i ∈ Submodule.span ℝ (Set.range A') := by
    have hsuccAbove_mem : ∀ r : Fin 4, a (t₀.succAbove r).succ ∈ Submodule.span ℝ (Set.range A') :=
      fun r => Submodule.subset_span ⟨r, rfl⟩
    have ht₀_mem : a t₀.succ ∈ Submodule.span ℝ (Set.range A') := by
      have hsplit :
          c t₀ • a t₀.succ + ∑ r : Fin 4, c (t₀.succAbove r) • a (t₀.succAbove r).succ = 0 := by
        rw [← Fin.sum_univ_succAbove (fun t : Fin 5 => c t • a t.succ) t₀]
        exact hc_sum
      have hneg :
          c t₀ • a t₀.succ = - ∑ r : Fin 4, c (t₀.succAbove r) • a (t₀.succAbove r).succ :=
        eq_neg_of_add_eq_zero_left hsplit
      have hinv :
          a t₀.succ = -(c t₀)⁻¹ • ∑ r : Fin 4, c (t₀.succAbove r) • a (t₀.succAbove r).succ := by
        have h1 := congrArg ((c t₀)⁻¹ • ·) hneg
        rw [smul_smul, inv_mul_cancel₀ hct₀, one_smul] at h1
        rw [h1, smul_neg, neg_smul]
      rw [hinv]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun r _ => ?_)
      exact Submodule.smul_mem _ _ (hsuccAbove_mem r)
    have hsucc_mem : ∀ t : Fin 5, a t.succ ∈ Submodule.span ℝ (Set.range A') := fun t => by
      by_cases ht : t = t₀
      · subst ht; exact ht₀_mem
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq ht
        exact hsuccAbove_mem r
    intro i
    refine Fin.cases ?_ hsucc_mem i
    have ha0 : a 0 = - ∑ t : Fin 5, a t.succ := by
      have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
        simpa only [← Fin.sum_univ_succ] using ha_sum0
      exact eq_neg_of_add_eq_zero_left hsplit
    rw [ha0]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun t _ => hsucc_mem t)
  exact separating_normals_rref_of_a_span hd C hcov n hnnotS hsep_nn hnsym A' ha_span_A'

private lemma exists_vec_inner_eq {d : ℕ}
    (a : Fin 6 → Ambient d) (ha_sum0 : ∑ i : Fin 6, a i = 0)
    (hindep : LinearIndependent ℝ (fun t : Fin 5 => a t.succ))
    (y : Fin 6 → ℝ) (hy : ∑ i : Fin 6, y i = 0) :
    ∃ x : Ambient d, ∀ i : Fin 6, ⟪a i, x⟫_ℝ = y i := by
  let Φ : Ambient d →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin 5) ℝ).symm (fun t => ⟪a t.succ, x⟫_ℝ)
      map_add' := fun x₁ x₂ => by
        ext t
        change ⟪a t.succ, x₁ + x₂⟫_ℝ = ⟪a t.succ, x₁⟫_ℝ + ⟪a t.succ, x₂⟫_ℝ
        exact inner_add_right _ _ _
      map_smul' := fun r x => by
        ext t
        change ⟪a t.succ, r • x⟫_ℝ = r * ⟪a t.succ, x⟫_ℝ
        exact real_inner_smul_right _ _ _ }
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    let v : Ambient d := ∑ t : Fin 5, z t • a t.succ
    have hz_perp : ⟪Φ v, z⟫_ℝ = 0 := hz (Φ v) ⟨v, rfl⟩
    have hinner : ⟪Φ v, z⟫_ℝ = ⟪v, v⟫_ℝ := by
      have h1 : ⟪Φ v, z⟫_ℝ = ∑ t : Fin 5, z t * ⟪a t.succ, v⟫_ℝ := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
        rfl
      have h2 : ⟪v, v⟫_ℝ = ∑ t : Fin 5, z t * ⟪a t.succ, v⟫_ℝ := by
        dsimp [v]
        rw [sum_inner]
        refine Finset.sum_congr rfl fun t _ => real_inner_smul_left _ _ _
      exact h1.trans h2.symm
    rw [hinner, inner_self_eq_zero] at hz_perp
    have hz_coef : ∀ t : Fin 5, z t = 0 :=
      (Fintype.linearIndependent_iff.mp hindep) z hz_perp
    exact PiLp.ext hz_coef
  let y' : EuclideanSpace ℝ (Fin 5) := (EuclideanSpace.equiv (Fin 5) ℝ).symm (fun t => y t.succ)
  have hy'_mem : y' ∈ LinearMap.range Φ := hrange ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hy'_mem
  refine ⟨x, fun i => ?_⟩
  have hsucc : ∀ t : Fin 5, ⟪a t.succ, x⟫_ℝ = y t.succ := fun t => by
    have ht := congrArg (fun w : EuclideanSpace ℝ (Fin 5) => w t) hx
    simpa [Φ, y'] using ht
  refine Fin.cases ?_ hsucc i
  have ha0 : a 0 = - ∑ t : Fin 5, a t.succ := by
    have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
      simpa only [← Fin.sum_univ_succ] using ha_sum0
    exact eq_neg_of_add_eq_zero_left hsplit
  have hy0 : y 0 = - ∑ t : Fin 5, y t.succ := by
    have hsplit : y 0 + ∑ t : Fin 5, y t.succ = 0 := by
      simpa only [← Fin.sum_univ_succ] using hy
    exact eq_neg_of_add_eq_zero_left hsplit
  rw [ha0, hy0, inner_neg_left, sum_inner]
  congr 1
  exact Finset.sum_congr rfl fun t _ => hsucc t

private lemma hyperplane_miss_orthants_eq_zero {b : EuclideanSpace ℝ (Fin 3)} (hb : b ≠ 0)
    (β : ℝ)
    (hpos : ∀ z : EuclideanSpace ℝ (Fin 3), (∀ r : Fin 3, 0 < z r) → ⟪b, z⟫_ℝ ≠ β)
    (hneg : ∀ z : EuclideanSpace ℝ (Fin 3), (∀ r : Fin 3, z r < 0) → ⟪b, z⟫_ℝ ≠ β) :
    β = 0 := by
  by_contra hβ
  have himp : ∀ (z : Fin 3 → ℝ),
      ⟪b, (EuclideanSpace.equiv (Fin 3) ℝ).symm z⟫_ℝ = ∑ r : Fin 3, b r * z r := fun z => by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, mul_comm]
    rfl
  by_cases hmix : ∃ p q : Fin 3, 0 < b p ∧ b q < 0
  · obtain ⟨p, q, hbp, hbq⟩ := hmix
    let z₁ : Fin 3 → ℝ := fun _ => 1
    let s₁ := ∑ r : Fin 3, b r * z₁ r
    rcases lt_trichotomy s₁ β with hs1 | hs1 | hs1
    · let z : Fin 3 → ℝ := fun j => if j = p then 1 + (β - s₁) / b p else 1
      have hz_pos : ∀ r : Fin 3, 0 < z r := fun r => by
        dsimp [z]
        split_ifs
        · have hdiv : 0 < (β - s₁) / b p := div_pos (by linarith) hbp
          linarith
        · norm_num
      apply hpos ((EuclideanSpace.equiv (Fin 3) ℝ).symm z) hz_pos
      rw [himp]
      have hp_term : b p * z p = b p * 1 + (β - s₁) := by
        dsimp [z]
        simp only [↓reduceIte]
        field_simp [hbp.ne']
      have hdiff : ∑ r : Fin 3, b r * z r = ∑ r : Fin 3, b r * z₁ r + (β - s₁) := by
        rw [← Finset.add_sum_erase Finset.univ (fun r => b r * z r) (Finset.mem_univ p),
            ← Finset.add_sum_erase Finset.univ (fun r => b r * z₁ r) (Finset.mem_univ p)]
        have hrest : ∑ r ∈ Finset.univ.erase p, b r * z r = ∑ r ∈ Finset.univ.erase p, b r * z₁ r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrp : r ≠ p := (Finset.mem_erase.mp hr).1
          simp [z, z₁, hrp]
        rw [hrest, hp_term]
        dsimp [z₁]
        ring
      rw [hdiff]
      dsimp [s₁]
      ring
    · apply hpos ((EuclideanSpace.equiv (Fin 3) ℝ).symm z₁) (fun _ => by norm_num)
      rw [himp]
      exact hs1
    · let z : Fin 3 → ℝ := fun j => if j = q then 1 + (β - s₁) / b q else 1
      have hz_pos : ∀ r : Fin 3, 0 < z r := fun r => by
        dsimp [z]
        split_ifs
        · have hdiv : 0 < (β - s₁) / b q := div_pos_of_neg_of_neg (by linarith) hbq
          linarith
        · norm_num
      apply hpos ((EuclideanSpace.equiv (Fin 3) ℝ).symm z) hz_pos
      rw [himp]
      have hq_term : b q * z q = b q * 1 + (β - s₁) := by
        dsimp [z]
        simp only [↓reduceIte]
        field_simp [hbq.ne]
      have hdiff : ∑ r : Fin 3, b r * z r = ∑ r : Fin 3, b r * z₁ r + (β - s₁) := by
        rw [← Finset.add_sum_erase Finset.univ (fun r => b r * z r) (Finset.mem_univ q),
            ← Finset.add_sum_erase Finset.univ (fun r => b r * z₁ r) (Finset.mem_univ q)]
        have hrest : ∑ r ∈ Finset.univ.erase q, b r * z r = ∑ r ∈ Finset.univ.erase q, b r * z₁ r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
          simp [z, z₁, hrq]
        rw [hrest, hq_term]
        dsimp [z₁]
        ring
      rw [hdiff]
      dsimp [s₁]
      ring
  · have h_same : (∀ r : Fin 3, 0 ≤ b r) ∨ (∀ r : Fin 3, b r ≤ 0) := by
      by_cases hex_pos : ∃ p : Fin 3, 0 < b p
      · left
        obtain ⟨p, hbp⟩ := hex_pos
        intro q
        exact le_of_not_gt fun hbq => hmix ⟨p, q, hbp, hbq⟩
      · right
        push Not at hex_pos
        exact hex_pos
    have hex_ne : ∃ r : Fin 3, b r ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hb (PiLp.ext hall)
    let s := ∑ r : Fin 3, b r
    have hs_ne : s ≠ 0 := by
      obtain ⟨r₀, hr₀⟩ := hex_ne
      rcases h_same with hnn | hnp
      · have hpos_r : 0 < b r₀ := lt_of_le_of_ne (hnn r₀) hr₀.symm
        have hge : b r₀ ≤ s := Finset.single_le_sum (fun r _ => hnn r) (Finset.mem_univ r₀)
        linarith
      · have hneg_r : b r₀ < 0 := lt_of_le_of_ne (hnp r₀) hr₀
        have hle : s ≤ b r₀ := by
          have h := Finset.single_le_sum (fun r _ => neg_nonneg.mpr (hnp r)) (Finset.mem_univ r₀)
          simp only [Finset.sum_neg_distrib] at h
          linarith
        linarith
    let t := β / s
    have ht_ne : t ≠ 0 := div_ne_zero hβ hs_ne
    let z : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm fun _ => t
    have hdot : ⟪b, z⟫_ℝ = β := by
      rw [himp, ← Finset.sum_mul]
      change s * (β / s) = β
      exact mul_div_cancel₀ β hs_ne
    rcases lt_or_gt_of_ne ht_ne with ht_neg | ht_pos
    · exact hneg z (fun _ => ht_neg) hdot
    · exact hpos z (fun _ => ht_pos) hdot

private lemma rank5_triangle_dependent {d : ℕ}
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnnotS : ∀ i j, i ∉ nonEmptyIntParts C ∨ j ∉ nonEmptyIntParts C → n i j = 0)
    (hsep_all : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0) ∧
      (∀ x ∈ interior (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ < 0))
    (hnsym : ∀ i j, n j i = - n i j)
    (hindep : LinearIndependent ℝ (fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)) :
    (nonEmptyIntParts C = Finset.univ) ∧
    (∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
      ∃ c₁ c₂ c₃ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
        c₁ • n i j + c₂ • n j k + c₃ • n k i = 0) := by
  let a : Fin 6 → Ambient d := fun i => ∑ j : Fin 6, n i j
  have ha_sum0 : ∑ i : Fin 6, a i = 0 := normal_row_sum_zero n hnsym
  have hS_univ : nonEmptyIntParts C = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro i
    by_contra hiS
    have hai0 : a i = 0 := Finset.sum_eq_zero fun j _ => hnnotS i j (Or.inl hiS)
    refine Fin.cases (fun hi0 => ?_) (fun t ht0 => ?_) i hai0
    · have hsum0 : ∑ t : Fin 5, (1 : ℝ) • a t.succ = 0 := by
        simp only [one_smul]
        have hsplit : a 0 + ∑ t : Fin 5, a t.succ = 0 := by
          simpa only [← Fin.sum_univ_succ] using ha_sum0
        rw [hi0, zero_add] at hsplit
        exact hsplit
      have h10 := (Fintype.linearIndependent_iff.mp hindep) (fun _ => 1) hsum0 0
      norm_num at h10
    · exact (hindep.ne_zero t) ht0
  have hinner_a_ge : ∀ (l : Fin 6) {y : Ambient d}, y ∈ (C l : Set (Ambient d)) → 0 ≤ ⟪a l, y⟫_ℝ := by
    intro l y hy
    dsimp [a]
    rw [sum_inner]
    refine Finset.sum_nonneg fun q _ => ?_
    by_cases hql : l = q
    · subst hql
      have hadd : n l l + n l l = 0 := by
        conv_lhs => rhs; rw [hnsym l l]
        exact add_neg_cancel _
      have h2 : (2 : ℝ) • n l l = 0 := by rwa [two_smul]
      rw [(smul_eq_zero.mp h2).resolve_left two_ne_zero, inner_zero_left]
    · exact (hsep_all l (hS_univ ▸ Finset.mem_univ l) q (hS_univ ▸ Finset.mem_univ q) hql).1 y hy
  have hpos_of_other_neg : ∀ (p : Fin 6) {x : Ambient d},
      (∀ l : Fin 6, l ≠ p → ⟪a l, x⟫_ℝ < 0) →
      ∀ q : Fin 6, q ≠ p → 0 < ⟪n p q, x⟫_ℝ := by
    intro p x hneg q hqp
    let α : ℝ := (2 * (‖x‖ + 1))⁻¹
    have hα_pos : 0 < α := inv_pos.mpr (by positivity)
    let z : Ambient d := α • x
    have hz_ball : z ∈ Metric.ball (0 : Ambient d) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [z]
      rw [norm_smul, Real.norm_of_nonneg hα_pos.le]
      dsimp [α]
      have hden : 0 < 2 * (‖x‖ + 1) := by positivity
      rw [inv_mul_lt_one₀ hden]
      linarith [norm_nonneg x]
    let U : Set (Ambient d) :=
      Metric.ball (0 : Ambient d) 1 ∩ ⋂ l ∈ Finset.univ.erase p, {y : Ambient d | ⟪a l, y⟫_ℝ < 0}
    have hU_open : IsOpen U :=
      Metric.isOpen_ball.inter <| isOpen_biInter_finset fun l _ =>
        isOpen_lt (continuous_const.inner continuous_id) continuous_const
    have hz_U : z ∈ U := by
      refine ⟨hz_ball, Set.mem_iInter₂.mpr fun l hl => ?_⟩
      have hlp : l ≠ p := (Finset.mem_erase.mp hl).1
      change ⟪a l, α • x⟫_ℝ < 0
      rw [real_inner_smul_right]
      exact mul_neg_of_pos_of_neg hα_pos (hneg l hlp)
    have hU_sub : U ⊆ (C p : Set (Ambient d)) := by
      intro y hyU
      have hy_ball : y ∈ unitBall d := Metric.ball_subset_closedBall hyU.1
      rw [hcov] at hy_ball
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hy_ball
      by_cases hlp : l = p
      · exact hlp ▸ hl
      · have hle := hinner_a_ge l hl
        have hlt : ⟪a l, y⟫_ℝ < 0 :=
          Set.mem_iInter₂.mp hyU.2 l (Finset.mem_erase.mpr ⟨hlp, Finset.mem_univ l⟩)
        exact False.elim (not_lt_of_ge hle hlt)
    have hz_int : z ∈ interior (C p : Set (Ambient d)) := interior_maximal hU_sub hU_open hz_U
    have hz_pos : 0 < ⟪n p q, z⟫_ℝ :=
      (hsep_all p (hS_univ ▸ Finset.mem_univ p) q (hS_univ ▸ Finset.mem_univ q) hqp.symm).2.1 z hz_int
    dsimp [z] at hz_pos
    rw [real_inner_smul_right] at hz_pos
    exact pos_of_mul_pos_right hz_pos hα_pos.le
  refine ⟨hS_univ, fun i j k hij hjk hik => ?_⟩
  let M₀ : Finset (Fin 6) := Finset.univ.filter fun m => m ≠ i ∧ m ≠ j ∧ m ≠ k
  have hM₀_card : M₀.card = 3 := by
    have heq : M₀ = Finset.univ \ ({i, j, k} : Finset (Fin 6)) := by
      ext m; simp [M₀, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
    have h3 : ({i, j, k} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hjk]
      · simp [hij, hik]
    omega
  have hex_x0 := exists_vec_inner_eq a ha_sum0 hindep
    (fun l => if l = i ∨ l = j ∨ l = k then 1 else -1) (by
      have hsplit : (∑ l : Fin 6, if l = i ∨ l = j ∨ l = k then (1 : ℝ) else -1) =
          ∑ l ∈ ({i, j, k} : Finset (Fin 6)), (1 : ℝ) + ∑ l ∈ M₀, (-1 : ℝ) := by
        have hdisj : Disjoint ({i, j, k} : Finset (Fin 6)) M₀ := by
          rw [Finset.disjoint_left]
          intro l hl hlM
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hlM
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          tauto
        have hun : ({i, j, k} : Finset (Fin 6)) ∪ M₀ = Finset.univ := by
          ext l
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, M₀,
            Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          tauto
        rw [← hun, Finset.sum_union hdisj]
        congr 1
        · refine Finset.sum_congr rfl fun l hl => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          simp [hl]
        · refine Finset.sum_congr rfl fun l hl => ?_
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          simp [hl.1, hl.2.1, hl.2.2]
      have h3 : ({i, j, k} : Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hjk]
        · simp [hij, hik]
      rw [hsplit, Finset.sum_const, Finset.sum_const, h3, hM₀_card]
      norm_num)
  obtain ⟨x₀, hx₀⟩ := hex_x0
  have hex_w1 := exists_vec_inner_eq a ha_sum0 hindep
    (fun l => if l = i then 1 else if l = k then -1 else 0) (by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [↓reduceIte]
      have hk_mem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
      rw [← Finset.add_sum_erase _ _ hk_mem]
      simp only [hik.symm, ↓reduceIte]
      have hrest : (∑ l ∈ (Finset.univ.erase i).erase k,
          if l = i then (1 : ℝ) else if l = k then -1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlk := (Finset.mem_erase.mp hl).1
        have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        simp [hli, hlk]
      rw [hrest]; ring)
  obtain ⟨w₁, hw₁⟩ := hex_w1
  have hex_w2 := exists_vec_inner_eq a ha_sum0 hindep
    (fun l => if l = j then 1 else if l = k then -1 else 0) (by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
      simp only [↓reduceIte]
      have hk_mem : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
      rw [← Finset.add_sum_erase _ _ hk_mem]
      simp only [hjk.symm, ↓reduceIte]
      have hrest : (∑ l ∈ (Finset.univ.erase j).erase k,
          if l = j then (1 : ℝ) else if l = k then -1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlk := (Finset.mem_erase.mp hl).1
        have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        simp [hlj, hlk]
      rw [hrest]; ring)
  obtain ⟨w₂, hw₂⟩ := hex_w2
  have hex_e : ∀ m ∈ M₀, ∃ em : Ambient d, ∀ l : Fin 6,
      ⟪a l, em⟫_ℝ = if l = m then -1 else if l = i then 1 else 0 := by
    intro m hm
    have hmi : m ≠ i := (Finset.mem_filter.mp hm).2.1
    refine exists_vec_inner_eq a ha_sum0 hindep
      (fun l => if l = m then -1 else if l = i then 1 else 0) ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m)]
    simp only [↓reduceIte]
    have hi_mem : i ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hmi.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase _ _ hi_mem]
    simp only [hmi.symm, ↓reduceIte]
    have hrest : (∑ l ∈ (Finset.univ.erase m).erase i,
        if l = m then (-1 : ℝ) else if l = i then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hli := (Finset.mem_erase.mp hl).1
      have hlm := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      simp [hlm, hli]
    rw [hrest]; ring
  choose eOf heOf using hex_e
  let T : Ambient d →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![⟪n i j, x⟫_ℝ, ⟪n j k, x⟫_ℝ, ⟪n k i, x⟫_ℝ]
      map_add' := fun x y => by
        ext r
        fin_cases r <;> exact inner_add_right _ _ _
      map_smul' := fun r x => by
        ext q
        fin_cases q <;> exact real_inner_smul_right _ _ _ }
  let uI : Ambient d := (2 : ℝ) • w₁ - w₂
  let uJ : Ambient d := -w₁ + (2 : ℝ) • w₂
  let uK : Ambient d := -w₁ - w₂
  have hx₀_l : ∀ l : Fin 6, l ∉ ({i, j, k} : Finset (Fin 6)) → ⟪a l, x₀⟫_ℝ = -1 := fun l hl => by
    rw [hx₀ l]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    simp [hl]
  have hw_m : ∀ l : Fin 6, l ∉ ({i, j, k} : Finset (Fin 6)) → ⟪a l, w₁⟫_ℝ = 0 ∧ ⟪a l, w₂⟫_ℝ = 0 :=
    fun l hl => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    push Not at hl
    rw [hw₁ l, hw₂ l]
    simp [hl.1, hl.2.1, hl.2.2]
  have hcone_I : ∀ (α β : ℝ), 0 < α → β < 0 → 0 < α + β →
      ∀ v : Ambient d, v = α • w₁ + β • w₂ → 0 ≤ T v 0 ∧ T v 2 ≤ 0 := by
    intro α β hα hβ hαβ v hv
    have hneg_t : ∀ t : ℝ, 2 / α < t → 2 / (-β) < t → 2 / (α + β) < t →
        ∀ l : Fin 6, l ≠ i → ⟪a l, x₀ + t • v⟫_ℝ < 0 := by
      intro t ht1 ht2 ht3 l hli
      rw [inner_add_right, real_inner_smul_right]
      by_cases hl_j : l = j
      · rw [hl_j]
        have hvj : ⟪a j, v⟫_ℝ = β := by
          rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
            hw₁ j, hw₂ j]
          simp [hij.symm, hjk]
        have hx0j : ⟪a j, x₀⟫_ℝ = 1 := by simp [hx₀ j]
        rw [hx0j, hvj]
        have hlt : 2 < t * (-β) := (div_lt_iff₀ (by linarith)).mp ht2
        linarith
      · by_cases hl_k : l = k
        · rw [hl_k]
          have hvk : ⟪a k, v⟫_ℝ = -(α + β) := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              hw₁ k, hw₂ k]
            simp [hik.symm, hjk.symm]
            ring
          have hx0k : ⟪a k, x₀⟫_ℝ = 1 := by simp [hx₀ k]
          rw [hx0k, hvk]
          have hlt : 2 < t * (α + β) := (div_lt_iff₀ hαβ).mp ht3
          linarith
        · have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hl_j, hl_k]
          have hvm : ⟪a l, v⟫_ℝ = 0 := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              (hw_m l hl_not).1, (hw_m l hl_not).2]
            ring
          rw [hx₀_l l hl_not, hvm]
          linarith
    have hall_t : ∀ t : ℝ, max (2 / α) (max (2 / (-β)) (2 / (α + β))) < t →
        0 < T (x₀ + t • v) 0 ∧ T (x₀ + t • v) 2 < 0 := fun t ht => by
      have hnt := hneg_t t (lt_of_le_of_lt (le_max_left _ _) ht)
        (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) ht)
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) ht)
      have h1 := hpos_of_other_neg i hnt j hij.symm
      have h2 := hpos_of_other_neg i hnt k hik.symm
      have h2' : ⟪n k i, x₀ + t • v⟫_ℝ < 0 := by
        rw [hnsym i k, inner_neg_left]; linarith
      exact ⟨h1, h2'⟩
    have hT0 : 0 ≤ T v 0 := by
      by_contra hv0
      push Not at hv0
      let M := max (max (2 / α) (max (2 / (-β)) (2 / (α + β)))) ((|T x₀ 0| + 1) / (-T v 0))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hgt : (|T x₀ 0| + 1) / (-T v 0) < M + 1 :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one M)
      have hmul : |T x₀ 0| + 1 < (M + 1) * (-T v 0) := (div_lt_iff₀ (by linarith)).mp hgt
      have hlin : T (x₀ + (M + 1) • v) 0 = T x₀ 0 + (M + 1) * T v 0 := by
        rw [map_add, map_smul]; rfl
      have hle : T x₀ 0 ≤ |T x₀ 0| := le_abs_self _
      linarith [ht.1]
    have hT2 : T v 2 ≤ 0 := by
      by_contra hv2
      push Not at hv2
      let M := max (max (2 / α) (max (2 / (-β)) (2 / (α + β)))) ((|T x₀ 2| + 1) / (T v 2))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hgt : (|T x₀ 2| + 1) / T v 2 < M + 1 :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one M)
      have hmul : |T x₀ 2| + 1 < (M + 1) * T v 2 := (div_lt_iff₀ hv2).mp hgt
      have hlin : T (x₀ + (M + 1) • v) 2 = T x₀ 2 + (M + 1) * T v 2 := by
        rw [map_add, map_smul]; rfl
      have hle : -T x₀ 2 ≤ |T x₀ 2| := neg_le_abs _
      linarith [ht.2]
    exact ⟨hT0, hT2⟩
  have hcone_J : ∀ (α β : ℝ), α < 0 → 0 < β → 0 < α + β →
      ∀ v : Ambient d, v = α • w₁ + β • w₂ → T v 0 ≤ 0 ∧ 0 ≤ T v 1 := by
    intro α β hα hβ hαβ v hv
    have hneg_t : ∀ t : ℝ, 2 / (-α) < t → 2 / β < t → 2 / (α + β) < t →
        ∀ l : Fin 6, l ≠ j → ⟪a l, x₀ + t • v⟫_ℝ < 0 := by
      intro t ht1 ht2 ht3 l hlj
      rw [inner_add_right, real_inner_smul_right]
      by_cases hl_i : l = i
      · rw [hl_i]
        have hvi : ⟪a i, v⟫_ℝ = α := by
          rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ i, hw₂ i]
          simp [hij, hik]
        have hx0i : ⟪a i, x₀⟫_ℝ = 1 := by simp [hx₀ i]
        rw [hx0i, hvi]
        have hlt : 2 < t * (-α) := (div_lt_iff₀ (by linarith)).mp ht1
        linarith
      · by_cases hl_k : l = k
        · rw [hl_k]
          have hvk : ⟪a k, v⟫_ℝ = -(α + β) := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ k, hw₂ k]
            simp [hik.symm, hjk.symm]; ring
          have hx0k : ⟪a k, x₀⟫_ℝ = 1 := by simp [hx₀ k]
          rw [hx0k, hvk]
          have hlt : 2 < t * (α + β) := (div_lt_iff₀ hαβ).mp ht3
          linarith
        · have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hl_i, hlj, hl_k]
          have hvm : ⟪a l, v⟫_ℝ = 0 := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              (hw_m l hl_not).1, (hw_m l hl_not).2]; ring
          rw [hx₀_l l hl_not, hvm]; linarith
    have hall_t : ∀ t : ℝ, max (2 / (-α)) (max (2 / β) (2 / (α + β))) < t →
        T (x₀ + t • v) 0 < 0 ∧ 0 < T (x₀ + t • v) 1 := fun t ht => by
      have hnt := hneg_t t (lt_of_le_of_lt (le_max_left _ _) ht)
        (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) ht)
        (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) ht)
      have h1 := hpos_of_other_neg j hnt i hij
      have h2 := hpos_of_other_neg j hnt k hjk.symm
      have h1' : ⟪n i j, x₀ + t • v⟫_ℝ < 0 := by
        rw [hnsym j i, inner_neg_left]; linarith
      exact ⟨h1', h2⟩
    have hT0 : T v 0 ≤ 0 := by
      by_contra hv0
      push Not at hv0
      let M := max (max (2 / (-α)) (max (2 / β) (2 / (α + β)))) ((|T x₀ 0| + 1) / (T v 0))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 0| + 1 < (M + 1) * T v 0 :=
        (div_lt_iff₀ hv0).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 0 = T x₀ 0 + (M + 1) * T v 0 := by
        rw [map_add, map_smul]; rfl
      have hle : -T x₀ 0 ≤ |T x₀ 0| := neg_le_abs _
      linarith [ht.1]
    have hT1 : 0 ≤ T v 1 := by
      by_contra hv1
      push Not at hv1
      let M := max (max (2 / (-α)) (max (2 / β) (2 / (α + β)))) ((|T x₀ 1| + 1) / (-T v 1))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 1| + 1 < (M + 1) * (-T v 1) :=
        (div_lt_iff₀ (by linarith)).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 1 = T x₀ 1 + (M + 1) * T v 1 := by
        rw [map_add, map_smul]; rfl
      have hle : T x₀ 1 ≤ |T x₀ 1| := le_abs_self _
      linarith [ht.2]
    exact ⟨hT0, hT1⟩
  have hcone_K : ∀ (α β : ℝ), α < 0 → β < 0 →
      ∀ v : Ambient d, v = α • w₁ + β • w₂ → T v 1 ≤ 0 ∧ 0 ≤ T v 2 := by
    intro α β hα hβ v hv
    have hneg_t : ∀ t : ℝ, 2 / (-α) < t → 2 / (-β) < t →
        ∀ l : Fin 6, l ≠ k → ⟪a l, x₀ + t • v⟫_ℝ < 0 := by
      intro t ht1 ht2 l hlk
      rw [inner_add_right, real_inner_smul_right]
      by_cases hl_i : l = i
      · rw [hl_i]
        have hvi : ⟪a i, v⟫_ℝ = α := by
          rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ i, hw₂ i]
          simp [hij, hik]
        have hx0i : ⟪a i, x₀⟫_ℝ = 1 := by simp [hx₀ i]
        rw [hx0i, hvi]
        have hlt : 2 < t * (-α) := (div_lt_iff₀ (by linarith)).mp ht1
        linarith
      · by_cases hl_j : l = j
        · rw [hl_j]
          have hvj : ⟪a j, v⟫_ℝ = β := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, hw₁ j, hw₂ j]
            simp [hij.symm, hjk]
          have hx0j : ⟪a j, x₀⟫_ℝ = 1 := by simp [hx₀ j]
          rw [hx0j, hvj]
          have hlt : 2 < t * (-β) := (div_lt_iff₀ (by linarith)).mp ht2
          linarith
        · have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hl_i, hl_j, hlk]
          have hvm : ⟪a l, v⟫_ℝ = 0 := by
            rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              (hw_m l hl_not).1, (hw_m l hl_not).2]; ring
          rw [hx₀_l l hl_not, hvm]; linarith
    have hall_t : ∀ t : ℝ, max (2 / (-α)) (2 / (-β)) < t →
        T (x₀ + t • v) 1 < 0 ∧ 0 < T (x₀ + t • v) 2 := fun t ht => by
      have hnt := hneg_t t (lt_of_le_of_lt (le_max_left _ _) ht)
        (lt_of_le_of_lt (le_max_right _ _) ht)
      have h1 := hpos_of_other_neg k hnt j hjk
      have h2 := hpos_of_other_neg k hnt i hik
      have h1' : ⟪n j k, x₀ + t • v⟫_ℝ < 0 := by
        rw [hnsym k j, inner_neg_left]; linarith
      exact ⟨h1', h2⟩
    have hT1 : T v 1 ≤ 0 := by
      by_contra hv1
      push Not at hv1
      let M := max (max (2 / (-α)) (2 / (-β))) ((|T x₀ 1| + 1) / (T v 1))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 1| + 1 < (M + 1) * T v 1 :=
        (div_lt_iff₀ hv1).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 1 = T x₀ 1 + (M + 1) * T v 1 := by
        rw [map_add, map_smul]; rfl
      have hle : -T x₀ 1 ≤ |T x₀ 1| := neg_le_abs _
      linarith [ht.1]
    have hT2 : 0 ≤ T v 2 := by
      by_contra hv2
      push Not at hv2
      let M := max (max (2 / (-α)) (2 / (-β))) ((|T x₀ 2| + 1) / (-T v 2))
      have ht := hall_t (M + 1) (lt_of_le_of_lt (le_max_left _ _) (lt_add_one M))
      have hmul : |T x₀ 2| + 1 < (M + 1) * (-T v 2) :=
        (div_lt_iff₀ (by linarith)).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one M))
      have hlin : T (x₀ + (M + 1) • v) 2 = T x₀ 2 + (M + 1) * T v 2 := by
        rw [map_add, map_smul]; rfl
      have hle : T x₀ 2 ≤ |T x₀ 2| := le_abs_self _
      linarith [ht.2]
    exact ⟨hT1, hT2⟩
  have hT_nz : ∀ r : Fin 3, T w₁ r ≠ 0 ∨ T w₂ r ≠ 0 := fun r => by
    by_contra hboth
    push Not at hboth
    have hzI : T uI r = 0 := by
      have h1 : T uI = (2 : ℝ) • T w₁ - T w₂ := by simp [uI, map_sub, map_smul]
      rw [h1]; simp [hboth.1, hboth.2]
    have hzJ : T uJ r = 0 := by
      have h1 : T uJ = - T w₁ + (2 : ℝ) • T w₂ := by simp [uJ, map_add, map_neg, map_smul]
      rw [h1]; simp [hboth.1, hboth.2]
    have hzK : T uK r = 0 := by
      have h1 : T uK = - T w₁ - T w₂ := by simp [uK, map_sub, map_neg]
      rw [h1]; simp [hboth.1, hboth.2]
    have huI_a : ∀ l : Fin 6,
        ⟪a l, x₀ + (3 : ℝ) • uI⟫_ℝ = ⟪a l, x₀⟫_ℝ + 3 * (2 * ⟪a l, w₁⟫_ℝ - ⟪a l, w₂⟫_ℝ) := fun l => by
      dsimp [uI]
      rw [inner_add_right, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
    have huJ_a : ∀ l : Fin 6,
        ⟪a l, x₀ + (3 : ℝ) • uJ⟫_ℝ = ⟪a l, x₀⟫_ℝ + 3 * (-⟪a l, w₁⟫_ℝ + 2 * ⟪a l, w₂⟫_ℝ) := fun l => by
      dsimp [uJ]
      rw [inner_add_right, real_inner_smul_right, inner_add_right, inner_neg_right,
        real_inner_smul_right]
    have huK_a : ∀ l : Fin 6,
        ⟪a l, x₀ + (3 : ℝ) • uK⟫_ℝ = ⟪a l, x₀⟫_ℝ + 3 * (-⟪a l, w₁⟫_ℝ - ⟪a l, w₂⟫_ℝ) := fun l => by
      dsimp [uK]
      rw [inner_add_right, real_inner_smul_right, inner_sub_right, inner_neg_right]
    have hnegI : ∀ l ≠ i, ⟪a l, x₀ + (3 : ℝ) • uI⟫_ℝ < 0 := fun l hli => by
      rw [huI_a l]
      by_cases hlj : l = j
      · rw [hlj, hx₀ j, hw₁ j, hw₂ j]; simp [hij.symm, hjk]; try norm_num
      · by_cases hlk : l = k
        · rw [hlk, hx₀ k, hw₁ k, hw₂ k]; simp [hik.symm, hjk.symm]; try norm_num
        · have hln : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hlj, hlk]
          rw [hx₀_l l hln, (hw_m l hln).1, (hw_m l hln).2]; norm_num
    have hnegJ : ∀ l ≠ j, ⟪a l, x₀ + (3 : ℝ) • uJ⟫_ℝ < 0 := fun l hlj => by
      rw [huJ_a l]
      by_cases hli : l = i
      · rw [hli, hx₀ i, hw₁ i, hw₂ i]; simp [hij, hik]; try norm_num
      · by_cases hlk : l = k
        · rw [hlk, hx₀ k, hw₁ k, hw₂ k]; simp [hik.symm, hjk.symm]; try norm_num
        · have hln : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hlj, hlk]
          rw [hx₀_l l hln, (hw_m l hln).1, (hw_m l hln).2]; norm_num
    have hnegK : ∀ l ≠ k, ⟪a l, x₀ + (3 : ℝ) • uK⟫_ℝ < 0 := fun l hlk => by
      rw [huK_a l]
      by_cases hli : l = i
      · rw [hli, hx₀ i, hw₁ i, hw₂ i]; simp [hij, hik]
      · by_cases hlj : l = j
        · rw [hlj, hx₀ j, hw₁ j, hw₂ j]; simp [hij.symm, hjk]
        · have hln : l ∉ ({i, j, k} : Finset (Fin 6)) := by simp [hli, hlj, hlk]
          rw [hx₀_l l hln, (hw_m l hln).1, (hw_m l hln).2]; norm_num
    fin_cases r
    · have hp1 : 0 < ⟪n i j, x₀ + (3 : ℝ) • uI⟫_ℝ := hpos_of_other_neg i hnegI j hij.symm
      have hp2 : ⟪n i j, x₀ + (3 : ℝ) • uJ⟫_ℝ < 0 := by
        have h := hpos_of_other_neg j hnegJ i hij
        rw [hnsym i j, inner_neg_left] at h; linarith
      have h1 : ⟪n i j, x₀⟫_ℝ = ⟪n i j, x₀ + (3 : ℝ) • uI⟫_ℝ := by
        have h : T uI 0 = 0 := hzI
        change ⟪n i j, uI⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      have h2 : ⟪n i j, x₀⟫_ℝ = ⟪n i j, x₀ + (3 : ℝ) • uJ⟫_ℝ := by
        have h : T uJ 0 = 0 := hzJ
        change ⟪n i j, uJ⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      linarith
    · have hp1 : 0 < ⟪n j k, x₀ + (3 : ℝ) • uJ⟫_ℝ := hpos_of_other_neg j hnegJ k hjk.symm
      have hp2 : ⟪n j k, x₀ + (3 : ℝ) • uK⟫_ℝ < 0 := by
        have h := hpos_of_other_neg k hnegK j hjk
        rw [hnsym j k, inner_neg_left] at h; linarith
      have h1 : ⟪n j k, x₀⟫_ℝ = ⟪n j k, x₀ + (3 : ℝ) • uJ⟫_ℝ := by
        have h : T uJ 1 = 0 := hzJ
        change ⟪n j k, uJ⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      have h2 : ⟪n j k, x₀⟫_ℝ = ⟪n j k, x₀ + (3 : ℝ) • uK⟫_ℝ := by
        have h : T uK 1 = 0 := hzK
        change ⟪n j k, uK⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      linarith
    · have hp1 : 0 < ⟪n k i, x₀ + (3 : ℝ) • uK⟫_ℝ := hpos_of_other_neg k hnegK i hik
      have hp2 : ⟪n k i, x₀ + (3 : ℝ) • uI⟫_ℝ < 0 := by
        have h := hpos_of_other_neg i hnegI k hik.symm
        rw [hnsym k i, inner_neg_left] at h; linarith
      have h1 : ⟪n k i, x₀⟫_ℝ = ⟪n k i, x₀ + (3 : ℝ) • uK⟫_ℝ := by
        have h : T uK 2 = 0 := hzK
        change ⟪n k i, uK⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      have h2 : ⟪n k i, x₀⟫_ℝ = ⟪n k i, x₀ + (3 : ℝ) • uI⟫_ℝ := by
        have h : T uI 2 = 0 := hzI
        change ⟪n k i, uI⟫_ℝ = 0 at h
        rw [inner_add_right, real_inner_smul_right, h]; ring
      linarith
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ {T w₁, T w₂}
  have hW_finrank : Module.finrank ℝ W = 2 := by
    have hle : Module.finrank ℝ W ≤ 2 := by
      have h1 : Module.finrank ℝ W ≤
          ({T w₁, T w₂} : Set (EuclideanSpace ℝ (Fin 3))).toFinset.card :=
        finrank_span_le_card ({T w₁, T w₂} : Set (EuclideanSpace ℝ (Fin 3)))
      have h2 : ({T w₁, T w₂} : Set (EuclideanSpace ℝ (Fin 3))).toFinset.card ≤ 2 := by
        simpa using Finset.card_le_two (a := T w₁) (b := T w₂)
      exact h1.trans h2
    have hge : 2 ≤ Module.finrank ℝ W := by
      by_contra hlt
      have hle1 : Module.finrank ℝ W ≤ 1 := by omega
      have hw1_W : T w₁ ∈ W := Submodule.subset_span (by simp)
      have hw2_W : T w₂ ∈ W := Submodule.subset_span (by simp)
      obtain ⟨v₀, hv₀, hv₀_ne⟩ : ∃ v₀ : Ambient d, (v₀ = w₁ ∨ v₀ = w₂) ∧ T v₀ 0 ≠ 0 := by
        rcases hT_nz 0 with h1 | h2
        · exact ⟨w₁, Or.inl rfl, h1⟩
        · exact ⟨w₂, Or.inr rfl, h2⟩
      have hv₀_W : T v₀ ∈ W := by rcases hv₀ with rfl | rfl <;> assumption
      have hv₀_ne0 : T v₀ ≠ 0 := fun h => hv₀_ne (by rw [h]; rfl)
      have hW_eq : W = Submodule.span ℝ {T v₀} := by
        refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀_W)
        · rw [finrank_span_singleton hv₀_ne0]; exact hle1
      have hprop : ∀ v : Ambient d, (∃ c₁ c₂ : ℝ, v = c₁ • w₁ + c₂ • w₂) →
          ∃ μ : ℝ, T v = μ • T v₀ := fun v ⟨c₁, c₂, hv⟩ => by
        have hTv_W : T v ∈ W := by
          rw [hv, map_add, map_smul, map_smul]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ hw1_W) (Submodule.smul_mem _ _ hw2_W)
        rw [hW_eq, Submodule.mem_span_singleton] at hTv_W
        exact hTv_W.imp fun μ hμ => hμ.symm
      let β := T v₀ 1 / T v₀ 0
      let γ := T v₀ 2 / T v₀ 0
      have hscale : ∀ v : Ambient d, (∃ c₁ c₂ : ℝ, v = c₁ • w₁ + c₂ • w₂) →
          T v 1 = β * T v 0 ∧ T v 2 = γ * T v 0 := fun v hv => by
        obtain ⟨μ, hμ⟩ := hprop v hv
        constructor
        · have h0 : T v 0 = μ * T v₀ 0 := by rw [hμ]; rfl
          have h1 : T v 1 = μ * T v₀ 1 := by rw [hμ]; rfl
          rw [h0, h1]; dsimp [β]; field_simp [hv₀_ne]
        · have h0 : T v 0 = μ * T v₀ 0 := by rw [hμ]; rfl
          have h2 : T v 2 = μ * T v₀ 2 := by rw [hμ]; rfl
          rw [h0, h2]; dsimp [γ]; field_simp [hv₀_ne]
      have h_no_vanish_I : 0 < T uI 0 := by
        have hge0 := (hcone_I 2 (-1) (by norm_num) (by norm_num) (by norm_num) uI
          (by dsimp [uI]; module)).1
        refine lt_of_le_of_ne hge0 (Ne.symm fun h0 => ?_)
        have hI_pert : ∀ ε : ℝ, |ε| < 1 / 4 →
            0 ≤ T (uI + ε • v₀) 0 := fun ε hε => by
          rcases hv₀ with hvw | hvw
          · exact (hcone_I (2 + ε) (-1) (by linarith [abs_lt.mp hε]) (by norm_num)
              (by linarith [abs_lt.mp hε]) (uI + ε • v₀) (by dsimp [uI]; rw [hvw]; module)).1
          · exact (hcone_I 2 (-1 + ε) (by norm_num) (by linarith [abs_lt.mp hε])
              (by linarith [abs_lt.mp hε]) (uI + ε • v₀) (by dsimp [uI]; rw [hvw]; module)).1
        let ε : ℝ := if T v₀ 0 > 0 then -(1 / 8) else 1 / 8
        have hε_abs : |ε| < 1 / 4 := by dsimp [ε]; split_ifs <;> norm_num
        have hlin : T (uI + ε • v₀) 0 = T uI 0 + ε * T v₀ 0 := by
          rw [map_add, map_smul]; rfl
        have hpos_ge := hI_pert ε hε_abs
        rw [hlin, h0, zero_add] at hpos_ge
        dsimp [ε] at hpos_ge
        split_ifs at hpos_ge with hpos
        · linarith
        · have hneg : T v₀ 0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv₀_ne
          linarith
      have h_no_vanish_J : T uJ 0 < 0 := by
        have hle0 := (hcone_J (-1) 2 (by norm_num) (by norm_num) (by norm_num) uJ
          (by dsimp [uJ]; module)).1
        refine lt_of_le_of_ne hle0 fun h0 => ?_
        have hJ_pert : ∀ ε : ℝ, |ε| < 1 / 4 →
            T (uJ + ε • v₀) 0 ≤ 0 := fun ε hε => by
          rcases hv₀ with hvw | hvw
          · exact (hcone_J (-1 + ε) 2 (by linarith [abs_lt.mp hε]) (by norm_num)
              (by linarith [abs_lt.mp hε]) (uJ + ε • v₀) (by dsimp [uJ]; rw [hvw]; module)).1
          · exact (hcone_J (-1) (2 + ε) (by norm_num) (by linarith [abs_lt.mp hε])
              (by linarith [abs_lt.mp hε]) (uJ + ε • v₀) (by dsimp [uJ]; rw [hvw]; module)).1
        let ε : ℝ := if T v₀ 0 > 0 then 1 / 8 else -(1 / 8)
        have hε_abs : |ε| < 1 / 4 := by dsimp [ε]; split_ifs <;> norm_num
        have hlin : T (uJ + ε • v₀) 0 = T uJ 0 + ε * T v₀ 0 := by
          rw [map_add, map_smul]; rfl
        have hneg_le := hJ_pert ε hε_abs
        rw [hlin, h0, zero_add] at hneg_le
        dsimp [ε] at hneg_le
        split_ifs at hneg_le with hpos
        · linarith
        · have hneg : T v₀ 0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv₀_ne
          linarith
      have hβ_ne : β ≠ 0 := by
        intro hβ0
        have hw1_1 : T w₁ 1 = 0 := by rw [(hscale w₁ ⟨1, 0, by simp⟩).1, hβ0, zero_mul]
        have hw2_1 : T w₂ 1 = 0 := by rw [(hscale w₂ ⟨0, 1, by simp⟩).1, hβ0, zero_mul]
        rcases hT_nz 1 with h | h
        · exact h hw1_1
        · exact h hw2_1
      have hγ_ne : γ ≠ 0 := by
        intro hγ0
        have hw1_2 : T w₁ 2 = 0 := by rw [(hscale w₁ ⟨1, 0, by simp⟩).2, hγ0, zero_mul]
        have hw2_2 : T w₂ 2 = 0 := by rw [(hscale w₂ ⟨0, 1, by simp⟩).2, hγ0, zero_mul]
        rcases hT_nz 2 with h | h
        · exact h hw1_2
        · exact h hw2_2
      have hK_ne0 : T uK 0 ≠ 0 := by
        intro h0
        have hK1 : T uK 1 = 0 := by rw [(hscale uK ⟨-1, -1, by dsimp [uK]; module⟩).1, h0, mul_zero]
        have hcK1 := hK1
        have hK_pert : ∀ ε : ℝ, |ε| < 1 / 4 → T (uK + ε • v₀) 1 ≤ 0 := fun ε hε => by
          rcases hv₀ with hvw | hvw
          · exact (hcone_K (-1 + ε) (-1) (by linarith [abs_lt.mp hε]) (by norm_num)
              (uK + ε • v₀) (by dsimp [uK]; rw [hvw]; module)).1
          · exact (hcone_K (-1) (-1 + ε) (by norm_num) (by linarith [abs_lt.mp hε])
              (uK + ε • v₀) (by dsimp [uK]; rw [hvw]; module)).1
        have hv0_1_ne : T v₀ 1 ≠ 0 := by
          rw [(hscale v₀ (by rcases hv₀ with rfl | rfl; exact ⟨1, 0, by simp⟩; exact ⟨0, 1, by simp⟩)).1]
          exact mul_ne_zero hβ_ne hv₀_ne
        let ε : ℝ := if T v₀ 1 > 0 then 1 / 8 else -(1 / 8)
        have hε_abs : |ε| < 1 / 4 := by dsimp [ε]; split_ifs <;> norm_num
        have hlin : T (uK + ε • v₀) 1 = T uK 1 + ε * T v₀ 1 := by
          rw [map_add, map_smul]; rfl
        have hle := hK_pert ε hε_abs
        rw [hlin, hcK1, zero_add] at hle
        dsimp [ε] at hle
        split_ifs at hle with hpos
        · linarith
        · have hneg : T v₀ 1 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hv0_1_ne
          linarith
      rcases lt_or_gt_of_ne hK_ne0 with hK_neg | hK_pos
      · have hJ1 : 0 ≤ T uJ 1 := (hcone_J (-1) 2 (by norm_num) (by norm_num) (by norm_num) uJ
          (by dsimp [uJ]; module)).2
        have hK1 : T uK 1 ≤ 0 := (hcone_K (-1) (-1) (by norm_num) (by norm_num) uK
          (by dsimp [uK]; module)).1
        rw [(hscale uJ ⟨-1, 2, by dsimp [uJ]; module⟩).1] at hJ1
        rw [(hscale uK ⟨-1, -1, by dsimp [uK]; module⟩).1] at hK1
        have hβ_le : β ≤ 0 := nonpos_of_mul_nonneg_left hJ1 h_no_vanish_J
        have hβ_ge : 0 ≤ β := nonneg_of_mul_nonpos_left hK1 hK_neg
        exact hβ_ne (le_antisymm hβ_le hβ_ge)
      · have hI2 : T uI 2 ≤ 0 := (hcone_I 2 (-1) (by norm_num) (by norm_num) (by norm_num) uI
          (by dsimp [uI]; module)).2
        have hK2 : 0 ≤ T uK 2 := (hcone_K (-1) (-1) (by norm_num) (by norm_num) uK
          (by dsimp [uK]; module)).2
        rw [(hscale uI ⟨2, -1, by dsimp [uI]; module⟩).2] at hI2
        rw [(hscale uK ⟨-1, -1, by dsimp [uK]; module⟩).2] at hK2
        have hγ_le : γ ≤ 0 := nonpos_of_mul_nonpos_left hI2 h_no_vanish_I
        have hγ_ge : 0 ≤ γ := nonneg_of_mul_nonneg_left hK2 hK_pos
        exact hγ_ne (le_antisymm hγ_le hγ_ge)
    omega
  have hW_ne_top : W ≠ ⊤ := by
    intro htop
    have h3 : Module.finrank ℝ W =
        Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) := by rw [htop]
    rw [hW_finrank, finrank_top, finrank_euclideanSpace_fin] at h3
    norm_num at h3
  have hW_orth_ne_bot : Wᗮ ≠ ⊥ := by
    rwa [Ne, Submodule.orthogonal_eq_bot_iff]
  obtain ⟨b, hb_mem, hb_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_orth_ne_bot
  have hb_w1 : ⟪b, T w₁⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hb_mem (T w₁) (Submodule.subset_span (by simp))
  have hb_w2 : ⟪b, T w₂⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hb_mem (T w₂) (Submodule.subset_span (by simp))
  have hW_orth_eq : (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ = W := by
    have hle : W ≤ (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
      rw [← Submodule.orthogonal_orthogonal W]
      exact Submodule.orthogonal_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hb_mem))
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))
    rw [finrank_span_singleton hb_ne, finrank_euclideanSpace_fin] at hsum
    omega
  have h_beta_zero : ∀ x_c : Ambient d,
      (∀ m ∈ M₀, ⟪a m, x_c⟫_ℝ < 0) → ⟪b, T x_c⟫_ℝ = 0 := fun x_c hx_c => by
    refine hyperplane_miss_orthants_eq_zero hb_ne ⟪b, T x_c⟫_ℝ ?_ ?_
    · intro z hz_pos hdot
      have hz_diff : z - T x_c ∈ (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_sub_left, real_inner_comm b z, real_inner_comm b (T x_c), hdot, sub_self]
      rw [hW_orth_eq, Submodule.mem_span_pair] at hz_diff
      obtain ⟨lam1, lam2, hcomb⟩ := hz_diff
      let x := x_c + lam1 • w₁ + lam2 • w₂
      have hTx : T x = z := by
        have h1 : T x = T x_c + (lam1 • T w₁ + lam2 • T w₂) := by
          dsimp [x]
          rw [map_add, map_add, map_smul, map_smul]; abel
        rw [h1, hcomb]; abel
      have hx_m : ∀ m ∈ M₀, ⟪a m, x⟫_ℝ < 0 := fun m hm => by
        have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        dsimp [x]
        rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          (hw_m m hm_not).1, (hw_m m hm_not).2]
        simpa using hx_c m hm
      have hx_ne0 : x ≠ 0 := by
        have hexm : M₀.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨m, hm⟩ := hexm
        intro hx0
        have := hx_m m hm
        rw [hx0, inner_zero_right] at this
        exact lt_irrefl 0 this
      have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne0
      let u_x : Ambient d := ‖x‖⁻¹ • x
      have hu_ball : u_x ∈ unitBall d := by
        change dist (‖x‖⁻¹ • x) 0 ≤ 1
        rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx_norm_pos.le),
          inv_mul_cancel₀ hx_norm_pos.ne']
      rw [hcov] at hu_ball
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu_ball
      have hl_not_M : l ∉ M₀ := fun hlM => by
        have hge := hinner_a_ge l hl
        have hlt := hx_m l hlM
        dsimp [u_x] at hge
        rw [real_inner_smul_right] at hge
        have hge' := nonneg_of_mul_nonneg_right hge (inv_pos.mpr hx_norm_pos)
        linarith
      have hl_ijk : l = i ∨ l = j ∨ l = k := by
        by_contra hnone
        push Not at hnone
        exact hl_not_M (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hnone⟩)
      have hz0 : 0 < ⟪n i j, x⟫_ℝ := by simpa [← hTx, T] using hz_pos 0
      have hz1 : 0 < ⟪n j k, x⟫_ℝ := by simpa [← hTx, T] using hz_pos 1
      have hz2 : 0 < ⟪n k i, x⟫_ℝ := by simpa [← hTx, T] using hz_pos 2
      rcases hl_ijk with hli | hlj | hlk
      · rw [hli] at hl
        have hle := (hsep_all i (hS_univ ▸ Finset.mem_univ i) k
          (hS_univ ▸ Finset.mem_univ k) hik).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right, hnsym k i, inner_neg_left] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlj] at hl
        have hle := (hsep_all j (hS_univ ▸ Finset.mem_univ j) i
          (hS_univ ▸ Finset.mem_univ i) hij.symm).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right, hnsym i j, inner_neg_left] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlk] at hl
        have hle := (hsep_all k (hS_univ ▸ Finset.mem_univ k) j
          (hS_univ ▸ Finset.mem_univ j) hjk.symm).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right, hnsym j k, inner_neg_left] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
    · intro z hz_neg hdot
      have hz_diff : z - T x_c ∈ (Submodule.span ℝ ({b} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_sub_left, real_inner_comm b z, real_inner_comm b (T x_c), hdot, sub_self]
      rw [hW_orth_eq, Submodule.mem_span_pair] at hz_diff
      obtain ⟨lam1, lam2, hcomb⟩ := hz_diff
      let x := x_c + lam1 • w₁ + lam2 • w₂
      have hTx : T x = z := by
        have h1 : T x = T x_c + (lam1 • T w₁ + lam2 • T w₂) := by
          dsimp [x]; rw [map_add, map_add, map_smul, map_smul]; abel
        rw [h1, hcomb]; abel
      have hx_m : ∀ m ∈ M₀, ⟪a m, x⟫_ℝ < 0 := fun m hm => by
        have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
          simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        dsimp [x]
        rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          (hw_m m hm_not).1, (hw_m m hm_not).2]
        simpa using hx_c m hm
      have hx_ne0 : x ≠ 0 := by
        have hexm : M₀.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨m, hm⟩ := hexm
        intro hx0
        have := hx_m m hm
        rw [hx0, inner_zero_right] at this
        exact lt_irrefl 0 this
      have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne0
      let u_x : Ambient d := ‖x‖⁻¹ • x
      have hu_ball : u_x ∈ unitBall d := by
        change dist (‖x‖⁻¹ • x) 0 ≤ 1
        rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx_norm_pos.le),
          inv_mul_cancel₀ hx_norm_pos.ne']
      rw [hcov] at hu_ball
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu_ball
      have hl_not_M : l ∉ M₀ := fun hlM => by
        have hge := hinner_a_ge l hl
        have hlt := hx_m l hlM
        dsimp [u_x] at hge
        rw [real_inner_smul_right] at hge
        have hge' := nonneg_of_mul_nonneg_right hge (inv_pos.mpr hx_norm_pos)
        linarith
      have hl_ijk : l = i ∨ l = j ∨ l = k := by
        by_contra hnone
        push Not at hnone
        exact hl_not_M (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hnone⟩)
      have hz0 : ⟪n i j, x⟫_ℝ < 0 := by simpa [← hTx, T] using hz_neg 0
      have hz1 : ⟪n j k, x⟫_ℝ < 0 := by simpa [← hTx, T] using hz_neg 1
      have hz2 : ⟪n k i, x⟫_ℝ < 0 := by simpa [← hTx, T] using hz_neg 2
      rcases hl_ijk with hli | hlj | hlk
      · rw [hli] at hl
        have hle := (hsep_all i (hS_univ ▸ Finset.mem_univ i) j
          (hS_univ ▸ Finset.mem_univ j) hij).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlj] at hl
        have hle := (hsep_all j (hS_univ ▸ Finset.mem_univ j) k
          (hS_univ ▸ Finset.mem_univ k) hjk).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
      · rw [hlk] at hl
        have hle := (hsep_all k (hS_univ ▸ Finset.mem_univ k) i
          (hS_univ ▸ Finset.mem_univ i) hik.symm).1 u_x hl
        dsimp [u_x] at hle
        rw [real_inner_smul_right] at hle
        have := nonneg_of_mul_nonneg_right hle (inv_pos.mpr hx_norm_pos)
        linarith
  have hbx0 : ⟪b, T x₀⟫_ℝ = 0 := h_beta_zero x₀ fun m hm => by
    have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
      simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hx₀_l m hm_not]; norm_num
  have hbe : ∀ m : Fin 6, ∀ hm : m ∈ M₀, ⟪b, T (eOf m hm)⟫_ℝ = 0 := fun m hm => by
    have hxm : ∀ l ∈ M₀, ⟪a l, x₀ + eOf m hm⟫_ℝ < 0 := fun l hl => by
      have hl_not : l ∉ ({i, j, k} : Finset (Fin 6)) := by
        simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have hli : l ≠ i := (Finset.mem_filter.mp hl).2.1
      rw [inner_add_right, hx₀_l l hl_not, heOf m hm l]
      split_ifs <;> norm_num
    have hsum0 := h_beta_zero (x₀ + eOf m hm) hxm
    rw [map_add, inner_add_right, hbx0, zero_add] at hsum0
    exact hsum0
  let v : Ambient d := b 0 • n i j + b 1 • n j k + b 2 • n k i
  have hv_inner : ∀ x : Ambient d, ⟪v, x⟫_ℝ = ⟪b, T x⟫_ℝ := fun x => by
    conv_rhs => rw [PiLp.inner_apply, Fin.sum_univ_three]
    dsimp [v, T]
    simp only [inner_add_left, real_inner_smul_left, real_inner_eq_re_inner,
      RCLike.inner_apply, conj_trivial]
    change b 0 * ⟪n i j, x⟫_ℝ + b 1 * ⟪n j k, x⟫_ℝ + b 2 * ⟪n k i, x⟫_ℝ =
      T x 0 * b 0 + T x 1 * b 1 + T x 2 * b 2
    have ht0 : T x 0 = ⟪n i j, x⟫_ℝ := rfl
    have ht1 : T x 1 = ⟪n j k, x⟫_ℝ := rfl
    have ht2 : T x 2 = ⟪n k i, x⟫_ℝ := rfl
    rw [ht0, ht1, ht2]
    ring
  have hv0 : v = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    let x := v
    let basisSum : Ambient d :=
      (∑ m ∈ M₀, (-⟪a m, x⟫_ℝ) • (if hm : m ∈ M₀ then eOf m hm - w₁ else 0)) +
        ⟪a i, x⟫_ℝ • w₁ + ⟪a j, x⟫_ℝ • w₂
    let y : Ambient d := x - basisSum
    have hy_m : ∀ m ∈ M₀, ⟪a m, y⟫_ℝ = 0 := fun m hm => by
      have hm_not : m ∉ ({i, j, k} : Finset (Fin 6)) := by
        simp only [M₀, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have hmi : m ≠ i := (Finset.mem_filter.mp hm).2.1
      have hbasis : ⟪a m, basisSum⟫_ℝ = ⟪a m, x⟫_ℝ := by
        dsimp [basisSum]
        rw [inner_add_right, inner_add_right, inner_sum]
        have hsum : (∑ m' ∈ M₀, ⟪a m, (-⟪a m', x⟫_ℝ) •
            (if hm' : m' ∈ M₀ then eOf m' hm' - w₁ else 0)⟫_ℝ) = ⟪a m, x⟫_ℝ := by
          rw [Finset.sum_eq_single m]
          · simp only [hm, ↓reduceDIte, real_inner_smul_right, inner_sub_right,
              heOf m hm m, ↓reduceIte, (hw_m m hm_not).1]
            ring
          · intro m' hm' hm'm
            simp only [hm', ↓reduceDIte, real_inner_smul_right, inner_sub_right,
              heOf m' hm' m, hm'm.symm, hmi, ↓reduceIte, (hw_m m hm_not).1]
            ring
          · intro hm'; exact False.elim (hm' hm)
        rw [hsum, real_inner_smul_right, real_inner_smul_right,
          (hw_m m hm_not).1, (hw_m m hm_not).2]
        ring
      dsimp [y]
      rw [inner_sub_right, hbasis, sub_self]
    have hy_i : ⟪a i, y⟫_ℝ = 0 := by
      have hbasis : ⟪a i, basisSum⟫_ℝ = ⟪a i, x⟫_ℝ := by
        dsimp [basisSum]
        rw [inner_add_right, inner_add_right, inner_sum]
        have hsum : (∑ m' ∈ M₀, ⟪a i, (-⟪a m', x⟫_ℝ) •
            (if hm' : m' ∈ M₀ then eOf m' hm' - w₁ else 0)⟫_ℝ) = 0 := by
          refine Finset.sum_eq_zero fun m' hm' => ?_
          have hm'i : i ≠ m' := ((Finset.mem_filter.mp hm').2.1).symm
          simp only [hm', ↓reduceDIte, real_inner_smul_right, inner_sub_right,
            heOf m' hm' i, hm'i, ↓reduceIte, hw₁ i]
          ring
        rw [hsum, real_inner_smul_right, real_inner_smul_right, hw₁ i, hw₂ i]
        simp [hij, hik]
      dsimp [y]
      rw [inner_sub_right, hbasis, sub_self]
    have hy_j : ⟪a j, y⟫_ℝ = 0 := by
      have hbasis : ⟪a j, basisSum⟫_ℝ = ⟪a j, x⟫_ℝ := by
        dsimp [basisSum]
        rw [inner_add_right, inner_add_right, inner_sum]
        have hsum : (∑ m' ∈ M₀, ⟪a j, (-⟪a m', x⟫_ℝ) •
            (if hm' : m' ∈ M₀ then eOf m' hm' - w₁ else 0)⟫_ℝ) = 0 := by
          refine Finset.sum_eq_zero fun m' hm' => ?_
          have hm'j : j ≠ m' := ((Finset.mem_filter.mp hm').2.2.1).symm
          simp only [hm', ↓reduceDIte, real_inner_smul_right, inner_sub_right,
            heOf m' hm' j, hm'j, ↓reduceIte, hw₁ j, hij.symm, hjk]
          ring
        rw [hsum, real_inner_smul_right, real_inner_smul_right, hw₁ j, hw₂ j]
        simp [hij.symm, hjk]
      dsimp [y]
      rw [inner_sub_right, hbasis, sub_self]
    have hy_k : ⟪a k, y⟫_ℝ = 0 := by
      have htot : ∑ l : Fin 6, ⟪a l, y⟫_ℝ = 0 := by
        rw [← sum_inner, ha_sum0, inner_zero_left]
      have hsplit : ∑ l ∈ Finset.univ.erase k, ⟪a l, y⟫_ℝ = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlk := (Finset.mem_erase.mp hl).1
        by_cases hli : l = i
        · exact hli ▸ hy_i
        · by_cases hlj : l = j
          · exact hlj ▸ hy_j
          · exact hy_m l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hli, hlj, hlk⟩)
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), hsplit, add_zero] at htot
      exact htot
    have hy_all : ∀ l : Fin 6, ⟪a l, y⟫_ℝ = 0 := fun l => by
      by_cases hli : l = i
      · exact hli ▸ hy_i
      · by_cases hlj : l = j
        · exact hlj ▸ hy_j
        · by_cases hlk : l = k
          · exact hlk ▸ hy_k
          · exact hy_m l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hli, hlj, hlk⟩)
    have hy_n : ∀ p q : Fin 6, ⟪n p q, y⟫_ℝ = 0 :=
      central_partition_normal_rank C hcov n hnnotS
        (fun p hp q hq hpq => ⟨(hsep_all p hp q hq hpq).1, (hsep_all p hp q hq hpq).2.1⟩)
        hnsym hy_all
    have hvy : ⟪v, y⟫_ℝ = 0 := by
      dsimp [v]
      simp only [inner_add_left, real_inner_smul_left, hy_n i j, hy_n j k, hy_n k i,
        mul_zero, add_zero]
    have hvb : ⟪v, basisSum⟫_ℝ = 0 := by
      dsimp [basisSum]
      rw [inner_add_right, inner_add_right, inner_sum]
      have hsum : (∑ m ∈ M₀, ⟪v, (-⟪a m, x⟫_ℝ) •
          (if hm : m ∈ M₀ then eOf m hm - w₁ else 0)⟫_ℝ) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [dif_pos hm, real_inner_smul_right]
        have h1 : ⟪v, eOf m hm - w₁⟫_ℝ = 0 := by
          rw [inner_sub_right, hv_inner, hbe m hm, hv_inner, hb_w1, sub_zero]
        rw [h1, mul_zero]
      rw [hsum, real_inner_smul_right, real_inner_smul_right, hv_inner, hb_w1,
        hv_inner, hb_w2]
      ring
    have hvx : ⟪v, x⟫_ℝ = ⟪v, y⟫_ℝ + ⟪v, basisSum⟫_ℝ := by
      dsimp [y]
      rw [inner_sub_right]
      ring
    rw [hvy, hvb, add_zero] at hvx
    exact hvx
  have hb_nz : b 0 ≠ 0 ∨ b 1 ≠ 0 ∨ b 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hb_ne
    ext r
    fin_cases r <;> simp [hall]
  exact ⟨b 0, b 1, b 2, hb_nz, hv0⟩

private lemma finrank_triangle_span_le {d n : ℕ} (v : Fin n → Fin n → Ambient d)
    (hanti : ∀ i j, v j i = - v i j) (hne : ∀ i j, i ≠ j → v i j ≠ 0)
    (htri : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      ∃ c₁ c₂ c₃ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
        c₁ • v i j + c₂ • v j k + c₃ • v k i = 0) :
    ∀ k : ℕ, ∀ A : Finset (Fin n), A.Nonempty → A.card = k →
      Module.finrank ℝ (Submodule.span ℝ {x | ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ x = v i j}) ≤ k - 1 := by
  intro k
  induction k with
  | zero =>
    intro A hAne hcard
    exfalso
    exact hAne.ne_empty (Finset.card_eq_zero.mp hcard)
  | succ k ih =>
    intro A hAne hcard
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
      subst hx
      have hset : {y | ∃ i ∈ ({x} : Finset (Fin n)), ∃ j ∈ ({x} : Finset (Fin n)),
          i ≠ j ∧ y = v i j} = ∅ := by
        ext y
        simp only [Finset.mem_singleton, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i, rfl, j, rfl, hij, _⟩
        exact hij rfl
      rw [hset, Submodule.span_empty, finrank_bot]
    · obtain ⟨x, hxA⟩ := hAne
      let B := A.erase x
      have hB_card : B.card = k := by
        rw [Finset.card_erase_of_mem hxA, hcard]; simp
      have hB_ne : B.Nonempty := Finset.card_pos.mp (by omega)
      have hih := ih B hB_ne hB_card
      let W_A := Submodule.span ℝ {y | ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ y = v i j}
      let W_B := Submodule.span ℝ {y | ∃ i ∈ B, ∃ j ∈ B, i ≠ j ∧ y = v i j}
      have hex_w0 : ∃ w₀ : Ambient d, W_A ≤ W_B ⊔ Submodule.span ℝ {w₀} := by
        by_cases hall : ∀ b ∈ B, v x b ∈ W_B
        · refine ⟨0, Submodule.span_le.mpr ?_⟩
          rintro y ⟨i, hiA, j, hjA, hij, rfl⟩
          rw [SetLike.mem_coe]
          by_cases hix : i = x
          · subst hix
            have hjB : j ∈ B := Finset.mem_erase.mpr ⟨hij.symm, hjA⟩
            exact Submodule.mem_sup_left (hall j hjB)
          · by_cases hjx : j = x
            · subst hjx
              have hiB : i ∈ B := Finset.mem_erase.mpr ⟨hij, hiA⟩
              rw [hanti j i]
              exact Submodule.neg_mem _ (Submodule.mem_sup_left (hall i hiB))
            · have hiB : i ∈ B := Finset.mem_erase.mpr ⟨hix, hiA⟩
              have hjB : j ∈ B := Finset.mem_erase.mpr ⟨hjx, hjA⟩
              exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, hiB, j, hjB, hij, rfl⟩)
        · push Not at hall
          obtain ⟨b₀, hb₀B, hb₀_not⟩ := hall
          have hb₀_ne_x : b₀ ≠ x := (Finset.mem_erase.mp hb₀B).1
          refine ⟨v x b₀, Submodule.span_le.mpr ?_⟩
          have hxb : ∀ b ∈ B, v x b ∈ W_B ⊔ Submodule.span ℝ {v x b₀} := fun b hbB => by
            by_cases hbb0 : b = b₀
            · subst hbb0
              exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
            · have hbx_ne : b ≠ x := (Finset.mem_erase.mp hbB).1
              obtain ⟨c₁, c₂, c₃, hcnz, hceq⟩ := htri x b₀ b hb₀_ne_x.symm (Ne.symm hbb0) hbx_ne.symm
              have hc₃_ne : c₃ ≠ 0 := by
                intro hc₃
                rw [hc₃, zero_smul, add_zero] at hceq
                have hc₁_ne : c₁ ≠ 0 := by
                  intro hc₁
                  rw [hc₁, zero_smul, zero_add, smul_eq_zero] at hceq
                  rcases hceq with hc₂ | hv0
                  · exact hcnz.elim (absurd hc₁) (fun h => h.elim (absurd hc₂) (absurd hc₃))
                  · exact hne b₀ b (Ne.symm hbb0) hv0
                have hv_eq : v x b₀ = (-c₂ / c₁) • v b₀ b := by
                  have h1 := congrArg (c₁⁻¹ • ·) hceq
                  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hc₁_ne, one_smul,
                    smul_zero] at h1
                  have h2 := eq_neg_of_add_eq_zero_left h1
                  rw [h2, ← neg_smul]
                  congr 1; ring
                apply hb₀_not
                rw [hv_eq]
                exact Submodule.smul_mem _ _
                  (Submodule.subset_span ⟨b₀, hb₀B, b, hbB, Ne.symm hbb0, rfl⟩)
              have hv_eq : v x b = (c₁ / c₃) • v x b₀ + (c₂ / c₃) • v b₀ b := by
                rw [hanti x b, smul_neg] at hceq
                have hsub : c₁ • v x b₀ + c₂ • v b₀ b = c₃ • v x b :=
                  eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hceq)
                have h1 := congrArg (c₃⁻¹ • ·) hsub
                rw [smul_add, smul_smul, smul_smul, smul_smul,
                  inv_mul_cancel₀ hc₃_ne, one_smul] at h1
                rw [← h1]
                congr 1 <;> congr 1 <;> ring
              rw [hv_eq]
              refine Submodule.add_mem _ ?_ ?_
              · exact Submodule.mem_sup_right
                  (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
              · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
                  (Submodule.subset_span ⟨b₀, hb₀B, b, hbB, Ne.symm hbb0, rfl⟩))
          rintro y ⟨i, hiA, j, hjA, hij, rfl⟩
          rw [SetLike.mem_coe]
          by_cases hix : i = x
          · subst hix
            exact hxb j (Finset.mem_erase.mpr ⟨hij.symm, hjA⟩)
          · by_cases hjx : j = x
            · rw [hjx, hanti x i]
              exact Submodule.neg_mem _ (hxb i (Finset.mem_erase.mpr ⟨hix, hiA⟩))
            · have hiB : i ∈ B := Finset.mem_erase.mpr ⟨hix, hiA⟩
              have hjB : j ∈ B := Finset.mem_erase.mpr ⟨hjx, hjA⟩
              exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, hiB, j, hjB, hij, rfl⟩)
      obtain ⟨w₀, hw₀⟩ := hex_w0
      have hfin_le : Module.finrank ℝ W_A ≤
          Module.finrank ℝ W_B + Module.finrank ℝ (Submodule.span ℝ ({w₀} : Set (Ambient d))) :=
        (Submodule.finrank_mono hw₀).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
      have hspan_w0 : Module.finrank ℝ (Submodule.span ℝ ({w₀} : Set (Ambient d))) ≤ 1 := by
        have h1 : Module.finrank ℝ (Submodule.span ℝ ({w₀} : Set (Ambient d))) ≤
            ({w₀} : Set (Ambient d)).toFinset.card :=
          finrank_span_le_card ({w₀} : Set (Ambient d))
        have h2 : ({w₀} : Set (Ambient d)).toFinset.card ≤ 1 := by simp
        exact h1.trans h2
      change Module.finrank ℝ W_B ≤ k - 1 at hih
      change Module.finrank ℝ W_A ≤ (k + 1) - 1
      omega

private lemma fin_succ_ne {n : ℕ} {a b : Fin n} (h : a ≠ b) : a.succ ≠ b.succ :=
  fun heq => h (Fin.ext (Nat.succ.inj (congrArg Fin.val heq)))

private def castPair {n m : ℕ} (h : n = m) (e : Pairs n) : Pairs m :=
  ⟨(Fin.cast h e.1.1, Fin.cast h e.1.2), e.2⟩

private lemma castPair_rfl {n : ℕ} (e : Pairs n) : castPair rfl e = e :=
  Subtype.ext (Prod.ext rfl rfl)

private inductive TreeShape (d : ℕ) : ℕ → Type
  | unit : TreeShape d 0
  | star (q : Fin 6)
      (perm : Equiv.Perm (Fin (q.1 + 1)))
      (I : {I : Fin q.1 → Fin d // Function.Injective I})
      (k₀ : Fin q.1 → Fin q.1)
      (root : Fin q.1 → Fin q.1)
      (useLeft : Pairs q.1 → Bool) : TreeShape d 0
  | lift {fuel : ℕ} (sh : TreeShape d fuel) : TreeShape d (fuel + 1)
  | split {fuel : ℕ} (q s : Fin 6)
      (cls : Fin q.1 → Fin s.1)
      (shU : TreeShape d fuel)
      (shC : Fin s.1 → TreeShape d fuel) : TreeShape d (fuel + 1)

private instance instFiniteTreeShape (d fuel : ℕ) : Finite (TreeShape d fuel) := by
  induction fuel with
  | zero =>
    let T0 := Option (Σ q : Fin 6, Equiv.Perm (Fin (q.1 + 1)) ×
      {I : Fin q.1 → Fin d // Function.Injective I} ×
      (Fin q.1 → Fin q.1) × (Fin q.1 → Fin q.1) × (Pairs q.1 → Bool))
    let f : TreeShape d 0 → T0
      | .unit => none
      | .star q perm I k₀ root useLeft => some ⟨q, perm, I, k₀, root, useLeft⟩
    let g : T0 → TreeShape d 0
      | none => .unit
      | some ⟨q, perm, I, k₀, root, useLeft⟩ => .star q perm I k₀ root useLeft
    have hli : Function.LeftInverse g f := fun x => by cases x <;> rfl
    exact Finite.of_injective f hli.injective
  | succ fuel ih =>
    let T1 := TreeShape d fuel ⊕ (Σ q : Fin 6, Σ s : Fin 6,
      (Fin q.1 → Fin s.1) × TreeShape d fuel × (Fin s.1 → TreeShape d fuel))
    let f : TreeShape d (fuel + 1) → T1
      | .lift sh => Sum.inl sh
      | .split q s cls shU shC => Sum.inr ⟨q, s, cls, shU, shC⟩
    let g : T1 → TreeShape d (fuel + 1)
      | Sum.inl sh => .lift sh
      | Sum.inr ⟨q, s, cls, shU, shC⟩ => .split q s cls shU shC
    have hli : Function.LeftInverse g f := fun x => by cases x <;> rfl
    exact Finite.of_injective f hli.injective

private def TreeShape.dim {d : ℕ} : {fuel : ℕ} → TreeShape d fuel → ℕ
  | 0, .unit => 0
  | 0, .star q _ _ _ _ _ => q.1
  | _ + 1, .lift sh => sh.dim
  | _ + 1, .split q _ _ _ _ => q.1

private def classSet (q s : ℕ) (cls : Fin q → Fin s) (r : Fin s) : Finset (Fin q) :=
  Finset.univ.filter fun a => cls a = r

private def TreeShape.Valid {d : ℕ} : {fuel : ℕ} → TreeShape d fuel → Prop
  | 0, .unit => True
  | 0, .star q _ _ _ root _ => 1 ≤ q.1 ∧ q.1 ≤ d ∧ ∃ a₀ : Fin q.1, root a₀ = a₀
  | _ + 1, .lift sh => sh.Valid
  | _ + 1, .split q s cls shU shC =>
      2 ≤ q.1 ∧ q.1 ≤ d ∧ 1 ≤ s.1 ∧ s.1 < q.1 ∧
      (∀ r : Fin s.1, 1 ≤ (classSet q.1 s.1 cls r).card) ∧
      shU.Valid ∧ shU.dim = s.1 ∧
      ∀ r : Fin s.1, (shC r).Valid ∧ (shC r).dim = (classSet q.1 s.1 cls r).card - 1

private def TreeShape.ParamIdx {d : ℕ} : {fuel : ℕ} → TreeShape d fuel → Type
  | 0, .unit => Empty
  | 0, .star q _ I k₀ root _ =>
      (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
      (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
      {a : Fin q.1 // root a ≠ a}
  | _ + 1, .lift sh => sh.ParamIdx
  | _ + 1, .split _ s _ shU shC =>
      shU.ParamIdx ⊕ (Σ r : Fin s.1, (shC r).ParamIdx)

private noncomputable instance TreeShape.fintypeParamIdx {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) → Fintype sh.ParamIdx
  | 0, .unit => by
      change Fintype Empty
      exact inferInstance
  | 0, .star q _ I k₀ root _ => by
      change Fintype (
        (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
        (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
        {a : Fin q.1 // root a ≠ a})
      classical
      exact inferInstance
  | _ + 1, .lift sh => sh.fintypeParamIdx
  | _ + 1, .split _ s _ shU shC => by
      change Fintype (shU.ParamIdx ⊕ (Σ r : Fin s.1, (shC r).ParamIdx))
      letI := shU.fintypeParamIdx
      letI := fun r => (shC r).fintypeParamIdx
      exact inferInstance

private lemma TreeShape.dim_le_d {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) → sh.Valid → sh.dim ≤ d
  | 0, .unit, _ => Nat.zero_le d
  | 0, .star _ _ _ _ _ _, h => h.2.1
  | _ + 1, .lift sh, h => sh.dim_le_d h
  | _ + 1, .split _ _ _ _ _, h => h.2.1

private lemma card_paramIdx_bound {d fuel : ℕ} (sh : TreeShape d fuel) (hv : sh.Valid) :
    Fintype.card sh.ParamIdx ≤ sh.dim * d - 1 := by
  induction fuel generalizing d with
  | zero =>
    cases sh with
    | unit =>
      haveI : IsEmpty (TreeShape.unit (d := d)).ParamIdx := by
        change IsEmpty Empty
        exact inferInstance
      rw [Fintype.card_eq_zero]
      exact Nat.zero_le _
    | star q perm I k₀ root useLeft =>
      rcases hv with ⟨hq1, hqd, a₀, ha₀⟩
      have hcard_eq : Fintype.card (TreeShape.star q perm I k₀ root useLeft).ParamIdx = by
          classical
          exact Fintype.card (
            (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
            (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
            {a : Fin q.1 // root a ≠ a}) := by
        classical
        exact Fintype.card_congr (Equiv.refl _)
      rw [hcard_eq]
      change _ ≤ q.1 * d - 1
      have hcard_free : Fintype.card {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j} = d - q.1 := by
        let p : Fin d → Prop := fun j => ∃ s : Fin q.1, I.1 s = j
        have heq1 : Fintype.card {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j} =
            Fintype.card {j : Fin d // ¬ p j} := by
          refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
          simp only [p]
          push Not
          rfl
        have heq2 : Fintype.card {j : Fin d // ¬ p j} = d - Fintype.card {j : Fin d // p j} := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin]
        have heq3 : Fintype.card {j : Fin d // p j} = q.1 := by
          let f : Fin q.1 → {j : Fin d // p j} := fun s => ⟨I.1 s, s, rfl⟩
          have hf_bij : Function.Bijective f := by
            refine ⟨fun s₁ s₂ h => I.2 (congrArg Subtype.val h), fun ⟨j, s, hs⟩ => ?_⟩
            exact ⟨s, Subtype.ext hs⟩
          exact (Fintype.card_of_bijective hf_bij).symm.trans (Fintype.card_fin q.1)
        rw [heq1, heq2, heq3]
      have hcard_k₀ : ∀ a : Fin q.1, Fintype.card {r : Fin q.1 // r ≠ k₀ a} = q.1 - 1 := fun a => by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
      have hcard_root : Fintype.card {a : Fin q.1 // root a ≠ a} ≤ q.1 - 1 := by
        let g : {a : Fin q.1 // root a ≠ a} → {a : Fin q.1 // a ≠ a₀} := fun ⟨a, ha⟩ =>
          ⟨a, fun h => ha (h ▸ ha₀)⟩
        have hg : Function.Injective g := by
          rintro ⟨a, ha⟩ ⟨b, hb⟩ h
          have hab : a = b := congrArg Subtype.val h
          exact Subtype.ext hab
        have hle := Fintype.card_le_of_injective g hg
        have heq : Fintype.card {a : Fin q.1 // a ≠ a₀} = q.1 - 1 := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
        omega
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
        hcard_free, Fintype.card_sigma]
      simp only [hcard_k₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hcalc1 : q.1 * (d - q.1) + q.1 * (q.1 - 1) = q.1 * (d - 1) := by
        rw [← mul_add, show d - q.1 + (q.1 - 1) = d - 1 by omega]
      have hcalc3 : q.1 * (d - 1) + (q.1 - 1) = q.1 * d - 1 := by
        rw [Nat.mul_sub_left_distrib, mul_one]
        have hqd1 : q.1 ≤ q.1 * d := Nat.le_mul_of_pos_right q.1 (by omega)
        omega
      omega
  | succ fuel ih =>
    cases sh with
    | lift sh => exact ih sh hv
    | split q s cls shU shC =>
      rcases hv with ⟨hq2, hqd, hs1, hsq, hcard_ge, hUval, hUdim, hCval⟩
      have hcard_eq : Fintype.card (TreeShape.split q s cls shU shC).ParamIdx =
          @Fintype.card (shU.ParamIdx ⊕ (Σ r : Fin s.1, (shC r).ParamIdx)) (by
            letI := shU.fintypeParamIdx
            letI := fun r => (shC r).fintypeParamIdx
            exact inferInstance) :=
        Fintype.card_congr (Equiv.refl _)
      rw [hcard_eq]
      letI := shU.fintypeParamIdx
      letI := fun r => (shC r).fintypeParamIdx
      rw [Fintype.card_sum, Fintype.card_sigma]
      change _ + _ ≤ q.1 * d - 1
      have hU_le : Fintype.card shU.ParamIdx ≤ s.1 * d - 1 := by
        have h := ih shU hUval
        rwa [hUdim] at h
      have hC_le : ∀ r : Fin s.1,
          Fintype.card (shC r).ParamIdx ≤ ((classSet q.1 s.1 cls r).card - 1) * d := fun r => by
        have h := ih (shC r) (hCval r).1
        rw [(hCval r).2] at h
        exact h.trans (Nat.sub_le _ _)
      have hsum_C : (∑ r : Fin s.1, Fintype.card (shC r).ParamIdx) ≤
          (∑ r : Fin s.1, ((classSet q.1 s.1 cls r).card - 1)) * d := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun r _ => hC_le r
      have hfib : ∑ r : Fin s.1, (classSet q.1 s.1 cls r).card = q.1 := by
        have h := Finset.card_eq_sum_card_fiberwise (f := cls) (s := Finset.univ) (t := Finset.univ)
          (fun a _ => Finset.mem_univ (cls a))
        simpa [classSet] using h.symm
      have hsum_sub : s.1 + ∑ r : Fin s.1, ((classSet q.1 s.1 cls r).card - 1) = q.1 := by
        have h1 : ∑ r : Fin s.1, (classSet q.1 s.1 cls r).card =
            ∑ r : Fin s.1, (1 + ((classSet q.1 s.1 cls r).card - 1)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hcr := hcard_ge r
          omega
        rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one] at hfib
        exact hfib
      have h1d : 1 ≤ d := by omega
      have hsd : 1 ≤ s.1 * d := Nat.mul_pos hs1 h1d
      have hmul : s.1 * d + (∑ r : Fin s.1, ((classSet q.1 s.1 cls r).card - 1)) * d = q.1 * d := by
        rw [← add_mul, hsum_sub]
      omega

private noncomputable def evalStar {d : ℕ} (q : Fin 6)
    (perm : Equiv.Perm (Fin (q.1 + 1)))
    (I : {I : Fin q.1 → Fin d // Function.Injective I})
    (k₀ root : Fin q.1 → Fin q.1)
    (useLeft : Pairs q.1 → Bool)
    (θ : (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
         (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕
         {a : Fin q.1 // root a ≠ a} → ℝ)
    (e : Pairs (q.1 + 1)) : Ambient d :=
  let u : Fin q.1 → Ambient d := fun r =>
    ∑ j : Fin d,
      (if hj : ∀ s : Fin q.1, I.1 s ≠ j then
        θ (Sum.inl (r, ⟨j, hj⟩))
      else
        if I.1 r = j then (1 : ℝ) else 0) •
      EuclideanSpace.single j (1 : ℝ)
  let w : Fin q.1 → Ambient d := fun a =>
    ∑ r : Fin q.1,
      (if hr : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) • u r
  let t : Fin q.1 → ℝ := fun a =>
    if ha : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha⟩))
  let i := perm.symm e.1.1
  let j := perm.symm e.1.2
  Fin.cases
    (Fin.cases (0 : Ambient d) (fun b => w b) j)
    (fun a => Fin.cases (-w a) (fun b =>
      if root a = root b then t a • w a - t b • w b
      else if hab : a < b then if useLeft ⟨(a, b), hab⟩ then w a else w b
      else if hba : b < a then if useLeft ⟨(b, a), hba⟩ then w b else w a
      else 0) j)
    i

private lemma differentiable_ite {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Prop} [Decidable P] {f g : E → F}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun x => if P then f x else g x) := by
  by_cases h : P <;> simp [h, hf, hg]

private lemma differentiable_dite {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Prop} [Decidable P]
    {f : P → E → F} {g : ¬ P → E → F}
    (hf : ∀ h : P, Differentiable ℝ (f h)) (hg : ∀ h : ¬ P, Differentiable ℝ (g h)) :
    Differentiable ℝ (fun x => if h : P then f h x else g h x) := by
  by_cases h : P
  · simpa [h] using hf h
  · simpa [h] using hg h

private lemma differentiable_fin_cases {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : Fin (n + 1)) {f0 : E → F} {fs : Fin n → E → F}
    (hf0 : Differentiable ℝ f0) (hfs : ∀ i, Differentiable ℝ (fs i)) :
    Differentiable ℝ (fun x => Fin.cases (motive := fun _ => F) (f0 x) (fun i => fs i x) k) := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · exact hf0
  · exact hfs i

private lemma differentiable_evalStar {d : ℕ} (q : Fin 6)
    (perm : Equiv.Perm (Fin (q.1 + 1)))
    (I : {I : Fin q.1 → Fin d // Function.Injective I})
    (k₀ root : Fin q.1 → Fin q.1)
    (useLeft : Pairs q.1 → Bool)
    (e : Pairs (q.1 + 1)) :
    Differentiable ℝ (fun θ => evalStar q perm I k₀ root useLeft θ e) := by
  let γ := (Fin q.1 × {j : Fin d // ∀ s : Fin q.1, I.1 s ≠ j}) ⊕
    (Σ a : Fin q.1, {r : Fin q.1 // r ≠ k₀ a}) ⊕ {a : Fin q.1 // root a ≠ a}
  have hu : ∀ r : Fin q.1, Differentiable ℝ (fun θ : γ → ℝ =>
      ∑ j : Fin d,
        (if hj : ∀ s : Fin q.1, I.1 s ≠ j then
          θ (Sum.inl (r, ⟨j, hj⟩))
        else if I.1 r = j then (1 : ℝ) else 0) •
        EuclideanSpace.single j (1 : ℝ)) := fun r => by
    refine Differentiable.fun_sum fun j _ => ?_
    by_cases hj : ∀ s : Fin q.1, I.1 s ≠ j
    · have hfn : (fun θ : γ → ℝ =>
          (if hj' : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj'⟩))
           else if I.1 r = j then (1 : ℝ) else 0) • EuclideanSpace.single j (1 : ℝ)) =
          fun θ => θ (Sum.inl (r, ⟨j, hj⟩)) • EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact (differentiable_apply _).smul_const _
    · have hfn : (fun θ : γ → ℝ =>
          (if hj' : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj'⟩))
           else if I.1 r = j then (1 : ℝ) else 0) • EuclideanSpace.single j (1 : ℝ)) =
          fun _ => (if I.1 r = j then (1 : ℝ) else 0) • EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact differentiable_const _
  have hw : ∀ a : Fin q.1, Differentiable ℝ (fun θ : γ → ℝ =>
      ∑ r : Fin q.1,
        (if hr : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) •
        (∑ j : Fin d,
          (if hj : ∀ s : Fin q.1, I.1 s ≠ j then
            θ (Sum.inl (r, ⟨j, hj⟩))
          else if I.1 r = j then (1 : ℝ) else 0) •
          EuclideanSpace.single j (1 : ℝ))) := fun a => by
    refine Differentiable.fun_sum fun r _ => ?_
    by_cases hr : r = k₀ a
    · have hfn : (fun θ : γ → ℝ =>
          (if hr' : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr'⟩⟩))) •
          ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ)) = fun θ =>
          (1 : ℝ) • ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact (differentiable_const (1 : ℝ)).smul (hu r)
    · have hfn : (fun θ : γ → ℝ =>
          (if hr' : r = k₀ a then (1 : ℝ) else θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr'⟩⟩))) •
          ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ)) = fun θ =>
          θ (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩)) • ∑ j : Fin d,
            (if hj : ∀ s : Fin q.1, I.1 s ≠ j then θ (Sum.inl (r, ⟨j, hj⟩))
             else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]
      exact (differentiable_apply _).smul (hu r)
  have ht : ∀ a : Fin q.1, Differentiable ℝ (fun θ : γ → ℝ =>
      if ha : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha⟩))) := fun a => by
    by_cases ha : root a = a
    · have hfn : (fun θ : γ → ℝ =>
          if ha' : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha'⟩))) = fun _ => 1 :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]; exact differentiable_const _
    · have hfn : (fun θ : γ → ℝ =>
          if ha' : root a = a then (1 : ℝ) else θ (Sum.inr (Sum.inr ⟨a, ha'⟩))) =
          fun θ => θ (Sum.inr (Sum.inr ⟨a, ha⟩)) :=
        funext fun θ => by split_ifs <;> first | rfl | contradiction
      rw [hfn]; exact differentiable_apply _
  unfold evalStar
  refine differentiable_fin_cases (perm.symm e.1.1) ?_ fun a => ?_
  · refine differentiable_fin_cases (perm.symm e.1.2) (differentiable_const 0) fun b => hw b
  · refine differentiable_fin_cases (perm.symm e.1.2) (hw a).neg fun b => ?_
    refine differentiable_ite (((ht a).smul (hw a)).sub ((ht b).smul (hw b))) ?_
    refine differentiable_dite (fun hab => ?_) (fun _ => ?_)
    · exact differentiable_ite (hw a) (hw b)
    · refine differentiable_dite (fun hba => ?_) (fun _ => differentiable_const 0)
      exact differentiable_ite (hw b) (hw a)

private noncomputable def TreeShape.evalEdges {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) →
    (sh.ParamIdx → ℝ) → Pairs (sh.dim + 1) → Ambient d
  | 0, .unit, _, _ => 0
  | 0, .star q perm I k₀ root useLeft, θ, e => evalStar q perm I k₀ root useLeft θ e
  | _ + 1, .lift sh, θ, e => sh.evalEdges θ e
  | _ + 1, .split q s cls shU shC, θ, e =>
      Fin.cases
        (Fin.cases (0 : Ambient d) (fun b =>
          if hU : s.1 + 1 = shU.dim + 1 then
            shU.evalEdges (fun x => θ (Sum.inl x))
              (castPair hU ⟨(0, (cls b).succ), Nat.zero_lt_succ _⟩)
          else 0) e.1.2)
        (fun a => Fin.cases (0 : Ambient d) (fun b =>
          if hcls : cls a = cls b then
            let r := cls a
            let C := classSet q.1 s.1 cls r
            if hC : C.card = (shC r).dim + 1 then
              let ord := C.orderIsoOfFin rfl
              let i' : Fin C.card := ord.symm ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              let j' : Fin C.card :=
                ord.symm ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩⟩
              if hij' : i' < j' then
                (shC r).evalEdges (fun x => θ (Sum.inr ⟨r, x⟩))
                  (castPair hC ⟨(i', j'), hij'⟩)
              else 0
            else 0
          else
            if hU : s.1 + 1 = shU.dim + 1 then
              if hlt : cls a < cls b then
                shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls a).succ, (cls b).succ), Nat.succ_lt_succ hlt⟩)
              else if hgt : cls b < cls a then
                - shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls b).succ, (cls a).succ), Nat.succ_lt_succ hgt⟩)
              else 0
            else 0) e.1.2)
        e.1.1

private lemma evalEdges_split {d fuel : ℕ} (q s : Fin 6)
    (cls : Fin q.1 → Fin s.1) (shU : TreeShape d fuel) (shC : Fin s.1 → TreeShape d fuel)
    (θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ) (e : Pairs (q.1 + 1)) :
    (TreeShape.split q s cls shU shC).evalEdges θ e =
      Fin.cases
        (Fin.cases (0 : Ambient d) (fun b =>
          if hU : s.1 + 1 = shU.dim + 1 then
            shU.evalEdges (fun x => θ (Sum.inl x))
              (castPair hU ⟨(0, (cls b).succ), Nat.zero_lt_succ _⟩)
          else 0) e.1.2)
        (fun a => Fin.cases (0 : Ambient d) (fun b =>
          if hcls : cls a = cls b then
            let r := cls a
            let C := classSet q.1 s.1 cls r
            if hC : C.card = (shC r).dim + 1 then
              let ord := C.orderIsoOfFin rfl
              let i' : Fin C.card := ord.symm ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              let j' : Fin C.card :=
                ord.symm ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩⟩
              if hij' : i' < j' then
                (shC r).evalEdges (fun x => θ (Sum.inr ⟨r, x⟩))
                  (castPair hC ⟨(i', j'), hij'⟩)
              else 0
            else 0
          else
            if hU : s.1 + 1 = shU.dim + 1 then
              if hlt : cls a < cls b then
                shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls a).succ, (cls b).succ), Nat.succ_lt_succ hlt⟩)
              else if hgt : cls b < cls a then
                - shU.evalEdges (fun x => θ (Sum.inl x))
                  (castPair hU ⟨((cls b).succ, (cls a).succ), Nat.succ_lt_succ hgt⟩)
              else 0
            else 0) e.1.2)
        e.1.1 := rfl

private lemma differentiable_evalEdges {d : ℕ} :
    {fuel : ℕ} → (sh : TreeShape d fuel) →
    (e : Pairs (sh.dim + 1)) →
    Differentiable ℝ (fun θ : sh.ParamIdx → ℝ => sh.evalEdges θ e)
  | 0, .unit, _ => differentiable_const _
  | 0, .star q perm I k₀ root useLeft, e => differentiable_evalStar q perm I k₀ root useLeft e
  | _ + 1, .lift sh, e => differentiable_evalEdges sh e
  | _ + 1, .split q s cls shU shC, e => by
    unfold TreeShape.evalEdges
    have hinl : Differentiable ℝ (fun θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ =>
        fun x : shU.ParamIdx => θ (Sum.inl x)) :=
      differentiable_pi.mpr fun x => differentiable_apply (Sum.inl x)
    have hinr : ∀ r : Fin s.1, Differentiable ℝ
        (fun θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ =>
          fun x : (shC r).ParamIdx => θ (Sum.inr (Sigma.mk r x))) := fun r =>
      differentiable_pi.mpr fun x => by
        change Differentiable ℝ (fun θ : (TreeShape.split q s cls shU shC).ParamIdx → ℝ =>
          θ (Sum.inr (Sigma.mk r x)))
        exact differentiable_apply _
    refine differentiable_fin_cases e.1.1 ?_ fun a => ?_
    · refine differentiable_fin_cases e.1.2 (differentiable_const 0) fun b => ?_
      refine differentiable_dite (fun hU => (differentiable_evalEdges shU _).comp hinl)
        (fun _ => differentiable_const 0)
    · refine differentiable_fin_cases e.1.2 (differentiable_const 0) fun b => ?_
      refine differentiable_dite (fun hcls => ?_) (fun _ => ?_)
      · refine differentiable_dite (fun hC => ?_) (fun _ => differentiable_const 0)
        refine differentiable_dite (fun hij' => (differentiable_evalEdges (shC (cls a)) _).comp (hinr (cls a)))
          (fun _ => differentiable_const 0)
      · refine differentiable_dite (fun hU => ?_) (fun _ => differentiable_const 0)
        refine differentiable_dite (fun hlt => (differentiable_evalEdges shU _).comp hinl) (fun _ => ?_)
        exact differentiable_dite (fun hgt => ((differentiable_evalEdges shU _).comp hinl).neg)
          (fun _ => differentiable_const 0)

private lemma exists_liftShape {d : ℕ} {fuel₁ : ℕ} (fuel₂ : ℕ) (h : fuel₁ ≤ fuel₂)
    (sh : TreeShape d fuel₁) (hval : sh.Valid)
    (v : Pairs (sh.dim + 1) → Ambient d)
    (hrep : ∃ θ : sh.ParamIdx → ℝ, ∀ e : Pairs (sh.dim + 1),
      ∃ c : ℝ, c ≠ 0 ∧ sh.evalEdges θ e = c • v e) :
    ∃ (sh' : TreeShape d fuel₂) (heq : sh'.dim = sh.dim),
      sh'.Valid ∧
      ∃ θ' : sh'.ParamIdx → ℝ, ∀ e : Pairs (sh'.dim + 1),
        ∃ c : ℝ, c ≠ 0 ∧ sh'.evalEdges θ' e = c • v (castPair (congrArg (· + 1) heq) e) := by
  induction fuel₂ with
  | zero =>
    have h0 : fuel₁ = 0 := by omega
    subst h0
    refine ⟨sh, rfl, hval, ?_⟩
    obtain ⟨θ, hθ⟩ := hrep
    refine ⟨θ, fun e => ?_⟩
    rw [castPair_rfl]
    exact hθ e
  | succ f ih =>
    by_cases hle : fuel₁ ≤ f
    · obtain ⟨sh', heq, hval', θ', hθ'⟩ := ih hle
      exact ⟨.lift sh', heq, hval', θ', hθ'⟩
    · have hf : fuel₁ = f + 1 := by omega
      subst hf
      refine ⟨sh, rfl, hval, ?_⟩
      obtain ⟨θ, hθ⟩ := hrep
      refine ⟨θ, fun e => ?_⟩
      rw [castPair_rfl]
      exact hθ e

private lemma orderIsoOfFin_symm_val {α : Type*} [LinearOrder α] (S : Finset α)
    {n m : ℕ} (hn : S.card = n) (hm : S.card = m) (x : S) :
    ((S.orderIsoOfFin hn).symm x).1 = ((S.orderIsoOfFin hm).symm x).1 := by
  subst hn
  subst hm
  rfl

private lemma orderIsoOfFin_val_eq {α : Type*} [LinearOrder α] (S : Finset α)
    {n m : ℕ} (hn : S.card = n) (hm : S.card = m)
    (i : Fin n) (j : Fin m) (hij : (i : ℕ) = (j : ℕ)) :
    ((S.orderIsoOfFin hn) i).1 = ((S.orderIsoOfFin hm) j).1 := by
  subst hn
  subst hm
  have hij' : i = j := Fin.ext hij
  rw [hij']

private lemma exists_treeParam {d : ℕ} :
    ∀ (q : ℕ), 1 ≤ q → q ≤ 5 → q ≤ d →
      ∀ (v : Fin (q + 1) → Fin (q + 1) → Ambient d),
      (∀ i j, v j i = - v i j) →
      (∀ i j, i ≠ j → v i j ≠ 0) →
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • v i j + c₂ • v j k + c₃ • v k i = 0) →
      (q ≤ Module.finrank ℝ
        (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q + 1), x = v i j})) →
      ∃ (sh : TreeShape d q) (heq : sh.dim = q),
        sh.Valid ∧
        ∃ θ : sh.ParamIdx → ℝ,
          ∀ e : Pairs (sh.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
            sh.evalEdges θ e = c • v (Fin.cast (congrArg (· + 1) heq) e.1.1)
                                     (Fin.cast (congrArg (· + 1) heq) e.1.2) := by
  intro q
  classical
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq1 hq5 hqd v hv_sym hv_nz hv_tri hv_dim
    by_cases hstar : ∃ r₀ : Fin (q + 1),
        LinearIndependent ℝ (fun a : Fin q => v r₀ (r₀.succAbove a))
    · obtain ⟨r₀, hlin⟩ := hstar
      let q' : Fin 6 := ⟨q, by omega⟩
      let perm : Equiv.Perm (Fin (q'.1 + 1)) := Equiv.swap (0 : Fin (q + 1)) r₀
      let v' : Fin (q + 1) → Fin (q + 1) → Ambient d := fun i j => v (perm i) (perm j)
      have hv'_sym : ∀ i j, v' j i = - v' i j := fun i j => hv_sym (perm i) (perm j)
      have hv'_nz : ∀ i j, i ≠ j → v' i j ≠ 0 := fun i j hij =>
        hv_nz (perm i) (perm j) (fun h => hij (perm.injective h))
      have hv'_tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
          ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧
            c₁ • v' i j + c₂ • v' j k + c₃ • v' k i = 0 := fun i j k hij hjk hik =>
        hv_tri (perm i) (perm j) (perm k) (fun h => hij (perm.injective h))
          (fun h => hjk (perm.injective h)) (fun h => hik (perm.injective h))
      let w : Fin q → Ambient d := fun a => v' 0 a.succ
      have hw_indep : LinearIndependent ℝ w := by
        have hperm0 : perm 0 = r₀ := Equiv.swap_apply_left 0 r₀
        have hex : ∀ a : Fin q, ∃ b : Fin q, r₀.succAbove b = perm a.succ := fun a => by
          apply Fin.exists_succAbove_eq
          intro h
          have : perm a.succ = perm 0 := h.trans hperm0.symm
          exact Fin.succ_ne_zero a (perm.injective this)
        let φ : Fin q → Fin q := fun a => Classical.choose (hex a)
        have hφ_eq : ∀ a : Fin q, r₀.succAbove (φ a) = perm a.succ := fun a =>
          Classical.choose_spec (hex a)
        have hφ_inj : Function.Injective φ := fun a₁ a₂ h => by
          have : perm a₁.succ = perm a₂.succ := by rw [← hφ_eq a₁, ← hφ_eq a₂, h]
          exact Fin.succ_injective _ (perm.injective this)
        have hw_eq : w = (fun b : Fin q => v r₀ (r₀.succAbove b)) ∘ φ := by
          ext a j
          change v (perm 0) (perm a.succ) j = v r₀ (r₀.succAbove (φ a)) j
          rw [hperm0, hφ_eq a]
        rw [hw_eq]
        exact hlin.comp φ hφ_inj
      obtain ⟨I0, u0, hI0_inj, hu0_rref, hw_span⟩ := exists_rref q hqd w
      let I : {I : Fin q'.1 → Fin d // Function.Injective I} := ⟨I0, hI0_inj⟩
      have hu_decomp : ∀ x ∈ Submodule.span ℝ (Set.range u0),
          x = ∑ r : Fin q, x (I.1 r) • u0 r := fun x hx => by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨r₀, rfl⟩
          symm
          calc ∑ r : Fin q, u0 r₀ (I.1 r) • u0 r
              = ∑ r : Fin q, (if r₀ = r then (1 : ℝ) else 0) • u0 r := by
                refine Finset.sum_congr rfl fun r _ => by rw [hu0_rref r₀ r]
            _ = u0 r₀ := by simp
        · simp
        · intro x y _ _ hx_eq hy_eq
          calc x + y = (∑ r : Fin q, x (I.1 r) • u0 r) + (∑ r : Fin q, y (I.1 r) • u0 r) := by
                conv_lhs => rw [hx_eq, hy_eq]
            _ = ∑ r : Fin q, (x (I.1 r) + y (I.1 r)) • u0 r := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun r _ => (add_smul _ _ _).symm
            _ = ∑ r : Fin q, (x + y) (I.1 r) • u0 r := rfl
        · intro c x _ hx_eq
          calc c • x = c • ∑ r : Fin q, x (I.1 r) • u0 r := by conv_lhs => rw [hx_eq]
            _ = ∑ r : Fin q, (c * x (I.1 r)) • u0 r := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun r _ => smul_smul c _ _
            _ = ∑ r : Fin q, (c • x) (I.1 r) • u0 r := rfl
      have hk_ex : ∀ a : Fin q, ∃ r : Fin q, w a (I.1 r) ≠ 0 := fun a => by
        by_contra hall
        push Not at hall
        have hwa : w a = 0 := by
          rw [hu_decomp (w a) (hw_span a)]
          exact Finset.sum_eq_zero fun r _ => by rw [hall r, zero_smul]
        exact hv'_nz 0 a.succ (Fin.succ_ne_zero a).symm hwa
      let k₀ : Fin q'.1 → Fin q'.1 := fun a => Classical.choose (hk_ex a)
      have hk₀_ne : ∀ a : Fin q, w a (I.1 (k₀ a)) ≠ 0 := fun a => Classical.choose_spec (hk_ex a)
      let wnorm : Fin q → Ambient d := fun a => (w a (I.1 (k₀ a)))⁻¹ • w a
      have hwnorm_k0 : ∀ a : Fin q, wnorm a (I.1 (k₀ a)) = 1 := fun a => by
        dsimp [wnorm]
        exact inv_mul_cancel₀ (hk₀_ne a)
      have hwnorm_span : ∀ a : Fin q, wnorm a ∈ Submodule.span ℝ (Set.range u0) := fun a =>
        Submodule.smul_mem _ _ (hw_span a)
      have hwnorm_indep : LinearIndependent ℝ wnorm := by
        let units_fn : Fin q → ℝˣ := fun a => Units.mk0 _ (inv_ne_zero (hk₀_ne a))
        have hwnorm_eq : wnorm = fun a => units_fn a • w a := funext fun a => rfl
        rw [hwnorm_eq]
        exact hw_indep.units_smul units_fn
      have hwnorm_ne0 : ∀ a : Fin q, wnorm a ≠ 0 := fun a h => by
        have := hwnorm_k0 a
        rw [h] at this
        simp at this
      have hlin2 : ∀ {a b : Fin q} (hab : a ≠ b) (c₁ c₂ : ℝ),
          c₁ • wnorm a + c₂ • wnorm b = 0 → c₁ = 0 ∧ c₂ = 0 := fun {a b} hab c₁ c₂ hsum => by
        let f : Fin q → ℝ := fun x => if x = a then c₁ else if x = b then c₂ else 0
        have hf : ∑ x : Fin q, f x • wnorm x = 0 := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
          have hb_mem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hb_mem]
          have hrest : ∑ x ∈ (Finset.univ.erase a).erase b, f x • wnorm x = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
            have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            simp [f, hxa, hxb]
          rw [hrest, add_zero]
          have ha_v : f a = c₁ := by simp [f]
          have hb_v : f b = c₂ := by simp [f, hab.symm]
          rw [ha_v, hb_v, hsum]
        have h0 := Fintype.linearIndependent_iff.mp hwnorm_indep f hf
        exact ⟨by simpa [f] using h0 a, by simpa [f, hab.symm] using h0 b⟩
      have hlin3 : ∀ {a b c : Fin q}, a ≠ b → b ≠ c → a ≠ c → ∀ c₁ c₂ c₃ : ℝ,
          c₁ • wnorm a + c₂ • wnorm b + c₃ • wnorm c = 0 → c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 :=
          fun {a b c} hab hbc hac c₁ c₂ c₃ hsum => by
        let f : Fin q → ℝ := fun x =>
          if x = a then c₁ else if x = b then c₂ else if x = c then c₃ else 0
        have hf : ∑ x : Fin q, f x • wnorm x = 0 := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
          have hb_mem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hb_mem]
          have hc_mem : c ∈ (Finset.univ.erase a).erase b :=
            Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ _⟩⟩
          rw [← Finset.add_sum_erase _ _ hc_mem]
          have hrest : ∑ x ∈ ((Finset.univ.erase a).erase b).erase c, f x • wnorm x = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            have hxc : x ≠ c := (Finset.mem_erase.mp hx).1
            have hxb : x ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2).1
            simp [f, hxa, hxb, hxc]
          rw [hrest, add_zero]
          have ha_v : f a = c₁ := by simp [f]
          have hb_v : f b = c₂ := by simp [f, hab.symm]
          have hc_v : f c = c₃ := by simp [f, hac.symm, hbc.symm]
          rw [ha_v, hb_v, hc_v]
          rw [← add_assoc]
          exact hsum
        have h0 := Fintype.linearIndependent_iff.mp hwnorm_indep f hf
        exact ⟨by simpa [f] using h0 a,
               by simpa [f, hab.symm] using h0 b,
               by simpa [f, hac.symm, hbc.symm] using h0 c⟩
      have hedge_span : ∀ {a b : Fin q}, a ≠ b →
          ∃ α β : ℝ, v' a.succ b.succ = α • wnorm a + β • wnorm b := fun {a b} hab => by
        obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv'_tri 0 a.succ b.succ
          (Fin.succ_ne_zero a).symm (fun h => hab (Fin.succ_injective _ h))
          (Fin.succ_ne_zero b).symm
        have hc₂ : c₂ ≠ 0 := by
          intro hc2
          rw [hc2, zero_smul, add_zero, hv'_sym 0 b.succ] at hcomb
          change c₁ • v' 0 a.succ + c₃ • (-v' 0 b.succ) = 0 at hcomb
          have hw_comb : (c₁ * w a (I.1 (k₀ a))) • wnorm a + (-c₃ * w b (I.1 (k₀ b))) • wnorm b = 0 := by
            have hwa_eq : w a = w a (I.1 (k₀ a)) • wnorm a := by
              dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne a), one_smul]
            have hwb_eq : w b = w b (I.1 (k₀ b)) • wnorm b := by
              dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne b), one_smul]
            calc (c₁ * w a (I.1 (k₀ a))) • wnorm a + (-c₃ * w b (I.1 (k₀ b))) • wnorm b
                = c₁ • (w a (I.1 (k₀ a)) • wnorm a) + (-c₃) • (w b (I.1 (k₀ b)) • wnorm b) := by
                  simp [mul_smul]
              _ = c₁ • v' 0 a.succ + c₃ • (-v' 0 b.succ) := by
                  rw [← hwa_eq, ← hwb_eq]; simp [w]
              _ = 0 := hcomb
          obtain ⟨h1, h2⟩ := hlin2 hab _ _ hw_comb
          have hc1 : c₁ = 0 := (mul_eq_zero.mp h1).resolve_right (hk₀_ne a)
          have hc3 : c₃ = 0 := neg_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (hk₀_ne b))
          exact hne (by simp [hc1, hc2, hc3])
        refine ⟨(-c₁ / c₂) * w a (I.1 (k₀ a)), (c₃ / c₂) * w b (I.1 (k₀ b)), ?_⟩
        have hwa_eq : w a = w a (I.1 (k₀ a)) • wnorm a := by
          dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne a), one_smul]
        have hwb_eq : w b = w b (I.1 (k₀ b)) • wnorm b := by
          dsimp [wnorm]; rw [smul_smul, mul_inv_cancel₀ (hk₀_ne b), one_smul]
        rw [hv'_sym 0 b.succ] at hcomb
        have h1 : c₂ • v' a.succ b.succ = (-c₁) • w a + c₃ • w b := by
          have : c₁ • v' 0 a.succ + c₂ • v' a.succ b.succ + c₃ • (-v' 0 b.succ) = 0 := hcomb
          change c₁ • w a + c₂ • v' a.succ b.succ + c₃ • (-w b) = 0 at this
          rw [smul_neg, ← sub_eq_add_neg] at this
          calc c₂ • v' a.succ b.succ
              = c₂ • v' a.succ b.succ - (c₁ • w a + c₂ • v' a.succ b.succ - c₃ • w b) := by
                rw [this, sub_zero]
            _ = (-c₁) • w a + c₃ • w b := by module
        have h2 : v' a.succ b.succ = c₂⁻¹ • ((-c₁) • w a + c₃ • w b) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
        conv_lhs => rw [h2, hwa_eq, hwb_eq]
        module
      let H : Fin q → Fin q → Prop := fun a b =>
        a = b ∨ (v' a.succ b.succ ∉ Submodule.span ℝ {wnorm a} ∧ v' a.succ b.succ ∉ Submodule.span ℝ {wnorm b})
      have H_symm : ∀ a b, H a b → H b a := fun a b hab => by
        rcases hab with rfl | ⟨ha, hb⟩
        · exact Or.inl rfl
        · right
          rw [hv'_sym a.succ b.succ, Submodule.neg_mem_iff, Submodule.neg_mem_iff]
          exact ⟨hb, ha⟩
      have H_pair_coeff : ∀ {a b : Fin q}, a ≠ b → H a b →
          ∃ α β : ℝ, α ≠ 0 ∧ β ≠ 0 ∧ v' a.succ b.succ = α • wnorm a + β • wnorm b := fun {a b} hab hH => by
        rcases hH with h_eq | ⟨hna, hnb⟩
        · exact False.elim (hab h_eq)
        · obtain ⟨α, β, heq⟩ := hedge_span hab
          have hα : α ≠ 0 := by
            intro h0
            apply hnb
            rw [heq, h0, zero_smul, zero_add]
            exact Submodule.smul_mem _ β (Submodule.subset_span rfl)
          have hβ : β ≠ 0 := by
            intro h0
            apply hna
            rw [heq, h0, zero_smul, add_zero]
            exact Submodule.smul_mem _ α (Submodule.subset_span rfl)
          exact ⟨α, β, hα, hβ, heq⟩
      have H_trans : ∀ a b c, H a b → H b c → H a c := fun a b c hab hbc => by
        by_cases h1 : a = b; · subst h1; exact hbc
        by_cases h2 : b = c; · subst h2; exact hab
        by_cases h3 : a = c; · exact Or.inl h3
        obtain ⟨α₁, β₁, hα1, hβ1, heq_ab⟩ := H_pair_coeff h1 hab
        obtain ⟨α₂, β₂, hα2, hβ2, heq_bc⟩ := H_pair_coeff h2 hbc
        obtain ⟨γ, δ, heq_ca⟩ := hedge_span (Ne.symm h3)
        obtain ⟨p, q₁, r₁, hpqr, htri⟩ := hv'_tri a.succ b.succ c.succ
          (fin_succ_ne h1) (fin_succ_ne h2) (fin_succ_ne h3)
        have hcomb : (p * α₁ + r₁ * δ) • wnorm a + (p * β₁ + q₁ * α₂) • wnorm b +
            (q₁ * β₂ + r₁ * γ) • wnorm c = 0 := by
          calc (p * α₁ + r₁ * δ) • wnorm a + (p * β₁ + q₁ * α₂) • wnorm b + (q₁ * β₂ + r₁ * γ) • wnorm c
              = p • (α₁ • wnorm a + β₁ • wnorm b) + q₁ • (α₂ • wnorm b + β₂ • wnorm c) +
                  r₁ • (γ • wnorm c + δ • wnorm a) := by module
            _ = p • v' a.succ b.succ + q₁ • v' b.succ c.succ + r₁ • v' c.succ a.succ := by
                rw [heq_ab, heq_bc, heq_ca]
            _ = 0 := htri
        obtain ⟨ha0, hb0, hc0⟩ := hlin3 h1 h2 h3 _ _ _ hcomb
        have hr1 : r₁ ≠ 0 := by
          intro hr0
          rw [hr0, zero_mul, add_zero] at ha0 hc0
          have hp0 : p = 0 := (mul_eq_zero.mp ha0).resolve_right hα1
          have hq0 : q₁ = 0 := (mul_eq_zero.mp hc0).resolve_right hβ2
          exact hpqr (by simp [hp0, hq0, hr0])
        have hp0 : p ≠ 0 := by
          intro hpz
          rw [hpz, zero_mul, zero_add] at ha0 hb0
          have hδ0 : δ = 0 := (mul_eq_zero.mp ha0).resolve_left hr1
          have hq0 : q₁ = 0 := (mul_eq_zero.mp hb0).resolve_right hα2
          rw [hq0, zero_mul, zero_add] at hc0
          have hγ0 : γ = 0 := (mul_eq_zero.mp hc0).resolve_left hr1
          have hv0 : v' c.succ a.succ = 0 := by rw [heq_ca, hγ0, hδ0, zero_smul, zero_smul, add_zero]
          exact hv'_nz c.succ a.succ (fin_succ_ne (Ne.symm h3)) hv0
        have hq0 : q₁ ≠ 0 := by
          intro hqz
          rw [hqz, zero_mul, add_zero] at hb0
          rw [hqz, zero_mul, zero_add] at hc0
          have hpz : p = 0 := (mul_eq_zero.mp hb0).resolve_right hβ1
          exact hp0 hpz
        have hδ_ne : δ ≠ 0 := fun h0 => by
          rw [h0, mul_zero, add_zero] at ha0
          exact hp0 ((mul_eq_zero.mp ha0).resolve_right hα1)
        have hγ_ne : γ ≠ 0 := fun h0 => by
          rw [h0, mul_zero, add_zero] at hc0
          exact hq0 ((mul_eq_zero.mp hc0).resolve_right hβ2)
        have hac_mem : v' a.succ c.succ = (-δ) • wnorm a + (-γ) • wnorm c := by
          rw [hv'_sym c.succ a.succ, heq_ca]; module
        right
        constructor
        · intro hmem
          obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hmem
          have hsub : (-δ - u) • wnorm a + (-γ) • wnorm c = 0 := by
            calc (-δ - u) • wnorm a + (-γ) • wnorm c
                = ((-δ) • wnorm a + (-γ) • wnorm c) - u • wnorm a := by module
              _ = v' a.succ c.succ - v' a.succ c.succ := by rw [← hac_mem, hu]
              _ = 0 := sub_self _
          exact hγ_ne (neg_eq_zero.mp (hlin2 h3 _ _ hsub).2)
        · intro hmem
          obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hmem
          have hsub : (-δ) • wnorm a + (-γ - u) • wnorm c = 0 := by
            calc (-δ) • wnorm a + (-γ - u) • wnorm c
                = ((-δ) • wnorm a + (-γ) • wnorm c) - u • wnorm c := by module
              _ = v' a.succ c.succ - v' a.succ c.succ := by rw [← hac_mem, hu]
              _ = 0 := sub_self _
          exact hδ_ne (neg_eq_zero.mp (hlin2 h3 _ _ hsub).1)
      let root : Fin q'.1 → Fin q'.1 := fun a =>
        (Finset.univ.filter fun b => H a b).min' ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩
      have hroot_H : ∀ a : Fin q, H a (root a) := fun a =>
        (Finset.mem_filter.mp (Finset.min'_mem _ ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩)).2
      have hroot_iff : ∀ a b : Fin q, H a b ↔ root a = root b := fun a b => by
        constructor
        · intro hab
          have hfilt : (Finset.univ.filter fun x => H a x) = (Finset.univ.filter fun x => H b x) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun hax => H_trans b a x (H_symm a b hab) hax, fun hbx => H_trans a b x hab hbx⟩
          dsimp [root]
          congr 1
        · intro heq
          have h1 := hroot_H a
          have h2 := hroot_H b
          rw [← heq] at h2
          exact H_trans a (root a) b h1 (H_symm b (root a) h2)
      have hroot_idem : ∀ a : Fin q, root (root a) = root a := fun a =>
        ((hroot_iff (root a) a).mp (H_symm a (root a) (hroot_H a)))
      have hroot_ex : ∃ a₀ : Fin q'.1, root a₀ = a₀ := by
        let a₁ : Fin q := ⟨0, hq1⟩
        exact ⟨root a₁, hroot_idem a₁⟩
      have ht_all : ∀ a : Fin q, ∃ t : ℝ, (root a ≠ a → t ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧
          wnorm (root a) - t • wnorm a = c • v' (root a).succ a.succ) := fun a => by
        by_cases ha : root a = a
        · exact ⟨1, fun h => absurd ha h⟩
        · obtain ⟨α, β, hα, hβ, heq⟩ := H_pair_coeff ha (H_symm a (root a) (hroot_H a))
          refine ⟨-β / α, fun _ => ⟨div_ne_zero (neg_ne_zero.mpr hβ) hα, α⁻¹, inv_ne_zero hα, ?_⟩⟩
          have hc : -(-β / α) = α⁻¹ * β := by field_simp [hα]
          calc wnorm (root a) - (-β / α) • wnorm a
              = wnorm (root a) + (α⁻¹ * β) • wnorm a := by rw [sub_eq_add_neg, ← neg_smul, hc]
            _ = α⁻¹ • (α • wnorm (root a) + β • wnorm a) := by
                rw [smul_add, mul_smul]
                congr 1
                rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
            _ = α⁻¹ • v' (root a).succ a.succ := by rw [heq]
      choose t_val ht_spec using ht_all
      let useLeft : Pairs q'.1 → Bool := fun p =>
        decide (v' p.1.1.succ p.1.2.succ ∈ Submodule.span ℝ {wnorm p.1.1})
      let sh0 : TreeShape d 0 := .star q' perm I k₀ root useLeft
      have hsh0_val : sh0.Valid := ⟨hq1, hqd, hroot_ex⟩
      let θ0 : sh0.ParamIdx → ℝ :=
        Sum.elim (fun p => u0 p.1 p.2.1)
          (Sum.elim (fun p => wnorm p.1 (I.1 p.2.1)) (fun p => t_val p.1))
      have hu_eq_u0 : ∀ r : Fin q,
          (∑ j : Fin d,
            (if hj : ∀ s : Fin q'.1, I.1 s ≠ j then
              θ0 (Sum.inl (r, ⟨j, hj⟩))
            else if I.1 r = j then (1 : ℝ) else 0) •
            EuclideanSpace.single j (1 : ℝ)) = u0 r := fun r => by
        ext j
        have hsum_apply : ∀ (s : Finset (Fin d)) (g : Fin d → Ambient d),
            (∑ k ∈ s, g k) j = ∑ k ∈ s, g k j := fun s g => by
          induction s using Finset.induction with
          | empty => simp
          | insert _ _ h ih => simp [Finset.sum_insert h, ih]
        rw [hsum_apply]
        have hsingle : ∀ k : Fin d,
            (if hk : ∀ s : Fin q'.1, I.1 s ≠ k then
              θ0 (Sum.inl (r, ⟨k, hk⟩))
            else if I.1 r = k then (1 : ℝ) else 0) * (EuclideanSpace.single k (1 : ℝ)) j =
            if k = j then
              (if hk : ∀ s : Fin q'.1, I.1 s ≠ k then
                θ0 (Sum.inl (r, ⟨k, hk⟩))
              else if I.1 r = k then (1 : ℝ) else 0)
            else 0 := fun k => by
          by_cases hkj : k = j
          · subst hkj; simp [EuclideanSpace.single]
          · simp [EuclideanSpace.single, hkj, Ne.symm hkj]
        simp only [PiLp.smul_apply, smul_eq_mul, hsingle, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
        split_ifs with hj hrs
        · rfl
        · rw [← hrs, hu0_rref r r]; simp
        · push Not at hj
          obtain ⟨s, hs⟩ := hj
          subst hs
          rw [hu0_rref r s]
          have hne : r ≠ s := fun h => hrs (congrArg I.1 h)
          simp [hne]
      have hw_eq_wnorm : ∀ a : Fin q,
          (∑ r : Fin q'.1,
            (if hr : r = k₀ a then (1 : ℝ) else θ0 (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) •
            (∑ j : Fin d,
              (if hj : ∀ s : Fin q'.1, I.1 s ≠ j then
                θ0 (Sum.inl (r, ⟨j, hj⟩))
              else if I.1 r = j then (1 : ℝ) else 0) •
              EuclideanSpace.single j (1 : ℝ))) = wnorm a := fun a => by
        calc _ = ∑ r : Fin q, (if hr : r = k₀ a then (1 : ℝ) else θ0 (Sum.inr (Sum.inl ⟨a, ⟨r, hr⟩⟩))) • u0 r := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [hu_eq_u0 r]
          _ = ∑ r : Fin q, wnorm a (I.1 r) • u0 r := by
              refine Finset.sum_congr rfl fun r _ => ?_
              by_cases hr : r = k₀ a
              · subst hr; simp only [↓reduceDIte, hwnorm_k0]
              · simp only [hr, ↓reduceDIte, θ0]; rfl
          _ = wnorm a := (hu_decomp (wnorm a) (hwnorm_span a)).symm
      have hrep0 : ∀ e : Pairs (sh0.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
          sh0.evalEdges θ0 e = c • v e.1.1 e.1.2 := fun e => by
        change ∃ c : ℝ, c ≠ 0 ∧ evalStar q' perm I k₀ root useLeft θ0 e = c • v e.1.1 e.1.2
        let t_fun : Fin q → ℝ := fun a =>
          if ha : root a = a then 1 else θ0 (Sum.inr (Sum.inr ⟨a, ha⟩))
        have ht_fun_spec : ∀ a : Fin q, t_fun a = if root a = a then 1 else t_val a := fun a => by
          dsimp [t_fun]; split_ifs <;> rfl
        have hperm_ne : perm.symm e.1.1 ≠ perm.symm e.1.2 := fun h =>
          Fin.ne_of_lt e.2 (perm.symm.injective h)
        have hve_eq : v e.1.1 e.1.2 = v' (perm.symm e.1.1) (perm.symm e.1.2) := by
          dsimp [v']
          congr 1 <;> exact (perm.apply_symm_apply _).symm
        rw [hve_eq]
        unfold evalStar
        dsimp only
        simp_rw [hw_eq_wnorm]
        induction hpi : perm.symm e.1.1 using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero]
          induction hpj : perm.symm e.1.2 using Fin.cases with
          | zero => exact False.elim (hperm_ne (hpi.trans hpj.symm))
          | succ b =>
            simp only [Fin.cases_succ]
            refine ⟨(w b (I.1 (k₀ b)))⁻¹, inv_ne_zero (hk₀_ne b), ?_⟩
            rfl
        | succ a =>
          simp only [Fin.cases_succ]
          induction hpj : perm.symm e.1.2 using Fin.cases with
          | zero =>
            simp only [Fin.cases_zero]
            refine ⟨(w a (I.1 (k₀ a)))⁻¹, inv_ne_zero (hk₀_ne a), ?_⟩
            rw [hv'_sym 0 a.succ, smul_neg]
          | succ b =>
            simp only [Fin.cases_succ]
            have hab : a ≠ b := fun h => hperm_ne (by rw [hpi, hpj, h])
            by_cases hrab : root a = root b
            · rw [if_pos hrab]
              have hHab : H a b := (hroot_iff a b).mpr hrab
              change ∃ c : ℝ, c ≠ 0 ∧ t_fun a • wnorm a - t_fun b • wnorm b = c • v' a.succ b.succ
              by_cases har : root a = a
              · have hbr : root b ≠ b := fun h => hab (by rw [← har, hrab, h])
                obtain ⟨ht_ne, c, hc, hce⟩ := ht_spec b hbr
                have htf_a : t_fun a = 1 := by rw [ht_fun_spec, if_pos har]
                have htf_b : t_fun b = t_val b := by rw [ht_fun_spec, if_neg hbr]
                have hrb : root b = a := hrab.symm.trans har
                rw [hrb] at hce
                refine ⟨c, hc, ?_⟩
                rw [htf_a, htf_b, one_smul, hce]
              · by_cases hbr : root b = b
                · obtain ⟨ht_ne, c, hc, hce⟩ := ht_spec a har
                  have htf_a : t_fun a = t_val a := by rw [ht_fun_spec, if_neg har]
                  have htf_b : t_fun b = 1 := by rw [ht_fun_spec, if_pos hbr]
                  have hra : root a = b := hrab.trans hbr
                  rw [hra] at hce
                  refine ⟨c, hc, ?_⟩
                  rw [htf_a, htf_b, one_smul]
                  calc t_val a • wnorm a - wnorm b = -(wnorm b - t_val a • wnorm a) := by module
                    _ = -(c • v' b.succ a.succ) := by rw [hce]
                    _ = c • v' a.succ b.succ := by rw [hv'_sym a.succ b.succ]; module
                · let r := root a
                  have hr_b : root b = r := hrab.symm
                  obtain ⟨ta_ne, ca, hca, hcea⟩ := ht_spec a har
                  obtain ⟨tb_ne, cb, hcb, hceb⟩ := ht_spec b hbr
                  have htf_a : t_fun a = t_val a := by rw [ht_fun_spec, if_neg har]
                  have htf_b : t_fun b = t_val b := by rw [ht_fun_spec, if_neg hbr]
                  rw [htf_a, htf_b]
                  obtain ⟨γ, δ, hγ, hδ, heq_ab⟩ := H_pair_coeff hab hHab
                  have har_ne : r ≠ a := fun h => har h
                  have hbr_ne : r ≠ b := fun h => hbr (hr_b.trans h)
                  obtain ⟨p, q₁, r₁, hpqr, htri⟩ := hv'_tri r.succ a.succ b.succ
                    (fin_succ_ne har_ne) (fin_succ_ne hab)
                    (fin_succ_ne hbr_ne)
                  have hva : v' r.succ a.succ = ca⁻¹ • (wnorm r - t_val a • wnorm a) := by
                    rw [hcea, smul_smul, inv_mul_cancel₀ hca, one_smul]
                  have hvb : v' b.succ r.succ = -(cb⁻¹ • (wnorm r - t_val b • wnorm b)) := by
                    rw [hv'_sym r.succ b.succ, ← hr_b, hceb, smul_smul, inv_mul_cancel₀ hcb, one_smul]
                  have hcomb : (p * ca⁻¹ - r₁ * cb⁻¹) • wnorm r +
                      (-p * ca⁻¹ * t_val a + q₁ * γ) • wnorm a +
                      (r₁ * cb⁻¹ * t_val b + q₁ * δ) • wnorm b = 0 := by
                    calc _ = p • (ca⁻¹ • (wnorm r - t_val a • wnorm a)) +
                              q₁ • (γ • wnorm a + δ • wnorm b) +
                              r₁ • (-(cb⁻¹ • (wnorm r - t_val b • wnorm b))) := by module
                      _ = p • v' r.succ a.succ + q₁ • v' a.succ b.succ + r₁ • v' b.succ r.succ := by
                          rw [← hva, ← heq_ab, ← hvb]
                      _ = 0 := htri
                  obtain ⟨hr0, ha0, hb0⟩ := hlin3 har_ne hab hbr_ne _ _ _ hcomb
                  have hpr : p * ca⁻¹ = r₁ * cb⁻¹ := sub_eq_zero.mp hr0
                  have hq₁ : q₁ ≠ 0 := fun hqz => by
                    rw [hqz, zero_mul, add_zero] at ha0 hb0
                    have hpz : p = 0 := by
                      rcases mul_eq_zero.mp ha0 with h1 | h1
                      · rcases mul_eq_zero.mp h1 with h2 | h2
                        · exact neg_eq_zero.mp h2
                        · exact False.elim (inv_ne_zero hca h2)
                      · exact False.elim (ta_ne h1)
                    have hrz : r₁ = 0 := by
                      rw [hpz, zero_mul] at hpr
                      exact (mul_eq_zero.mp hpr.symm).resolve_right (inv_ne_zero hcb)
                    exact hpqr (by simp [hpz, hqz, hrz])
                  have hp_ne : p ≠ 0 := fun hpz => by
                    rw [hpz, neg_zero, zero_mul, zero_mul, zero_add] at ha0
                    exact hγ ((mul_eq_zero.mp ha0).resolve_left hq₁)
                  have hden : p * ca⁻¹ ≠ 0 := mul_ne_zero hp_ne (inv_ne_zero hca)
                  refine ⟨q₁ / (p * ca⁻¹), div_ne_zero hq₁ hden, ?_⟩
                  have hγ_eq : q₁ * γ = (p * ca⁻¹) * t_val a := by linarith
                  have hδ_eq : q₁ * δ = -((p * ca⁻¹) * t_val b) := by rw [hpr]; linarith
                  have heq_v : (q₁ / (p * ca⁻¹)) • v' a.succ b.succ =
                      (q₁ / (p * ca⁻¹)) • (γ • wnorm a + δ • wnorm b) := by rw [heq_ab]
                  have ht1 : (q₁ / (p * ca⁻¹)) * γ = t_val a := by
                    calc (q₁ / (p * ca⁻¹)) * γ = (q₁ * γ) / (p * ca⁻¹) := by ring
                      _ = ((p * ca⁻¹) * t_val a) / (p * ca⁻¹) := by rw [hγ_eq]
                      _ = t_val a := mul_div_cancel_left₀ _ hden
                  have ht2 : (q₁ / (p * ca⁻¹)) * δ = -t_val b := by
                    calc (q₁ / (p * ca⁻¹)) * δ = (q₁ * δ) / (p * ca⁻¹) := by ring
                      _ = (-((p * ca⁻¹) * t_val b)) / (p * ca⁻¹) := by rw [hδ_eq]
                      _ = -t_val b := by rw [neg_div, mul_div_cancel_left₀ _ hden]
                  have hlhs_eq : (q₁ / (p * ca⁻¹)) • (γ • wnorm a + δ • wnorm b) =
                      t_val a • wnorm a - t_val b • wnorm b := by
                    rw [smul_add, sub_eq_add_neg]
                    congr 1
                    · rw [smul_smul, ht1]
                    · rw [smul_smul, ht2, neg_smul]
                  rw [heq_v, hlhs_eq]
            · rw [if_neg hrab]
              have hnH : ¬ H a b := fun h => hrab ((hroot_iff a b).mp h)
              have hmem_or : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a} ∨
                  v' a.succ b.succ ∈ Submodule.span ℝ {wnorm b} := by
                dsimp [H] at hnH
                push Not at hnH
                by_cases hmem_a : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a}
                · exact Or.inl hmem_a
                · exact Or.inr (hnH.2 hmem_a)
              rcases lt_or_gt_of_ne hab with hlt | hgt
              · simp only [hlt, ↓reduceDIte]
                by_cases huL : useLeft ⟨(a, b), hlt⟩ = true
                · simp only [huL, ↓reduceIte]
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a} := by
                    simpa [useLeft] using huL
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
                · simp only [huL, Bool.false_eq_true, ↓reduceIte]
                  have hna : v' a.succ b.succ ∉ Submodule.span ℝ {wnorm a} := by
                    simpa [useLeft] using huL
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm b} := hmem_or.resolve_left hna
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
              · have hnot : ¬ a < b := Nat.not_lt.mpr hgt.le
                simp only [hnot, ↓reduceDIte, hgt]
                by_cases huL : useLeft ⟨(b, a), hgt⟩ = true
                · simp only [huL, ↓reduceIte]
                  have hmem_ba : v' b.succ a.succ ∈ Submodule.span ℝ {wnorm b} := by
                    simpa [useLeft] using huL
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm b} := by
                    rwa [hv'_sym a.succ b.succ, Submodule.neg_mem_iff] at hmem_ba
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
                · simp only [huL, Bool.false_eq_true, ↓reduceIte]
                  have hnb_ba : v' b.succ a.succ ∉ Submodule.span ℝ {wnorm b} := by
                    simpa [useLeft] using huL
                  have hnb : v' a.succ b.succ ∉ Submodule.span ℝ {wnorm b} := fun h =>
                    hnb_ba (by rw [hv'_sym a.succ b.succ, Submodule.neg_mem_iff]; exact h)
                  have hmem : v' a.succ b.succ ∈ Submodule.span ℝ {wnorm a} := hmem_or.resolve_right hnb
                  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
                  have hc0 : c ≠ 0 := fun h0 => by
                    rw [h0, zero_smul] at hc
                    exact hv'_nz a.succ b.succ (fin_succ_ne hab) hc.symm
                  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
                  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      exact exists_liftShape q (Nat.zero_le q) sh0 hsh0_val
        (fun e => v e.1.1 e.1.2) ⟨θ0, hrep0⟩
    · push Not at hstar
      let w : Fin q → Ambient d := fun a => v 0 a.succ
      have hw_not_indep : ¬ LinearIndependent ℝ w := by
        have h := hstar 0
        have hw_eq : w = fun a : Fin q => v 0 ((0 : Fin (q + 1)).succAbove a) := rfl
        rwa [hw_eq]
      have hq2 : 2 ≤ q := by
        by_contra hlt2
        have hq_eq1 : q = 1 := by omega
        subst hq_eq1
        apply hw_not_indep
        refine Fintype.linearIndependent_iff.mpr fun g hg a => ?_
        have ha0 : a = 0 := Fin.eq_zero a
        subst ha0
        rw [Fin.sum_univ_one] at hg
        exact (smul_eq_zero.mp hg).resolve_right (hv_nz 0 1 (by decide))
      let U : Submodule ℝ (Ambient d) := Submodule.span ℝ (Set.range w)
      have hU_lt_q : Module.finrank ℝ U < q := by
        have hle : Module.finrank ℝ U ≤ q := by
          have h1 : Module.finrank ℝ U ≤ (Set.range w).toFinset.card :=
            finrank_span_le_card (Set.range w)
          have h2 : (Set.range w).toFinset.card ≤ q := by
            calc (Set.range w).toFinset.card = (Finset.univ.image w).card := by
                  congr 1; ext x; simp
              _ ≤ Finset.univ.card := Finset.card_image_le
              _ = q := Fintype.card_fin q
          exact h1.trans h2
        refine lt_of_le_of_ne hle fun hfin => hw_not_indep ?_
        rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
        exact hfin.symm
      let cls_raw : Fin q → Fin q := fun a =>
        (Finset.univ.filter fun b => Submodule.span ℝ {w a} = Submodule.span ℝ {w b}).min'
          ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      have hcls_raw_mem : ∀ a : Fin q,
          Submodule.span ℝ {w a} = Submodule.span ℝ {w (cls_raw a)} := fun a =>
        (Finset.mem_filter.mp ((Finset.univ.filter fun b =>
          Submodule.span ℝ {w a} = Submodule.span ℝ {w b}).min'_mem
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩)).2
      have hcls_raw_iff : ∀ a b : Fin q,
          cls_raw a = cls_raw b ↔ Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := fun a b => by
        constructor
        · intro h
          rw [hcls_raw_mem a, hcls_raw_mem b, h]
        · intro h
          have hfilt : (Finset.univ.filter fun x => Submodule.span ℝ {w a} = Submodule.span ℝ {w x}) =
              (Finset.univ.filter fun x => Submodule.span ℝ {w b} = Submodule.span ℝ {w x}) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
          dsimp [cls_raw]
          congr 1
      have hcls_raw_idem : ∀ a : Fin q, cls_raw (cls_raw a) = cls_raw a := fun a =>
        (hcls_raw_iff (cls_raw a) a).mpr (hcls_raw_mem a).symm
      let roots : Finset (Fin q) := Finset.univ.image cls_raw
      obtain ⟨s, hs_eq⟩ : ∃ s : ℕ, s = roots.card := ⟨roots.card, rfl⟩
      have hs1 : 1 ≤ s := hs_eq.symm ▸
        Finset.card_pos.mpr ⟨cls_raw ⟨0, hq1⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      let ordRoots : Fin s ≃o roots := roots.orderIsoOfFin hs_eq.symm
      let cls : Fin q → Fin s := fun a =>
        ordRoots.symm ⟨cls_raw a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
      have hcls_iff : ∀ a b : Fin q,
          cls a = cls b ↔ Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := fun a b => by
        rw [← hcls_raw_iff a b]
        constructor
        · intro h
          have : (⟨cls_raw a, _⟩ : roots) = ⟨cls_raw b, _⟩ := ordRoots.symm.injective h
          exact congrArg Subtype.val this
        · intro h
          apply congrArg (ordRoots.symm)
          exact Subtype.ext h
      let rep : Fin s → Fin q := fun r => (ordRoots r).1
      have hcls_rep : ∀ r : Fin s, cls (rep r) = r := fun r => by
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (ordRoots r).2
        have hraw : cls_raw (rep r) = rep r := by
          dsimp [rep]; rw [← hb, hcls_raw_idem b]
        dsimp [cls]
        have : (⟨cls_raw (rep r), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ : roots) = ordRoots r :=
          Subtype.ext hraw
        rw [this, OrderIso.symm_apply_apply]
      have hC_ge1 : ∀ r : Fin s, 1 ≤ (classSet q s cls r).card := fun r =>
        Finset.card_pos.mpr ⟨rep r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls_rep r⟩⟩
      let V : Fin s → Submodule ℝ (Ambient d) := fun r =>
        Submodule.span ℝ {x : Ambient d |
          ∃ a ∈ classSet q s cls r, ∃ b ∈ classSet q s cls r, a ≠ b ∧ x = v a.succ b.succ}
      have hV_finrank : ∀ r : Fin s,
          Module.finrank ℝ (V r) ≤ (classSet q s cls r).card - 1 := fun r =>
        finrank_triangle_span_le (fun a b => v a.succ b.succ)
          (fun a b => hv_sym a.succ b.succ)
          (fun a b hab => hv_nz a.succ b.succ (fin_succ_ne hab))
          (fun a b c hab hbc hac => by
            obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv_tri a.succ b.succ c.succ
              (fin_succ_ne hab) (fin_succ_ne hbc) (fin_succ_ne hac)
            refine ⟨c₁, c₂, c₃, ?_, hcomb⟩
            by_contra hall
            push Not at hall
            exact hne (Prod.ext hall.1 (Prod.ext hall.2.1 hall.2.2)))
          (classSet q s cls r).card (classSet q s cls r)
          ⟨rep r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls_rep r⟩⟩ rfl
      have hU_eq_rep : U = Submodule.span ℝ (Set.range fun r : Fin s => w (rep r)) := by
        refine le_antisymm ?_ ?_
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨a, rfl⟩
          have hsp : w a ∈ Submodule.span ℝ {w (rep (cls a))} := by
            rw [← (hcls_iff a (rep (cls a))).mp (hcls_rep (cls a)).symm]
            exact Submodule.subset_span rfl
          exact Submodule.span_mono (by
            rintro _ rfl
            exact ⟨cls a, rfl⟩) hsp
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨r, rfl⟩
          exact Submodule.subset_span ⟨rep r, rfl⟩
      have hU_finrank_le : Module.finrank ℝ U ≤ s := by
        rw [hU_eq_rep]
        have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range fun r : Fin s => w (rep r))) ≤
            (Set.range fun r : Fin s => w (rep r)).toFinset.card :=
          finrank_span_le_card _
        have h2 : (Set.range fun r : Fin s => w (rep r)).toFinset.card ≤ s := by
          calc (Set.range fun r : Fin s => w (rep r)).toFinset.card
              = (Finset.univ.image fun r : Fin s => w (rep r)).card := by
                congr 1; ext x; simp
            _ ≤ Finset.univ.card := Finset.card_image_le
            _ = s := Fintype.card_fin s
        exact h1.trans h2
      let W_sup : Submodule ℝ (Ambient d) := Finset.univ.sup V
      let W_top : Submodule ℝ (Ambient d) := U ⊔ W_sup
      have hW_sub : Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q + 1), x = v i j} ≤ W_top := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, j, rfl⟩
        rw [SetLike.mem_coe]
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero =>
            have hv00 : v 0 0 = 0 := by
              have h := hv_sym 0 0
              have : (2 : ℝ) • v 0 0 = 0 := by
                calc (2 : ℝ) • v 0 0 = v 0 0 + v 0 0 := two_smul ℝ _
                  _ = v 0 0 + (- v 0 0) := by conv_lhs => rhs; rw [h]
                  _ = 0 := add_neg_cancel _
              exact (smul_eq_zero.mp this).resolve_left two_ne_zero
            rw [hv00]
            exact Submodule.zero_mem _
          | succ b => exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩)
        | succ a =>
          induction j using Fin.cases with
          | zero =>
            rw [hv_sym 0 a.succ]
            exact Submodule.neg_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩))
          | succ b =>
            by_cases hab : a = b
            · subst hab
              have hvaa : v a.succ a.succ = 0 := by
                have h := hv_sym a.succ a.succ
                have : (2 : ℝ) • v a.succ a.succ = 0 := by
                  calc (2 : ℝ) • v a.succ a.succ = v a.succ a.succ + v a.succ a.succ := two_smul ℝ _
                    _ = v a.succ a.succ + (- v a.succ a.succ) := by conv_lhs => rhs; rw [h]
                    _ = 0 := add_neg_cancel _
                exact (smul_eq_zero.mp this).resolve_left two_ne_zero
              rw [hvaa]
              exact Submodule.zero_mem _
            · by_cases hcls : cls a = cls b
              · refine Submodule.mem_sup_right ?_
                have hle : V (cls a) ≤ (Finset.univ.sup V : Submodule ℝ (Ambient d)) :=
                  Finset.le_sup (Finset.mem_univ (cls a))
                apply hle
                exact Submodule.subset_span ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
                  b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩, hab, rfl⟩
              · obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv_tri 0 a.succ b.succ
                  (Fin.succ_ne_zero a).symm (fin_succ_ne hab) (Fin.succ_ne_zero b).symm
                have hc₂ : c₂ ≠ 0 := by
                  intro hc2
                  rw [hc2, zero_smul, add_zero, hv_sym 0 b.succ] at hcomb
                  have hspan_eq : Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := by
                    have hwa0 : w a ≠ 0 := hv_nz 0 a.succ (Fin.succ_ne_zero a).symm
                    have hwb0 : w b ≠ 0 := hv_nz 0 b.succ (Fin.succ_ne_zero b).symm
                    have hc13 : c₁ • w a = c₃ • w b := by
                      have : c₁ • w a + c₃ • (-w b) = 0 := hcomb
                      rw [smul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
                      exact this
                    have hc1_ne : c₁ ≠ 0 := fun h1 => by
                      rw [h1, zero_smul] at hc13
                      have hc3_ne : c₃ ≠ 0 := fun h3 => hne (by simp [h1, hc2, h3])
                      exact hwb0 ((smul_eq_zero.mp hc13.symm).resolve_left hc3_ne)
                    have hc3_ne : c₃ ≠ 0 := fun h3 => by
                      rw [h3, zero_smul] at hc13
                      exact hwa0 ((smul_eq_zero.mp hc13).resolve_left hc1_ne)
                    refine le_antisymm ?_ ?_
                    · refine Submodule.span_le.mpr ?_
                      rintro _ rfl
                      have : w a = (c₁⁻¹ * c₃) • w b := by
                        rw [mul_smul, ← hc13, smul_smul, inv_mul_cancel₀ hc1_ne, one_smul]
                      rw [SetLike.mem_coe, this]
                      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
                    · refine Submodule.span_le.mpr ?_
                      rintro _ rfl
                      have : w b = (c₃⁻¹ * c₁) • w a := by
                        rw [mul_smul, hc13, smul_smul, inv_mul_cancel₀ hc3_ne, one_smul]
                      rw [SetLike.mem_coe, this]
                      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
                  exact hcls ((hcls_iff a b).mpr hspan_eq)
                refine Submodule.mem_sup_left ?_
                have hv_eq : v a.succ b.succ = (-c₁ / c₂) • w a + (c₃ / c₂) • w b := by
                  rw [hv_sym 0 b.succ] at hcomb
                  have h1 : c₂ • v a.succ b.succ = (-c₁) • w a + c₃ • w b := by
                    change c₁ • w a + c₂ • v a.succ b.succ + c₃ • (-w b) = 0 at hcomb
                    rw [smul_neg, ← sub_eq_add_neg] at hcomb
                    calc c₂ • v a.succ b.succ
                        = c₂ • v a.succ b.succ - (c₁ • w a + c₂ • v a.succ b.succ - c₃ • w b) := by
                          rw [hcomb, sub_zero]
                      _ = (-c₁) • w a + c₃ • w b := by module
                  have h2 : v a.succ b.succ = c₂⁻¹ • ((-c₁) • w a + c₃ • w b) := by
                    rw [← h1, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
                  rw [h2]; module
                rw [hv_eq]
                exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
                  (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      have hsup_le : ∀ T : Finset (Fin s),
          Module.finrank ℝ ((T.sup V : Submodule ℝ (Ambient d))) ≤ ∑ r ∈ T, Module.finrank ℝ (V r) := fun T => by
        induction T using Finset.induction with
        | empty => simp
        | insert r T hr ihT =>
          rw [Finset.sup_insert, Finset.sum_insert hr]
          exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add_right ihT _)
      have hfib_q : ∑ r : Fin s, (classSet q s cls r).card = q := by
        have h := Finset.card_eq_sum_card_fiberwise (f := cls) (s := Finset.univ) (t := Finset.univ)
          (fun a _ => Finset.mem_univ (cls a))
        simpa [classSet] using h.symm
      have hsum_sub_q : s + ∑ r : Fin s, ((classSet q s cls r).card - 1) = q := by
        have h1 : ∑ r : Fin s, (classSet q s cls r).card =
            ∑ r : Fin s, (1 + ((classSet q s cls r).card - 1)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hcr := hC_ge1 r
          omega
        rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one] at hfib_q
        exact hfib_q
      have hsandwich_top : q ≤ Module.finrank ℝ W_top :=
        hv_dim.trans (Submodule.finrank_mono hW_sub)
      have hW_sup_le : Module.finrank ℝ W_sup ≤ ∑ r : Fin s, Module.finrank ℝ (V r) :=
        hsup_le Finset.univ
      have hsandwich_sum : Module.finrank ℝ W_top ≤
          Module.finrank ℝ U + ∑ r : Fin s, Module.finrank ℝ (V r) :=
        (Submodule.finrank_add_le_finrank_add_finrank U W_sup).trans
          (Nat.add_le_add_left hW_sup_le _)
      have hsum_V_le : ∑ r : Fin s, Module.finrank ℝ (V r) ≤
          ∑ r : Fin s, ((classSet q s cls r).card - 1) :=
        Finset.sum_le_sum fun r _ => hV_finrank r
      have hU_finrank : Module.finrank ℝ U = s := by omega
      have hs_lt_q : s < q := by omega
      have hV_finrank_eq : ∀ r : Fin s, Module.finrank ℝ (V r) = (classSet q s cls r).card - 1 := fun r => by
        by_contra hne
        have hlt : Module.finrank ℝ (V r) < (classSet q s cls r).card - 1 :=
          lt_of_le_of_ne (hV_finrank r) hne
        have hsum_lt : ∑ x : Fin s, Module.finrank ℝ (V x) <
            ∑ x : Fin s, ((classSet q s cls x).card - 1) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
          conv_rhs => rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
          exact add_lt_add_of_lt_of_le hlt
            (Finset.sum_le_sum fun x _ => hV_finrank x)
        omega
      have hUV_disj : ∀ r : Fin s, U ⊓ V r = ⊥ := fun r => by
        let T_erase : Submodule ℝ (Ambient d) := (Finset.univ.erase r).sup V
        let T0 : Submodule ℝ (Ambient d) := U ⊔ T_erase
        have hT0_sup : T0 ⊔ V r = W_top := by
          have hpart : Finset.univ = insert r (Finset.univ.erase r) :=
            (Finset.insert_erase (Finset.mem_univ r)).symm
          have hsup_eq : V r ⊔ T_erase = W_sup := by
            dsimp [W_sup, T_erase]
            rw [← Finset.sup_insert, ← hpart]
          dsimp [T0, W_top]
          rw [sup_assoc, sup_comm T_erase (V r), hsup_eq]
        have hT0_finrank : Module.finrank ℝ T0 + Module.finrank ℝ (V r) ≤ q := by
          have hT_erase_le : Module.finrank ℝ T_erase ≤
              ∑ x ∈ Finset.univ.erase r, Module.finrank ℝ (V x) :=
            hsup_le (Finset.univ.erase r)
          have h1 : Module.finrank ℝ T0 ≤ Module.finrank ℝ U + ∑ x ∈ Finset.univ.erase r, Module.finrank ℝ (V x) :=
            (Submodule.finrank_add_le_finrank_add_finrank U T_erase).trans
              (Nat.add_le_add_left hT_erase_le _)
          have h2 : (∑ x ∈ Finset.univ.erase r, Module.finrank ℝ (V x)) + Module.finrank ℝ (V r) =
              ∑ x : Fin s, Module.finrank ℝ (V x) := by
            rw [add_comm, Finset.add_sum_erase Finset.univ (fun x => Module.finrank ℝ (V x)) (Finset.mem_univ r)]
          omega
        let T0_inter : Submodule ℝ (Ambient d) := T0 ⊓ V r
        have hinf0 : Module.finrank ℝ T0_inter = 0 := by
          have hadd := Submodule.finrank_sup_add_finrank_inf_eq T0 (V r)
          rw [hT0_sup] at hadd
          change Module.finrank ℝ W_top + Module.finrank ℝ T0_inter =
            Module.finrank ℝ T0 + Module.finrank ℝ (V r) at hadd
          omega
        have hbot : T0_inter = ⊥ := Submodule.finrank_eq_zero.mp hinf0
        exact le_bot_iff.mp (by rw [← hbot]; exact inf_le_inf_right _ le_sup_left)
      have hcross_in_U : ∀ a b : Fin q, cls a ≠ cls b → v a.succ b.succ ∈ U := fun a b hcls => by
        obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := hv_tri 0 a.succ b.succ
          (Fin.succ_ne_zero a).symm (fin_succ_ne (fun h => hcls (congrArg cls h)))
          (Fin.succ_ne_zero b).symm
        have hc₂ : c₂ ≠ 0 := by
          intro hc2
          rw [hc2, zero_smul, add_zero, hv_sym 0 b.succ] at hcomb
          have hspan_eq : Submodule.span ℝ {w a} = Submodule.span ℝ {w b} := by
            have hwa0 : w a ≠ 0 := hv_nz 0 a.succ (Fin.succ_ne_zero a).symm
            have hwb0 : w b ≠ 0 := hv_nz 0 b.succ (Fin.succ_ne_zero b).symm
            have hc13 : c₁ • w a = c₃ • w b := by
              have : c₁ • w a + c₃ • (-w b) = 0 := hcomb
              rw [smul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
              exact this
            have hc1_ne : c₁ ≠ 0 := fun h1 => by
              rw [h1, zero_smul] at hc13
              have hc3_ne : c₃ ≠ 0 := fun h3 => hne (by simp [h1, hc2, h3])
              exact hwb0 ((smul_eq_zero.mp hc13.symm).resolve_left hc3_ne)
            have hc3_ne : c₃ ≠ 0 := fun h3 => by
              rw [h3, zero_smul] at hc13
              exact hwa0 ((smul_eq_zero.mp hc13).resolve_left hc1_ne)
            refine le_antisymm ?_ ?_
            · refine Submodule.span_le.mpr ?_
              rintro _ rfl
              have : w a = (c₁⁻¹ * c₃) • w b := by
                rw [mul_smul, ← hc13, smul_smul, inv_mul_cancel₀ hc1_ne, one_smul]
              rw [SetLike.mem_coe, this]
              exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
            · refine Submodule.span_le.mpr ?_
              rintro _ rfl
              have : w b = (c₃⁻¹ * c₁) • w a := by
                rw [mul_smul, hc13, smul_smul, inv_mul_cancel₀ hc3_ne, one_smul]
              rw [SetLike.mem_coe, this]
              exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
          exact hcls ((hcls_iff a b).mpr hspan_eq)
        have hv_eq : v a.succ b.succ = (-c₁ / c₂) • w a + (c₃ / c₂) • w b := by
          rw [hv_sym 0 b.succ] at hcomb
          have h1 : c₂ • v a.succ b.succ = (-c₁) • w a + c₃ • w b := by
            change c₁ • w a + c₂ • v a.succ b.succ + c₃ • (-w b) = 0 at hcomb
            rw [smul_neg, ← sub_eq_add_neg] at hcomb
            calc c₂ • v a.succ b.succ
                = c₂ • v a.succ b.succ - (c₁ • w a + c₂ • v a.succ b.succ - c₃ • w b) := by
                  rw [hcomb, sub_zero]
              _ = (-c₁) • w a + c₃ • w b := by module
          have h2 : v a.succ b.succ = c₂⁻¹ • ((-c₁) • w a + c₃ • w b) := by
            rw [← h1, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
          rw [h2]; module
        rw [hv_eq]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      have hcross_step : ∀ {a a' b : Fin q}, cls a = cls a' → cls a ≠ cls b →
          ∃ c : ℝ, c ≠ 0 ∧ v a'.succ b.succ = c • v a.succ b.succ := fun {a a' b} haa' hab => by
        by_cases ha : a = a'
        · subst ha; exact ⟨1, one_ne_zero, (one_smul ℝ _).symm⟩
        · obtain ⟨p, q₁, r₁, hpqr, htri⟩ := hv_tri a.succ a'.succ b.succ
            (fin_succ_ne ha)
            (fin_succ_ne (fun h => hab (haa'.trans (congrArg cls h))))
            (fin_succ_ne (fun h => hab (congrArg cls h)))
          have hVmem : p • v a.succ a'.succ ∈ V (cls a) :=
            Submodule.smul_mem _ p (Submodule.subset_span ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
              a', Finset.mem_filter.mpr ⟨Finset.mem_univ _, haa'.symm⟩, ha, rfl⟩)
          have hUmem : r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ ∈ U := by
            refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hcross_in_U a b hab)) ?_
            exact Submodule.smul_mem _ _ (hcross_in_U a' b (haa' ▸ hab))
          have heq : p • v a.succ a'.succ = r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ := by
            rw [hv_sym a.succ b.succ] at htri
            calc p • v a.succ a'.succ
                = p • v a.succ a'.succ - (p • v a.succ a'.succ + q₁ • v a'.succ b.succ + r₁ • (-v a.succ b.succ)) := by
                  rw [htri, sub_zero]
              _ = r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ := by module
          have h0 : p • v a.succ a'.succ = 0 := by
            have hmem : p • v a.succ a'.succ ∈ U ⊓ V (cls a) :=
              ⟨heq ▸ hUmem, hVmem⟩
            rw [hUV_disj (cls a), Submodule.mem_bot] at hmem
            exact hmem
          have hp0 : p = 0 := (smul_eq_zero.mp h0).resolve_right (hv_nz a.succ a'.succ (fin_succ_ne ha))
          have heq0 : r₁ • v a.succ b.succ - q₁ • v a'.succ b.succ = 0 := by rw [← heq, h0]
          have hq1_ne : q₁ ≠ 0 := fun hq0 => by
            rw [hq0, zero_smul, sub_zero] at heq0
            have hr1_ne : r₁ ≠ 0 := fun hr0 => hpqr (by simp [hp0, hq0, hr0])
            exact hv_nz a.succ b.succ (fin_succ_ne (fun h => hab (congrArg cls h)))
              ((smul_eq_zero.mp heq0).resolve_left hr1_ne)
          have hr1_ne : r₁ ≠ 0 := fun hr0 => by
            rw [hr0, zero_smul, zero_sub, neg_eq_zero] at heq0
            exact hv_nz a'.succ b.succ (fin_succ_ne (fun h => hab (haa'.trans (congrArg cls h))))
              ((smul_eq_zero.mp heq0).resolve_left hq1_ne)
          refine ⟨r₁ / q₁, div_ne_zero hr1_ne hq1_ne, ?_⟩
          have heq1 : q₁ • v a'.succ b.succ = r₁ • v a.succ b.succ := (sub_eq_zero.mp heq0).symm
          calc v a'.succ b.succ = q₁⁻¹ • (q₁ • v a'.succ b.succ) := by
                rw [smul_smul, inv_mul_cancel₀ hq1_ne, one_smul]
            _ = (r₁ / q₁) • v a.succ b.succ := by rw [heq1, smul_smul, div_eq_inv_mul]
      have hcross_prop : ∀ {a a' b b' : Fin q}, cls a = cls a' → cls b = cls b' → cls a ≠ cls b →
          ∃ c : ℝ, c ≠ 0 ∧ v a'.succ b'.succ = c • v a.succ b.succ := fun {a a' b b'} ha hb hab => by
        obtain ⟨c₁, hc1, hstep1⟩ := hcross_step ha hab
        obtain ⟨c₂, hc2, hstep2⟩ := hcross_step hb (fun h => hab (ha.trans h.symm))
        refine ⟨c₁ * c₂, mul_ne_zero hc1 hc2, ?_⟩
        calc v a'.succ b'.succ = - v b'.succ a'.succ := hv_sym _ _
          _ = - (c₂ • v b.succ a'.succ) := by rw [hstep2]
          _ = c₂ • (- v b.succ a'.succ) := (smul_neg _ _).symm
          _ = c₂ • v a'.succ b.succ := by rw [← hv_sym b.succ a'.succ]
          _ = c₂ • (c₁ • v a.succ b.succ) := by rw [hstep1]
          _ = (c₁ * c₂) • v a.succ b.succ := by rw [smul_smul, mul_comm c₂ c₁]
      let vU : Fin (s + 1) → Fin (s + 1) → Ambient d := fun i j =>
        Fin.cases
          (Fin.cases 0 (fun r => v 0 (rep r).succ) j)
          (fun r₁ => Fin.cases (v (rep r₁).succ 0) (fun r₂ => v (rep r₁).succ (rep r₂).succ) j)
          i
      have hvU_rep : ∀ i j : Fin (s + 1),
          vU i j = v (Fin.cases 0 (fun r => (rep r).succ) i) (Fin.cases 0 (fun r => (rep r).succ) j) := by
        intro i j
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero =>
            simp only [vU, Fin.cases_zero]
            have hv00 : v 0 0 = 0 := by
              have h := hv_sym 0 0
              have : (2 : ℝ) • v 0 0 = 0 := by
                calc (2 : ℝ) • v 0 0 = v 0 0 + v 0 0 := two_smul ℝ _
                  _ = v 0 0 + (- v 0 0) := by conv_lhs => rhs; rw [h]
                  _ = 0 := add_neg_cancel _
              exact (smul_eq_zero.mp this).resolve_left two_ne_zero
            exact hv00.symm
          | succ r => simp only [vU, Fin.cases_zero, Fin.cases_succ]
        | succ r₁ =>
          induction j using Fin.cases with
          | zero => simp only [vU, Fin.cases_zero, Fin.cases_succ]
          | succ r₂ => simp only [vU, Fin.cases_succ]
      have hrep_inj : Function.Injective (Fin.cases (0 : Fin (q + 1)) (fun r => (rep r).succ)) := by
        intro x y h
        induction x using Fin.cases with
        | zero =>
          induction y using Fin.cases with
          | zero => rfl
          | succ r => simp only [Fin.cases_zero, Fin.cases_succ] at h; exact False.elim (Fin.succ_ne_zero _ h.symm)
        | succ r₁ =>
          induction y using Fin.cases with
          | zero => simp only [Fin.cases_zero, Fin.cases_succ] at h; exact False.elim (Fin.succ_ne_zero _ h)
          | succ r₂ =>
            simp only [Fin.cases_succ] at h
            have hrep_eq : rep r₁ = rep r₂ := Fin.succ_injective _ h
            rw [← hcls_rep r₁, ← hcls_rep r₂, hrep_eq]
      have hvU_sym : ∀ i j, vU j i = - vU i j := fun i j => by
        rw [hvU_rep, hvU_rep, hv_sym]
      have hvU_nz : ∀ i j, i ≠ j → vU i j ≠ 0 := fun i j hij => by
        rw [hvU_rep]
        exact hv_nz _ _ (fun h => hij (hrep_inj h))
      have hvU_tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
          ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • vU i j + c₂ • vU j k + c₃ • vU k i = 0 :=
          fun i j k hij hjk hik => by
        rw [hvU_rep, hvU_rep, hvU_rep]
        exact hv_tri _ _ _ (fun h => hij (hrep_inj h)) (fun h => hjk (hrep_inj h)) (fun h => hik (hrep_inj h))
      have hvU_dim : s ≤ Module.finrank ℝ
          (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (s + 1), x = vU i j}) := by
        have hle : U ≤ Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (s + 1), x = vU i j} := by
          rw [hU_eq_rep]
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨r, rfl⟩
          exact Submodule.subset_span ⟨0, r.succ, rfl⟩
        exact hU_finrank.symm.le.trans (Submodule.finrank_mono hle)
      obtain ⟨shU₀, heqU₀, hvalU₀, θU₀, hθU₀⟩ := ih s hs_lt_q hs1 (by omega) (by omega) vU hvU_sym hvU_nz hvU_tri hvU_dim
      obtain ⟨shU, heqU, hvalU, θU, hθU⟩ := exists_liftShape (q - 1) (by omega) shU₀ hvalU₀
        (fun e => vU (Fin.cast (congrArg (· + 1) heqU₀) e.1.1) (Fin.cast (congrArg (· + 1) heqU₀) e.1.2))
        ⟨θU₀, fun e => hθU₀ e⟩
      have hshC_ex : ∀ r : Fin s, ∃ (shC : TreeShape d (q - 1))
          (heqC : shC.dim = (classSet q s cls r).card - 1),
          shC.Valid ∧
          ∃ θC : shC.ParamIdx → ℝ,
            ∀ e : Pairs (shC.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
              let ord := (classSet q s cls r).orderIsoOfFin rfl
              shC.evalEdges θC e = c • v (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                         (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r => by
        let C := classSet q s cls r
        by_cases hC1 : C.card = 1
        · have hunit_dim : (TreeShape.unit (d := d)).dim = 0 := rfl
          obtain ⟨shC, heqC, hvalC, θC, _⟩ := exists_liftShape (q - 1) (Nat.zero_le _)
            (TreeShape.unit (d := d)) (by trivial)
            (fun _ => 0) ⟨Empty.elim, fun e => by
              exfalso
              have hle0 : (e.1.1 : ℕ) < (e.1.2 : ℕ) := e.2
              have hlt0 : (e.1.2 : ℕ) < (TreeShape.unit (d := d)).dim + 1 := e.1.2.2
              omega⟩
          have hdim0 : shC.dim = 0 := heqC.trans hunit_dim
          have hcard1 : (classSet q s cls r).card = 1 := hC1
          refine ⟨shC, by rw [hdim0, hcard1], hvalC, θC, fun e => ?_⟩
          exfalso
          have hle0 : (e.1.1 : ℕ) < (e.1.2 : ℕ) := e.2
          have hlt0 : (e.1.2 : ℕ) < shC.dim + 1 := e.1.2.2
          omega
        · have hC_ge1' : 1 ≤ (classSet q s cls r).card := hC_ge1 r
          have hC1' : (classSet q s cls r).card ≠ 1 := hC1
          have hC2 : 2 ≤ C.card := by
            change 2 ≤ (classSet q s cls r).card
            omega
          let q_r := C.card - 1
          have hqr1 : 1 ≤ q_r := by omega
          have hqr_lt : q_r < q := by
            have hle : C.card ≤ q := by simpa [C] using Finset.card_le_univ C
            omega
          have hC_card_eq : C.card = q_r + 1 := by omega
          let ord : Fin (q_r + 1) ≃o C := C.orderIsoOfFin hC_card_eq
          let v_r : Fin (q_r + 1) → Fin (q_r + 1) → Ambient d := fun i j => v (ord i).1.succ (ord j).1.succ
          have hv_r_sym : ∀ i j, v_r j i = - v_r i j := fun i j => hv_sym _ _
          have hv_r_nz : ∀ i j, i ≠ j → v_r i j ≠ 0 := fun i j hij =>
            hv_nz _ _ (fin_succ_ne (fun h => hij (ord.injective (Subtype.ext h))))
          have hv_r_tri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
              ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • v_r i j + c₂ • v_r j k + c₃ • v_r k i = 0 :=
              fun i j k hij hjk hik =>
            hv_tri _ _ _
              (fin_succ_ne (fun h => hij (ord.injective (Subtype.ext h))))
              (fin_succ_ne (fun h => hjk (ord.injective (Subtype.ext h))))
              (fin_succ_ne (fun h => hik (ord.injective (Subtype.ext h))))
          have hv_r_dim : q_r ≤ Module.finrank ℝ
              (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q_r + 1), x = v_r i j}) := by
            have hle : V r ≤ Submodule.span ℝ {x : Ambient d | ∃ i j : Fin (q_r + 1), x = v_r i j} := by
              refine Submodule.span_le.mpr ?_
              rintro _ ⟨a, ha, b, hb, _, rfl⟩
              exact Submodule.subset_span ⟨ord.symm ⟨a, ha⟩, ord.symm ⟨b, hb⟩, by simp [v_r]⟩
            exact (hV_finrank_eq r).symm.le.trans (Submodule.finrank_mono hle)
          obtain ⟨shC₀, heqC₀, hvalC₀, θC₀, hθC₀⟩ :=
            ih q_r hqr_lt hqr1 (by omega) (by omega) v_r hv_r_sym hv_r_nz hv_r_tri hv_r_dim
          obtain ⟨shC, heqC, hvalC, θC, hθC⟩ :=
            exists_liftShape (q - 1) (by omega) shC₀ hvalC₀
              (fun e => v_r (Fin.cast (congrArg (· + 1) heqC₀) e.1.1) (Fin.cast (congrArg (· + 1) heqC₀) e.1.2))
              ⟨θC₀, fun e => hθC₀ e⟩
          refine ⟨shC, heqC.trans heqC₀, hvalC, θC, fun e => ?_⟩
          obtain ⟨c, hc, hce⟩ := hθC e
          refine ⟨c, hc, ?_⟩
          rw [hce]
          have hcast1 : (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.1))).1 =
              (((classSet q s cls r).orderIsoOfFin rfl)
                (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.1)).1 :=
            orderIsoOfFin_val_eq (classSet q s cls r) hC_card_eq rfl _ _ rfl
          have hcast2 : (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.2))).1 =
              (((classSet q s cls r).orderIsoOfFin rfl)
                (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.2)).1 :=
            orderIsoOfFin_val_eq (classSet q s cls r) hC_card_eq rfl _ _ rfl
          change c • v (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.1))).1.succ
                       (ord (Fin.cast (congrArg (· + 1) heqC₀) (Fin.cast (congrArg (· + 1) heqC) e.1.2))).1.succ =
                 c • v (((classSet q s cls r).orderIsoOfFin rfl)
                         (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.1)).1.succ
                       (((classSet q s cls r).orderIsoOfFin rfl)
                         (Fin.cast (by rw [heqC.trans heqC₀, ← hC_card_eq]) e.1.2)).1.succ
          rw [hcast1, hcast2]
      let q' : Fin 6 := ⟨q, by omega⟩
      let s' : Fin 6 := ⟨s, by omega⟩
      let shC_fn : Fin s'.1 → TreeShape d (q - 1) := fun r => Classical.choose (hshC_ex r)
      have hshC_spec : ∀ r : Fin s, ∃ (heqC : (shC_fn r).dim = (classSet q s cls r).card - 1),
          (shC_fn r).Valid ∧
          ∃ θC : (shC_fn r).ParamIdx → ℝ,
            ∀ e : Pairs ((shC_fn r).dim + 1), ∃ c : ℝ, c ≠ 0 ∧
              let ord := (classSet q s cls r).orderIsoOfFin rfl
              (shC_fn r).evalEdges θC e = c • v (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                               (ord (Fin.cast (by rw [heqC]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r =>
        Classical.choose_spec (hshC_ex r)
      let heqC_fn : ∀ r : Fin s, (shC_fn r).dim = (classSet q s cls r).card - 1 := fun r =>
        Classical.choose (hshC_spec r)
      have hshC_val : ∀ r : Fin s, (shC_fn r).Valid ∧
          ∃ θC : (shC_fn r).ParamIdx → ℝ,
            ∀ e : Pairs ((shC_fn r).dim + 1), ∃ c : ℝ, c ≠ 0 ∧
              let ord := (classSet q s cls r).orderIsoOfFin rfl
              (shC_fn r).evalEdges θC e = c • v (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                               (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r =>
        Classical.choose_spec (hshC_spec r)
      let θC_fn : ∀ r : Fin s, (shC_fn r).ParamIdx → ℝ := fun r => Classical.choose (hshC_val r).2
      have hθC_fn : ∀ (r : Fin s) (e : Pairs ((shC_fn r).dim + 1)), ∃ c : ℝ, c ≠ 0 ∧
          let ord := (classSet q s cls r).orderIsoOfFin rfl
          (shC_fn r).evalEdges (θC_fn r) e = c • v (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.1)).1.succ
                                                 (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) e.1.2)).1.succ := fun r =>
        Classical.choose_spec (hshC_val r).2
      let sh1 : TreeShape d ((q - 1) + 1) := .split q' s' cls shU shC_fn
      have hsh1_val : sh1.Valid := ⟨hq2, hqd, hs1, hs_lt_q, hC_ge1, hvalU, heqU.trans heqU₀,
        fun r => ⟨(hshC_val r).1, heqC_fn r⟩⟩
      let θ1 : (TreeShape.split q' s' cls shU shC_fn).ParamIdx → ℝ :=
        Sum.elim θU (fun p => θC_fn p.1 p.2)
      have hs_dim_eq : shU.dim = s := heqU.trans heqU₀
      have hs'_val : s'.1 = s := rfl
      have hU_dim_eq : s'.1 + 1 = shU.dim + 1 := by rw [hs_dim_eq, hs'_val]
      have hrep1_aux : ∀ (e : Pairs (q'.1 + 1)), ∃ c : ℝ, c ≠ 0 ∧
          (TreeShape.split q' s' cls shU shC_fn).evalEdges θ1 e = c • v e.1.1 e.1.2 := fun e => by
        rw [evalEdges_split]
        have hlt_e : e.1.1 < e.1.2 := e.2
        have hθU_eq : (fun x => θ1 (Sum.inl x)) = θU := rfl
        rcases Fin.eq_zero_or_eq_succ e.1.1 with hi | ⟨a, hi⟩
        · rcases Fin.eq_zero_or_eq_succ e.1.2 with hj | ⟨b, hj⟩
          · exact False.elim (Fin.ne_of_lt hlt_e (hi.trans hj.symm))
          · rw [hi, hj]
            simp only [Fin.cases_zero, Fin.cases_succ, hU_dim_eq, ↓reduceDIte, hθU_eq]
            obtain ⟨c₀, hc0, hce0⟩ := hθU (castPair hU_dim_eq ⟨(0, (cls b).succ), Nat.zero_lt_succ _⟩)
            have hspan : Submodule.span ℝ {w b} = Submodule.span ℝ {w (rep (cls b))} :=
              (hcls_iff b (rep (cls b))).mp (hcls_rep (cls b)).symm
            have hmem : w (rep (cls b)) ∈ Submodule.span ℝ {w b} := by
              rw [hspan]; exact Submodule.subset_span rfl
            obtain ⟨c₁, hc1⟩ := Submodule.mem_span_singleton.mp hmem
            have hc1_ne : c₁ ≠ 0 := fun h0 => by
              rw [h0, zero_smul] at hc1
              exact hv_nz 0 (rep (cls b)).succ (Fin.succ_ne_zero _).symm hc1.symm
            refine ⟨c₀ * c₁, mul_ne_zero hc0 hc1_ne, ?_⟩
            rw [hce0]
            have hc0_eq : Fin.cast (congrArg (· + 1) heqU₀)
                (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (0 : Fin (s'.1 + 1)))) =
                (0 : Fin (s + 1)) := Fin.ext rfl
            have hcb_eq : Fin.cast (congrArg (· + 1) heqU₀)
                (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)) =
                (cls b).succ := Fin.ext rfl
            have hvU0 : vU (Fin.cast (congrArg (· + 1) heqU₀)
                  (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (0 : Fin (s'.1 + 1)))))
                (Fin.cast (congrArg (· + 1) heqU₀)
                  (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ))) =
                v 0 (rep (cls b)).succ := by
              rw [hvU_rep, hc0_eq, hcb_eq]; rfl
            dsimp [castPair] at hvU0 ⊢
            rw [hvU0]
            change c₀ • w (rep (cls b)) = (c₀ * c₁) • v 0 b.succ
            rw [← hc1]
            change c₀ • (c₁ • v 0 b.succ) = (c₀ * c₁) • v 0 b.succ
            rw [smul_smul]
        · rcases Fin.eq_zero_or_eq_succ e.1.2 with hj | ⟨b, hj⟩
          · rw [hi, hj] at hlt_e
            exact False.elim (Nat.not_lt_zero _ hlt_e)
          · have hab_lt : a < b := by
              have hlt' : (e.1.1 : ℕ) < (e.1.2 : ℕ) := hlt_e
              rw [hi, hj] at hlt'
              exact Nat.succ_lt_succ_iff.mp hlt'
            rw [hi, hj]
            simp only [Fin.cases_succ]
            by_cases hcls : cls a = cls b
            · simp only [dif_pos hcls]
              let r := cls a
              let C := classSet q'.1 s'.1 cls r
              have hC_ge1' : 1 ≤ (classSet q s cls r).card := hC_ge1 r
              have heqC' : (shC_fn r).dim = (classSet q s cls r).card - 1 := heqC_fn r
              have hC_eq : C.card = (shC_fn r).dim + 1 := by
                change (classSet q s cls r).card = (shC_fn r).dim + 1
                omega
              rw [dif_pos hC_eq]
              let ord := C.orderIsoOfFin rfl
              let i' : Fin C.card := ord.symm ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              let j' : Fin C.card := ord.symm ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls.symm⟩⟩
              have hij' : i' < j' := ord.symm.strictMono (Subtype.mk_lt_mk.mpr hab_lt)
              have hθC_eq : (fun x => θ1 (Sum.inr ⟨r, x⟩)) = θC_fn r := rfl
              rw [dif_pos hij', hθC_eq]
              obtain ⟨c₀, hc0, hce0⟩ := hθC_fn r (castPair hC_eq ⟨(i', j'), hij'⟩)
              refine ⟨c₀, hc0, ?_⟩
              rw [hce0]
              have hord_i : (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega)
                  (Fin.cast hC_eq i'))).1 = a := by
                have hfi : Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq i') = i' := by
                  ext; rfl
                rw [hfi]
                change (ord (ord.symm ⟨a, _⟩)).1 = a
                simp
              have hord_j : (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega)
                  (Fin.cast hC_eq j'))).1 = b := by
                have hfj : Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq j') = j' := by
                  ext; rfl
                rw [hfj]
                change (ord (ord.symm ⟨b, _⟩)).1 = b
                simp
              dsimp [castPair]
              change c₀ • v (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq i'))).1.succ
                           (ord (Fin.cast (by rw [heqC_fn r]; have := hC_ge1 r; omega) (Fin.cast hC_eq j'))).1.succ =
                     c₀ • v a.succ b.succ
              rw [hord_i, hord_j]
            · simp only [dif_neg hcls, dif_pos hU_dim_eq, hθU_eq]
              rcases lt_or_gt_of_ne hcls with hlt | hgt
              · simp only [dif_pos hlt]
                obtain ⟨c₀, hc0, hce0⟩ := hθU (castPair hU_dim_eq ⟨((cls a).succ, (cls b).succ), Nat.succ_lt_succ hlt⟩)
                obtain ⟨c₃, hc3, hce3⟩ := hcross_prop (hcls_rep (cls a)).symm (hcls_rep (cls b)).symm hcls
                refine ⟨c₀ * c₃, mul_ne_zero hc0 hc3, ?_⟩
                rw [hce0]
                have hca_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ)) =
                    (cls a).succ := Fin.ext rfl
                have hcb_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)) =
                    (cls b).succ := Fin.ext rfl
                have hvU_e : vU (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ)))
                    (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ))) =
                    v (rep (cls a)).succ (rep (cls b)).succ := by
                  rw [hvU_rep, hca_eq, hcb_eq]; rfl
                dsimp [castPair] at hvU_e ⊢
                rw [hvU_e, hce3, smul_smul]
              · have hnot : ¬ cls a < cls b := Nat.not_lt.mpr hgt.le
                simp only [dif_neg hnot, dif_pos hgt]
                obtain ⟨c₀, hc0, hce0⟩ := hθU (castPair hU_dim_eq ⟨((cls b).succ, (cls a).succ), Nat.succ_lt_succ hgt⟩)
                obtain ⟨c₃, hc3, hce3⟩ := hcross_prop (hcls_rep (cls a)).symm (hcls_rep (cls b)).symm hcls
                refine ⟨c₀ * c₃, mul_ne_zero hc0 hc3, ?_⟩
                rw [hce0]
                have hcb_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)) =
                    (cls b).succ := Fin.ext rfl
                have hca_eq : Fin.cast (congrArg (· + 1) heqU₀)
                    (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ)) =
                    (cls a).succ := Fin.ext rfl
                have hvU_e : vU (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls b).succ)))
                    (Fin.cast (congrArg (· + 1) heqU₀)
                      (Fin.cast (congrArg (· + 1) heqU) (Fin.cast hU_dim_eq (cls a).succ))) =
                    v (rep (cls b)).succ (rep (cls a)).succ := by
                  rw [hvU_rep, hcb_eq, hca_eq]; rfl
                dsimp [castPair] at hvU_e ⊢
                rw [hvU_e, hv_sym (rep (cls a)).succ (rep (cls b)).succ, smul_neg, neg_neg, hce3, smul_smul]
      have hrep1 : ∀ e : Pairs (sh1.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
          sh1.evalEdges θ1 e = c • v e.1.1 e.1.2 := hrep1_aux
      obtain ⟨sh, heq, hval, θ, hθ⟩ := exists_liftShape q (by omega) sh1 hsh1_val
        (fun e => v e.1.1 e.1.2) ⟨θ1, hrep1⟩
      refine ⟨sh, heq, hval, θ, fun e => ?_⟩
      exact hθ e

private structure MaxRankConfig (d m : ℕ) where
  sh : {sh : TreeShape d 5 // sh.Valid ∧ sh.dim = 5}
  σ : Fin m → Pairs6
  piv : Fin m → Fin d

private instance instFiniteMaxRankConfig (d m : ℕ) : Finite (MaxRankConfig d m) :=
  Finite.of_injective
    (fun c : MaxRankConfig d m => (c.sh, c.σ, c.piv))
    (fun c₁ c₂ h => by
      cases c₁; cases c₂
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl)

private abbrev MaxRankParamIdx (d m : ℕ) (c : MaxRankConfig d m) : Type :=
  c.sh.1.ParamIdx ⊕ ((a : Fin m) × {j : Fin d // j ≠ c.piv a})

private lemma card_maxRankParamIdx {d m : ℕ} (c : MaxRankConfig d m) :
    Fintype.card (MaxRankParamIdx d m c) ≤ 5 * d - 1 + m * (d - 1) := by
  have h1 : Fintype.card c.sh.1.ParamIdx ≤ 5 * d - 1 := by
    have hb := card_paramIdx_bound c.sh.1 c.sh.2.1
    rwa [c.sh.2.2] at hb
  have h2 : ∀ a : Fin m, Fintype.card {j : Fin d // j ≠ c.piv a} = d - 1 := fun a => by
    have heq : {j : Fin d // j ≠ c.piv a} ≃
        {j : Fin d // j ∈ Finset.univ.erase (c.piv a)} :=
      Equiv.subtypeEquivRight fun j => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  simp only [MaxRankParamIdx, Fintype.card_sum, Fintype.card_sigma, h2, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_le_add_right h1 (m * (d - 1))

private noncomputable def coordCLM {d : ℕ} (j : Fin d) : Ambient d →L[ℝ] ℝ :=
  { toFun := fun x => x j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    cont := (continuous_apply j).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous }

private noncomputable def maxRankNormal {d m : ℕ} (c : MaxRankConfig d m)
    (y : MaxRankParamIdx d m c → ℝ) (a : Fin m) : Ambient d :=
  c.sh.1.evalEdges (fun idx => y (Sum.inl idx))
    (castPair (congrArg (· + 1) c.sh.2.2.symm) (c.σ a))

private def maxRankP0 {d m : ℕ} (c : MaxRankConfig d m)
    (y : MaxRankParamIdx d m c → ℝ) (a : Fin m) (j : Fin d) : ℝ :=
  if h : j = c.piv a then 0 else y (Sum.inr ⟨a, ⟨j, h⟩⟩)

private noncomputable def maxRankOpen {d m : ℕ} (c : MaxRankConfig d m) :
    Set (MaxRankParamIdx d m c → ℝ) :=
  {y | ∀ a : Fin m, maxRankNormal c y a (c.piv a) ≠ 0}

private noncomputable def maxRankMap {d m : ℕ} (c : MaxRankConfig d m)
    (y : MaxRankParamIdx d m c → ℝ) : Fin (m * d) → ℝ :=
  fun x =>
    let p := finProdFinEquiv.symm x
    if p.2 = c.piv p.1 then
      - (∑ j : Fin d, maxRankNormal c y p.1 j * maxRankP0 c y p.1 j) /
          maxRankNormal c y p.1 (c.piv p.1)
    else
      maxRankP0 c y p.1 p.2

private lemma differentiableOn_maxRankMap {d m : ℕ} (c : MaxRankConfig d m) :
    DifferentiableOn ℝ (maxRankMap c) (maxRankOpen c) := by
  have hθ : Differentiable ℝ (fun y : MaxRankParamIdx d m c → ℝ => fun idx => y (Sum.inl idx)) :=
    differentiable_pi.mpr fun idx => differentiable_apply (Sum.inl idx)
  have hn : ∀ a j, Differentiable ℝ fun y => maxRankNormal c y a j := fun a j =>
    (coordCLM j).differentiable.comp
      ((differentiable_evalEdges c.sh.1 _).comp hθ)
  have hp0 : ∀ a j, Differentiable ℝ fun y => maxRankP0 c y a j := fun a j => by
    dsimp [maxRankP0]
    split_ifs
    · exact differentiable_const 0
    · exact differentiable_apply _
  refine differentiableOn_pi.mpr fun x => ?_
  dsimp [maxRankMap]
  split_ifs
  · simp_rw [div_eq_mul_inv]
    exact ((Differentiable.fun_sum fun j _ => (hn _ j).mul (hp0 _ j)).neg.differentiableOn).mul
      (((hn _ _).differentiableOn).inv fun y (hy : y ∈ maxRankOpen c) => hy _)
  · exact (hp0 _ _).differentiableOn

private lemma mem_range_maxRankMap_of_tree {d m : ℕ}
    (z : Fin (m * d) → ℝ)
    (hz_ball : ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j)
    (hS_univ : nonEmptyIntParts C = Finset.univ)
    (hnne : ∀ i j : Fin 6, i ≠ j → n i j ≠ 0)
    (hnsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hno_int : ∀ (k₁ : Fin 6) (a : Fin m), evalPoints z a ∉ interior (C k₁ : Set (Ambient d)))
    (sh : TreeShape d 5) (hsh_val : sh.Valid) (hsh_dim : sh.dim = 5)
    (θ : sh.ParamIdx → ℝ)
    (hθ : ∀ e : Pairs (sh.dim + 1), ∃ c : ℝ, c ≠ 0 ∧
      sh.evalEdges θ e =
        c • n (Fin.cast (congrArg (· + 1) hsh_dim) e.1.1)
              (Fin.cast (congrArg (· + 1) hsh_dim) e.1.2)) :
    ∃ c : MaxRankConfig d m, z ∈ maxRankMap c '' maxRankOpen c := by
  classical
  let p : Fin m → Ambient d := evalPoints z
  have hex_sig : ∀ a : Fin m, ∃ e : Pairs6, ⟪n e.1.1 e.1.2, p a⟫_ℝ = 0 := fun a => by
    obtain ⟨i, _hiS, j, _hjS, hij, hzero⟩ :=
      skeleton_in_separating_hyperplanes C hcov n hnsep hnsym (hz_ball a)
        (fun q hq => hno_int q a hq)
    exact ⟨⟨(i, j), hij⟩, hzero⟩
  choose σ hσ_zero using hex_sig
  have hex_piv : ∀ a : Fin m, ∃ j : Fin d,
      sh.evalEdges θ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)) j ≠ 0 := fun a => by
    obtain ⟨c₀, hc0, hce0⟩ := hθ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a))
    have hcast1 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.1 = (σ a).1.1 := Fin.ext rfl
    have hcast2 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.2 = (σ a).1.2 := Fin.ext rfl
    rw [hcast1, hcast2] at hce0
    have hne0 : sh.evalEdges θ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)) ≠ 0 := by
      rw [hce0]
      exact smul_ne_zero hc0 (hnne _ _ (Fin.ne_of_lt (σ a).2))
    by_contra hall
    push Not at hall
    exact hne0 (PiLp.ext hall)
  choose piv hpiv_ne using hex_piv
  let cfg : MaxRankConfig d m := ⟨⟨sh, hsh_val, hsh_dim⟩, σ, piv⟩
  let y : MaxRankParamIdx d m cfg → ℝ :=
    Sum.elim θ (fun q => p q.1 q.2.1)
  have hy_open : y ∈ maxRankOpen cfg := fun a => by
    dsimp [maxRankNormal, cfg]
    exact hpiv_ne a
  have hy_N_perp : ∀ a : Fin m, ∑ j : Fin d, maxRankNormal cfg y a j * p a j = 0 := fun a => by
    obtain ⟨c₀, _, hce0⟩ := hθ (castPair (congrArg (· + 1) hsh_dim.symm) (σ a))
    have hcast1 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.1 = (σ a).1.1 := Fin.ext rfl
    have hcast2 : Fin.cast (congrArg (· + 1) hsh_dim)
        (castPair (congrArg (· + 1) hsh_dim.symm) (σ a)).1.2 = (σ a).1.2 := Fin.ext rfl
    rw [hcast1, hcast2] at hce0
    have hinner0 : ⟪maxRankNormal cfg y a, p a⟫_ℝ = 0 := by
      have heq_θ : (fun idx => y (Sum.inl idx)) = θ := rfl
      dsimp [maxRankNormal, cfg]
      rw [heq_θ, hce0, real_inner_smul_left, hσ_zero a, mul_zero]
    simpa only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
      conj_trivial, mul_comm] using hinner0
  refine ⟨cfg, y, hy_open, ?_⟩
  funext x
  obtain ⟨⟨a, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  have hp_eq : p a j = z (finProdFinEquiv (a, j)) := rfl
  dsimp [maxRankMap]
  rw [finProdFinEquiv.symm_apply_apply]
  split_ifs with hj
  · have hj_eq : j = cfg.piv a := hj
    have hp0_eq : ∀ q : Fin d, maxRankP0 cfg y a q =
        if q = cfg.piv a then 0 else p a q := fun q => by
      dsimp [maxRankP0, cfg, y]
    simp_rw [hp0_eq]
    have hsplit : ∑ q : Fin d, maxRankNormal cfg y a q * (if q = cfg.piv a then 0 else p a q) =
        ∑ q ∈ Finset.univ.erase (cfg.piv a), maxRankNormal cfg y a q * p a q := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (cfg.piv a))]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp [(Finset.mem_erase.mp hq).1]
    have hsplit_full : ∑ q : Fin d, maxRankNormal cfg y a q * p a q =
        maxRankNormal cfg y a (cfg.piv a) * p a (cfg.piv a) +
          ∑ q ∈ Finset.univ.erase (cfg.piv a), maxRankNormal cfg y a q * p a q :=
      (Finset.add_sum_erase Finset.univ (fun q => maxRankNormal cfg y a q * p a q)
        (Finset.mem_univ (cfg.piv a))).symm
    rw [hy_N_perp a] at hsplit_full
    have hpiv0 : maxRankNormal cfg y a (cfg.piv a) ≠ 0 := hy_open a
    have hpj : p a (cfg.piv a) = z (finProdFinEquiv (a, j)) := by
      rw [← hj_eq, hp_eq]
    rw [hsplit, ← hpj]
    exact div_eq_of_eq_mul hpiv0 (by rw [mul_comm]; linarith)
  · have hj_ne : j ≠ cfg.piv a := hj
    dsimp [maxRankP0, y]
    split_ifs with h
    · exact False.elim (hj_ne h)
    · exact hp_eq

/-- Unconditional existence of `5 * d` central blocking points in `unitBall d` (`d ≥ 30`). -/
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

private def mkPair6 (i j : Fin 6) (hij : i ≠ j) : Pairs6 :=
  if h : i < j then ⟨(i, j), h⟩ else ⟨(j, i), lt_of_le_of_ne (not_lt.mp h) hij.symm⟩

private lemma mkPair6_comm (i j : Fin 6) (hij : i ≠ j) :
    mkPair6 j i hij.symm = mkPair6 i j hij := by
  dsimp [mkPair6]
  split_ifs with h1 h2 h3
  · exact False.elim (lt_asymm h1 h2)
  · rfl
  · rfl
  · exact False.elim (hij (le_antisymm (not_lt.mp h1) (not_lt.mp h3)))

/-! ### Section 1: DAG parametrization & finite closed-cover interior lemma -/

private inductive DagOp (t : ℕ) : Type
  | free (piv : Fin 4) : DagOp t
  | ridge (a b : Fin t) : DagOp t

private instance instFiniteDagOp (t : ℕ) : Finite (DagOp t) :=
  Finite.of_injective
    (fun op : DagOp t => match op with
      | .free p => Sum.inl p
      | .ridge a b => Sum.inr (a, b))
    (fun op₁ op₂ h => by
      cases op₁ <;> cases op₂ <;> simp_all)

private def dagArity {t : ℕ} : DagOp t → ℕ
  | .free _ => 3
  | .ridge _ _ => 1

private def freeVec (p : Fin 4) (v : Fin 3 → ℝ) (q : Fin 4) : ℝ :=
  if q = p then 1 else ∑ k : Fin 3, if p.succAbove k = q then v k else 0

private lemma freeVec_self (p : Fin 4) (v : Fin 3 → ℝ) : freeVec p v p = 1 := by
  simp [freeVec]

private lemma freeVec_ne_zero (p : Fin 4) (v : Fin 3 → ℝ) : freeVec p v ≠ 0 := by
  intro h
  have := congrFun h p
  rw [freeVec_self] at this
  exact one_ne_zero this

private lemma freeVec_eq_smul (x : Fin 4 → ℝ) (p : Fin 4) (hp : x p ≠ 0) :
    x = (x p) • freeVec p (fun k => x (p.succAbove k) / x p) := by
  funext q
  simp only [Pi.smul_apply, smul_eq_mul, freeVec]
  by_cases hqp : q = p
  · subst hqp; simp
  · simp only [hqp, ↓reduceIte]
    obtain ⟨k₀, hk₀⟩ := Fin.exists_succAbove_eq hqp
    rw [Finset.sum_eq_single k₀]
    · simp [hk₀]; field_simp [hp]
    · intro k _ hkne
      split_ifs with hk
      · exact False.elim (hkne (Fin.succAbove_right_injective (hk.trans hk₀.symm)))
      · rfl
    · simp

private lemma differentiable_freeVec (p : Fin 4) (q : Fin 4) :
    Differentiable ℝ (fun v : Fin 3 → ℝ => freeVec p v q) := by
  dsimp [freeVec]
  split_ifs
  · exact differentiable_const 1
  · refine Differentiable.fun_sum fun k _ => ?_
    split_ifs
    · exact differentiable_apply k
    · exact differentiable_const 0

private def evalDagStep {t : ℕ} (op : DagOp t) (prev : Fin t → (Fin 4 → ℝ))
    (u : Fin (dagArity op) → ℝ) : Fin 4 → ℝ :=
  match op with
  | .free p => freeVec p u
  | .ridge a b =>
    let s := u ⟨0, by simp [dagArity]⟩
    fun q => prev a q + s * prev b q

private lemma differentiable_evalDagStep {t : ℕ} (op : DagOp t) (q : Fin 4) :
    Differentiable ℝ (fun pair : (Fin t → (Fin 4 → ℝ)) × (Fin (dagArity op) → ℝ) =>
      evalDagStep op pair.1 pair.2 q) := by
  cases op with
  | free p =>
    exact (differentiable_freeVec p q).comp differentiable_snd
  | ridge a b =>
    have ha : Differentiable ℝ (fun pair : (Fin t → (Fin 4 → ℝ)) × (Fin 1 → ℝ) => pair.1 a q) := by
      fun_prop
    have hb : Differentiable ℝ (fun pair : (Fin t → (Fin 4 → ℝ)) × (Fin 1 → ℝ) => pair.1 b q) := by
      fun_prop
    have hs : Differentiable ℝ (fun pair : (Fin t → (Fin 4 → ℝ)) × (Fin 1 → ℝ) =>
        pair.2 ⟨0, by decide⟩) := by
      fun_prop
    exact ha.add (hs.mul hb)

private def evalDagNormalsAux {M : ℕ} (steps : (t : Fin M) → DagOp t.1)
    (ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ) :
    (t : ℕ) → t < M → (Fin 4 → ℝ)
  | t, ht =>
    evalDagStep (steps ⟨t, ht⟩)
      (fun i => evalDagNormalsAux steps ψ i.1 (Nat.lt_trans i.2 ht))
      (ψ ⟨t, ht⟩)
termination_by t => t

private def evalDagNormals {M : ℕ} (steps : (t : Fin M) → DagOp t.1)
    (ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ) (t : Fin M) : Fin 4 → ℝ :=
  evalDagNormalsAux steps ψ t.1 t.2

private lemma evalDagNormals_eq {M : ℕ} (steps : (t : Fin M) → DagOp t.1)
    (ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ) (t : Fin M) :
    evalDagNormals steps ψ t =
      evalDagStep (steps t)
        (fun i => evalDagNormals steps ψ ⟨i.1, Nat.lt_trans i.2 t.2⟩)
        (ψ t) := by
  cases t with
  | mk t ht =>
    change evalDagNormalsAux steps ψ t ht = _
    conv_lhs => rw [evalDagNormalsAux]
    rfl

private lemma differentiable_evalDagNormals {M : ℕ} (steps : (t : Fin M) → DagOp t.1) :
    ∀ (t : Fin M) (q : Fin 4),
      Differentiable ℝ (fun ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ =>
        evalDagNormals steps ψ t q) := by
  intro ⟨t, ht⟩ q
  change Differentiable ℝ (fun ψ => evalDagNormalsAux steps ψ t ht q)
  induction t using Nat.strong_induction_on generalizing q with
  | h t ih =>
    have hunfold : ∀ ψ, evalDagNormalsAux steps ψ t ht q =
        evalDagStep (steps ⟨t, ht⟩)
          (fun i => evalDagNormalsAux steps ψ i.1 (Nat.lt_trans i.2 ht))
          (ψ ⟨t, ht⟩) q := fun ψ => by
      conv_lhs => rw [evalDagNormalsAux]
    simp_rw [hunfold]
    refine (differentiable_evalDagStep (steps ⟨t, ht⟩) q).comp (Differentiable.prodMk ?_ ?_)
    · exact differentiable_pi.mpr fun i => differentiable_pi.mpr fun r =>
        ih i.1 i.2 (Nat.lt_trans i.2 ht) r
    · exact differentiable_apply (⟨t, ht⟩ : Fin M)

private lemma nonempty_interior_of_finite_closed_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} (S : Finset ι) (C : ι → Set X) (hC : ∀ i ∈ S, IsClosed (C i))
    {W : Set X} (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hcov : W ⊆ ⋃ i ∈ S, C i) :
    ∃ i ∈ S, (W ∩ interior (C i)).Nonempty := by
  classical
  induction S using Finset.induction_on generalizing W with
  | empty =>
    obtain ⟨x, hx⟩ := hW_ne
    have hx' := hcov hx
    simp at hx'
  | insert a S ha ih =>
    by_cases hhit : (W ∩ interior (C a)).Nonempty
    · exact ⟨a, Finset.mem_insert_self a S, hhit⟩
    · have hWa_open : IsOpen (W \ C a) := hW_open.sdiff (hC a (Finset.mem_insert_self a S))
      have hWa_ne : (W \ C a).Nonempty := by
        by_contra hnone
        rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hnone
        have hsub : W ⊆ interior (C a) := interior_maximal hnone hW_open
        obtain ⟨x, hxW⟩ := hW_ne
        exact hhit ⟨x, hxW, hsub hxW⟩
      have hWa_cov : W \ C a ⊆ ⋃ i ∈ S, C i := by
        intro x ⟨hxW, hxCa⟩
        have hmem := hcov hxW
        rw [Set.mem_iUnion₂] at hmem
        obtain ⟨i, hi, hxi⟩ := hmem
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact False.elim (hxCa hxi)
        · exact Set.mem_iUnion₂.mpr ⟨i, hiS, hxi⟩
      obtain ⟨i, hiS, x, ⟨hxW, _⟩, hxint⟩ :=
        ih (fun j hj => hC j (Finset.mem_insert_of_mem hj)) hWa_open hWa_ne hWa_cov
      exact ⟨i, Finset.mem_insert_of_mem hiS, x, hxW, hxint⟩

/-! ### Section 2: Hyperplanes, coplanarity, and avoiding lower-dim subspaces in E4 -/

private def hp (v : E4) : Submodule ℝ E4 :=
  (innerSL ℝ v).ker

private lemma mem_hp_iff (v x : E4) : x ∈ hp v ↔ ⟪v, x⟫_ℝ = 0 := by
  simp [hp]

private lemma hp_neg (v : E4) : hp (-v) = hp v := by
  ext x; simp [mem_hp_iff]

private lemma hp_smul {c : ℝ} (hc : c ≠ 0) (v : E4) : hp (c • v) = hp v := by
  ext x; simp [mem_hp_iff, real_inner_smul_left, hc]

private lemma isClosed_hp (v : E4) : IsClosed (hp v : Set E4) :=
  (hp v).closed_of_finiteDimensional

private lemma finrank_hp {v : E4} (hv : v ≠ 0) : Module.finrank ℝ (hp v) = 3 := by
  have hsurj : Function.Surjective (innerSL ℝ v) := fun r => by
    refine ⟨(r / ‖v‖ ^ 2) • v, ?_⟩
    change ⟪v, (r / ‖v‖ ^ 2) • v⟫_ℝ = r
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    field_simp [hv2]
  have hrk := LinearMap.finrank_range_add_finrank_ker (innerSL ℝ v).toLinearMap
  have hrg : LinearMap.range (innerSL ℝ v).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrg, finrank_top, Module.finrank_self] at hrk
  have hE4 : Module.finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  change 1 + Module.finrank ℝ (hp v) = Module.finrank ℝ E4 at hrk
  omega

private lemma hp_eq_iff {v₁ v₂ : E4} (hv₂ : v₂ ≠ 0) :
    hp v₁ = hp v₂ → ∃ c : ℝ, c ≠ 0 ∧ v₂ = c • v₁ := by
  intro heq
  have hsp : (Submodule.span ℝ {v₁} : Submodule ℝ E4) = Submodule.span ℝ {v₂} := by
    have horth : ∀ w : E4, (Submodule.span ℝ {w})ᗮ = hp w := fun w => by
      ext x
      simp [Submodule.mem_orthogonal_singleton_iff_inner_right, mem_hp_iff]
    have h12 : (Submodule.span ℝ {v₁})ᗮ = (Submodule.span ℝ {v₂})ᗮ := by
      rw [horth, horth, heq]
    have hdd := congrArg Submodule.orthogonal h12
    rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at hdd
  have hmem : v₂ ∈ Submodule.span ℝ {v₁} := by
    rw [hsp]; exact Submodule.subset_span rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_, hc.symm⟩
  intro hc0
  rw [hc0, zero_smul] at hc
  exact hv₂ hc.symm

private lemma hp_eq_of_le {H₁ H₂ : Submodule ℝ E4}
    (h₁ : Module.finrank ℝ H₁ = 3) (h₂ : Module.finrank ℝ H₂ = 3) (hle : H₁ ≤ H₂) :
    H₁ = H₂ :=
  Submodule.eq_of_le_of_finrank_eq hle (by omega)

private lemma finrank_hp_inf {H₁ H₂ : Submodule ℝ E4}
    (h₁ : Module.finrank ℝ H₁ = 3) (h₂ : Module.finrank ℝ H₂ = 3) (hne : H₁ ≠ H₂) :
    Module.finrank ℝ (H₁ ⊓ H₂ : Submodule ℝ E4) = 2 := by
  have hsup : (H₁ ⊔ H₂ : Submodule ℝ E4) = ⊤ := by
    by_contra hlt
    have hle1 : H₁ ≤ H₁ ⊔ H₂ := le_sup_left
    have hle2 : H₂ ≤ H₁ ⊔ H₂ := le_sup_right
    have hfin_lt : Module.finrank ℝ (H₁ ⊔ H₂ : Submodule ℝ E4) < 4 := by
      have hle4 : Module.finrank ℝ (H₁ ⊔ H₂ : Submodule ℝ E4) ≤ Module.finrank ℝ E4 :=
        Submodule.finrank_le _
      have hE4 : Module.finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
      rcases lt_or_eq_of_le (hle4.trans_eq hE4) with h | h
      · exact h
      · exact False.elim (hlt (Submodule.eq_top_of_finrank_eq (h.trans hE4.symm)))
    have hrk1 : Module.finrank ℝ (H₁ ⊔ H₂ : Submodule ℝ E4) = 3 := by
      have := Submodule.finrank_mono hle1
      omega
    have h1eq : H₁ = H₁ ⊔ H₂ := Submodule.eq_of_le_of_finrank_eq hle1 (by omega)
    have h2eq : H₂ = H₁ ⊔ H₂ := Submodule.eq_of_le_of_finrank_eq hle2 (by omega)
    exact hne (h1eq.trans h2eq.symm)
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq H₁ H₂
  rw [hsup, finrank_top, finrank_euclideanSpace_fin, h₁, h₂] at hadd
  omega

private def CoplanarTriple (H₁ H₂ H₃ : Submodule ℝ E4) : Prop :=
  H₁ ≠ H₂ ∧ H₂ ≠ H₃ ∧ H₁ ≠ H₃ ∧ H₁ ⊓ H₂ ≤ H₃

private lemma coplanarTriple_symm_swap12 {H₁ H₂ H₃ : Submodule ℝ E4}
    (h : CoplanarTriple H₁ H₂ H₃) : CoplanarTriple H₂ H₁ H₃ := by
  refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
  rw [inf_comm]; exact h.2.2.2

private lemma coplanarTriple_symm_swap23 {H₁ H₂ H₃ : Submodule ℝ E4}
    (h₁ : Module.finrank ℝ H₁ = 3) (h₂ : Module.finrank ℝ H₂ = 3)
    (h₃ : Module.finrank ℝ H₃ = 3) (h : CoplanarTriple H₁ H₂ H₃) :
    CoplanarTriple H₁ H₃ H₂ := by
  refine ⟨h.2.2.1, h.2.1.symm, h.1, ?_⟩
  have heq : (H₁ ⊓ H₂ : Submodule ℝ E4) = H₁ ⊓ H₃ :=
    Submodule.eq_of_le_of_finrank_eq (le_inf inf_le_left h.2.2.2)
      (by rw [finrank_hp_inf h₁ h₂ h.1, finrank_hp_inf h₁ h₃ h.2.2.1])
  rw [← heq]
  exact inf_le_right

private lemma coplanarTriple_all_perms {H₁ H₂ H₃ : Submodule ℝ E4}
    (h₁ : Module.finrank ℝ H₁ = 3) (h₂ : Module.finrank ℝ H₂ = 3)
    (h₃ : Module.finrank ℝ H₃ = 3) (h : CoplanarTriple H₁ H₂ H₃) :
    CoplanarTriple H₁ H₃ H₂ ∧ CoplanarTriple H₂ H₁ H₃ ∧
    CoplanarTriple H₂ H₃ H₁ ∧ CoplanarTriple H₃ H₁ H₂ ∧ CoplanarTriple H₃ H₂ H₁ := by
  have h132 := coplanarTriple_symm_swap23 h₁ h₂ h₃ h
  have h213 := coplanarTriple_symm_swap12 h
  have h231 := coplanarTriple_symm_swap23 h₂ h₁ h₃ h213
  have h312 := coplanarTriple_symm_swap12 h132
  have h321 := coplanarTriple_symm_swap12 h231
  exact ⟨h132, h213, h231, h312, h321⟩

private lemma exists_ridge_normal_combo {v₁ v₂ v₃ : E4}
    (hv₃ : v₃ ≠ 0)
    (hcop : CoplanarTriple (hp v₁) (hp v₂) (hp v₃)) :
    ∃ (c α : ℝ), α ≠ 0 ∧ v₃ = α • (v₁ + c • v₂) := by
  have horth : ∀ w : E4, (Submodule.span ℝ {w})ᗮ = hp w := fun w => by
    ext x; simp [Submodule.mem_orthogonal_singleton_iff_inner_right, mem_hp_iff]
  have hle_span : (Submodule.span ℝ {v₃} : Submodule ℝ E4) ≤ Submodule.span ℝ {v₁, v₂} := by
    have hinf : (Submodule.span ℝ {v₁, v₂})ᗮ = hp v₁ ⊓ hp v₂ := by
      ext x
      simp only [Submodule.mem_orthogonal, Submodule.mem_span_pair, Submodule.mem_inf, mem_hp_iff]
      constructor
      · intro hx
        exact ⟨hx v₁ ⟨1, 0, by simp⟩, hx v₂ ⟨0, 1, by simp⟩⟩
      · rintro ⟨hx1, hx2⟩ y ⟨a, b, rfl⟩
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hx1, hx2]
        ring
    have hsub : (Submodule.span ℝ {v₁, v₂})ᗮ ≤ (Submodule.span ℝ {v₃})ᗮ := by
      rw [hinf, horth]
      exact hcop.2.2.2
    have hdd := Submodule.orthogonal_le hsub
    rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at hdd
  have hv3_mem : v₃ ∈ Submodule.span ℝ {v₁, v₂} :=
    hle_span (Submodule.subset_span rfl)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv3_mem
  have ha : a ≠ 0 := by
    intro ha0
    subst ha0
    rw [zero_smul, zero_add] at hab
    have hb : b ≠ 0 := fun h0 => hv₃ (by rw [← hab, h0, zero_smul])
    exact hcop.2.1 (by rw [← hab, hp_smul hb])
  refine ⟨b / a, a, ha, ?_⟩
  rw [smul_add, smul_smul, mul_div_cancel₀ b ha, hab]

private lemma exists_mem_open_avoiding_subspaces {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) (F : Finset (Submodule ℝ E))
    (hnot : ∀ H ∈ F, ¬ K ≤ H)
    {U : Set K} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    ∃ p ∈ U, ∀ H ∈ F, (p : E) ∉ H := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨p, hpU⟩ := hU_ne
    exact ⟨p, hpU, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | insert H F hHF ih =>
    obtain ⟨p, hpU, hpF⟩ := ih (fun H' h' => hnot H' (Finset.mem_insert_of_mem h'))
    by_cases hpH : (p : E) ∈ H
    · obtain ⟨v, hvK, hvH⟩ : ∃ v : E, v ∈ K ∧ v ∉ H := by
        by_contra hall
        push Not at hall
        exact hnot H (Finset.mem_insert_self H F) fun x hx => hall x hx
      let vk : K := ⟨v, hvK⟩
      let U' : Set K := U ∩ ⋂ H' ∈ F, {x : K | (x : E) ∉ H'}
      have hU'_open : IsOpen U' :=
        hU_open.inter (isOpen_biInter_finset fun H' _ =>
          (H'.closed_of_finiteDimensional).isOpen_compl.preimage continuous_subtype_val)
      have hpU' : p ∈ U' := ⟨hpU, Set.mem_iInter₂.mpr hpF⟩
      have hcont : Continuous (fun t : ℝ => p + t • vk) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hnhds : ∀ᶠ t : ℝ in nhds (0 : ℝ), p + t • vk ∈ U' :=
        hcont.continuousAt.preimage_mem_nhds (by simpa using hU'_open.mem_nhds hpU')
      obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
      let t : ℝ := δ' / 2
      have ht_pos : 0 < t := half_pos hδ'_pos
      have ht_dist : dist t 0 < δ' := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
        exact half_lt_self hδ'_pos
      have hpt : p + t • vk ∈ U' := hδ' ht_dist
      refine ⟨p + t • vk, hpt.1, fun H' hH' => ?_⟩
      rcases Finset.mem_insert.mp hH' with rfl | hH'F
      · intro hmem
        have hsub : (t • v : E) ∈ H' := by
          have := H'.sub_mem hmem hpH
          simpa using this
        exact hvH (by simpa [ht_pos.ne'] using H'.smul_mem t⁻¹ hsub)
      · exact Set.mem_iInter₂.mp hpt.2 H' hH'F
    · refine ⟨p, hpU, fun H' hH' => ?_⟩
      rcases Finset.mem_insert.mp hH' with rfl | hH'F
      · exact hpH
      · exact hpF H' hH'F

/-! ### Section 3: Greedy triangle closure and cardinality counting -/

private def hasCoplanarTriple (ℋ : Finset (Submodule ℝ E4)) (H : Submodule ℝ E4) : Prop :=
  ∃ H₁ ∈ ℋ, ∃ H₂ ∈ ℋ, CoplanarTriple H H₁ H₂

private structure TripleSeqItem where
  H : Submodule ℝ E4
  parents : Option (ℕ × ℕ)

private def freeCount (L : List TripleSeqItem) : ℕ :=
  L.countP (·.parents.isNone)

private def ValidSeq (Tset : Finset (Submodule ℝ E4)) (L : List TripleSeqItem) : Prop :=
  (L.map (·.H)).Nodup ∧
  (∀ x ∈ L, x.H ∈ Tset) ∧
  ∀ (i : ℕ) (hi : i < L.length),
    match (L[i]'hi).parents with
    | none => True
    | some (a, b) => ∃ ha : a < i, ∃ hb : b < i,
        CoplanarTriple (L[i]'hi).H (L[a]'(Nat.lt_trans ha hi)).H (L[b]'(Nat.lt_trans hb hi)).H

private lemma validSeq_append_free {Tset : Finset (Submodule ℝ E4)} {L : List TripleSeqItem}
    (hL : ValidSeq Tset L) {H : Submodule ℝ E4} (hHT : H ∈ Tset) (hHn : H ∉ L.map (·.H)) :
    ValidSeq Tset (L ++ [⟨H, none⟩]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hL.1, List.nodup_singleton H, fun x hx y hy hxy => ?_⟩
    dsimp at hy
    rw [List.mem_singleton] at hy
    subst hy; subst hxy
    exact hHn hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hL.2.1 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hHT
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hilt : i < L.length
    · have hget : (L ++ [⟨H, none⟩])[i]'(by simpa using hi) = L[i]'hilt :=
        List.getElem_append_left hilt
      rw [hget]
      cases hp : (L[i]'hilt).parents with
      | none => trivial
      | some ab =>
        obtain ⟨ha, hb, hcop⟩ := by simpa [hp] using hL.2.2 i hilt
        refine ⟨ha, hb, ?_⟩
        rw [List.getElem_append_left (Nat.lt_trans ha hilt),
            List.getElem_append_left (Nat.lt_trans hb hilt)]
        exact hcop
    · have hieq : i = L.length := by omega
      subst hieq
      simp

private lemma validSeq_append_ridge {Tset : Finset (Submodule ℝ E4)} {L : List TripleSeqItem}
    (hL : ValidSeq Tset L) {H : Submodule ℝ E4} (hHT : H ∈ Tset) (hHn : H ∉ L.map (·.H))
    {a b : ℕ} (ha : a < L.length) (hb : b < L.length)
    (hcop : CoplanarTriple H (L[a]'ha).H (L[b]'hb).H) :
    ValidSeq Tset (L ++ [⟨H, some (a, b)⟩]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hL.1, List.nodup_singleton H, fun x hx y hy hxy => ?_⟩
    dsimp at hy
    rw [List.mem_singleton] at hy
    subst hy; subst hxy
    exact hHn hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hL.2.1 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hHT
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hilt : i < L.length
    · have hget : (L ++ [⟨H, some (a, b)⟩])[i]'(by simpa using hi) = L[i]'hilt :=
        List.getElem_append_left hilt
      rw [hget]
      cases hp : (L[i]'hilt).parents with
      | none => trivial
      | some ab =>
        obtain ⟨ha', hb', hcop'⟩ := by simpa [hp] using hL.2.2 i hilt
        refine ⟨ha', hb', ?_⟩
        rw [List.getElem_append_left (Nat.lt_trans ha' hilt),
            List.getElem_append_left (Nat.lt_trans hb' hilt)]
        exact hcop'
    · have hieq : i = L.length := by omega
      subst hieq
      have hget : (L ++ [⟨H, some (a, b)⟩])[L.length]'(by simp) = ⟨H, some (a, b)⟩ := by
        simp
      rw [hget]
      refine ⟨ha, hb, ?_⟩
      rw [List.getElem_append_left ha, List.getElem_append_left hb]
      exact hcop

private lemma freeCount_append_none (L : List TripleSeqItem) (H : Submodule ℝ E4) :
    freeCount (L ++ [⟨H, none⟩]) = freeCount L + 1 := by
  simp [freeCount, List.countP_append]

private lemma freeCount_append_some (L : List TripleSeqItem) (H : Submodule ℝ E4) (a b : ℕ) :
    freeCount (L ++ [⟨H, some (a, b)⟩]) = freeCount L := by
  simp [freeCount, List.countP_append]

private lemma extend_validSeq (Tset : Finset (Submodule ℝ E4))
    (hfin : ∀ H ∈ Tset, Module.finrank ℝ H = 3)
    (htri : ∀ H ∈ Tset, ∃ H₁ ∈ Tset, ∃ H₂ ∈ Tset, CoplanarTriple H H₁ H₂) :
    ∀ n : ℕ, ∀ L : List TripleSeqItem, ValidSeq Tset L →
      Tset.card - L.length = n →
      ∃ L' : List TripleSeqItem, ValidSeq Tset L' ∧ L'.length = Tset.card ∧
        3 * freeCount L' + 2 * L.length ≤ 2 * L'.length + 3 * freeCount L := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hL hdiff
    have hL_sub : (L.map (·.H)).toFinset ⊆ Tset := by
      intro H hH
      rw [List.mem_toFinset, List.mem_map] at hH
      obtain ⟨x, hxL, rfl⟩ := hH
      exact hL.2.1 x hxL
    have hlen_le : L.length ≤ Tset.card := by
      have hc := Finset.card_le_card hL_sub
      rw [List.toFinset_card_of_nodup hL.1, List.length_map] at hc
      exact hc
    by_cases hdone : L.length = Tset.card
    · exact ⟨L, hL, hdone, by omega⟩
    · have hlt : L.length < Tset.card := lt_of_le_of_ne hlen_le hdone
      have hex_out : ∃ H ∈ Tset, H ∉ L.map (·.H) := by
        by_contra hall
        push Not at hall
        have hsub' : Tset ⊆ (L.map (·.H)).toFinset := fun H hH => by
          rw [List.mem_toFinset]; exact hall H hH
        have hc := Finset.card_le_card hsub'
        rw [List.toFinset_card_of_nodup hL.1, List.length_map] at hc
        omega
      by_cases hstep1 : ∃ H ∈ Tset, H ∉ L.map (·.H) ∧
          ∃ a : Fin L.length, ∃ b : Fin L.length,
            CoplanarTriple H (L[a.1]'a.2).H (L[b.1]'b.2).H
      · obtain ⟨H, hHT, hHn, a, b, hcop⟩ := hstep1
        let L1 := L ++ [⟨H, some (a.1, b.1)⟩]
        have hL1 : ValidSeq Tset L1 := validSeq_append_ridge hL hHT hHn a.2 b.2 hcop
        have hlen1 : L1.length = L.length + 1 := by simp [L1]
        have hfc1 : freeCount L1 = freeCount L := freeCount_append_some L H a.1 b.1
        have hm1 : Tset.card - L1.length < n := by omega
        obtain ⟨L', hL', hlen', hineq⟩ := ih (Tset.card - L1.length) hm1 L1 hL1 rfl
        refine ⟨L', hL', hlen', ?_⟩
        omega
      · obtain ⟨H, hHT, hHn⟩ := hex_out
        obtain ⟨H₁, hH1T, H₂, hH2T, hcop⟩ := htri H hHT
        by_cases h1in : H₁ ∈ L.map (·.H)
        · have h2out : H₂ ∉ L.map (·.H) := fun h2in => by
            rw [List.mem_map] at h1in h2in
            obtain ⟨x₁, hx1, rfl⟩ := h1in
            obtain ⟨x₂, hx2, rfl⟩ := h2in
            obtain ⟨a, ha, haeq⟩ := List.getElem_of_mem hx1
            obtain ⟨b, hb, hbeq⟩ := List.getElem_of_mem hx2
            exact hstep1 ⟨H, hHT, hHn, ⟨a, ha⟩, ⟨b, hb⟩, by simpa [haeq, hbeq] using hcop⟩
          rw [List.mem_map] at h1in
          obtain ⟨x₁, hx1, h1eq⟩ := h1in
          obtain ⟨a, ha, haeq⟩ := List.getElem_of_mem hx1
          let L1 := L ++ [⟨H, none⟩]
          have hL1 := validSeq_append_free hL hHT hHn
          have ha1 : a < L1.length := by simp [L1]; omega
          have hH1_get : (L1[a]'ha1).H = H₁ := by
            dsimp [L1]; rw [List.getElem_append_left ha, haeq, h1eq]
          let b1 := L.length
          have hb1 : b1 < L1.length := by simp [L1, b1]
          have hH_get : (L1[b1]'hb1).H = H := by simp [L1, b1]
          have h2not1 : H₂ ∉ L1.map (·.H) := by
            simp only [L1, List.map_append, List.map_singleton, List.mem_append,
              List.mem_singleton, not_or]
            exact ⟨h2out, hcop.2.2.1.symm⟩
          have hcop2 : CoplanarTriple H₂ (L1[b1]'hb1).H (L1[a]'ha1).H := by
            rw [hH_get, hH1_get]
            exact (coplanarTriple_all_perms (hfin H hHT) (hfin H₁ hH1T) (hfin H₂ hH2T) hcop).2.2.2.1
          let L2 := L1 ++ [⟨H₂, some (b1, a)⟩]
          have hL2 := validSeq_append_ridge hL1 hH2T h2not1 hb1 ha1 hcop2
          have hlen2 : L2.length = L.length + 2 := by simp [L2, L1]
          have hfc2 : freeCount L2 = freeCount L + 1 := by
            dsimp [L2]
            rw [freeCount_append_some, freeCount_append_none]
          have hm2 : Tset.card - L2.length < n := by omega
          obtain ⟨L', hL', hlen', hineq⟩ := ih (Tset.card - L2.length) hm2 L2 hL2 rfl
          exact ⟨L', hL', hlen', by omega⟩
        · by_cases h2in : H₂ ∈ L.map (·.H)
          · rw [List.mem_map] at h2in
            obtain ⟨x₂, hx2, h2eq⟩ := h2in
            obtain ⟨a, ha, haeq⟩ := List.getElem_of_mem hx2
            let L1 := L ++ [⟨H, none⟩]
            have hL1 := validSeq_append_free hL hHT hHn
            have ha1 : a < L1.length := by simp [L1]; omega
            have hH2_get : (L1[a]'ha1).H = H₂ := by
              dsimp [L1]; rw [List.getElem_append_left ha, haeq, h2eq]
            let b1 := L.length
            have hb1 : b1 < L1.length := by simp [L1, b1]
            have hH_get : (L1[b1]'hb1).H = H := by simp [L1, b1]
            have h1not1 : H₁ ∉ L1.map (·.H) := by
              simp only [L1, List.map_append, List.map_singleton, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨h1in, hcop.1.symm⟩
            have hcop1 : CoplanarTriple H₁ (L1[b1]'hb1).H (L1[a]'ha1).H := by
              rw [hH_get, hH2_get]
              exact (coplanarTriple_all_perms (hfin H hHT) (hfin H₁ hH1T) (hfin H₂ hH2T) hcop).2.1
            let L2 := L1 ++ [⟨H₁, some (b1, a)⟩]
            have hL2 := validSeq_append_ridge hL1 hH1T h1not1 hb1 ha1 hcop1
            have hlen2 : L2.length = L.length + 2 := by simp [L2, L1]
            have hfc2 : freeCount L2 = freeCount L + 1 := by
              dsimp [L2]
              rw [freeCount_append_some, freeCount_append_none]
            have hm2 : Tset.card - L2.length < n := by omega
            obtain ⟨L', hL', hlen', hineq⟩ := ih (Tset.card - L2.length) hm2 L2 hL2 rfl
            exact ⟨L', hL', hlen', by omega⟩
          · let L1 := L ++ [⟨H, none⟩]
            have hL1 := validSeq_append_free hL hHT hHn
            have h1not1 : H₁ ∉ L1.map (·.H) := by
              simp only [L1, List.map_append, List.map_singleton, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨h1in, hcop.1.symm⟩
            let L2 := L1 ++ [⟨H₁, none⟩]
            have hL2 := validSeq_append_free hL1 hH1T h1not1
            have h2not2 : H₂ ∉ L2.map (·.H) := by
              simp only [L2, L1, List.map_append, List.map_singleton, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨⟨h2in, hcop.2.2.1.symm⟩, hcop.2.1.symm⟩
            let i0 := L.length
            let i1 := L.length + 1
            have hi0 : i0 < L2.length := by simp [L2, L1, i0]
            have hi1 : i1 < L2.length := by simp [L2, L1, i1]
            have hH_get : (L2[i0]'hi0).H = H := by simp [L2, L1, i0]
            have hH1_get : (L2[i1]'hi1).H = H₁ := by simp [L2, L1, i1]
            have hcop2 : CoplanarTriple H₂ (L2[i0]'hi0).H (L2[i1]'hi1).H := by
              rw [hH_get, hH1_get]
              exact (coplanarTriple_all_perms (hfin H hHT) (hfin H₁ hH1T) (hfin H₂ hH2T) hcop).2.2.2.1
            let L3 := L2 ++ [⟨H₂, some (i0, i1)⟩]
            have hL3 := validSeq_append_ridge hL2 hH2T h2not2 hi0 hi1 hcop2
            have hlen3 : L3.length = L.length + 3 := by simp [L3, L2, L1]
            have hfc3 : freeCount L3 = freeCount L + 2 := by
              dsimp [L3, L2, L1]
              rw [freeCount_append_some, freeCount_append_none, freeCount_append_none]
            have hm3 : Tset.card - L3.length < n := by omega
            obtain ⟨L', hL', hlen', hineq⟩ := ih (Tset.card - L3.length) hm3 L3 hL3 rfl
            exact ⟨L', hL', hlen', by omega⟩

private lemma greedy_triples_bound
    (Tset : Finset (Submodule ℝ E4))
    (hfin : ∀ H ∈ Tset, Module.finrank ℝ H = 3)
    (htri : ∀ H ∈ Tset, ∃ H₁ ∈ Tset, ∃ H₂ ∈ Tset, CoplanarTriple H H₁ H₂)
    (hnot_part : Tset.card = 15 →
      ∃ H ∈ Tset, ∃ H₁ ∈ Tset, ∃ H₁' ∈ Tset, ∃ H₂ ∈ Tset, ∃ H₂' ∈ Tset,
        CoplanarTriple H H₁ H₁' ∧ CoplanarTriple H H₂ H₂' ∧
        H₂ ∉ ({H, H₁, H₁'} : Finset (Submodule ℝ E4))) :
    ∃ L : List TripleSeqItem,
      ValidSeq Tset L ∧ L.length = Tset.card ∧
      3 * freeCount L ≤ 2 * Tset.card ∧
      (Tset.card = 15 → freeCount L ≤ 9) := by
  classical
  have hvalid0 : ValidSeq Tset [] := ⟨List.nodup_nil, fun _ h => False.elim (by simp at h), fun i hi => by simp at hi⟩
  by_cases h15 : Tset.card = 15
  · obtain ⟨H, hHT, H₁, hH1T, H₁', hH1pT, H₂, hH2T, H₂', hH2pT, hcop1, hcop2, hH2not⟩ := hnot_part h15
    let L1 : List TripleSeqItem := [⟨H, none⟩]
    let L2 : List TripleSeqItem := L1 ++ [⟨H₁, none⟩]
    let L3 : List TripleSeqItem := L2 ++ [⟨H₁', some (0, 1)⟩]
    have hL1 : ValidSeq Tset L1 := validSeq_append_free hvalid0 hHT (by simp)
    have hL2 : ValidSeq Tset L2 :=
      validSeq_append_free hL1 hH1T (by simp [L1, hcop1.1.symm])
    have hL3 : ValidSeq Tset L3 := by
      refine validSeq_append_ridge hL2 hH1pT ?_ (by simp [L2, L1]) (by simp [L2, L1]) ?_
      · simp [L2, L1, hcop1.2.2.1.symm, hcop1.2.1.symm]
      · simpa [L2, L1] using (coplanarTriple_all_perms (hfin H hHT) (hfin H₁ hH1T) (hfin H₁' hH1pT) hcop1).2.2.2.1
    have hH2_not3 : H₂ ∉ L3.map (·.H) := by
      simpa [L3, L2, L1, Finset.mem_insert, Finset.mem_singleton] using hH2not
    have hL4_ex : ∃ L4 : List TripleSeqItem, ValidSeq Tset L4 ∧ 3 * freeCount L4 + 1 ≤ 2 * L4.length := by
      by_cases h2pin : H₂' ∈ L3.map (·.H)
      · rw [List.mem_map] at h2pin
        obtain ⟨x, hx, hxeq⟩ := h2pin
        obtain ⟨b, hb, hbeq⟩ := List.getElem_of_mem hx
        have h0 : 0 < L3.length := by simp [L3, L2, L1]
        have hcop_rev : CoplanarTriple H₂ (L3[0]'h0).H (L3[b]'hb).H := by
          have h0eq : (L3[0]'h0).H = H := by simp [L3, L2, L1]
          rw [h0eq, hbeq, hxeq]
          exact (coplanarTriple_all_perms (hfin H hHT) (hfin H₂ hH2T) (hfin H₂' hH2pT) hcop2).2.1
        refine ⟨L3 ++ [⟨H₂, some (0, b)⟩], validSeq_append_ridge hL3 hH2T hH2_not3 h0 hb hcop_rev, ?_⟩
        rw [freeCount_append_some]
        have hfc3 : freeCount L3 = 2 := by simp [L3, L2, L1, freeCount]
        have hlen3 : L3.length = 3 := by simp [L3, L2, L1]
        rw [List.length_append, List.length_singleton, hfc3, hlen3]
        norm_num
      · let L4a := L3 ++ [⟨H₂, none⟩]
        have hL4a := validSeq_append_free hL3 hH2T hH2_not3
        have h2pnot4a : H₂' ∉ L4a.map (·.H) := by
          simp only [L4a, List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, not_or]
          exact ⟨h2pin, hcop2.2.1.symm⟩
        have h0 : 0 < L4a.length := by simp [L4a, L3, L2, L1]
        have h3 : 3 < L4a.length := by simp [L4a, L3, L2, L1]
        have hcop2p : CoplanarTriple H₂' (L4a[0]'h0).H (L4a[3]'h3).H := by
          have heq0 : (L4a[0]'h0).H = H := by simp [L4a, L3, L2, L1]
          have heq3 : (L4a[3]'h3).H = H₂ := by simp [L4a, L3, L2, L1]
          rw [heq0, heq3]
          exact (coplanarTriple_all_perms (hfin H hHT) (hfin H₂ hH2T) (hfin H₂' hH2pT) hcop2).2.2.2.1
        let L4 := L4a ++ [⟨H₂', some (0, 3)⟩]
        refine ⟨L4, validSeq_append_ridge hL4a hH2pT h2pnot4a h0 h3 hcop2p, ?_⟩
        have hfc4 : freeCount L4 = 3 := by simp [L4, L4a, L3, L2, L1, freeCount]
        have hlen4 : L4.length = 5 := by simp [L4, L4a, L3, L2, L1]
        omega
    obtain ⟨L4, hL4, hineq4⟩ := hL4_ex
    obtain ⟨L', hL', hlen', hineq⟩ := extend_validSeq Tset hfin htri (Tset.card - L4.length) L4 hL4 rfl
    refine ⟨L', hL', hlen', by omega, fun _ => by omega⟩
  · obtain ⟨L', hL', hlen', hineq⟩ := extend_validSeq Tset hfin htri Tset.card [] hvalid0 (by simp)
    have hineq' : 3 * freeCount L' ≤ 2 * Tset.card := by
      rw [hlen'] at hineq
      simpa [freeCount] using hineq
    exact ⟨L', hL', hlen', hineq', fun h => False.elim (h15 h)⟩

/-! ### Section 4: Convex cones, Baire facet walls, 4-quadrant ridges in E4 -/

private def Kbar (c : Fin 6 → Fin 6 → E4) (i : Fin 6) : Set E4 :=
  {x | ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ}

private def Kopen (c : Fin 6 → Fin 6 → E4) (i : Fin 6) : Set E4 :=
  {x | ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ}

private lemma isClosed_Kbar (c : Fin 6 → Fin 6 → E4) (i : Fin 6) : IsClosed (Kbar c i) := by
  have heq : Kbar c i = ⋂ j ∈ Finset.univ.erase i, {x : E4 | 0 ≤ ⟪c i j, x⟫_ℝ} := by
    ext x; simp [Kbar, Finset.mem_erase, ne_comm]
  rw [heq]
  exact isClosed_biInter fun j _ => isClosed_le continuous_const (continuous_const.inner continuous_id)

private lemma isOpen_Kopen (c : Fin 6 → Fin 6 → E4) (i : Fin 6) : IsOpen (Kopen c i) := by
  have heq : Kopen c i = ⋂ j ∈ Finset.univ.erase i, {x : E4 | 0 < ⟪c i j, x⟫_ℝ} := by
    ext x; simp [Kopen, Finset.mem_erase, ne_comm]
  rw [heq]
  exact isOpen_biInter_finset fun j _ =>
    isOpen_lt continuous_const (continuous_const.inner continuous_id)

private lemma Kopen_subset_Kbar (c : Fin 6 → Fin 6 → E4) (i : Fin 6) : Kopen c i ⊆ Kbar c i :=
  fun _ hx j hj => (hx j hj).le

private lemma Kopen_disjoint {c : Fin 6 → Fin 6 → E4} (hc_sym : ∀ i j, c j i = -c i j)
    {i j : Fin 6} (hij : i ≠ j) : Disjoint (Kopen c i) (Kopen c j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have h1 := hxi j hij.symm
  have h2 := hxj i hij
  rw [hc_sym, inner_neg_left] at h2
  linarith

private lemma mem_interior_Kbar_iff {c : Fin 6 → Fin 6 → E4} (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (i : Fin 6) (x : E4) : x ∈ interior (Kbar c i) ↔ x ∈ Kopen c i := by
  constructor
  · intro hx j hji
    have hge : 0 ≤ ⟪c i j, x⟫_ℝ := interior_subset hx j hji
    by_contra hle
    have h0 : ⟪c i j, x⟫_ℝ = 0 := le_antisymm (not_lt.mp hle) hge
    obtain ⟨r, hr_pos, hr⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    let v := c i j
    have hv0 : v ≠ 0 := hc_ne i j hji.symm
    let ε := (r / 2) / ‖v‖
    have hε_pos : 0 < ε := div_pos (half_pos hr_pos) (norm_pos_iff.mpr hv0)
    have hball : x - ε • v ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hε_pos.le]
      dsimp [ε]
      rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv0)]
      exact half_lt_self hr_pos
    have hmem : x - ε • v ∈ Kbar c i := interior_subset (hr hball)
    have hnonneg : 0 ≤ ⟪v, x - ε • v⟫_ℝ := hmem j hji
    rw [inner_sub_right, real_inner_smul_right, h0, zero_sub, real_inner_self_eq_norm_sq] at hnonneg
    have hpos : 0 < ε * ‖v‖ ^ 2 := mul_pos hε_pos (pow_pos (norm_pos_iff.mpr hv0) 2)
    linarith
  · intro hx
    exact interior_maximal (Kopen_subset_Kbar c i) (isOpen_Kopen c i) hx

private def HasBallInHp (S : Set E4) (H : Submodule ℝ E4) : Prop :=
  ∃ p ∈ H, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball p r, y ∈ H → y ∈ S

private def IsWallPair (c : Fin 6 → Fin 6 → E4) (i j : Fin 6) : Prop :=
  i ≠ j ∧ HasBallInHp (Kbar c i ∩ Kbar c j) (hp (c i j))

private lemma isWallPair_symm {c : Fin 6 → Fin 6 → E4} (hc_sym : ∀ i j, c j i = -c i j)
    {i j : Fin 6} (h : IsWallPair c i j) : IsWallPair c j i := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with ⟨p, hpH, r, hr, hball⟩
  rw [hc_sym, hp_neg]
  refine ⟨p, hpH, r, hr, fun y hy hyH => ?_⟩
  have := hball y hy hyH
  exact ⟨this.2, this.1⟩

private lemma exists_min_facets (c : Fin 6 → Fin 6 → E4) (i : Fin 6) :
    ∃ F : Finset (Fin 6), F ⊆ Finset.univ.erase i ∧
      Kbar c i = {x | ∀ j ∈ F, 0 ≤ ⟪c i j, x⟫_ℝ} ∧
      ∀ F' ⊂ F, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ} := by
  classical
  let Cand : Finset (Finset (Fin 6)) :=
    (Finset.univ.erase i).powerset.filter fun S => Kbar c i = {x | ∀ j ∈ S, 0 ≤ ⟪c i j, x⟫_ℝ}
  have mem : Finset.univ.erase i ∈ Cand := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.Subset.rfl, ?_⟩
    ext x
    simp [Kbar, Finset.mem_erase, ne_comm]
  obtain ⟨F, hFC, hFmin⟩ := Finset.exists_min_image Cand Finset.card ⟨_, mem⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hFC
  refine ⟨F, hFC.1, hFC.2, fun F' hF' hEq => ?_⟩
  have hF'C : F' ∈ Cand := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hF'.subset.trans hFC.1, hEq⟩
  have hlt := Finset.card_lt_card hF'
  have hle := hFmin F' hF'C
  omega

private lemma exists_facet_interior_pt {c : Fin 6 → Fin 6 → E4}
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    {i : Fin 6} {F : Finset (Fin 6)}
    (hF_sub : F ⊆ Finset.univ.erase i)
    (hF_eq : Kbar c i = {x | ∀ j ∈ F, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ F' ⊂ F, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {j : Fin 6} (hj : j ∈ F) :
    ∃ p₀ : E4, p₀ ∈ hp (c i j) ∧ ∀ k ∈ F, k ≠ j → 0 < ⟪c i k, p₀⟫_ℝ := by
  classical
  have hneq := hF_min (F.erase j) (Finset.erase_ssubset hj)
  have hex_x0 : ∃ x₀ : E4, ⟪c i j, x₀⟫_ℝ < 0 ∧ ∀ k ∈ F, k ≠ j → 0 ≤ ⟪c i k, x₀⟫_ℝ := by
    by_contra hnone
    push Not at hnone
    apply hneq
    ext x
    rw [hF_eq]
    simp only [Set.mem_ofPred_eq, Finset.mem_erase, and_imp]
    constructor
    · intro h k _ hkF; exact h k hkF
    · intro h k hkF
      by_cases hkj : k = j
      · subst hkj
        by_contra hneg
        obtain ⟨k', hk'F, hk'ne, hk'neg⟩ := hnone x (not_le.mp hneg)
        exact absurd (h k' hk'ne hk'F) (not_le.mpr hk'neg)
      · exact h k hkj hkF
  obtain ⟨x₀, hx0_neg, hx0_pos⟩ := hex_x0
  obtain ⟨yᵢ, hyᵢ⟩ := hK_nonempty i
  have hyᵢ_pos : ∀ k ∈ F, 0 < ⟪c i k, yᵢ⟫_ℝ := fun k hk =>
    hyᵢ k (Finset.mem_erase.mp (hF_sub hk)).1
  let a := -⟪c i j, x₀⟫_ℝ
  let b := ⟪c i j, yᵢ⟫_ℝ
  have ha_pos : 0 < a := neg_pos.mpr hx0_neg
  have hb_pos : 0 < b := hyᵢ_pos j hj
  have hab_pos : 0 < a + b := by positivity
  let t : ℝ := a / (a + b)
  have ht0 : 0 < t := div_pos ha_pos hab_pos
  have ht1 : t < 1 := (div_lt_one hab_pos).mpr (by linarith)
  let p₀ : E4 := (1 - t) • x₀ + t • yᵢ
  refine ⟨p₀, ?_, ?_⟩
  · rw [mem_hp_iff]
    dsimp [p₀]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hx_val : ⟪c i j, x₀⟫_ℝ = -a := by dsimp [a]; ring
    have hy_val : ⟪c i j, yᵢ⟫_ℝ = b := rfl
    rw [hx_val, hy_val]
    dsimp [t]
    field_simp [hab_pos.ne']
    ring
  · intro k hk hkj
    dsimp [p₀]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 : 0 ≤ (1 - t) * ⟪c i k, x₀⟫_ℝ := mul_nonneg (sub_nonneg.mpr ht1.le) (hx0_pos k hk hkj)
    have h2 : 0 < t * ⟪c i k, yᵢ⟫_ℝ := mul_pos ht0 (hyᵢ_pos k hk)
    linarith

private lemma neg_ray_limit_mem_Kbar {c : Fin 6 → Fin 6 → E4}
    (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {i j : Fin 6} (hji : j ≠ i) {y : E4} (hy0 : ⟪c i j, y⟫_ℝ = 0) :
    ∃ k ∈ Finset.univ.erase i, y ∈ Kbar c k := by
  classical
  let f : ℕ → Fin 6 := fun n =>
    Classical.choose (hK_cover (y - ((1 : ℝ) / ((n : ℝ) + 1)) • c i j))
  have hf : ∀ n : ℕ, y - ((1 : ℝ) / ((n : ℝ) + 1)) • c i j ∈ Kbar c (f n) := fun n =>
    Classical.choose_spec (hK_cover _)
  have hf_ne : ∀ n : ℕ, f n ≠ i := fun n heq => by
    have hge := (heq ▸ hf n) j hji
    rw [inner_sub_right, real_inner_smul_right, hy0, zero_sub,
      real_inner_self_eq_norm_sq] at hge
    have hv0 : c i j ≠ 0 := hc_ne i j hji.symm
    have hneg : 0 < ((1 : ℝ) / ((n : ℝ) + 1)) * ‖c i j‖ ^ 2 := by positivity
    linarith
  obtain ⟨k, hinf⟩ := Finite.exists_infinite_fiber f
  have hk_ne : k ≠ i := by
    obtain ⟨n, hn⟩ := hinf.nonempty
    exact hn ▸ hf_ne n
  have hinfS : Set.Infinite (f ⁻¹' {k}) := Set.infinite_coe_iff.mp hinf
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, y - ((1 : ℝ) / ((n : ℝ) + 1)) • c i j ∈ Kbar c k :=
    Filter.frequently_atTop.mpr fun N => by
      obtain ⟨n, hn_mem, hn_ge⟩ := hinfS.exists_gt N
      have hfnk : f n = k := hn_mem
      exact ⟨n, hn_ge.le, hfnk ▸ hf n⟩
  have htend : Filter.Tendsto (fun n : ℕ => y - ((1 : ℝ) / ((n : ℝ) + 1)) • c i j)
      Filter.atTop (nhds y) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1)) • c i j)
        Filter.atTop (nhds ((0 : ℝ) • c i j)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (c i j)
    rw [zero_smul] at h0
    simpa only [sub_zero] using tendsto_const_nhds.sub h0
  exact ⟨k, Finset.mem_erase.mpr ⟨hk_ne, Finset.mem_univ k⟩,
    (isClosed_Kbar c k).mem_of_frequently_of_tendsto hfreq htend⟩

private lemma hp_eq_of_wall_ball {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    {H₀ : Submodule ℝ E4} (hH₀_fin : Module.finrank ℝ H₀ = 3)
    {i k : Fin 6} (hki : k ≠ i)
    (hball : HasBallInHp (Kbar c i ∩ Kbar c k) H₀) :
    H₀ = hp (c i k) ∧ IsWallPair c i k := by
  obtain ⟨p₁, hp1H, r₂, hr₂_pos, hr₂_ball⟩ := hball
  have hH_le : H₀ ≤ hp (c i k) := by
    intro w hwH₀
    rw [mem_hp_iff]
    have hp1_pair : p₁ ∈ Kbar c i ∩ Kbar c k :=
      hr₂_ball p₁ (Metric.mem_ball_self hr₂_pos) hp1H
    have hp1_0 : ⟪c i k, p₁⟫_ℝ = 0 := by
      have h1 := hp1_pair.1 k hki
      have h2 := hp1_pair.2 i hki.symm
      rw [hc_sym, inner_neg_left] at h2
      linarith
    let ε := (r₂ / 2) / (‖w‖ + 1)
    have hε_pos : 0 < ε := by positivity
    have hw_ball : p₁ + ε • w ∈ Metric.ball p₁ r₂ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hε_pos.le]
      dsimp [ε]
      have hden : 0 < ‖w‖ + 1 := by positivity
      calc (r₂ / 2) / (‖w‖ + 1) * ‖w‖ = (r₂ / 2) * (‖w‖ / (‖w‖ + 1)) := by ring
        _ < (r₂ / 2) * 1 := by
          refine mul_lt_mul_of_pos_left ?_ (half_pos hr₂_pos)
          rw [div_lt_one hden]
          linarith
        _ < r₂ := by linarith
    have hpw_pair := hr₂_ball (p₁ + ε • w) hw_ball (H₀.add_mem hp1H (H₀.smul_mem ε hwH₀))
    have hpw_0 : ⟪c i k, p₁ + ε • w⟫_ℝ = 0 := by
      have h1 := hpw_pair.1 k hki
      have h2 := hpw_pair.2 i hki.symm
      rw [hc_sym, inner_neg_left] at h2
      linarith
    rw [inner_add_right, real_inner_smul_right, hp1_0, zero_add] at hpw_0
    exact (mul_eq_zero.mp hpw_0).resolve_left hε_pos.ne'
  have hH_eq : H₀ = hp (c i k) :=
    hp_eq_of_le hH₀_fin (finrank_hp (hc_ne i k hki.symm)) hH_le
  refine ⟨hH_eq, hki.symm, ?_⟩
  rw [← hH_eq]
  exact ⟨p₁, hp1H, r₂, hr₂_pos, hr₂_ball⟩

private lemma baire_facet_wall_aux {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j)
    (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {i j : Fin 6} (hji : j ≠ i) {F : Finset (Fin 6)}
    (hF_eq : Kbar c i = {x | ∀ m ∈ F, 0 ≤ ⟪c i m, x⟫_ℝ})
    {p₀ : E4} {r₀ : ℝ} (hr₀_pos : 0 < r₀)
    (hr₀ : ∀ y ∈ Metric.ball p₀ r₀, ∀ m ∈ F.erase j, 0 < ⟪c i m, y⟫_ℝ)
    (H₀ : Submodule ℝ E4) (hH₀ : H₀ = hp (c i j)) (hp₀_hp : p₀ ∈ H₀) :
    ∃ k : Fin 6, k ≠ i ∧ IsWallPair c i k ∧ H₀ = hp (c i k) := by
  classical
  let W : Set H₀ := {y : H₀ | dist (y : E4) p₀ < r₀}
  have hW_open : IsOpen W := Metric.isOpen_ball.preimage continuous_subtype_val
  have hW_ne : W.Nonempty := ⟨⟨p₀, hp₀_hp⟩, by simp [W, hr₀_pos]⟩
  let Cset : Fin 6 → Set H₀ := fun k => {y : H₀ | (y : E4) ∈ Kbar c k}
  have hC_closed : ∀ k ∈ Finset.univ.erase i, IsClosed (Cset k) := fun k _ =>
    (isClosed_Kbar c k).preimage continuous_subtype_val
  have hW_cov : W ⊆ ⋃ k ∈ Finset.univ.erase i, Cset k := fun y _ => by
    have hy0 : ⟪c i j, (y : E4)⟫_ℝ = 0 := (mem_hp_iff _ _).mp (hH₀ ▸ y.2)
    obtain ⟨k, hk, hyk⟩ := neg_ray_limit_mem_Kbar hc_ne hK_cover hji hy0
    exact Set.mem_iUnion₂.mpr ⟨k, hk, hyk⟩
  obtain ⟨k, hk_er, ⟨p₁, hp1W, hp1_int⟩⟩ :=
    nonempty_interior_of_finite_closed_cover (Finset.univ.erase i) Cset hC_closed hW_open hW_ne hW_cov
  have hki : k ≠ i := (Finset.mem_erase.mp hk_er).1
  obtain ⟨r₁, hr₁_pos, hr₁⟩ := Metric.isOpen_iff.mp isOpen_interior p₁ hp1_int
  have hp1_ball : dist (p₁ : E4) p₀ < r₀ := hp1W
  let r₂ := min r₁ (r₀ - dist (p₁ : E4) p₀)
  have hr₂_pos : 0 < r₂ := lt_min hr₁_pos (sub_pos.mpr hp1_ball)
  have hr₂_ball : HasBallInHp (Kbar c i ∩ Kbar c k) H₀ := by
    refine ⟨(p₁ : E4), p₁.2, r₂, hr₂_pos, fun y hy hyH₀ => ⟨?_, ?_⟩⟩
    · have hyW : y ∈ Metric.ball p₀ r₀ := by
        rw [Metric.mem_ball]
        have h1 : dist y (p₁ : E4) < r₂ := hy
        have h2 : r₂ ≤ r₀ - dist (p₁ : E4) p₀ := min_le_right _ _
        linarith [dist_triangle y (p₁ : E4) p₀]
      rw [hF_eq]
      intro m hm
      by_cases hmj : m = j
      · subst hmj; exact le_of_eq ((mem_hp_iff _ _).mp (hH₀ ▸ hyH₀)).symm
      · exact (hr₀ y hyW m (Finset.mem_erase.mpr ⟨hmj, hm⟩)).le
    · have hy_lt : (⟨y, hyH₀⟩ : H₀) ∈ Metric.ball p₁ r₁ := by
        rw [Metric.mem_ball]
        change dist y (p₁ : E4) < r₁
        exact lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)
      have hmem : (⟨y, hyH₀⟩ : H₀) ∈ Cset k := interior_subset (hr₁ hy_lt)
      exact hmem
  have hH₀_fin : Module.finrank ℝ H₀ = 3 := hH₀ ▸ finrank_hp (hc_ne i j hji.symm)
  obtain ⟨hH_eq, hw⟩ := hp_eq_of_wall_ball hc_sym hc_ne hH₀_fin hki hr₂_ball
  exact ⟨k, hki, hw, hH_eq⟩

private lemma baire_facet_wall {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j)
    (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {i : Fin 6} {F : Finset (Fin 6)}
    (hF_sub : F ⊆ Finset.univ.erase i)
    (hF_eq : Kbar c i = {x | ∀ j ∈ F, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ F' ⊂ F, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {j : Fin 6} (hj : j ∈ F) :
    ∃ k : Fin 6, k ≠ i ∧ IsWallPair c i k ∧ hp (c i j) = hp (c i k) := by
  classical
  have hji : j ≠ i := (Finset.mem_erase.mp (hF_sub hj)).1
  obtain ⟨p₀, hp₀_hp, hp₀_pos⟩ := exists_facet_interior_pt hK_nonempty hF_sub hF_eq hF_min hj
  let U0 : Set E4 := ⋂ k ∈ F.erase j, {y : E4 | 0 < ⟪c i k, y⟫_ℝ}
  have hU0_open : IsOpen U0 :=
    isOpen_biInter_finset fun k _ => isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hp₀_U0 : p₀ ∈ U0 := Set.mem_iInter₂.mpr fun k hk =>
    hp₀_pos k (Finset.mem_erase.mp hk).2 (Finset.mem_erase.mp hk).1
  obtain ⟨r₀, hr₀_pos, hr₀⟩ := Metric.isOpen_iff.mp hU0_open p₀ hp₀_U0
  exact baire_facet_wall_aux hc_sym hc_ne hK_cover hji hF_eq hr₀_pos
    (fun y hy m hm => Set.mem_iInter₂.mp (hr₀ hy) m hm) (hp (c i j)) rfl hp₀_hp

private def wallHyperplanes (c : Fin 6 → Fin 6 → E4) : Finset (Submodule ℝ E4) := by
  classical
  exact (Finset.univ.filter fun e : Pairs6 => IsWallPair c e.1.1 e.1.2).image
    fun e => hp (c e.1.1 e.1.2)

private def wallPairsAt (c : Fin 6 → Fin 6 → E4) (H : Submodule ℝ E4) : Finset Pairs6 := by
  classical
  exact Finset.univ.filter fun e : Pairs6 =>
    IsWallPair c e.1.1 e.1.2 ∧ hp (c e.1.1 e.1.2) = H

private lemma wallHyperplanes_card_le (c : Fin 6 → Fin 6 → E4) :
    (wallHyperplanes c).card ≤ 15 := by
  classical
  calc (wallHyperplanes c).card ≤ (Finset.univ.filter fun e : Pairs6 => IsWallPair c e.1.1 e.1.2).card :=
        Finset.card_image_le
    _ ≤ (Finset.univ : Finset Pairs6).card := Finset.card_filter_le _ _
    _ = 15 := by decide

private lemma wallPairsAt_nonempty {c : Fin 6 → Fin 6 → E4} {H : Submodule ℝ E4}
    (hH : H ∈ wallHyperplanes c) : (wallPairsAt c H).Nonempty := by
  classical
  rw [wallHyperplanes, Finset.mem_image] at hH
  obtain ⟨e, he, rfl⟩ := hH
  rw [Finset.mem_filter] at he
  exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.2, rfl⟩⟩

private lemma wallPairsAt_disjoint (c : Fin 6 → Fin 6 → E4) :
    (wallHyperplanes c : Set (Submodule ℝ E4)).PairwiseDisjoint (wallPairsAt c) := by
  intro H₁ _ H₂ _ hne
  change Disjoint (wallPairsAt c H₁) (wallPairsAt c H₂)
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  simp only [wallPairsAt, Finset.mem_filter] at he₁ he₂
  exact hne (he₁.2.2.symm.trans he₂.2.2)

private lemma sum_wallPairsAt_le (c : Fin 6 → Fin 6 → E4) :
    ∑ H ∈ wallHyperplanes c, (wallPairsAt c H).card ≤ 15 := by
  classical
  rw [← Finset.card_biUnion (wallPairsAt_disjoint c)]
  calc ((wallHyperplanes c).biUnion (wallPairsAt c)).card ≤ (Finset.univ : Finset Pairs6).card :=
        Finset.card_le_univ _
    _ = 15 := by decide

private lemma wallHyperplanes_finrank {c : Fin 6 → Fin 6 → E4} (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    {H : Submodule ℝ E4} (hH : H ∈ wallHyperplanes c) : Module.finrank ℝ H = 3 := by
  classical
  obtain ⟨e, he⟩ := wallPairsAt_nonempty hH
  rw [wallPairsAt, Finset.mem_filter] at he
  rw [← he.2.2]
  exact finrank_hp (hc_ne e.1.1 e.1.2 (Fin.ne_of_lt e.2))

private lemma wallPair_mem_wallHyperplanes {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) {a b : Fin 6} (hab : a ≠ b) (hw : IsWallPair c a b) :
    mkPair6 a b hab ∈ wallPairsAt c (hp (c a b)) ∧ hp (c a b) ∈ wallHyperplanes c := by
  classical
  have h1 : IsWallPair c (mkPair6 a b hab).1.1 (mkPair6 a b hab).1.2 := by
    dsimp [mkPair6]
    split_ifs
    · exact hw
    · exact isWallPair_symm hc_sym hw
  have h2 : hp (c (mkPair6 a b hab).1.1 (mkPair6 a b hab).1.2) = hp (c a b) := by
    dsimp [mkPair6]
    split_ifs
    · rfl
    · rw [hc_sym, hp_neg]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩, ?_⟩
  rw [wallHyperplanes, Finset.mem_image]
  exact ⟨mkPair6 a b hab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩

private lemma wall_cover_of_facets {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ}) :
    ∀ x : E4, ∀ i : Fin 6, x ∈ Kbar c i → x ∉ Kopen c i →
      ∃ H ∈ wallHyperplanes c, x ∈ H := by
  intro x i hxi hnot
  have hex_j : ∃ j ∈ F i, ⟪c i j, x⟫_ℝ = 0 := by
    by_contra hnone
    push Not at hnone
    apply hnot
    have hxint : x ∈ interior (Kbar c i) := by
      have hmem : x ∈ ⋂ j ∈ F i, {y : E4 | 0 < ⟪c i j, y⟫_ℝ} := by
        rw [Set.mem_iInter₂]
        intro j hj
        have hle : 0 ≤ ⟪c i j, x⟫_ℝ := (hF_eq i ▸ hxi) j hj
        exact lt_of_le_of_ne hle (Ne.symm (hnone j hj))
      refine interior_maximal ?_ (isOpen_biInter_finset fun j _ =>
        isOpen_lt continuous_const (continuous_const.inner continuous_id)) hmem
      intro y hy
      rw [hF_eq i]
      intro j hj
      exact (Set.mem_iInter₂.mp hy j hj).le
    exact (mem_interior_Kbar_iff hc_ne i x).mp hxint
  obtain ⟨j, hjF, hj0⟩ := hex_j
  obtain ⟨k, hki, hw, hpeq⟩ :=
    baire_facet_wall hc_sym hc_ne hK_nonempty hK_cover (hF_sub i) (hF_eq i) (hF_min i) hjF
  have hmem := (wallPair_mem_wallHyperplanes hc_sym hki.symm hw).2
  refine ⟨hp (c i k), hmem, ?_⟩
  rw [← hpeq, mem_hp_iff]
  exact hj0

/-! ### Section 4b: Ridge trichotomy & 4-quadrant analysis -/

private lemma exists_vector_in_diff_hp {H₁ H₂ : Submodule ℝ E4}
    (h₁ : Module.finrank ℝ H₁ = 3) (h₂ : Module.finrank ℝ H₂ = 3) (hne : H₁ ≠ H₂) :
    ∃ v ∈ H₁, v ∉ H₂ := by
  by_contra hnone
  push Not at hnone
  exact hne (hp_eq_of_le h₁ h₂ fun v hv => hnone v hv)

private lemma Kbar_convex (c : Fin 6 → Fin 6 → E4) (i : Fin 6) : Convex ℝ (Kbar c i) := by
  intro x hx y hy a b ha hb _ j hji
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_nonneg (mul_nonneg ha (hx j hji)) (mul_nonneg hb (hy j hji))

private lemma quadrant_nonempty {p_r : E4} {δ : ℝ} (hδ : 0 < δ)
    {n₁ n₂ : E4} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hne : hp n₁ ≠ hp n₂)
    (hp₁ : p_r ∈ hp n₁) (hp₂ : p_r ∈ hp n₂) :
    ({y ∈ Metric.ball p_r δ | 0 < ⟪n₁, y⟫_ℝ ∧ 0 < ⟪n₂, y⟫_ℝ} : Set E4).Nonempty := by
  obtain ⟨u₁, hu1_in, hu1_out⟩ :=
    exists_vector_in_diff_hp (finrank_hp hn₁) (finrank_hp hn₂) hne
  obtain ⟨u₂, hu2_in, hu2_out⟩ :=
    exists_vector_in_diff_hp (finrank_hp hn₂) (finrank_hp hn₁) hne.symm
  have h21 : ⟪n₂, u₁⟫_ℝ ≠ 0 := fun h0 => hu1_out ((mem_hp_iff _ _).mpr h0)
  have h12 : ⟪n₁, u₂⟫_ℝ ≠ 0 := fun h0 => hu2_out ((mem_hp_iff _ _).mpr h0)
  let w₁ : E4 := (1 / ⟪n₂, u₁⟫_ℝ) • u₁
  let w₂ : E4 := (1 / ⟪n₁, u₂⟫_ℝ) • u₂
  let w : E4 := w₁ + w₂
  let ε := (δ / 2) / (‖w‖ + 1)
  have hε_pos : 0 < ε := by positivity
  refine ⟨p_r + ε • w, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hε_pos.le]
    dsimp [ε]
    have hden : 0 < ‖w‖ + 1 := by positivity
    calc (δ / 2) / (‖w‖ + 1) * ‖w‖ = (δ / 2) * (‖w‖ / (‖w‖ + 1)) := by ring
      _ < (δ / 2) * 1 := by
        refine mul_lt_mul_of_pos_left ?_ (half_pos hδ)
        rw [div_lt_one hden]; linarith
      _ < δ := by linarith
  · rw [inner_add_right, real_inner_smul_right, (mem_hp_iff _ _).mp hp₁, zero_add]
    have hw : ⟪n₁, w⟫_ℝ = 1 := by
      dsimp [w, w₁, w₂]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        (mem_hp_iff _ _).mp hu1_in, mul_zero, zero_add]
      field_simp [h12]
    rw [hw, mul_one]; exact hε_pos
  · rw [inner_add_right, real_inner_smul_right, (mem_hp_iff _ _).mp hp₂, zero_add]
    have hw : ⟪n₂, w⟫_ℝ = 1 := by
      dsimp [w, w₁, w₂]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        (mem_hp_iff _ _).mp hu2_in, mul_zero, add_zero]
      field_simp [h21]
    rw [hw, mul_one]; exact hε_pos

private lemma open_quadrant_subset_one_Kopen {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {p_r : E4} {δ : ℝ} (hδ : 0 < δ)
    {n₁ n₂ : E4} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hne : hp n₁ ≠ hp n₂)
    (hp₁ : p_r ∈ hp n₁) (hp₂ : p_r ∈ hp n₂)
    (havoid : ∀ y ∈ Metric.ball p_r δ, ∀ Hs ∈ wallHyperplanes c,
      Hs ≠ hp n₁ → Hs ≠ hp n₂ → y ∉ Hs) :
    ∃ α : Fin 6, {y ∈ Metric.ball p_r δ | 0 < ⟪n₁, y⟫_ℝ ∧ 0 < ⟪n₂, y⟫_ℝ} ⊆ Kopen c α := by
  let Q : Set E4 := {y | y ∈ Metric.ball p_r δ ∧ 0 < ⟪n₁, y⟫_ℝ ∧ 0 < ⟪n₂, y⟫_ℝ}
  have hQ_conv : Convex ℝ Q := by
    refine (convex_ball p_r δ).inter ?_
    intro x hx y hy a b ha hb hab
    have ha' := hx.1; have hb' := hy.1
    have ha2 := hx.2; have hb2 := hy.2
    refine ⟨?_, ?_⟩
    · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      by_cases ha0 : a = 0
      · subst ha0; simp only [zero_add] at hab; subst hab; simp [hb']
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        linarith [mul_pos hap ha', mul_nonneg hb hb'.le]
    · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      by_cases ha0 : a = 0
      · subst ha0; simp only [zero_add] at hab; subst hab; simp [hb2]
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        linarith [mul_pos hap ha2, mul_nonneg hb hb2.le]
  have hQ_ne : Q.Nonempty := quadrant_nonempty hδ hn₁ hn₂ hne hp₁ hp₂
  have hQ_cov : Q ⊆ ⋃ α : Fin 6, Kopen c α := by
    intro y hyQ
    obtain ⟨α, hα⟩ := hK_cover y
    refine Set.mem_iUnion.mpr ⟨α, ?_⟩
    by_contra hnot
    obtain ⟨Hs, hHs, hyHs⟩ :=
      wall_cover_of_facets hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min y α hα hnot
    by_cases h1 : Hs = hp n₁
    · rw [h1, mem_hp_iff] at hyHs; linarith [hyQ.2.1]
    · by_cases h2 : Hs = hp n₂
      · rw [h2, mem_hp_iff] at hyHs; linarith [hyQ.2.2]
      · exact havoid y hyQ.1 Hs hHs h1 h2 hyHs
  obtain ⟨y₀, hy₀Q⟩ := hQ_ne
  obtain ⟨α, hαy₀⟩ := Set.mem_iUnion.mp (hQ_cov hy₀Q)
  refine ⟨α, ?_⟩
  have hdisj : Disjoint (Kopen c α) (⋃ β ∈ Finset.univ.erase α, Kopen c β) := by
    rw [Set.disjoint_iUnion₂_right]
    intro β hβ
    exact Kopen_disjoint hc_sym (Finset.mem_erase.mp hβ).1.symm
  have hcov2 : Q ⊆ Kopen c α ∪ ⋃ β ∈ Finset.univ.erase α, Kopen c β := by
    intro y hy
    obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp (hQ_cov hy)
    by_cases hβα : β = α
    · exact Or.inl (hβα ▸ hβ)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨β, Finset.mem_erase.mpr ⟨hβα, Finset.mem_univ β⟩, hβ⟩)
  have hopen2 : IsOpen (⋃ β ∈ Finset.univ.erase α, Kopen c β) :=
    isOpen_biUnion fun β _ => isOpen_Kopen c β
  have hpre := hQ_conv.isPreconnected.subset_left_of_subset_union (isOpen_Kopen c α) hopen2
    (hdisj.mono (Set.Subset.rfl) (Set.Subset.rfl)) hcov2 ⟨y₀, hy₀Q, hαy₀⟩
  exact hpre

private lemma ridge_quadrant_wall {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    {p_r : E4} {δ : ℝ} (hδ : 0 < δ)
    {n_bdry n_other : E4} (hn_bdry : n_bdry ≠ 0) (hn_other : n_other ≠ 0)
    (hne : hp n_bdry ≠ hp n_other) (hp_b : p_r ∈ hp n_bdry) (hp_o : p_r ∈ hp n_other)
    {α β : Fin 6} (hαβ : α ≠ β)
    (hpos : {y ∈ Metric.ball p_r δ | 0 < ⟪n_bdry, y⟫_ℝ ∧ 0 < ⟪n_other, y⟫_ℝ} ⊆ Kopen c α)
    (hneg : {y ∈ Metric.ball p_r δ | ⟪n_bdry, y⟫_ℝ < 0 ∧ 0 < ⟪n_other, y⟫_ℝ} ⊆ Kopen c β) :
    hp n_bdry = hp (c α β) ∧ IsWallPair c α β := by
  obtain ⟨u₁, hu1_b, hu1_o⟩ :=
    exists_vector_in_diff_hp (finrank_hp hn_bdry) (finrank_hp hn_other) hne
  obtain ⟨u₂, hu2_o, hu2_b⟩ :=
    exists_vector_in_diff_hp (finrank_hp hn_other) (finrank_hp hn_bdry) hne.symm
  have h_o1 : ⟪n_other, u₁⟫_ℝ ≠ 0 := fun h0 => hu1_o ((mem_hp_iff _ _).mpr h0)
  have h_b2 : ⟪n_bdry, u₂⟫_ℝ ≠ 0 := fun h0 => hu2_b ((mem_hp_iff _ _).mpr h0)
  let w₁ : E4 := (1 / ⟪n_other, u₁⟫_ℝ) • u₁
  let w₂ : E4 := (1 / ⟪n_bdry, u₂⟫_ℝ) • u₂
  have hw1_b : w₁ ∈ hp n_bdry := (hp n_bdry).smul_mem _ hu1_b
  have hw1_o : ⟪n_other, w₁⟫_ℝ = 1 := by
    dsimp [w₁]; rw [real_inner_smul_right]; field_simp [h_o1]
  have hw2_o : w₂ ∈ hp n_other := (hp n_other).smul_mem _ hu2_o
  have hw2_b : ⟪n_bdry, w₂⟫_ℝ = 1 := by
    dsimp [w₂]; rw [real_inner_smul_right]; field_simp [h_b2]
  let t₀ := (δ / 2) / (‖w₁‖ + 1)
  have ht0_pos : 0 < t₀ := by positivity
  let m₁ := p_r + t₀ • w₁
  have hm1_b : m₁ ∈ hp n_bdry := (hp n_bdry).add_mem hp_b ((hp n_bdry).smul_mem t₀ hw1_b)
  have hm1_dist : dist m₁ p_r < δ / 2 := by
    rw [dist_eq_norm]
    dsimp [m₁]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0_pos.le]
    dsimp [t₀]
    have hden : 0 < ‖w₁‖ + 1 := by positivity
    calc (δ / 2) / (‖w₁‖ + 1) * ‖w₁‖ = (δ / 2) * (‖w₁‖ / (‖w₁‖ + 1)) := by ring
      _ < (δ / 2) * 1 := by
        refine mul_lt_mul_of_pos_left ?_ (half_pos hδ)
        rw [div_lt_one hden]; linarith
      _ = δ / 2 := mul_one _
  have hm1_o : ⟪n_other, m₁⟫_ℝ = t₀ := by
    dsimp [m₁]
    rw [inner_add_right, real_inner_smul_right, (mem_hp_iff _ _).mp hp_o, hw1_o, zero_add, mul_one]
  let r₁ := min (δ / 2) ((t₀ / 2) / (‖n_other‖ + 1))
  have hr1_pos : 0 < r₁ := lt_min (half_pos hδ) (by positivity)
  have hball : HasBallInHp (Kbar c α ∩ Kbar c β) (hp n_bdry) := by
    refine ⟨m₁, hm1_b, r₁, hr1_pos, fun y hy hyb => ?_⟩
    have hy_δ : dist y p_r < δ := by
      have h1 : dist y m₁ < r₁ := hy
      have h2 : r₁ ≤ δ / 2 := min_le_left _ _
      linarith [dist_triangle y m₁ p_r]
    have hy_o : 0 < ⟪n_other, y⟫_ℝ := by
      have hsub : |⟪n_other, y⟫_ℝ - ⟪n_other, m₁⟫_ℝ| ≤ ‖n_other‖ * dist y m₁ := by
        rw [← inner_sub_right]
        simpa [dist_eq_norm] using abs_real_inner_le_norm n_other (y - m₁)
      have h2 : r₁ ≤ (t₀ / 2) / (‖n_other‖ + 1) := min_le_right _ _
      have hlt : ‖n_other‖ * dist y m₁ < t₀ / 2 := by
        have hdm : dist y m₁ < (t₀ / 2) / (‖n_other‖ + 1) := lt_of_lt_of_le hy h2
        have hden : 0 < ‖n_other‖ + 1 := by positivity
        calc ‖n_other‖ * dist y m₁ ≤ ‖n_other‖ * ((t₀ / 2) / (‖n_other‖ + 1)) :=
              mul_le_mul_of_nonneg_left hdm.le (norm_nonneg _)
          _ < (‖n_other‖ + 1) * ((t₀ / 2) / (‖n_other‖ + 1)) := by
              nlinarith [div_pos (half_pos ht0_pos) hden]
          _ = t₀ / 2 := mul_div_cancel₀ _ hden.ne'
      linarith [(abs_le.mp hsub).1]
    let η₀ := ((δ - dist y p_r) / 2) / (‖w₂‖ + 1)
    have hη0_pos : 0 < η₀ := by positivity
    have hy_lim : ∀ (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (γ : Fin 6),
        (∀ n : ℕ, 0 < (sgn : ℝ) * ⟪n_bdry, y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂⟫_ℝ →
          y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂ ∈ Metric.ball p_r δ →
          0 < ⟪n_other, y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂⟫_ℝ →
          y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂ ∈ Kopen c γ) →
        y ∈ Kbar c γ := by
      intro sgn hsgn γ hmem
      have hseq : ∀ n : ℕ, y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂ ∈ Kbar c γ := fun n => by
        refine Kopen_subset_Kbar c γ (hmem n ?_ ?_ ?_)
        · rw [inner_add_right, real_inner_smul_right, (mem_hp_iff _ _).mp hyb, zero_add, hw2_b, mul_one]
          have hpos_η : 0 < η₀ / ((n : ℝ) + 1) := div_pos hη0_pos (by positivity)
          rcases hsgn with rfl | rfl
          · simpa using hpos_η
          · linarith
        · rw [Metric.mem_ball]
          have htri : dist (y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂) p_r ≤
              dist y p_r + ‖(sgn * (η₀ / ((n : ℝ) + 1))) • w₂‖ := by
            simpa [dist_eq_norm, add_sub_right_comm] using
              norm_add_le (y - p_r) ((sgn * (η₀ / ((n : ℝ) + 1))) • w₂)
          have hnorm : ‖(sgn * (η₀ / ((n : ℝ) + 1))) • w₂‖ < (δ - dist y p_r) / 2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul]
            have h1 : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> simp
            rw [h1, one_mul, abs_of_pos (div_pos hη0_pos (by positivity))]
            have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
            have hle : η₀ / ((n : ℝ) + 1) ≤ η₀ := div_le_self hη0_pos.le hn1
            have hden : 0 < ‖w₂‖ + 1 := by positivity
            calc η₀ / ((n : ℝ) + 1) * ‖w₂‖ ≤ η₀ * ‖w₂‖ :=
                  mul_le_mul_of_nonneg_right hle (norm_nonneg _)
              _ < ((δ - dist y p_r) / 2) / (‖w₂‖ + 1) * (‖w₂‖ + 1) := by
                  nlinarith [div_pos (half_pos (sub_pos.mpr hy_δ)) hden]
              _ = (δ - dist y p_r) / 2 := div_mul_cancel₀ _ hden.ne'
          linarith
        · rw [inner_add_right, real_inner_smul_right, (mem_hp_iff _ _).mp hw2_o, mul_zero, add_zero]
          exact hy_o
      have htend : Filter.Tendsto (fun n : ℕ => y + (sgn * (η₀ / ((n : ℝ) + 1))) • w₂)
          Filter.atTop (nhds y) := by
        have h0 : Filter.Tendsto (fun n : ℕ => (sgn * η₀) * (1 / ((n : ℝ) + 1))) Filter.atTop (nhds ((sgn * η₀) * 0)) :=
          tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
        rw [mul_zero] at h0
        have h0' : Filter.Tendsto (fun n : ℕ => (sgn * (η₀ / ((n : ℝ) + 1))) • w₂)
            Filter.atTop (nhds ((0 : ℝ) • w₂)) := by
          refine Filter.Tendsto.smul_const ?_ w₂
          convert h0 using 1
          ext n
          ring
        rw [zero_smul] at h0'
        simpa using tendsto_const_nhds.add h0'
      exact (isClosed_Kbar c γ).mem_of_tendsto htend (Filter.Eventually.of_forall hseq)
    refine ⟨hy_lim 1 (Or.inl rfl) α (fun n h1 h2 h3 => hpos ⟨h2, by simpa using h1, h3⟩),
      hy_lim (-1) (Or.inr rfl) β (fun n h1 h2 h3 => hneg ⟨h2, by linarith, h3⟩)⟩
  exact hp_eq_of_wall_ball hc_sym hc_ne (finrank_hp hn_bdry) hαβ.symm hball

private lemma facet_vec_hp_mem {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {i j : Fin 6} {v : E4}
    (hv : v ∈ ((F i).image (c i) ∪ (F j).image (c j))) :
    v ≠ 0 ∧ hp v ∈ wallHyperplanes c := by
  classical
  rcases Finset.mem_union.mp hv with hv_i | hv_j
  · rw [Finset.mem_image] at hv_i
    obtain ⟨a, haF, rfl⟩ := hv_i
    have hai : a ≠ i := (Finset.mem_erase.mp (hF_sub i haF)).1
    obtain ⟨k, hki, hw, hpeq⟩ :=
      baire_facet_wall hc_sym hc_ne hK_nonempty hK_cover (hF_sub i) (hF_eq i) (hF_min i) haF
    refine ⟨hc_ne i a hai.symm, ?_⟩
    rw [hpeq]
    exact (wallPair_mem_wallHyperplanes hc_sym hki.symm hw).2
  · rw [Finset.mem_image] at hv_j
    obtain ⟨b, hbF, rfl⟩ := hv_j
    have hbj : b ≠ j := (Finset.mem_erase.mp (hF_sub j hbF)).1
    obtain ⟨k, hkj, hw, hpeq⟩ :=
      baire_facet_wall hc_sym hc_ne hK_nonempty hK_cover (hF_sub j) (hF_eq j) (hF_min j) hbF
    refine ⟨hc_ne j b hbj.symm, ?_⟩
    rw [hpeq]
    exact (wallPair_mem_wallHyperplanes hc_sym hkj.symm hw).2

private lemma ridge_trichotomy {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {H : Submodule ℝ E4} (_hH : H ∈ wallHyperplanes c)
    {e : Pairs6} (he : e ∈ wallPairsAt c H)
    {L : Finset E4}
    (hL_sub : L ⊆ ((F e.1.1).image (c e.1.1) ∪ (F e.1.2).image (c e.1.2)).filter (fun v => hp v ≠ H))
    (hL_eq : {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} =
      {x : E4 | x ∈ H ∧ ∀ v ∈ L, 0 ≤ ⟪v, x⟫_ℝ})
    (hL_min : ∀ L' ⊂ L, {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} ≠
      {x : E4 | x ∈ H ∧ ∀ v ∈ L', 0 ≤ ⟪v, x⟫_ℝ})
    {v : E4} (hvL : v ∈ L) :
    (hp v ∈ (wallHyperplanes c).erase H) ∧
    ((∃ H'' ∈ wallHyperplanes c, CoplanarTriple H (hp v) H'') ∨
     2 ≤ (wallPairsAt c H).card ∨
     ∃ k : Fin 6, ∃ (hki : k ≠ e.1.1) (hkj : k ≠ e.1.2),
       mkPair6 e.1.1 k hki.symm ∈ wallPairsAt c (hp v) ∧
       mkPair6 e.1.2 k hkj.symm ∈ wallPairsAt c (hp v)) := by
  classical
  set i := e.1.1
  set j := e.1.2
  have hij : i ≠ j := Fin.ne_of_lt e.2
  have he_filt := Finset.mem_filter.mp he
  have hw_ij : IsWallPair c i j := he_filt.2.1
  have hH_eq : hp (c i j) = H := he_filt.2.2
  have hH_fin : Module.finrank ℝ H = 3 := hH_eq ▸ finrank_hp (hc_ne i j hij)
  have hv_mem0 := Finset.mem_filter.mp (hL_sub hvL)
  have hv_ne_H : hp v ≠ H := hv_mem0.2
  obtain ⟨hv_ne0, hHv_mem⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hv_mem0.1
  have hHv_fin : Module.finrank ℝ (hp v) = 3 := finrank_hp hv_ne0
  have hpv_er : hp v ∈ (wallHyperplanes c).erase H := Finset.mem_erase.mpr ⟨hv_ne_H, hHv_mem⟩
  refine ⟨hpv_er, ?_⟩
  obtain ⟨p₀, hp₀H, r₀, hr₀_pos, hr₀⟩ := hw_ij.2
  rw [hH_eq] at hp₀H hr₀
  have hp₀_in : p₀ ∈ Kbar c i ∩ Kbar c j := hr₀ p₀ (Metric.mem_ball_self hr₀_pos) hp₀H
  have hp₀_pos : ∀ w ∈ L, 0 < ⟪w, p₀⟫_ℝ := by
    intro w hwL
    have hw_filt := Finset.mem_filter.mp (hL_sub hwL)
    have hw_ne_H : hp w ≠ H := hw_filt.2
    obtain ⟨hw0, _⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hw_filt.1
    have hge : 0 ≤ ⟪w, p₀⟫_ℝ := by
      have hm : p₀ ∈ {x : E4 | x ∈ H ∧ x ∈ Kbar c i ∩ Kbar c j} := ⟨hp₀H, hp₀_in⟩
      rw [hL_eq] at hm
      exact hm.2 w hwL
    by_contra hle
    have hw_p0 : ⟪w, p₀⟫_ℝ = 0 := le_antisymm (not_lt.mp hle) hge
    obtain ⟨z, hzH, hz_not⟩ := exists_vector_in_diff_hp hH_fin (finrank_hp hw0) hw_ne_H.symm
    have hzw : ⟪w, z⟫_ℝ ≠ 0 := fun h0 => hz_not ((mem_hp_iff _ _).mpr h0)
    let ε := ((r₀ / 2) / (‖z‖ + 1)) * (if 0 < ⟪w, z⟫_ℝ then (-1 : ℝ) else 1)
    have hε_abs : |ε| = (r₀ / 2) / (‖z‖ + 1) := by
      dsimp [ε]
      rw [abs_mul, abs_of_pos (by positivity)]
      split_ifs <;> simp
    have hz_ball : p₀ + ε • z ∈ Metric.ball p₀ r₀ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hε_abs]
      have hden : 0 < ‖z‖ + 1 := by positivity
      calc (r₀ / 2) / (‖z‖ + 1) * ‖z‖ = (r₀ / 2) * (‖z‖ / (‖z‖ + 1)) := by ring
        _ < (r₀ / 2) * 1 := by
          refine mul_lt_mul_of_pos_left ?_ (half_pos hr₀_pos)
          rw [div_lt_one hden]; linarith
        _ < r₀ := by linarith
    have hpz_in : p₀ + ε • z ∈ Kbar c i ∩ Kbar c j :=
      hr₀ (p₀ + ε • z) hz_ball (H.add_mem hp₀H (H.smul_mem ε hzH))
    have hpz_pos : 0 ≤ ⟪w, p₀ + ε • z⟫_ℝ := by
      have hm : p₀ + ε • z ∈ {x : E4 | x ∈ H ∧ x ∈ Kbar c i ∩ Kbar c j} :=
        ⟨H.add_mem hp₀H (H.smul_mem ε hzH), hpz_in⟩
      rw [hL_eq] at hm
      exact hm.2 w hwL
    rw [inner_add_right, real_inner_smul_right, hw_p0, zero_add] at hpz_pos
    have hneg : ε * ⟪w, z⟫_ℝ < 0 := by
      dsimp [ε]
      split_ifs with hpos
      · have : 0 < (r₀ / 2) / (‖z‖ + 1) := by positivity
        nlinarith
      · have hlt0 : ⟪w, z⟫_ℝ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzw
        have : 0 < (r₀ / 2) / (‖z‖ + 1) := by positivity
        nlinarith
    linarith
  -- Interpolate to get `q ∈ H ⊓ hp v` strictly positive on `L.erase v`
  have hL_er := hL_min (L.erase v) (Finset.erase_ssubset hvL)
  have hex_x0 : ∃ x₀ ∈ H, ⟪v, x₀⟫_ℝ < 0 ∧ ∀ w ∈ L.erase v, 0 ≤ ⟪w, x₀⟫_ℝ := by
    by_contra hnone
    push Not at hnone
    apply hL_er
    ext x
    rw [hL_eq]
    simp only [Set.mem_ofPred_eq, Finset.mem_erase, and_imp]
    constructor
    · intro ⟨hxH, hxw⟩; exact ⟨hxH, fun w _ hwL => hxw w hwL⟩
    · intro ⟨hxH, hxw⟩
      refine ⟨hxH, fun w hwL => ?_⟩
      by_cases hwv : w = v
      · subst hwv
        by_contra hneg
        obtain ⟨w', hw', hw'neg⟩ := hnone x hxH (not_le.mp hneg)
        have hw'_mem := Finset.mem_erase.mp hw'
        exact absurd (hxw w' hw'_mem.1 hw'_mem.2) (not_le.mpr hw'neg)
      · exact hxw w hwv hwL
  obtain ⟨x₀, hx0H, hx0_neg, hx0_ge⟩ := hex_x0
  let a := -⟪v, x₀⟫_ℝ
  let b := ⟪v, p₀⟫_ℝ
  have ha_pos : 0 < a := neg_pos.mpr hx0_neg
  have hb_pos : 0 < b := hp₀_pos v hvL
  have hab_pos : 0 < a + b := by positivity
  let t : ℝ := a / (a + b)
  have ht0 : 0 < t := div_pos ha_pos hab_pos
  have ht1 : t < 1 := (div_lt_one hab_pos).mpr (by linarith)
  let q : E4 := (1 - t) • x₀ + t • p₀
  have hqH : q ∈ H := H.add_mem (H.smul_mem _ hx0H) (H.smul_mem _ hp₀H)
  have hqv : q ∈ hp v := by
    rw [mem_hp_iff]
    dsimp [q]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hx_val : ⟪v, x₀⟫_ℝ = -a := by dsimp [a]; ring
    have hp_val : ⟪v, p₀⟫_ℝ = b := rfl
    rw [hx_val, hp_val]
    dsimp [t]
    field_simp [hab_pos.ne']
    ring
  have hq_pos : ∀ w ∈ L.erase v, 0 < ⟪w, q⟫_ℝ := by
    intro w hw
    dsimp [q]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 : 0 ≤ (1 - t) * ⟪w, x₀⟫_ℝ := mul_nonneg (sub_nonneg.mpr ht1.le) (hx0_ge w hw)
    have h2 : 0 < t * ⟪w, p₀⟫_ℝ := mul_pos ht0 (hp₀_pos w (Finset.mem_erase.mp hw).2)
    linarith
  let K2 := (H ⊓ hp v : Submodule ℝ E4)
  let U2 : Set K2 := ⋂ w ∈ L.erase v, {x : K2 | 0 < ⟪w, (x : E4)⟫_ℝ}
  have hU2_open : IsOpen U2 :=
    isOpen_biInter_finset fun w _ =>
      isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  have hq_U2 : (⟨q, hqH, hqv⟩ : K2) ∈ U2 := Set.mem_iInter₂.mpr hq_pos
  let Fbad := ((wallHyperplanes c).erase H).erase (hp v)
  by_cases hcop_v : ∃ H'' ∈ Fbad, K2 ≤ H''
  · obtain ⟨H'', hH'', hle⟩ := hcop_v
    have h1 := Finset.mem_erase.mp hH''
    have h2 := Finset.mem_erase.mp h1.2
    exact Or.inl ⟨H'', h2.2, hv_ne_H.symm, h1.1.symm, h2.1.symm, hle⟩
  right
  have hnot_sub : ∀ H'' ∈ Fbad, ¬ K2 ≤ H'' := fun H'' hH'' hle => hcop_v ⟨H'', hH'', hle⟩
  obtain ⟨p_r_k, hpr_U2, hpr_avoid⟩ :=
    exists_mem_open_avoiding_subspaces K2 Fbad hnot_sub hU2_open ⟨_, hq_U2⟩
  let p_r : E4 := p_r_k.1
  have hprH : p_r ∈ H := p_r_k.2.1
  have hpr_v : p_r ∈ hp v := p_r_k.2.2
  have hpr_in : p_r ∈ Kbar c i ∩ Kbar c j := by
    have hmem : p_r ∈ {x : E4 | x ∈ H ∧ ∀ w ∈ L, 0 ≤ ⟪w, x⟫_ℝ} := by
      refine ⟨hprH, fun w hwL => ?_⟩
      by_cases hwv : w = v
      · subst hwv; exact le_of_eq ((mem_hp_iff _ _).mp hpr_v).symm
      · exact (Set.mem_iInter₂.mp hpr_U2 w (Finset.mem_erase.mpr ⟨hwv, hwL⟩)).le
    rw [← hL_eq] at hmem
    exact hmem.2
  let U_avoid : Set E4 := ⋂ H'' ∈ Fbad, (H'' : Set E4)ᶜ
  have hU_avoid_open : IsOpen U_avoid :=
    isOpen_biInter_finset fun H'' _ => (H''.closed_of_finiteDimensional).isOpen_compl
  have hpr_avoid' : p_r ∈ U_avoid := Set.mem_iInter₂.mpr hpr_avoid
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.isOpen_iff.mp hU_avoid_open p_r hpr_avoid'
  have havoid : ∀ (n₁ n₂ : E4), hp n₁ = H → hp n₂ = hp v →
      ∀ y ∈ Metric.ball p_r δ, ∀ Hs ∈ wallHyperplanes c, Hs ≠ hp n₁ → Hs ≠ hp n₂ → y ∉ Hs := by
    intro n₁ n₂ hn1 hn2 y hy Hs hHs h1 h2
    have hHs_bad : Hs ∈ Fbad :=
      Finset.mem_erase.mpr ⟨hn2 ▸ h2, Finset.mem_erase.mpr ⟨hn1 ▸ h1, hHs⟩⟩
    exact Set.mem_iInter₂.mp (hδ hy) Hs hHs_bad
  have hne_ij_v : hp (c i j) ≠ hp v := hH_eq.symm ▸ hv_ne_H.symm
  have hne_neg_ij_v : hp (-c i j) ≠ hp v := by rwa [hp_neg]
  have hne_ij_neg_v : hp (c i j) ≠ hp (-v) := by rwa [hp_neg]
  have hne_neg_ij_neg_v : hp (-c i j) ≠ hp (-v) := by rwa [hp_neg, hp_neg]
  have hpr_ij : p_r ∈ hp (c i j) := hH_eq.symm ▸ hprH
  have hpr_neg_ij : p_r ∈ hp (-c i j) := by rwa [hp_neg]
  have hpr_neg_v : p_r ∈ hp (-v) := by rwa [hp_neg]
  obtain ⟨α_pp, hQ_pp⟩ := open_quadrant_subset_one_Kopen hc_sym hc_ne hK_nonempty hK_cover
    hF_sub hF_eq hF_min hδ_pos (hc_ne i j hij) hv_ne0 hne_ij_v hpr_ij hpr_v
    (havoid _ _ hH_eq rfl)
  obtain ⟨α_mp, hQ_mp⟩ := open_quadrant_subset_one_Kopen hc_sym hc_ne hK_nonempty hK_cover
    hF_sub hF_eq hF_min hδ_pos (neg_ne_zero.mpr (hc_ne i j hij)) hv_ne0 hne_neg_ij_v hpr_neg_ij hpr_v
    (havoid _ _ (by rw [hp_neg, hH_eq]) rfl)
  obtain ⟨α_pm, hQ_pm⟩ := open_quadrant_subset_one_Kopen hc_sym hc_ne hK_nonempty hK_cover
    hF_sub hF_eq hF_min hδ_pos (hc_ne i j hij) (neg_ne_zero.mpr hv_ne0) hne_ij_neg_v hpr_ij hpr_neg_v
    (havoid _ _ hH_eq (hp_neg v))
  obtain ⟨α_mm, hQ_mm⟩ := open_quadrant_subset_one_Kopen hc_sym hc_ne hK_nonempty hK_cover
    hF_sub hF_eq hF_min hδ_pos (neg_ne_zero.mpr (hc_ne i j hij)) (neg_ne_zero.mpr hv_ne0)
    hne_neg_ij_neg_v hpr_neg_ij hpr_neg_v
    (havoid _ _ (by rw [hp_neg, hH_eq]) (hp_neg v))
  -- Identify α_pp = i and α_mp = j
  let tq := min (1 / 2 : ℝ) ((δ / 2) / (‖p₀ - p_r‖ + 1))
  have htq_pos : 0 < tq := lt_min (by norm_num) (by positivity)
  have htq_le : tq ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let q₀ := (1 - tq) • p_r + tq • p₀
  have hq0_dist : dist q₀ p_r < δ / 2 := by
    have hsub : q₀ - p_r = tq • (p₀ - p_r) := by dsimp [q₀]; module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg htq_pos.le]
    have htq_bd : tq ≤ (δ / 2) / (‖p₀ - p_r‖ + 1) := min_le_right _ _
    have hden : 0 < ‖p₀ - p_r‖ + 1 := by positivity
    calc tq * ‖p₀ - p_r‖ ≤ ((δ / 2) / (‖p₀ - p_r‖ + 1)) * ‖p₀ - p_r‖ :=
          mul_le_mul_of_nonneg_right htq_bd (norm_nonneg _)
      _ < ((δ / 2) / (‖p₀ - p_r‖ + 1)) * (‖p₀ - p_r‖ + 1) := by
          nlinarith [div_pos (half_pos hδ_pos) hden]
      _ = δ / 2 := div_mul_cancel₀ _ hden.ne'
  have hq0_v : 0 < ⟪v, q₀⟫_ℝ := by
    dsimp [q₀]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      (mem_hp_iff _ _).mp hpr_v, mul_zero, zero_add]
    exact mul_pos htq_pos (hp₀_pos v hvL)
  have hq0_ij : ⟪c i j, q₀⟫_ℝ = 0 := by
    dsimp [q₀]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      (mem_hp_iff _ _).mp hpr_ij, (mem_hp_iff _ _).mp (hH_eq ▸ hp₀H)]
    ring
  have hq0_Ki : q₀ ∈ Kbar c i := Kbar_convex c i hpr_in.1 hp₀_in.1 (sub_nonneg.mpr htq_le) htq_pos.le (by ring)
  have hq0_Kj : q₀ ∈ Kbar c j := Kbar_convex c j hpr_in.2 hp₀_in.2 (sub_nonneg.mpr htq_le) htq_pos.le (by ring)
  have hα_pp_eq : α_pp = i := by
    obtain ⟨yᵢ, hyᵢ⟩ := hK_nonempty i
    let η := min (1 / 2 : ℝ) (min ((δ / 2) / (‖yᵢ - q₀‖ + 1)) ((⟪v, q₀⟫_ℝ / 2) / (|⟪v, yᵢ - q₀⟫_ℝ| + 1)))
    have hη_pos : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hη_lt1 : η < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    let z := (1 - η) • q₀ + η • yᵢ
    have hz_Ki : z ∈ Kopen c i := by
      intro a hai
      dsimp [z]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      linarith [mul_nonneg (sub_nonneg.mpr hη_lt1.le) (hq0_Ki a hai), mul_pos hη_pos (hyᵢ a hai)]
    have hz_Q : z ∈ Metric.ball p_r δ ∧ 0 < ⟪c i j, z⟫_ℝ ∧ 0 < ⟪v, z⟫_ℝ := by
      have hz_sub : z - q₀ = η • (yᵢ - q₀) := by dsimp [z]; module
      refine ⟨?_, ?_, ?_⟩
      · have hd : dist z q₀ < δ / 2 := by
          rw [dist_eq_norm, hz_sub, norm_smul, Real.norm_of_nonneg hη_pos.le]
          have h1 : η ≤ (δ / 2) / (‖yᵢ - q₀‖ + 1) := (min_le_right _ _).trans (min_le_left _ _)
          have hden : 0 < ‖yᵢ - q₀‖ + 1 := by positivity
          calc η * ‖yᵢ - q₀‖ ≤ ((δ / 2) / (‖yᵢ - q₀‖ + 1)) * ‖yᵢ - q₀‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ < ((δ / 2) / (‖yᵢ - q₀‖ + 1)) * (‖yᵢ - q₀‖ + 1) := by
                nlinarith [div_pos (half_pos hδ_pos) hden]
            _ = δ / 2 := div_mul_cancel₀ _ hden.ne'
        rw [Metric.mem_ball]
        linarith [dist_triangle z q₀ p_r]
      · dsimp [z]
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hq0_ij, mul_zero, zero_add]
        exact mul_pos hη_pos (hyᵢ j hij.symm)
      · have hv_eq : ⟪v, z⟫_ℝ = ⟪v, q₀⟫_ℝ + η * ⟪v, yᵢ - q₀⟫_ℝ := by
          rw [← sub_add_cancel z q₀, hz_sub, inner_add_right, real_inner_smul_right]
          ring
        have h2 : η ≤ (⟪v, q₀⟫_ℝ / 2) / (|⟪v, yᵢ - q₀⟫_ℝ| + 1) :=
          (min_le_right _ _).trans (min_le_right _ _)
        have hden : 0 < |⟪v, yᵢ - q₀⟫_ℝ| + 1 := by positivity
        have hbd : |η * ⟪v, yᵢ - q₀⟫_ℝ| < ⟪v, q₀⟫_ℝ / 2 := by
          rw [abs_mul, abs_of_pos hη_pos]
          calc η * |⟪v, yᵢ - q₀⟫_ℝ| ≤ ((⟪v, q₀⟫_ℝ / 2) / (|⟪v, yᵢ - q₀⟫_ℝ| + 1)) * |⟪v, yᵢ - q₀⟫_ℝ| :=
                mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
            _ < ((⟪v, q₀⟫_ℝ / 2) / (|⟪v, yᵢ - q₀⟫_ℝ| + 1)) * (|⟪v, yᵢ - q₀⟫_ℝ| + 1) := by
                nlinarith [div_pos (half_pos hq0_v) hden]
            _ = ⟪v, q₀⟫_ℝ / 2 := div_mul_cancel₀ _ hden.ne'
        linarith [(abs_lt.mp hbd).1]
    have hz_α := hQ_pp hz_Q
    by_contra hne
    exact Set.disjoint_left.mp (Kopen_disjoint hc_sym hne) hz_α hz_Ki
  have hα_mp_eq : α_mp = j := by
    obtain ⟨yⱼ, hyⱼ⟩ := hK_nonempty j
    let η := min (1 / 2 : ℝ) (min ((δ / 2) / (‖yⱼ - q₀‖ + 1)) ((⟪v, q₀⟫_ℝ / 2) / (|⟪v, yⱼ - q₀⟫_ℝ| + 1)))
    have hη_pos : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hη_lt1 : η < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    let z := (1 - η) • q₀ + η • yⱼ
    have hz_Kj : z ∈ Kopen c j := by
      intro a haj
      dsimp [z]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      linarith [mul_nonneg (sub_nonneg.mpr hη_lt1.le) (hq0_Kj a haj), mul_pos hη_pos (hyⱼ a haj)]
    have hz_Q : z ∈ Metric.ball p_r δ ∧ 0 < ⟪-c i j, z⟫_ℝ ∧ 0 < ⟪v, z⟫_ℝ := by
      have hz_sub : z - q₀ = η • (yⱼ - q₀) := by dsimp [z]; module
      refine ⟨?_, ?_, ?_⟩
      · have hd : dist z q₀ < δ / 2 := by
          rw [dist_eq_norm, hz_sub, norm_smul, Real.norm_of_nonneg hη_pos.le]
          have h1 : η ≤ (δ / 2) / (‖yⱼ - q₀‖ + 1) := (min_le_right _ _).trans (min_le_left _ _)
          have hden : 0 < ‖yⱼ - q₀‖ + 1 := by positivity
          calc η * ‖yⱼ - q₀‖ ≤ ((δ / 2) / (‖yⱼ - q₀‖ + 1)) * ‖yⱼ - q₀‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ < ((δ / 2) / (‖yⱼ - q₀‖ + 1)) * (‖yⱼ - q₀‖ + 1) := by
                nlinarith [div_pos (half_pos hδ_pos) hden]
            _ = δ / 2 := div_mul_cancel₀ _ hden.ne'
        rw [Metric.mem_ball]
        linarith [dist_triangle z q₀ p_r]
      · dsimp [z]
        rw [inner_neg_left, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          hq0_ij, mul_zero, zero_add]
        have hj_lt : ⟪c i j, yⱼ⟫_ℝ < 0 := by
          have := hyⱼ i hij
          rw [hc_sym, inner_neg_left] at this
          linarith
        nlinarith
      · have hv_eq : ⟪v, z⟫_ℝ = ⟪v, q₀⟫_ℝ + η * ⟪v, yⱼ - q₀⟫_ℝ := by
          rw [← sub_add_cancel z q₀, hz_sub, inner_add_right, real_inner_smul_right]
          ring
        have h2 : η ≤ (⟪v, q₀⟫_ℝ / 2) / (|⟪v, yⱼ - q₀⟫_ℝ| + 1) :=
          (min_le_right _ _).trans (min_le_right _ _)
        have hden : 0 < |⟪v, yⱼ - q₀⟫_ℝ| + 1 := by positivity
        have hbd : |η * ⟪v, yⱼ - q₀⟫_ℝ| < ⟪v, q₀⟫_ℝ / 2 := by
          rw [abs_mul, abs_of_pos hη_pos]
          calc η * |⟪v, yⱼ - q₀⟫_ℝ| ≤ ((⟪v, q₀⟫_ℝ / 2) / (|⟪v, yⱼ - q₀⟫_ℝ| + 1)) * |⟪v, yⱼ - q₀⟫_ℝ| :=
                mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
            _ < ((⟪v, q₀⟫_ℝ / 2) / (|⟪v, yⱼ - q₀⟫_ℝ| + 1)) * (|⟪v, yⱼ - q₀⟫_ℝ| + 1) := by
                nlinarith [div_pos (half_pos hq0_v) hden]
            _ = ⟪v, q₀⟫_ℝ / 2 := div_mul_cancel₀ _ hden.ne'
        linarith [(abs_lt.mp hbd).1]
    have hz_α := hQ_mp hz_Q
    by_contra hne
    exact Set.disjoint_left.mp (Kopen_disjoint hc_sym hne) hz_α hz_Kj
  subst hα_pp_eq
  subst hα_mp_eq
  -- Check signs of α_pm and α_mm
  have hpm_ne_j : α_pm ≠ j := by
    intro heq
    subst heq
    obtain ⟨y, hy⟩ := quadrant_nonempty hδ_pos (hc_ne i j hij) (neg_ne_zero.mpr hv_ne0)
      hne_ij_neg_v hpr_ij hpr_neg_v
    have hlt : 0 < ⟪c j i, y⟫_ℝ := hQ_pm hy i hij
    rw [hc_sym, inner_neg_left] at hlt
    linarith [hy.2.1]
  have hmm_ne_i : α_mm ≠ i := by
    intro heq
    subst heq
    obtain ⟨y, hy⟩ := quadrant_nonempty hδ_pos (neg_ne_zero.mpr (hc_ne i j hij))
      (neg_ne_zero.mpr hv_ne0) hne_neg_ij_neg_v hpr_neg_ij hpr_neg_v
    have hlt := hQ_mm hy j hij.symm
    have hneg := hy.2.1
    rw [inner_neg_left] at hneg
    linarith
  have hne_or : α_pm ≠ i ∨ α_mm ≠ j := by
    rcases Finset.mem_union.mp hv_mem0.1 with hv_i | hv_j
    · rw [Finset.mem_image] at hv_i
      obtain ⟨αf, hαF, hαeq⟩ := hv_i
      have hai : αf ≠ i := (Finset.mem_erase.mp (hF_sub i hαF)).1
      left
      intro heq
      subst heq
      obtain ⟨y, hy⟩ := quadrant_nonempty hδ_pos (hc_ne i j hij) (neg_ne_zero.mpr hv_ne0)
        hne_ij_neg_v hpr_ij hpr_neg_v
      have hpos := hQ_pm hy αf hai
      have hneg := hy.2.2
      rw [← hαeq, inner_neg_left] at hneg
      linarith
    · rw [Finset.mem_image] at hv_j
      obtain ⟨βf, hβF, hβeq⟩ := hv_j
      have hbj : βf ≠ j := (Finset.mem_erase.mp (hF_sub j hβF)).1
      right
      intro heq
      subst heq
      obtain ⟨y, hy⟩ := quadrant_nonempty hδ_pos (neg_ne_zero.mpr (hc_ne i j hij))
        (neg_ne_zero.mpr hv_ne0) hne_neg_ij_neg_v hpr_neg_ij hpr_neg_v
      have hpos := hQ_mm hy βf hbj
      have hneg := hy.2.2
      rw [← hβeq, inner_neg_left] at hneg
      linarith
  -- Finish via ridge_quadrant_wall!
  by_cases hdiff : α_pm = α_mm
  · right
    let k := α_pm
    have hk_eq : α_mm = k := hdiff.symm
    have hki : k ≠ i := hk_eq ▸ hmm_ne_i
    have hkj : k ≠ j := hpm_ne_j
    have hQ_pp' : {y ∈ Metric.ball p_r δ | 0 < ⟪v, y⟫_ℝ ∧ 0 < ⟪c i j, y⟫_ℝ} ⊆ Kopen c i :=
      fun y hy => hQ_pp ⟨hy.1, hy.2.2, hy.2.1⟩
    have hQ_pm' : {y ∈ Metric.ball p_r δ | ⟪v, y⟫_ℝ < 0 ∧ 0 < ⟪c i j, y⟫_ℝ} ⊆ Kopen c k :=
      fun y hy => hQ_pm ⟨hy.1, hy.2.2, by simpa [inner_neg_left] using hy.2.1⟩
    have hw1 := ridge_quadrant_wall hc_sym hc_ne hδ_pos hv_ne0 (hc_ne i j hij) hne_ij_v.symm
      hpr_v hpr_ij hki.symm hQ_pp' hQ_pm'
    have hQ_mp' : {y ∈ Metric.ball p_r δ | 0 < ⟪v, y⟫_ℝ ∧ 0 < ⟪-c i j, y⟫_ℝ} ⊆ Kopen c j :=
      fun y hy => hQ_mp ⟨hy.1, hy.2.2, hy.2.1⟩
    have hQ_mm' : {y ∈ Metric.ball p_r δ | ⟪v, y⟫_ℝ < 0 ∧ 0 < ⟪-c i j, y⟫_ℝ} ⊆ Kopen c k :=
      fun y hy => hk_eq ▸ hQ_mm ⟨hy.1, hy.2.2, by simpa [inner_neg_left] using hy.2.1⟩
    have hw2 := ridge_quadrant_wall hc_sym hc_ne hδ_pos hv_ne0 (neg_ne_zero.mpr (hc_ne i j hij))
      hne_neg_ij_v.symm hpr_v hpr_neg_ij hkj.symm hQ_mp' hQ_mm'
    refine ⟨k, hki, hkj, ?_, ?_⟩
    · have hm := (wallPair_mem_wallHyperplanes hc_sym hki.symm hw1.2).1
      rwa [← hw1.1] at hm
    · have hm := (wallPair_mem_wallHyperplanes hc_sym hkj.symm hw2.2).1
      rwa [← hw2.1] at hm
  · left
    have hQ_mm' : {y ∈ Metric.ball p_r δ | ⟪c i j, y⟫_ℝ < 0 ∧ 0 < ⟪-v, y⟫_ℝ} ⊆ Kopen c α_mm :=
      fun y hy => hQ_mm ⟨hy.1, by simpa [inner_neg_left] using hy.2.1, hy.2.2⟩
    have hw := ridge_quadrant_wall hc_sym hc_ne hδ_pos (hc_ne i j hij) (neg_ne_zero.mpr hv_ne0)
      hne_ij_neg_v hpr_ij hpr_neg_v hdiff hQ_pm hQ_mm'
    have hm := (wallPair_mem_wallHyperplanes hc_sym hdiff hw.2).1
    rw [← hw.1, hH_eq] at hm
    have hne_p : e ≠ mkPair6 α_pm α_mm hdiff := fun heq => by
      have h1 : (mkPair6 α_pm α_mm hdiff).1 = e.1 := congrArg Subtype.val heq.symm
      rcases lt_or_gt_of_ne hdiff with hlt | hlt
      · have he_pm : α_pm = i := by simpa [mkPair6, hlt] using congrArg Prod.fst h1
        have he_mm : α_mm = j := by simpa [mkPair6, hlt] using congrArg Prod.snd h1
        exact hne_or.elim (· he_pm) (· he_mm)
      · have hnot : ¬ α_pm < α_mm := not_lt.mpr hlt.le
        have he_mm : α_mm = i := by simpa [mkPair6, hnot] using congrArg Prod.fst h1
        exact hmm_ne_i he_mm
    exact Finset.one_lt_card.mpr ⟨e, he, mkPair6 α_pm α_mm hdiff, hm, hne_p⟩

/-! ### Section 4c: Minimal ridge family `L`, `|L| ≤ 1` bounds, & wedge ticket counting -/

private lemma exists_minimal_L {c : Fin 6 → Fin 6 → E4}
    (_hc_sym : ∀ i j, c j i = -c i j) (_hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (F : Fin 6 → Finset (Fin 6))
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    {H : Submodule ℝ E4} {e : Pairs6} (he : e ∈ wallPairsAt c H) :
    ∃ L : Finset E4,
      L ⊆ ((F e.1.1).image (c e.1.1) ∪ (F e.1.2).image (c e.1.2)).filter (fun v => hp v ≠ H) ∧
      {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} =
        {x : E4 | x ∈ H ∧ ∀ v ∈ L, 0 ≤ ⟪v, x⟫_ℝ} ∧
      ∀ L' ⊂ L, {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} ≠
        {x : E4 | x ∈ H ∧ ∀ v ∈ L', 0 ≤ ⟪v, x⟫_ℝ} := by
  classical
  set i := e.1.1
  set j := e.1.2
  have hij : i ≠ j := Fin.ne_of_lt e.2
  have hH_eq : hp (c i j) = H := (Finset.mem_filter.mp he).2.2
  let L₀ : Finset E4 :=
    ((F i).image (c i) ∪ (F j).image (c j)).filter (fun v => hp v ≠ H)
  have hL0_eq : {x : E4 | x ∈ H ∧ x ∈ Kbar c i ∩ Kbar c j} =
      {x : E4 | x ∈ H ∧ ∀ v ∈ L₀, 0 ≤ ⟪v, x⟫_ℝ} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    refine ⟨fun ⟨hxH, hxi, hxj⟩ => ⟨hxH, fun v hvL => ?_⟩, fun ⟨hxH, hxL⟩ => ⟨hxH, ?_, ?_⟩⟩
    · have hv_mem := (Finset.mem_filter.mp hvL).1
      rcases Finset.mem_union.mp hv_mem with hv_i | hv_j
      · rw [Finset.mem_image] at hv_i; obtain ⟨a, ha, rfl⟩ := hv_i
        exact hxi a (Finset.mem_erase.mp (hF_sub i ha)).1
      · rw [Finset.mem_image] at hv_j; obtain ⟨b, hb, rfl⟩ := hv_j
        exact hxj b (Finset.mem_erase.mp (hF_sub j hb)).1
    · rw [hF_eq i]
      intro a ha
      by_cases hH_a : hp (c i a) = H
      · have h0 : ⟪c i a, x⟫_ℝ = 0 := (mem_hp_iff _ _).mp (hH_a.symm ▸ hxH)
        exact h0.ge
      · exact hxL (c i a) (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha), hH_a⟩)
    · rw [hF_eq j]
      intro b hb
      by_cases hH_b : hp (c j b) = H
      · have h0 : ⟪c j b, x⟫_ℝ = 0 := (mem_hp_iff _ _).mp (hH_b.symm ▸ hxH)
        exact h0.ge
      · exact hxL (c j b) (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), hH_b⟩)
  let Cand := L₀.powerset.filter fun S =>
    {x : E4 | x ∈ H ∧ x ∈ Kbar c i ∩ Kbar c j} = {x : E4 | x ∈ H ∧ ∀ v ∈ S, 0 ≤ ⟪v, x⟫_ℝ}
  have hmem : L₀ ∈ Cand := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hL0_eq⟩
  obtain ⟨L, hLC, hLmin⟩ := Finset.exists_min_image Cand Finset.card ⟨_, hmem⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hLC
  refine ⟨L, hLC.1, hLC.2, fun L' hL' hEq => ?_⟩
  have hL'C : L' ∈ Cand := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hL'.subset.trans hLC.1), hEq⟩
  have hlt := Finset.card_lt_card hL'
  have hle := hLmin L' hL'C
  omega

private lemma minimal_L_distinct_hps {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {H : Submodule ℝ E4} {e : Pairs6} (he : e ∈ wallPairsAt c H)
    {L : Finset E4}
    (hL_sub : L ⊆ ((F e.1.1).image (c e.1.1) ∪ (F e.1.2).image (c e.1.2)).filter (fun v => hp v ≠ H))
    (hL_eq : {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} =
      {x : E4 | x ∈ H ∧ ∀ v ∈ L, 0 ≤ ⟪v, x⟫_ℝ})
    (hL_min : ∀ L' ⊂ L, {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} ≠
      {x : E4 | x ∈ H ∧ ∀ v ∈ L', 0 ≤ ⟪v, x⟫_ℝ})
    {v₁ v₂ : E4} (hv₁ : v₁ ∈ L) (hv₂ : v₂ ∈ L) (hne : v₁ ≠ v₂) :
    H ⊓ hp v₁ ≠ H ⊓ hp v₂ := by
  classical
  set i := e.1.1
  set j := e.1.2
  have hij : i ≠ j := Fin.ne_of_lt e.2
  have he_filt := Finset.mem_filter.mp he
  have hH_eq : hp (c i j) = H := he_filt.2.2
  have hH_fin : Module.finrank ℝ H = 3 := hH_eq ▸ finrank_hp (hc_ne i j hij)
  obtain ⟨p₀, hp₀H, r₀, hr₀_pos, hr₀⟩ := he_filt.2.1.2
  rw [hH_eq] at hp₀H hr₀
  have hp₀_pos : ∀ w ∈ L, 0 < ⟪w, p₀⟫_ℝ := by
    intro w hwL
    have hw_filt := Finset.mem_filter.mp (hL_sub hwL)
    obtain ⟨hw0, _⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hw_filt.1
    have hge : 0 ≤ ⟪w, p₀⟫_ℝ := by
      have hm : p₀ ∈ {x : E4 | x ∈ H ∧ x ∈ Kbar c i ∩ Kbar c j} :=
        ⟨hp₀H, hr₀ p₀ (Metric.mem_ball_self hr₀_pos) hp₀H⟩
      rw [hL_eq] at hm
      exact hm.2 w hwL
    by_contra hle
    have hw_p0 : ⟪w, p₀⟫_ℝ = 0 := le_antisymm (not_lt.mp hle) hge
    obtain ⟨z, hzH, hz_not⟩ := exists_vector_in_diff_hp hH_fin (finrank_hp hw0) hw_filt.2.symm
    have hzw : ⟪w, z⟫_ℝ ≠ 0 := fun h0 => hz_not ((mem_hp_iff _ _).mpr h0)
    let ε := ((r₀ / 2) / (‖z‖ + 1)) * (if 0 < ⟪w, z⟫_ℝ then (-1 : ℝ) else 1)
    have hε_abs : |ε| = (r₀ / 2) / (‖z‖ + 1) := by
      dsimp [ε]; rw [abs_mul, abs_of_pos (by positivity)]; split_ifs <;> simp
    have hz_ball : p₀ + ε • z ∈ Metric.ball p₀ r₀ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hε_abs]
      have hden : 0 < ‖z‖ + 1 := by positivity
      calc (r₀ / 2) / (‖z‖ + 1) * ‖z‖ = (r₀ / 2) * (‖z‖ / (‖z‖ + 1)) := by ring
        _ < (r₀ / 2) * 1 := by refine mul_lt_mul_of_pos_left ?_ (half_pos hr₀_pos); rw [div_lt_one hden]; linarith
        _ < r₀ := by linarith
    have hpz_in := hr₀ (p₀ + ε • z) hz_ball (H.add_mem hp₀H (H.smul_mem ε hzH))
    have hpz_pos : 0 ≤ ⟪w, p₀ + ε • z⟫_ℝ := by
      have hm : p₀ + ε • z ∈ {x : E4 | x ∈ H ∧ x ∈ Kbar c i ∩ Kbar c j} :=
        ⟨H.add_mem hp₀H (H.smul_mem ε hzH), hpz_in⟩
      rw [hL_eq] at hm
      exact hm.2 w hwL
    rw [inner_add_right, real_inner_smul_right, hw_p0, zero_add] at hpz_pos
    dsimp [ε] at hpz_pos
    split_ifs at hpz_pos with hpos
    · have : 0 < (r₀ / 2) / (‖z‖ + 1) := by positivity
      nlinarith
    · have hlt0 : ⟪w, z⟫_ℝ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzw
      have : 0 < (r₀ / 2) / (‖z‖ + 1) := by positivity
      nlinarith
  intro hinf_eq
  have hv1_filt := Finset.mem_filter.mp (hL_sub hv₁)
  have hv2_filt := Finset.mem_filter.mp (hL_sub hv₂)
  obtain ⟨hv10, _⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hv1_filt.1
  obtain ⟨hv20, _⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hv2_filt.1
  obtain ⟨z₀, hz0H, hz0_not⟩ := exists_vector_in_diff_hp hH_fin (finrank_hp hv10) hv1_filt.2.symm
  have hz0_v1 : ⟪v₁, z₀⟫_ℝ ≠ 0 := fun h0 => hz0_not ((mem_hp_iff _ _).mpr h0)
  let α : ℝ := ⟪v₂, z₀⟫_ℝ / ⟪v₁, z₀⟫_ℝ
  have hprop : ∀ x ∈ H, ⟪v₂, x⟫_ℝ = α * ⟪v₁, x⟫_ℝ := fun x hxH => by
    let y : E4 := x - (⟪v₁, x⟫_ℝ / ⟪v₁, z₀⟫_ℝ) • z₀
    have hyH : y ∈ H := H.sub_mem hxH (H.smul_mem _ hz0H)
    have hy_v1 : y ∈ hp v₁ := by
      rw [mem_hp_iff]
      dsimp [y]
      rw [inner_sub_right, real_inner_smul_right]
      field_simp [hz0_v1]
      ring
    have hy_v2 : y ∈ hp v₂ := by
      have : y ∈ H ⊓ hp v₁ := ⟨hyH, hy_v1⟩
      rw [hinf_eq] at this
      exact this.2
    have hy_0 : ⟪v₂, y⟫_ℝ = 0 := (mem_hp_iff _ _).mp hy_v2
    dsimp [y] at hy_0
    rw [inner_sub_right, real_inner_smul_right] at hy_0
    dsimp [α]
    have hmul : ⟪v₂, x⟫_ℝ = (⟪v₁, x⟫_ℝ / ⟪v₁, z₀⟫_ℝ) * ⟪v₂, z₀⟫_ℝ := sub_eq_zero.mp hy_0
    rw [hmul]; ring
  have hα_pos : 0 < α := by
    have h1 := hp₀_pos v₁ hv₁
    have h2 := hp₀_pos v₂ hv₂
    have heq := hprop p₀ hp₀H
    rw [heq] at h2
    exact (mul_pos_iff_of_pos_right h1).mp h2
  apply hL_min (L.erase v₂) (Finset.erase_ssubset hv₂)
  ext x
  rw [hL_eq]
  simp only [Set.mem_ofPred_eq, Finset.mem_erase]
  refine ⟨fun ⟨hxH, hxw⟩ => ⟨hxH, fun w hw => hxw w hw.2⟩, fun ⟨hxH, hxw⟩ => ⟨hxH, fun w hwL => ?_⟩⟩
  by_cases hw2 : w = v₂
  · subst hw2
    rw [hprop x hxH]
    exact mul_nonneg hα_pos.le (hxw v₁ ⟨hne, hv₁⟩)
  · exact hxw w ⟨hw2, hwL⟩

private lemma pairsAvoiding_one_card (i : Fin 6) :
    (Finset.univ.filter fun e : Pairs6 => e.1.1 ≠ i ∧ e.1.2 ≠ i).card = 10 := by
  fin_cases i <;> decide

private lemma pairsAvoiding_two_card (i j : Fin 6) (hij : i ≠ j) :
    (Finset.univ.filter fun e : Pairs6 => e.1.1 ≠ i ∧ e.1.1 ≠ j ∧ e.1.2 ≠ i ∧ e.1.2 ≠ j).card = 6 := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (hij rfl) | decide

private lemma exists_mem_ball_avoiding_subspaces (K : Submodule ℝ E4)
    (Bad : Finset (Submodule ℝ E4)) (hnot : ∀ H ∈ Bad, ¬ K ≤ H)
    {p₀ : E4} (hp₀ : p₀ ∈ K) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ K, y ∈ Metric.ball p₀ r ∧ ∀ H ∈ Bad, y ∉ H := by
  classical
  induction Bad using Finset.induction_on with
  | empty =>
    exact ⟨p₀, hp₀, Metric.mem_ball_self hr, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | insert H Bad' hHB ih =>
    obtain ⟨p, hpK, hp_ball, hpBad⟩ := ih (fun H' h' => hnot H' (Finset.mem_insert_of_mem h'))
    by_cases hpH : p ∈ H
    · obtain ⟨v, hvK, hvH⟩ : ∃ v : E4, v ∈ K ∧ v ∉ H := by
        by_contra hall
        push Not at hall
        exact hnot H (Finset.mem_insert_self H Bad') fun x hx => hall x hx
      have hrem : 0 < r - dist p p₀ := sub_pos.mpr (Metric.mem_ball.mp hp_ball)
      let δ : ℝ := (r - dist p p₀) / ((‖v‖ + 1) * ((Bad'.card : ℝ) + 2))
      have hδ : 0 < δ := by positivity
      let t_fn : Fin (Bad'.card + 1) → ℝ := fun k => ((k.1 : ℝ) + 1) * δ
      have ht_pos : ∀ k, 0 < t_fn k := fun k => by positivity
      let pt : Fin (Bad'.card + 1) → E4 := fun k => p + t_fn k • v
      let hitSet : Finset (Fin (Bad'.card + 1)) :=
        Bad'.biUnion fun H' => Finset.univ.filter fun k : Fin (Bad'.card + 1) => pt k ∈ H'
      have hhit_one : ∀ H' ∈ Bad',
          (Finset.univ.filter fun k : Fin (Bad'.card + 1) => pt k ∈ H').card ≤ 1 := by
        intro H' hH'
        refine Finset.card_le_one.mpr fun k₁ hk₁ k₂ hk₂ => ?_
        have hm1 : pt k₁ ∈ H' := (Finset.mem_filter.mp hk₁).2
        have hm2 : pt k₂ ∈ H' := (Finset.mem_filter.mp hk₂).2
        by_contra hne
        have hsub : (t_fn k₁ - t_fn k₂) • v ∈ H' := by
          have := H'.sub_mem hm1 hm2
          simpa [pt, sub_smul] using this
        have ht_ne : t_fn k₁ - t_fn k₂ ≠ 0 := by
          intro h0
          have hk_eq : (k₁.1 : ℝ) = (k₂.1 : ℝ) := by
            dsimp [t_fn] at h0
            nlinarith
          exact hne (Fin.ext (Nat.cast_injective hk_eq))
        have hv_in : v ∈ H' := by simpa [ht_ne] using H'.smul_mem (t_fn k₁ - t_fn k₂)⁻¹ hsub
        have hp_in : p ∈ H' := by
          have := H'.sub_mem hm1 (H'.smul_mem (t_fn k₁) hv_in)
          simpa [pt] using this
        exact hpBad H' hH' hp_in
      have hhit_lt : hitSet.card < (Finset.univ : Finset (Fin (Bad'.card + 1))).card := by
        calc hitSet.card
            ≤ ∑ H' ∈ Bad', (Finset.univ.filter fun k : Fin (Bad'.card + 1) => pt k ∈ H').card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _H' ∈ Bad', 1 := Finset.sum_le_sum hhit_one
          _ = Bad'.card := by simp
          _ < (Finset.univ : Finset (Fin (Bad'.card + 1))).card := by simp
      have hex_k : ∃ k : Fin (Bad'.card + 1), k ∉ hitSet := by
        by_contra hall
        push Not at hall
        have hsub : Finset.univ ⊆ hitSet := fun k _ => hall k
        have := Finset.card_le_card hsub
        omega
      obtain ⟨k, hk_not⟩ := hex_k
      refine ⟨pt k, K.add_mem hpK (K.smul_mem _ hvK), ?_, fun H'' hH'' => ?_⟩
      · rw [Metric.mem_ball]
        have hdist_pt : dist (pt k) p ≤ t_fn k * ‖v‖ := by
          rw [dist_eq_norm]
          simp only [pt, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (ht_pos k).le]
          exact le_rfl
        have hk_bound : ((k.1 : ℝ) + 1) ≤ (Bad'.card : ℝ) + 1 := by
          have : (k.1 : ℝ) + 1 ≤ ((Bad'.card + 1 : ℕ) : ℝ) := by exact_mod_cast k.2
          simpa using this
        have hnv : ‖v‖ < ‖v‖ + 1 := lt_add_one _
        have hbn : (Bad'.card : ℝ) + 1 < (Bad'.card : ℝ) + 2 := by linarith
        have hstep : t_fn k * ‖v‖ < r - dist p p₀ := by
          calc t_fn k * ‖v‖
              = (((k.1 : ℝ) + 1) * ‖v‖) * δ := by dsimp [t_fn]; ring
            _ < (((Bad'.card : ℝ) + 2) * (‖v‖ + 1)) * δ := by
                refine mul_lt_mul_of_pos_right ?_ hδ
                have h1 : 0 ≤ (k.1 : ℝ) + 1 := by positivity
                have h2 : 0 ≤ ‖v‖ := norm_nonneg _
                exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hk_bound h2)
                  (mul_lt_mul' hbn.le hnv h2 (by positivity))
            _ = r - dist p p₀ := by
                dsimp [δ]
                have hden : ((‖v‖ + 1) * ((Bad'.card : ℝ) + 2)) ≠ 0 := by positivity
                field_simp [hden]
        calc dist (pt k) p₀ ≤ dist (pt k) p + dist p p₀ := dist_triangle _ _ _
          _ < r := by linarith [hdist_pt, hstep]
      · rcases Finset.mem_insert.mp hH'' with rfl | hH''B
        · intro hmem
          have hsub : t_fn k • v ∈ H'' := by
            have := H''.sub_mem hmem hpH
            simpa [pt] using this
          exact hvH (by simpa [(ht_pos k).ne'] using H''.smul_mem (t_fn k)⁻¹ hsub)
        · intro hmem
          exact hk_not (Finset.mem_biUnion.mpr ⟨H'', hH''B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩)
    · refine ⟨p, hpK, hp_ball, fun H'' hH'' => ?_⟩
      rcases Finset.mem_insert.mp hH'' with rfl | hH''B
      · exact hpH
      · exact hpBad H'' hH''B

private lemma wall_hyperplane_avoiding_of_subset {c : Fin 6 → Fin 6 → E4}
    (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    {Bad : Finset (Submodule ℝ E4)}
    (hBad : ∀ H' ∈ Bad, Module.finrank ℝ H' = 3)
    {i : Fin 6} (hi_facets : ∀ a ∈ F i, hp (c i a) ∈ Bad)
    {k : Fin 6} (hk : k ≠ i) (hw : IsWallPair c i k) :
    hp (c i k) ∈ Bad := by
  by_contra hnot
  obtain ⟨p, hpH, r, hr_pos, hr⟩ := hw.2
  have hfin : Module.finrank ℝ (hp (c i k)) = 3 := finrank_hp (hc_ne i k hk.symm)
  have hnot_sub : ∀ H' ∈ Bad, ¬ hp (c i k) ≤ H' := fun H' hH' hle =>
    hnot ((hp_eq_of_le hfin (hBad H' hH') hle) ▸ hH')
  obtain ⟨y, hy_hp, hy_ball, hy_Bad⟩ :=
    exists_mem_ball_avoiding_subspaces (hp (c i k)) Bad hnot_sub hpH hr_pos
  have hy_K : y ∈ Kbar c i := (hr y hy_ball hy_hp).1
  have hy_pos : ∀ a ∈ F i, 0 < ⟪c i a, y⟫_ℝ := fun a ha => by
    have hge : 0 ≤ ⟪c i a, y⟫_ℝ := (hF_eq i ▸ hy_K) a ha
    have hne0 : ⟪c i a, y⟫_ℝ ≠ 0 := fun h0 =>
      hy_Bad (hp (c i a)) (hi_facets a ha) ((mem_hp_iff _ _).mpr h0)
    exact lt_of_le_of_ne hge hne0.symm
  have hy_open : y ∈ Kopen c i := by
    refine (mem_interior_Kbar_iff hc_ne i y).mp ?_
    refine interior_maximal ?_ (isOpen_biInter_finset (s := F i)
      (f := fun a : Fin 6 => {z : E4 | 0 < ⟪c i a, z⟫_ℝ}) fun a _ =>
        isOpen_lt continuous_const (continuous_const.inner continuous_id)) ?_
    · intro z hz
      rw [hF_eq i]
      intro a ha
      exact (Set.mem_iInter₂.mp hz a ha).le
    · rw [Set.mem_iInter₂]
      exact hy_pos
  have hpos_ik : 0 < ⟪c i k, y⟫_ℝ := hy_open k hk
  have h0_ik : ⟪c i k, y⟫_ℝ = 0 := (mem_hp_iff _ _).mp hy_hp
  exact hpos_ik.ne' h0_ik

private lemma card_wallHyperplanes_le_add_of_avoiding {c : Fin 6 → Fin 6 → E4}
    (Bad : Finset (Submodule ℝ E4)) (S_avoid : Finset Pairs6)
    (hcover : ∀ e : Pairs6, IsWallPair c e.1.1 e.1.2 →
      hp (c e.1.1 e.1.2) ∈ Bad ∨ e ∈ S_avoid) :
    (wallHyperplanes c).card ≤ Bad.card + S_avoid.card := by
  classical
  have hsub : wallHyperplanes c ⊆ Bad ∪ S_avoid.image (fun e : Pairs6 => hp (c e.1.1 e.1.2)) := by
    intro H' hH'
    rw [wallHyperplanes, Finset.mem_image] at hH'
    obtain ⟨e, he, rfl⟩ := hH'
    rw [Finset.mem_filter] at he
    rcases hcover e he.2 with hin | hS
    · exact Finset.mem_union_left _ hin
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hS)
  calc (wallHyperplanes c).card
      ≤ (Bad ∪ S_avoid.image (fun e : Pairs6 => hp (c e.1.1 e.1.2))).card :=
        Finset.card_le_card hsub
    _ ≤ Bad.card + (S_avoid.image (fun e : Pairs6 => hp (c e.1.1 e.1.2))).card :=
        Finset.card_union_le _ _
    _ ≤ Bad.card + S_avoid.card := Nat.add_le_add_left Finset.card_image_le _

private lemma card_wallHyperplanes_le_of_kill_one {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j)
    (Bad : Finset (Submodule ℝ E4)) (i : Fin 6)
    (hkill : ∀ k ≠ i, IsWallPair c i k → hp (c i k) ∈ Bad) :
    (wallHyperplanes c).card ≤ Bad.card + 10 := by
  classical
  let S := Finset.univ.filter fun e : Pairs6 => e.1.1 ≠ i ∧ e.1.2 ≠ i
  have hcard : S.card = 10 := pairsAvoiding_one_card i
  rw [← hcard]
  refine card_wallHyperplanes_le_add_of_avoiding Bad S fun e hw => ?_
  by_cases h1 : e.1.1 = i
  · left
    have hne : e.1.2 ≠ i := by rw [← h1]; exact (Fin.ne_of_lt e.2).symm
    have hw' : IsWallPair c i e.1.2 := h1 ▸ hw
    have hmem := hkill e.1.2 hne hw'
    rw [← h1] at hmem
    exact hmem
  · by_cases h2 : e.1.2 = i
    · left
      have hne : e.1.1 ≠ i := by rw [← h2]; exact Fin.ne_of_lt e.2
      have hw' : IsWallPair c i e.1.1 := h2 ▸ isWallPair_symm hc_sym hw
      have hmem := hkill e.1.1 hne hw'
      rw [h2, hc_sym i e.1.1, hp_neg]
      exact hmem
    · right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩

private lemma card_wallHyperplanes_le_of_kill_two {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j)
    (Bad : Finset (Submodule ℝ E4)) {i j : Fin 6} (hij : i ≠ j)
    (hkilli : ∀ k ≠ i, IsWallPair c i k → hp (c i k) ∈ Bad)
    (hkillj : ∀ k ≠ j, IsWallPair c j k → hp (c j k) ∈ Bad) :
    (wallHyperplanes c).card ≤ Bad.card + 6 := by
  classical
  let S := Finset.univ.filter fun e : Pairs6 =>
    e.1.1 ≠ i ∧ e.1.1 ≠ j ∧ e.1.2 ≠ i ∧ e.1.2 ≠ j
  have hcard : S.card = 6 := pairsAvoiding_two_card i j hij
  rw [← hcard]
  refine card_wallHyperplanes_le_add_of_avoiding Bad S fun e hw => ?_
  by_cases h1i : e.1.1 = i
  · left
    have hne : e.1.2 ≠ i := by rw [← h1i]; exact (Fin.ne_of_lt e.2).symm
    have hmem := hkilli e.1.2 hne (h1i ▸ hw)
    rw [← h1i] at hmem; exact hmem
  · by_cases h1j : e.1.1 = j
    · left
      have hne : e.1.2 ≠ j := by rw [← h1j]; exact (Fin.ne_of_lt e.2).symm
      have hmem := hkillj e.1.2 hne (h1j ▸ hw)
      rw [← h1j] at hmem; exact hmem
    · by_cases h2i : e.1.2 = i
      · left
        have hne : e.1.1 ≠ i := by rw [← h2i]; exact Fin.ne_of_lt e.2
        have hmem := hkilli e.1.1 hne (h2i ▸ isWallPair_symm hc_sym hw)
        rw [h2i, hc_sym i e.1.1, hp_neg]; exact hmem
      · by_cases h2j : e.1.2 = j
        · left
          have hne : e.1.1 ≠ j := by rw [← h2j]; exact Fin.ne_of_lt e.2
          have hmem := hkillj e.1.1 hne (h2j ▸ isWallPair_symm hc_sym hw)
          rw [h2j, hc_sym j e.1.1, hp_neg]; exact hmem
        · right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1i, h1j, h2i, h2j⟩

private lemma L_empty_card_le_7 {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    {H : Submodule ℝ E4} (hH : H ∈ wallHyperplanes c)
    {e : Pairs6} (_he : e ∈ wallPairsAt c H)
    (hL_eq : {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} =
      {x : E4 | x ∈ H ∧ ∀ v ∈ (∅ : Finset E4), 0 ≤ ⟪v, x⟫_ℝ}) :
    (wallHyperplanes c).card ≤ 7 := by
  classical
  set i := e.1.1
  set j := e.1.2
  have hij : i ≠ j := Fin.ne_of_lt e.2
  have hH_fin : Module.finrank ℝ H = 3 := wallHyperplanes_finrank hc_ne hH
  have hH_sub_K : ∀ x ∈ H, x ∈ Kbar c i ∧ x ∈ Kbar c j := fun x hxH => by
    have hm : x ∈ {y : E4 | y ∈ H ∧ ∀ v ∈ (∅ : Finset E4), 0 ≤ ⟪v, y⟫_ℝ} :=
      ⟨hxH, fun _ hv => False.elim (Finset.notMem_empty _ hv)⟩
    rw [← hL_eq] at hm
    exact hm.2
  have hi_facets : ∀ a ∈ F i, hp (c i a) ∈ ({H} : Finset (Submodule ℝ E4)) := fun a ha => by
    have hai : a ≠ i := (Finset.mem_erase.mp (hF_sub i ha)).1
    have hfa_fin : Module.finrank ℝ (hp (c i a)) = 3 := finrank_hp (hc_ne i a hai.symm)
    rw [Finset.mem_singleton]
    by_contra hne
    obtain ⟨x, hxH, hxnot⟩ := exists_vector_in_diff_hp hH_fin hfa_fin (Ne.symm hne)
    have hpos : 0 ≤ ⟪c i a, x⟫_ℝ := (hF_eq i ▸ (hH_sub_K x hxH).1) a ha
    have hneg : 0 ≤ ⟪c i a, -x⟫_ℝ := (hF_eq i ▸ (hH_sub_K (-x) (H.neg_mem hxH)).1) a ha
    rw [inner_neg_right] at hneg
    exact hxnot ((mem_hp_iff _ _).mpr (by linarith))
  have hj_facets : ∀ b ∈ F j, hp (c j b) ∈ ({H} : Finset (Submodule ℝ E4)) := fun b hb => by
    have hbj : b ≠ j := (Finset.mem_erase.mp (hF_sub j hb)).1
    have hfb_fin : Module.finrank ℝ (hp (c j b)) = 3 := finrank_hp (hc_ne j b hbj.symm)
    rw [Finset.mem_singleton]
    by_contra hne
    obtain ⟨x, hxH, hxnot⟩ := exists_vector_in_diff_hp hH_fin hfb_fin (Ne.symm hne)
    have hpos : 0 ≤ ⟪c j b, x⟫_ℝ := (hF_eq j ▸ (hH_sub_K x hxH).2) b hb
    have hneg : 0 ≤ ⟪c j b, -x⟫_ℝ := (hF_eq j ▸ (hH_sub_K (-x) (H.neg_mem hxH)).2) b hb
    rw [inner_neg_right] at hneg
    exact hxnot ((mem_hp_iff _ _).mpr (by linarith))
  have hBad : ∀ H' ∈ ({H} : Finset (Submodule ℝ E4)), Module.finrank ℝ H' = 3 := by
    intro H' hH'
    rw [Finset.mem_singleton.mp hH']
    exact hH_fin
  have hkilli : ∀ k ≠ i, IsWallPair c i k → hp (c i k) ∈ ({H} : Finset _) :=
    fun k hk hw => wall_hyperplane_avoiding_of_subset hc_ne hF_eq hBad hi_facets hk hw
  have hkillj : ∀ k ≠ j, IsWallPair c j k → hp (c j k) ∈ ({H} : Finset _) :=
    fun k hk hw => wall_hyperplane_avoiding_of_subset hc_ne hF_eq hBad hj_facets hk hw
  have hle := card_wallHyperplanes_le_of_kill_two hc_sym {H} hij hkilli hkillj
  simp only [Finset.card_singleton] at hle
  omega

private lemma L_singleton_no_tri_card_le_8 {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {H : Submodule ℝ E4} (hH : H ∈ wallHyperplanes c)
    (hno_tri : ¬ hasCoplanarTriple (wallHyperplanes c) H)
    {e : Pairs6}
    {v : E4}
    (hv_sub : {v} ⊆ ((F e.1.1).image (c e.1.1) ∪ (F e.1.2).image (c e.1.2)).filter (fun w => hp w ≠ H))
    (hL_eq : {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} =
      {x : E4 | x ∈ H ∧ ∀ w ∈ ({v} : Finset E4), 0 ≤ ⟪w, x⟫_ℝ}) :
    (wallHyperplanes c).card ≤ 8 := by
  classical
  set i := e.1.1
  set j := e.1.2
  have hij : i ≠ j := Fin.ne_of_lt e.2
  have hH_fin : Module.finrank ℝ H = 3 := wallHyperplanes_finrank hc_ne hH
  have hv_mem := Finset.mem_filter.mp (hv_sub (Finset.mem_singleton_self v))
  have hv_ne_H : hp v ≠ H := hv_mem.2
  obtain ⟨hv_ne0, hHv_mem⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hv_mem.1
  have hHv_fin : Module.finrank ℝ (hp v) = 3 := finrank_hp hv_ne0
  let H₁ := hp v
  have hR_sub_K : ∀ x ∈ H ⊓ H₁, x ∈ Kbar c i ∧ x ∈ Kbar c j := fun x hx => by
    have hm : x ∈ {y : E4 | y ∈ H ∧ ∀ w ∈ ({v} : Finset E4), 0 ≤ ⟪w, y⟫_ℝ} := by
      refine ⟨hx.1, fun w hw => ?_⟩
      rw [Finset.mem_singleton.mp hw]
      exact ((mem_hp_iff v x).mp hx.2).ge
    rw [← hL_eq] at hm
    exact hm.2
  let Bad : Finset (Submodule ℝ E4) := {H, H₁}
  have hi_facets : ∀ a ∈ F i, hp (c i a) ∈ Bad := fun a ha => by
    have hai : a ≠ i := (Finset.mem_erase.mp (hF_sub i ha)).1
    obtain ⟨k, hki, hw, hk_eq⟩ :=
      baire_facet_wall hc_sym hc_ne hK_nonempty hK_cover (hF_sub i) (hF_eq i) (hF_min i) ha
    have hmemW : hp (c i a) ∈ wallHyperplanes c := by
      rw [hk_eq]; exact (wallPair_mem_wallHyperplanes hc_sym hki.symm hw).2
    have hinf_le : H ⊓ H₁ ≤ hp (c i a) := fun x hx => by
      have hpos : 0 ≤ ⟪c i a, x⟫_ℝ := (hF_eq i ▸ (hR_sub_K x hx).1) a ha
      have hneg : 0 ≤ ⟪c i a, -x⟫_ℝ := (hF_eq i ▸ (hR_sub_K (-x) ((H ⊓ H₁).neg_mem hx)).1) a ha
      rw [inner_neg_right] at hneg
      exact (mem_hp_iff _ _).mpr (by linarith)
    by_contra hnot
    have hne1 : hp (c i a) ≠ H := fun h => hnot (Finset.mem_insert.mpr (Or.inl h))
    have hne2 : hp (c i a) ≠ H₁ := fun h =>
      hnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    exact hno_tri ⟨H₁, hHv_mem, hp (c i a), hmemW, hv_ne_H.symm, hne2.symm, hne1.symm, hinf_le⟩
  have hj_facets : ∀ b ∈ F j, hp (c j b) ∈ Bad := fun b hb => by
    have hbj : b ≠ j := (Finset.mem_erase.mp (hF_sub j hb)).1
    obtain ⟨k, hkj, hw, hk_eq⟩ :=
      baire_facet_wall hc_sym hc_ne hK_nonempty hK_cover (hF_sub j) (hF_eq j) (hF_min j) hb
    have hmemW : hp (c j b) ∈ wallHyperplanes c := by
      rw [hk_eq]; exact (wallPair_mem_wallHyperplanes hc_sym hkj.symm hw).2
    have hinf_le : H ⊓ H₁ ≤ hp (c j b) := fun x hx => by
      have hpos : 0 ≤ ⟪c j b, x⟫_ℝ := (hF_eq j ▸ (hR_sub_K x hx).2) b hb
      have hneg : 0 ≤ ⟪c j b, -x⟫_ℝ := (hF_eq j ▸ (hR_sub_K (-x) ((H ⊓ H₁).neg_mem hx)).2) b hb
      rw [inner_neg_right] at hneg
      exact (mem_hp_iff _ _).mpr (by linarith)
    by_contra hnot
    have hne1 : hp (c j b) ≠ H := fun h => hnot (Finset.mem_insert.mpr (Or.inl h))
    have hne2 : hp (c j b) ≠ H₁ := fun h =>
      hnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    exact hno_tri ⟨H₁, hHv_mem, hp (c j b), hmemW, hv_ne_H.symm, hne2.symm, hne1.symm, hinf_le⟩
  have hBad : ∀ H' ∈ Bad, Module.finrank ℝ H' = 3 := by
    intro H' hH'
    rcases Finset.mem_insert.mp hH' with rfl | hH1
    · exact hH_fin
    · rw [Finset.mem_singleton.mp hH1]; exact hHv_fin
  have hkilli : ∀ k ≠ i, IsWallPair c i k → hp (c i k) ∈ Bad :=
    fun k hk hw => wall_hyperplane_avoiding_of_subset hc_ne hF_eq hBad hi_facets hk hw
  have hkillj : ∀ k ≠ j, IsWallPair c j k → hp (c j k) ∈ Bad :=
    fun k hk hw => wall_hyperplane_avoiding_of_subset hc_ne hF_eq hBad hj_facets hk hw
  have hle := card_wallHyperplanes_le_of_kill_two hc_sym Bad hij hkilli hkillj
  have hBad_card : Bad.card ≤ 2 := Finset.card_le_two
  omega

private lemma exists_pos_comb_of_three {w₁ w₂ w₃ u : E4}
    (h1 : 0 < ⟪w₁, u⟫_ℝ) (h2 : 0 < ⟪w₂, u⟫_ℝ) (h3 : 0 < ⟪w₃, u⟫_ℝ)
    (hne12 : hp w₁ ≠ hp w₂) (hne23 : hp w₂ ≠ hp w₃) (hne13 : hp w₁ ≠ hp w₃)
    (α₁ α₂ α₃ : ℝ) (hnz : α₁ ≠ 0 ∨ α₂ ≠ 0 ∨ α₃ ≠ 0)
    (hlin : α₁ • w₁ + α₂ • w₂ + α₃ • w₃ = 0) :
    (∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ w₁ = β₁ • w₂ + β₂ • w₃) ∨
    (∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ w₂ = β₁ • w₁ + β₂ • w₃) ∨
    (∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ w₃ = β₁ • w₁ + β₂ • w₂) := by
  have hw1_ne : w₁ ≠ 0 := fun h => by simp [h] at h1
  have hw2_ne : w₂ ≠ 0 := fun h => by simp [h] at h2
  have hw3_ne : w₃ ≠ 0 := fun h => by simp [h] at h3
  have ha3 : α₃ ≠ 0 := by
    intro h0
    subst h0
    rw [zero_smul, add_zero] at hlin
    have hnz12 : α₁ ≠ 0 ∨ α₂ ≠ 0 := by rcases hnz with h | h | h; exact Or.inl h; exact Or.inr h; exact False.elim (h rfl)
    have ha1 : α₁ ≠ 0 := by
      intro ha10
      subst ha10
      rw [zero_smul, zero_add] at hlin
      have ha2 : α₂ ≠ 0 := hnz12.resolve_left (not_not.mpr rfl)
      exact hw2_ne ((smul_eq_zero.mp hlin).resolve_left ha2)
    have ha2 : α₂ ≠ 0 := by
      intro ha20
      subst ha20
      rw [zero_smul, add_zero] at hlin
      exact hw1_ne ((smul_eq_zero.mp hlin).resolve_left ha1)
    have hcoef : (-α₂ / α₁) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha2) ha1
    have hsm : w₁ = (-α₂ / α₁) • w₂ := by
      have h1 := eq_neg_of_add_eq_zero_left hlin
      have h2 := congrArg (α₁⁻¹ • ·) h1
      rw [smul_smul, inv_mul_cancel₀ ha1, one_smul, smul_neg, smul_smul, ← neg_smul] at h2
      rw [h2]; congr 1; ring
    exact hne12 (by rw [hsm, hp_smul hcoef])
  have ha1 : α₁ ≠ 0 := by
    intro h0
    subst h0
    rw [zero_smul, zero_add] at hlin
    have ha2 : α₂ ≠ 0 := by
      intro ha20
      subst ha20
      rw [zero_smul, zero_add] at hlin
      exact hw3_ne ((smul_eq_zero.mp hlin).resolve_left ha3)
    have hcoef : (-α₃ / α₂) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha3) ha2
    have hsm : w₂ = (-α₃ / α₂) • w₃ := by
      have h1 := eq_neg_of_add_eq_zero_left hlin
      have h2 := congrArg (α₂⁻¹ • ·) h1
      rw [smul_smul, inv_mul_cancel₀ ha2, one_smul, smul_neg, smul_smul, ← neg_smul] at h2
      rw [h2]; congr 1; ring
    exact hne23 (by rw [hsm, hp_smul hcoef])
  have ha2 : α₂ ≠ 0 := by
    intro h0
    subst h0
    rw [zero_smul, add_zero] at hlin
    have hcoef : (-α₃ / α₁) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha3) ha1
    have hsm : w₁ = (-α₃ / α₁) • w₃ := by
      have h1 := eq_neg_of_add_eq_zero_left hlin
      have h2 := congrArg (α₁⁻¹ • ·) h1
      rw [smul_smul, inv_mul_cancel₀ ha1, one_smul, smul_neg, smul_smul, ← neg_smul] at h2
      rw [h2]; congr 1; ring
    exact hne13 (by rw [hsm, hp_smul hcoef])
  have hdot : α₁ * ⟪w₁, u⟫_ℝ + α₂ * ⟪w₂, u⟫_ℝ + α₃ * ⟪w₃, u⟫_ℝ = 0 := by
    have := congrArg (fun v : E4 => ⟪v, u⟫_ℝ) hlin
    simpa [inner_add_left, real_inner_smul_left, inner_zero_left] using this
  have solve1 : ∀ (_ : (0 < -α₂ / α₁) ∧ (0 < -α₃ / α₁)),
      ∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ w₁ = β₁ • w₂ + β₂ • w₃ := fun ⟨hb1, hb2⟩ => by
    refine ⟨-α₂ / α₁, -α₃ / α₁, hb1, hb2, ?_⟩
    have hc2 : -(α₁⁻¹ * α₂) = -α₂ / α₁ := by ring
    have hc3 : -(α₁⁻¹ * α₃) = -α₃ / α₁ := by ring
    calc w₁ = w₁ - α₁⁻¹ • (α₁ • w₁ + α₂ • w₂ + α₃ • w₃) := by rw [hlin, smul_zero, sub_zero]
      _ = (-(α₁⁻¹ * α₂)) • w₂ + (-(α₁⁻¹ * α₃)) • w₃ := by
        rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ ha1, one_smul]
        module
      _ = (-α₂ / α₁) • w₂ + (-α₃ / α₁) • w₃ := by rw [hc2, hc3]
  have solve2 : ∀ (_ : (0 < -α₁ / α₂) ∧ (0 < -α₃ / α₂)),
      ∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ w₂ = β₁ • w₁ + β₂ • w₃ := fun ⟨hb1, hb2⟩ => by
    refine ⟨-α₁ / α₂, -α₃ / α₂, hb1, hb2, ?_⟩
    have hc1 : -(α₂⁻¹ * α₁) = -α₁ / α₂ := by ring
    have hc3 : -(α₂⁻¹ * α₃) = -α₃ / α₂ := by ring
    calc w₂ = w₂ - α₂⁻¹ • (α₁ • w₁ + α₂ • w₂ + α₃ • w₃) := by rw [hlin, smul_zero, sub_zero]
      _ = (-(α₂⁻¹ * α₁)) • w₁ + (-(α₂⁻¹ * α₃)) • w₃ := by
        rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ ha2, one_smul]
        module
      _ = (-α₁ / α₂) • w₁ + (-α₃ / α₂) • w₃ := by rw [hc1, hc3]
  have solve3 : ∀ (_ : (0 < -α₁ / α₃) ∧ (0 < -α₂ / α₃)),
      ∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ w₃ = β₁ • w₁ + β₂ • w₂ := fun ⟨hb1, hb2⟩ => by
    refine ⟨-α₁ / α₃, -α₂ / α₃, hb1, hb2, ?_⟩
    have hc1 : -(α₃⁻¹ * α₁) = -α₁ / α₃ := by ring
    have hc2 : -(α₃⁻¹ * α₂) = -α₂ / α₃ := by ring
    calc w₃ = w₃ - α₃⁻¹ • (α₁ • w₁ + α₂ • w₂ + α₃ • w₃) := by rw [hlin, smul_zero, sub_zero]
      _ = (-(α₃⁻¹ * α₁)) • w₁ + (-(α₃⁻¹ * α₂)) • w₂ := by
        rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ ha3, one_smul]
        module
      _ = (-α₁ / α₃) • w₁ + (-α₂ / α₃) • w₂ := by rw [hc1, hc2]
  rcases lt_or_gt_of_ne ha1 with hα1 | hα1 <;>
  rcases lt_or_gt_of_ne ha2 with hα2 | hα2 <;>
  rcases lt_or_gt_of_ne ha3 with hα3 | hα3
  · exfalso; nlinarith
  · right; right; exact solve3 ⟨div_pos (neg_pos.mpr hα1) hα3, div_pos (neg_pos.mpr hα2) hα3⟩
  · right; left; exact solve2 ⟨div_pos (neg_pos.mpr hα1) hα2, div_pos (neg_pos.mpr hα3) hα2⟩
  · left; exact solve1 ⟨div_pos_of_neg_of_neg (neg_neg_of_pos hα2) hα1, div_pos_of_neg_of_neg (neg_neg_of_pos hα3) hα1⟩
  · left; exact solve1 ⟨div_pos (neg_pos.mpr hα2) hα1, div_pos (neg_pos.mpr hα3) hα1⟩
  · right; left; exact solve2 ⟨div_pos_of_neg_of_neg (neg_neg_of_pos hα1) hα2, div_pos_of_neg_of_neg (neg_neg_of_pos hα3) hα2⟩
  · right; right; exact solve3 ⟨div_pos_of_neg_of_neg (neg_neg_of_pos hα1) hα3, div_pos_of_neg_of_neg (neg_neg_of_pos hα2) hα3⟩
  · exfalso; nlinarith

private lemma L_singleton_card_le_12 {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    {H : Submodule ℝ E4} (hH : H ∈ wallHyperplanes c)
    {e : Pairs6}
    {v : E4}
    (hv_sub : {v} ⊆ ((F e.1.1).image (c e.1.1) ∪ (F e.1.2).image (c e.1.2)).filter (fun w => hp w ≠ H))
    (hL_eq : {x : E4 | x ∈ H ∧ x ∈ Kbar c e.1.1 ∩ Kbar c e.1.2} =
      {x : E4 | x ∈ H ∧ ∀ w ∈ ({v} : Finset E4), 0 ≤ ⟪w, x⟫_ℝ}) :
    (wallHyperplanes c).card ≤ 12 := by
  classical
  set i := e.1.1
  set j := e.1.2
  have hH_fin : Module.finrank ℝ H = 3 := wallHyperplanes_finrank hc_ne hH
  have hv_mem := Finset.mem_filter.mp (hv_sub (Finset.mem_singleton_self v))
  have hv_ne_H : hp v ≠ H := hv_mem.2
  obtain ⟨hv_ne0, _⟩ := facet_vec_hp_mem hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hv_mem.1
  have hHv_fin : Module.finrank ℝ (hp v) = 3 := finrank_hp hv_ne0
  let R : Submodule ℝ E4 := H ⊓ hp v
  have hR_fin : Module.finrank ℝ R = 2 := finrank_hp_inf hH_fin hHv_fin hv_ne_H.symm
  have hR_orth_fin : Module.finrank ℝ Rᗮ = 2 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal R
    rw [hR_fin, finrank_euclideanSpace_fin] at hsum
    omega
  have hsup_top : R ⊔ Rᗮ = ⊤ := by
    have hinf_bot : R ⊓ Rᗮ = ⊥ := Submodule.inf_orthogonal_eq_bot R
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq R Rᗮ
    rw [hinf_bot, finrank_bot, add_zero, hR_fin, hR_orth_fin] at hadd
    exact Submodule.eq_top_of_finrank_eq (by rw [hadd, finrank_euclideanSpace_fin])
  obtain ⟨x₀, hx0⟩ := hK_nonempty i
  have hx0_mem : x₀ ∈ R ⊔ Rᗮ := hsup_top.symm ▸ Submodule.mem_top
  obtain ⟨xR, hxR, u₀, hu0, hu0_eq⟩ := Submodule.mem_sup.mp hx0_mem
  have hR_sub_K : ∀ x ∈ R, x ∈ Kbar c i := fun x hx => by
    have hm : x ∈ {y : E4 | y ∈ H ∧ ∀ w ∈ ({v} : Finset E4), 0 ≤ ⟪w, y⟫_ℝ} := by
      refine ⟨hx.1, fun w hw => ?_⟩
      rw [Finset.mem_singleton.mp hw]
      exact ((mem_hp_iff v x).mp hx.2).ge
    rw [← hL_eq] at hm
    exact hm.2.1
  have hR_le_hp : ∀ a ∈ F i, R ≤ hp (c i a) := fun a ha x hx => by
    have hpos : 0 ≤ ⟪c i a, x⟫_ℝ := (hF_eq i ▸ hR_sub_K x hx) a ha
    have hneg : 0 ≤ ⟪c i a, -x⟫_ℝ := (hF_eq i ▸ hR_sub_K (-x) (R.neg_mem hx)) a ha
    rw [inner_neg_right] at hneg
    exact (mem_hp_iff _ _).mpr (by linarith)
  have hw_in_Rorth : ∀ a ∈ F i, c i a ∈ Rᗮ := fun a ha z hz => by
    have hz0 : ⟪c i a, z⟫_ℝ = 0 := (mem_hp_iff _ _).mp (hR_le_hp a ha hz)
    rwa [real_inner_comm]
  have hw_pos_u0 : ∀ a ∈ F i, 0 < ⟪c i a, u₀⟫_ℝ := fun a ha => by
    have hai : a ≠ i := (Finset.mem_erase.mp (hF_sub i ha)).1
    have h1 : 0 < ⟪c i a, x₀⟫_ℝ := hx0 a hai
    have hxR0 : ⟪c i a, xR⟫_ℝ = 0 := (mem_hp_iff _ _).mp (hR_le_hp a ha hxR)
    rw [← hu0_eq, inner_add_right, hxR0, zero_add] at h1
    exact h1
  let Bad : Finset (Submodule ℝ E4) := (F i).image (fun a => hp (c i a))
  have hBad_card : Bad.card ≤ 2 := by
    by_contra hlt
    have hgt : 2 < Bad.card := by omega
    obtain ⟨H₁, hH1B⟩ := Finset.card_pos.mp (by omega : 0 < Bad.card)
    have hcard1 : 1 < (Bad.erase H₁).card := by rw [Finset.card_erase_of_mem hH1B]; omega
    obtain ⟨H₂, hH2B⟩ := Finset.card_pos.mp (by omega : 0 < (Bad.erase H₁).card)
    have hcard2 : 0 < ((Bad.erase H₁).erase H₂).card := by rw [Finset.card_erase_of_mem hH2B]; omega
    obtain ⟨H₃, hH3B⟩ := Finset.card_pos.mp hcard2
    have hne12 : H₁ ≠ H₂ := (Finset.mem_erase.mp hH2B).1.symm
    have hne23 : H₂ ≠ H₃ := (Finset.mem_erase.mp hH3B).1.symm
    have hne13 : H₁ ≠ H₃ := (Finset.mem_erase.mp (Finset.mem_erase.mp hH3B).2).1.symm
    obtain ⟨a₁, ha₁, ha1eq⟩ := Finset.mem_image.mp hH1B
    obtain ⟨a₂, ha₂, ha2eq⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hH2B).2
    obtain ⟨a₃, ha₃, ha3eq⟩ := Finset.mem_image.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hH3B).2).2
    let vecs : Fin 3 → Rᗮ := ![⟨c i a₁, hw_in_Rorth a₁ ha₁⟩,
      ⟨c i a₂, hw_in_Rorth a₂ ha₂⟩, ⟨c i a₃, hw_in_Rorth a₃ ha₃⟩]
    have hnot_li : ¬ LinearIndependent ℝ vecs := fun hli => by
      have hle := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, hR_orth_fin] at hle
      omega
    obtain ⟨g, hg_sum, t₀, hgt0⟩ := Fintype.not_linearIndependent_iff.mp hnot_li
    have hsum_val : g 0 • c i a₁ + g 1 • c i a₂ + g 2 • c i a₃ = 0 := by
      have h1 := congrArg Subtype.val hg_sum
      simpa [vecs, Fin.sum_univ_three, add_assoc] using h1
    have hnz : g 0 ≠ 0 ∨ g 1 ≠ 0 ∨ g 2 ≠ 0 := by
      fin_cases t₀
      · exact Or.inl hgt0
      · exact Or.inr (Or.inl hgt0)
      · exact Or.inr (Or.inr hgt0)
    have hred := exists_pos_comb_of_three (hw_pos_u0 a₁ ha₁) (hw_pos_u0 a₂ ha₂) (hw_pos_u0 a₃ ha₃)
      (by rw [ha1eq, ha2eq]; exact hne12) (by rw [ha2eq, ha3eq]; exact hne23)
      (by rw [ha1eq, ha3eq]; exact hne13) (g 0) (g 1) (g 2) hnz hsum_val
    have red_elim : ∀ {b₀ b₁ b₂ : Fin 6},
        b₀ ∈ F i → b₁ ∈ F i → b₂ ∈ F i →
        b₀ ≠ b₁ → b₀ ≠ b₂ →
        (∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ c i b₀ = β₁ • c i b₁ + β₂ • c i b₂) → False := by
      intro b₀ b₁ b₂ hb0 hb1 hb2 hne01 hne02 ⟨β₁, β₂, hβ1, hβ2, hcomb⟩
      apply hF_min i ((F i).erase b₀) (Finset.erase_ssubset hb0)
      ext x
      rw [hF_eq i]
      refine ⟨fun hx a ha => hx a (Finset.erase_subset _ _ ha), fun hx a ha => ?_⟩
      by_cases hab : a = b₀
      · subst hab
        have hx1 : 0 ≤ ⟪c i b₁, x⟫_ℝ := hx b₁ (Finset.mem_erase.mpr ⟨hne01.symm, hb1⟩)
        have hx2 : 0 ≤ ⟪c i b₂, x⟫_ℝ := hx b₂ (Finset.mem_erase.mpr ⟨hne02.symm, hb2⟩)
        rw [hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left]
        exact add_nonneg (mul_nonneg hβ1.le hx1) (mul_nonneg hβ2.le hx2)
      · exact hx a (Finset.mem_erase.mpr ⟨hab, ha⟩)
    rcases hred with h1 | h2 | h3
    · exact red_elim ha₁ ha₂ ha₃ (fun h => hne12 (by rw [← ha1eq, ← ha2eq, h]))
        (fun h => hne13 (by rw [← ha1eq, ← ha3eq, h])) h1
    · exact red_elim ha₂ ha₁ ha₃ (fun h => hne12 (by rw [← ha1eq, ← ha2eq, h]))
        (fun h => hne23 (by rw [← ha2eq, ← ha3eq, h])) h2
    · exact red_elim ha₃ ha₁ ha₂ (fun h => hne13 (by rw [← ha1eq, ← ha3eq, h]))
        (fun h => hne23 (by rw [← ha2eq, ← ha3eq, h])) h3
  have hi_facets : ∀ a ∈ F i, hp (c i a) ∈ Bad := fun a ha => Finset.mem_image_of_mem _ ha
  have hBad_fin : ∀ H' ∈ Bad, Module.finrank ℝ H' = 3 := fun H' hH' => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH'
    exact finrank_hp (hc_ne i a (Finset.mem_erase.mp (hF_sub i ha)).1.symm)
  have hkill : ∀ k ≠ i, IsWallPair c i k → hp (c i k) ∈ Bad :=
    fun k hk hw => wall_hyperplane_avoiding_of_subset hc_ne hF_eq hBad_fin hi_facets hk hw
  have hle := card_wallHyperplanes_le_of_kill_one hc_sym Bad i hkill
  omega

/-! ### Section 4d: Wedge uniqueness, ticket counting, and DAG construction -/

private def HasWedge (c : Fin 6 → Fin 6 → E4) (Hs : Submodule ℝ E4) (e : Pairs6) : Prop :=
  ∃ k : Fin 6, ∃ (hki : k ≠ e.1.1) (hkj : k ≠ e.1.2),
    mkPair6 e.1.1 k hki.symm ∈ wallPairsAt c Hs ∧
    mkPair6 e.1.2 k hkj.symm ∈ wallPairsAt c Hs

private def verts6 (e : Pairs6) : Finset (Fin 6) := {e.1.1, e.1.2}

private lemma verts6_injective : Function.Injective verts6 := by
  intro e₁ e₂ heq
  dsimp [verts6] at heq
  apply Subtype.ext
  have h1 : e₁.1.1 = e₂.1.1 ∨ e₁.1.1 = e₂.1.2 := by
    have hm : e₁.1.1 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin 6)) :=
      heq ▸ Finset.mem_insert_self e₁.1.1 {e₁.1.2}
    simpa [Finset.mem_insert, Finset.mem_singleton] using hm
  have h2 : e₁.1.2 = e₂.1.1 ∨ e₁.1.2 = e₂.1.2 := by
    have hm : e₁.1.2 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin 6)) :=
      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self e₁.1.2)
    simpa [Finset.mem_insert, Finset.mem_singleton] using hm
  have h3 : e₂.1.1 = e₁.1.1 ∨ e₂.1.1 = e₁.1.2 := by
    have hm : e₂.1.1 ∈ ({e₁.1.1, e₁.1.2} : Finset (Fin 6)) :=
      heq.symm ▸ Finset.mem_insert_self e₂.1.1 {e₂.1.2}
    simpa [Finset.mem_insert, Finset.mem_singleton] using hm
  have hl1 : e₁.1.1 < e₁.1.2 := e₁.2
  have hl2 : e₂.1.1 < e₂.1.2 := e₂.2
  have hfst : e₁.1.1 = e₂.1.1 := by
    rcases h1 with ha | ha
    · exact ha
    · exfalso
      rcases h3 with hb | hb
      · rw [ha] at hb; exact hl2.ne hb
      · have : e₂.1.2 < e₂.1.2 := by calc e₂.1.2 = e₁.1.1 := ha.symm
          _ < e₁.1.2 := hl1
          _ = e₂.1.1 := hb.symm
          _ < e₂.1.2 := hl2
        exact lt_irrefl _ this
  have hsnd : e₁.1.2 = e₂.1.2 := by
    rcases h2 with hb | hb
    · exfalso; rw [← hfst] at hb; exact hl1.ne hb.symm
    · exact hb
  exact Prod.ext hfst hsnd

private lemma verts6_mkPair6 (a b : Fin 6) (hab : a ≠ b) :
    verts6 (mkPair6 a b hab) = {a, b} := by
  dsimp [verts6, mkPair6]
  split_ifs
  · rfl
  · exact Finset.pair_comm b a

private lemma symmDiff_verts_eq {i j k : Fin 6} (hki : k ≠ i) (hkj : k ≠ j) :
    symmDiff ({i, k} : Finset (Fin 6)) {j, k} = if i = j then ∅ else {i, j} := by
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, ↓reduceIte]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    rcases eq_or_ne x i with hxi | hxi <;>
    rcases eq_or_ne x j with hxj | hxj <;>
    rcases eq_or_ne x k with hxk | hxk <;>
      simp_all [Ne.symm]

private lemma card2_unique_wedge {c : Fin 6 → Fin 6 → E4} {Hs : Submodule ℝ E4}
    (hcard : (wallPairsAt c Hs).card = 2)
    {e₁ e₂ : Pairs6} (hw1 : HasWedge c Hs e₁) (hw2 : HasWedge c Hs e₂) :
    e₁ = e₂ := by
  obtain ⟨k₁, h1i, h1j, hp1a, hp1b⟩ := hw1
  obtain ⟨k₂, h2i, h2j, hp2a, hp2b⟩ := hw2
  set p1a := mkPair6 e₁.1.1 k₁ h1i.symm
  set p1b := mkPair6 e₁.1.2 k₁ h1j.symm
  set p2a := mkPair6 e₂.1.1 k₂ h2i.symm
  set p2b := mkPair6 e₂.1.2 k₂ h2j.symm
  have hp1_ne : p1a ≠ p1b := fun h => by
    have hv := congrArg verts6 h
    rw [verts6_mkPair6, verts6_mkPair6] at hv
    have hm : e₁.1.1 ∈ ({e₁.1.2, k₁} : Finset (Fin 6)) := hv ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq
    · exact e₁.2.ne heq
    · exact h1i heq.symm
  have hp2_ne : p2a ≠ p2b := fun h => by
    have hv := congrArg verts6 h
    rw [verts6_mkPair6, verts6_mkPair6] at hv
    have hm : e₂.1.1 ∈ ({e₂.1.2, k₂} : Finset (Fin 6)) := hv ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq
    · exact e₂.2.ne heq
    · exact h2i heq.symm
  have hset1 : wallPairsAt c Hs = {p1a, p1b} := by
    exact (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨hp1a, Finset.singleton_subset_iff.mpr hp1b⟩)
      (by rw [Finset.card_pair hp1_ne, hcard])).symm
  have hset2 : wallPairsAt c Hs = {p2a, p2b} := by
    exact (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨hp2a, Finset.singleton_subset_iff.mpr hp2b⟩)
      (by rw [Finset.card_pair hp2_ne, hcard])).symm
  have hpair_eq : ({p1a, p1b} : Finset Pairs6) = {p2a, p2b} := hset1.symm.trans hset2
  have hsymm : symmDiff (verts6 p1a) (verts6 p1b) = symmDiff (verts6 p2a) (verts6 p2b) := by
    have hp1a_in : p1a ∈ ({p2a, p2b} : Finset Pairs6) := hpair_eq ▸ Finset.mem_insert_self _ _
    have hp1b_in : p1b ∈ ({p2a, p2b} : Finset Pairs6) :=
      hpair_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp1a_in hp1b_in
    rcases hp1a_in with h1 | h1 <;> rcases hp1b_in with h2 | h2
    · exact False.elim (hp1_ne (h1.trans h2.symm))
    · rw [h1, h2]
    · rw [h1, h2]; exact symmDiff_comm _ _
    · exact False.elim (hp1_ne (h1.trans h2.symm))
  rw [verts6_mkPair6, verts6_mkPair6, verts6_mkPair6, verts6_mkPair6] at hsymm
  rw [symmDiff_verts_eq h1i h1j, symmDiff_verts_eq h2i h2j] at hsymm
  simp only [e₁.2.ne, e₂.2.ne, ↓reduceIte] at hsymm
  exact verts6_injective hsymm

private lemma ticket_counting {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    (ℋ_free : Finset (Submodule ℝ E4))
    (hℋ_free : ∀ H, H ∈ ℋ_free ↔ H ∈ wallHyperplanes c ∧ ¬ hasCoplanarTriple (wallHyperplanes c) H) :
    (12 ≤ (wallHyperplanes c).card →
      ℋ_free.card ≤ (15 - (wallHyperplanes c).card) + (15 - (wallHyperplanes c).card) / 2) ∧
    ((wallHyperplanes c).card = 15 → ℋ_free = ∅) := by
  classical
  set ℋ := wallHyperplanes c
  let ℋ_shared := ℋ.filter (fun H => 2 ≤ (wallPairsAt c H).card)
  let ℋ_ns := ℋ.filter (fun H => ¬ hasCoplanarTriple ℋ H ∧ (wallPairsAt c H).card = 1)
  have hfree_sub : ℋ_free ⊆ ℋ_shared ∪ ℋ_ns := by
    intro H hH
    obtain ⟨hHℋ, hno⟩ := (hℋ_free H).mp hH
    have hpos : 1 ≤ (wallPairsAt c H).card := Finset.card_pos.mpr (wallPairsAt_nonempty hHℋ)
    by_cases h2 : 2 ≤ (wallPairsAt c H).card
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hHℋ, h2⟩)
    · have h1 : (wallPairsAt c H).card = 1 := by omega
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hHℋ, hno, h1⟩)
  have hexcess : ℋ.card + ∑ H ∈ ℋ_shared, ((wallPairsAt c H).card - 1) ≤ 15 := by
    have hsum : ∑ H ∈ ℋ, (wallPairsAt c H).card =
        ℋ.card + ∑ H ∈ ℋ_shared, ((wallPairsAt c H).card - 1) := by
      have hid : ∀ H ∈ ℋ, (wallPairsAt c H).card =
          1 + (if 2 ≤ (wallPairsAt c H).card then (wallPairsAt c H).card - 1 else 0) := by
        intro H hH
        have hpos : 1 ≤ (wallPairsAt c H).card := Finset.card_pos.mpr (wallPairsAt_nonempty hH)
        split_ifs <;> omega
      rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      rw [← Finset.sum_filter]
    have htot := sum_wallPairsAt_le c
    change ∑ H ∈ ℋ, (wallPairsAt c H).card ≤ 15 at htot
    omega
  have hshared_le : ℋ_shared.card ≤ 15 - ℋ.card := by
    have h1 : ℋ_shared.card ≤ ∑ H ∈ ℋ_shared, ((wallPairsAt c H).card - 1) := by
      calc ℋ_shared.card = ∑ _H ∈ ℋ_shared, 1 := by simp
        _ ≤ ∑ H ∈ ℋ_shared, ((wallPairsAt c H).card - 1) := by
          refine Finset.sum_le_sum fun H hH => ?_
          have := (Finset.mem_filter.mp hH).2
          omega
    omega
  have hns_wedge : 12 ≤ ℋ.card → ∀ H ∈ ℋ_ns, ∃ e : Pairs6, wallPairsAt c H = {e} ∧
      2 ≤ (ℋ_shared.filter (fun Hs => HasWedge c Hs e)).card := by
    intro h12 H hHns
    obtain ⟨hHℋ, hno_tri, hcard1⟩ := Finset.mem_filter.mp hHns
    obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hcard1
    have he : e ∈ wallPairsAt c H := he_eq ▸ Finset.mem_singleton_self e
    obtain ⟨L, hL_sub, hL_eq, hL_min⟩ := exists_minimal_L hc_sym hc_ne F hF_sub hF_eq he
    have hL2 : 2 ≤ L.card := by
      by_contra hlt
      have hle1 : L.card ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
      · have heq := Finset.card_eq_zero.mp h0
        subst heq
        have h7 := L_empty_card_le_7 hc_sym hc_ne hF_sub hF_eq hHℋ he hL_eq
        change ℋ.card ≤ 7 at h7
        omega
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
        subst hv
        have h8 := L_singleton_no_tri_card_le_8 hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq
          hF_min hHℋ hno_tri hL_sub hL_eq
        change ℋ.card ≤ 8 at h8
        omega
    obtain ⟨v₁, hv₁, v₂, hv₂, hvne⟩ := Finset.one_lt_card.mp hL2
    have hinf_ne := minimal_L_distinct_hps hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq
      hF_min he hL_sub hL_eq hL_min hv₁ hv₂ hvne
    have hhp_ne : hp v₁ ≠ hp v₂ := fun heq => hinf_ne (by rw [heq])
    have ht1 := ridge_trichotomy hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hHℋ
      he hL_sub hL_eq hL_min hv₁
    have ht2 := ridge_trichotomy hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hHℋ
      he hL_sub hL_eq hL_min hv₂
    have hnot2 : ¬ 2 ≤ (wallPairsAt c H).card := by omega
    have hw1 : HasWedge c (hp v₁) e ∧ hp v₁ ∈ ℋ_shared := by
      rcases ht1.2 with ⟨H'', hH'', hcop⟩ | h2 | ⟨k, hki, hkj, hm1, hm2⟩
      · exact False.elim (hno_tri ⟨hp v₁, (Finset.mem_erase.mp ht1.1).2, H'', hH'', hcop⟩)
      · exact False.elim (hnot2 h2)
      · have hne_p : mkPair6 e.1.1 k hki.symm ≠ mkPair6 e.1.2 k hkj.symm := fun heq => by
          have hv := congrArg verts6 heq
          rw [verts6_mkPair6, verts6_mkPair6] at hv
          have hm := Finset.mem_insert.mp (hv ▸ Finset.mem_insert_self e.1.1 {k})
          simp only [Finset.mem_singleton] at hm
          exact hm.elim (Fin.ne_of_lt e.2) (fun h => hki h.symm)
        have hc2 : 2 ≤ (wallPairsAt c (hp v₁)).card := by
          have hsub : {mkPair6 e.1.1 k hki.symm, mkPair6 e.1.2 k hkj.symm} ⊆ wallPairsAt c (hp v₁) := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hm1
            · rw [Finset.mem_singleton.mp hx]; exact hm2
          calc 2 = ({mkPair6 e.1.1 k hki.symm, mkPair6 e.1.2 k hkj.symm} : Finset Pairs6).card :=
                (Finset.card_pair hne_p).symm
            _ ≤ (wallPairsAt c (hp v₁)).card := Finset.card_le_card hsub
        exact ⟨⟨k, hki, hkj, hm1, hm2⟩, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp ht1.1).2, hc2⟩⟩
    have hw2 : HasWedge c (hp v₂) e ∧ hp v₂ ∈ ℋ_shared := by
      rcases ht2.2 with ⟨H'', hH'', hcop⟩ | h2 | ⟨k, hki, hkj, hm1, hm2⟩
      · exact False.elim (hno_tri ⟨hp v₂, (Finset.mem_erase.mp ht2.1).2, H'', hH'', hcop⟩)
      · exact False.elim (hnot2 h2)
      · have hne_p : mkPair6 e.1.1 k hki.symm ≠ mkPair6 e.1.2 k hkj.symm := fun heq => by
          have hv := congrArg verts6 heq
          rw [verts6_mkPair6, verts6_mkPair6] at hv
          have hm := Finset.mem_insert.mp (hv ▸ Finset.mem_insert_self e.1.1 {k})
          simp only [Finset.mem_singleton] at hm
          exact hm.elim (Fin.ne_of_lt e.2) (fun h => hki h.symm)
        have hc2 : 2 ≤ (wallPairsAt c (hp v₂)).card := by
          have hsub : {mkPair6 e.1.1 k hki.symm, mkPair6 e.1.2 k hkj.symm} ⊆ wallPairsAt c (hp v₂) := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hm1
            · rw [Finset.mem_singleton.mp hx]; exact hm2
          calc 2 = ({mkPair6 e.1.1 k hki.symm, mkPair6 e.1.2 k hkj.symm} : Finset Pairs6).card :=
                (Finset.card_pair hne_p).symm
            _ ≤ (wallPairsAt c (hp v₂)).card := Finset.card_le_card hsub
        exact ⟨⟨k, hki, hkj, hm1, hm2⟩, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp ht2.1).2, hc2⟩⟩
    refine ⟨e, he_eq, ?_⟩
    let sub2 : Finset (Submodule ℝ E4) := {hp v₁, hp v₂}
    have hsub2 : sub2 ⊆ ℋ_shared.filter (fun Hs => HasWedge c Hs e) := fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨hw1.2, hw1.1⟩
      · rw [Finset.mem_singleton.mp hx]; exact Finset.mem_filter.mpr ⟨hw2.2, hw2.1⟩
    calc 2 = sub2.card := (Finset.card_pair hhp_ne).symm
      _ ≤ (ℋ_shared.filter (fun Hs => HasWedge c Hs e)).card := Finset.card_le_card hsub2
  have hinj_ns : ∀ {H_a H_b : Submodule ℝ E4} {e_a e_b : Pairs6},
      H_a ∈ ℋ_ns → H_b ∈ ℋ_ns → H_a ≠ H_b →
      wallPairsAt c H_a = {e_a} → wallPairsAt c H_b = {e_b} → e_a ≠ e_b := by
    intro H_a H_b e_a e_b ha hb hne hea heb heq
    subst heq
    have hdisj : Disjoint (wallPairsAt c H_a) (wallPairsAt c H_b) :=
      wallPairsAt_disjoint c (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hne
    rw [hea, heb, Finset.disjoint_singleton] at hdisj
    exact hdisj rfl
  have hmain : 12 ≤ ℋ.card → ℋ_free.card ≤ (15 - ℋ.card) + (15 - ℋ.card) / 2 := by
    intro h12
    have hns_le1 : ℋ_ns.card ≤ 1 := by
      by_contra hgt1
      have hgt1' : 1 < ℋ_ns.card := by omega
      obtain ⟨H_a, ha, H_b, hb, hne⟩ := Finset.one_lt_card.mp hgt1'
      obtain ⟨e_a, hea_eq, hwa⟩ := hns_wedge h12 H_a ha
      obtain ⟨e_b, heb_eq, hwb⟩ := hns_wedge h12 H_b hb
      have he_ne : e_a ≠ e_b := hinj_ns ha hb hne hea_eq heb_eq
      have hA_le : (ℋ_shared.filter (fun Hs => HasWedge c Hs e_a)).card ≤ ℋ_shared.card :=
        Finset.card_filter_le _ _
      by_cases hc1 : ℋ_shared.card ≤ 1
      · omega
      · by_cases hc2 : ℋ_shared.card = 2
        · have hex_two : ∃ Hs₀ ∈ ℋ_shared, (wallPairsAt c Hs₀).card = 2 := by
            by_contra hnone
            push Not at hnone
            have hge4 : 4 ≤ ∑ H ∈ ℋ_shared, ((wallPairsAt c H).card - 1) := by
              calc 4 = ∑ _H ∈ ℋ_shared, 2 := by simp [hc2]
                _ ≤ ∑ H ∈ ℋ_shared, ((wallPairsAt c H).card - 1) := by
                  refine Finset.sum_le_sum fun H hH => ?_
                  have h2 := (Finset.mem_filter.mp hH).2
                  have hne2 := hnone H hH
                  omega
            omega
          obtain ⟨Hs₀, hHs0_sh, hHs0_deg⟩ := hex_two
          have hAe : ℋ_shared.filter (fun Hs => HasWedge c Hs e_a) = ℋ_shared :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have hBe : ℋ_shared.filter (fun Hs => HasWedge c Hs e_b) = ℋ_shared :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have hHs0_A : Hs₀ ∈ ℋ_shared.filter (fun Hs => HasWedge c Hs e_a) := by
            rw [hAe]; exact hHs0_sh
          have hHs0_B : Hs₀ ∈ ℋ_shared.filter (fun Hs => HasWedge c Hs e_b) := by
            rw [hBe]; exact hHs0_sh
          have hw_a : HasWedge c Hs₀ e_a := (Finset.mem_filter.mp hHs0_A).2
          have hw_b : HasWedge c Hs₀ e_b := (Finset.mem_filter.mp hHs0_B).2
          exact he_ne (card2_unique_wedge hHs0_deg hw_a hw_b)
        · have hc3 : ℋ_shared.card = 3 := by omega
          let A := ℋ_shared.filter (fun Hs => HasWedge c Hs e_a)
          let B := ℋ_shared.filter (fun Hs => HasWedge c Hs e_b)
          have hAc : 2 ≤ A.card := hwa
          have hBc : 2 ≤ B.card := hwb
          have hAB_sub : A ∪ B ⊆ ℋ_shared :=
            Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          have hAB_pos : 0 < (A ∩ B).card := by
            have := Finset.card_union_add_card_inter A B
            have huc := Finset.card_le_card hAB_sub
            omega
          obtain ⟨Hs₀, hHs0⟩ := Finset.card_pos.mp hAB_pos
          obtain ⟨hA, hB⟩ := Finset.mem_inter.mp hHs0
          have hHs0_sh : Hs₀ ∈ ℋ_shared := (Finset.mem_filter.mp hA).1
          have hdeg_all : (wallPairsAt c Hs₀).card = 2 := by
            have hsum_er : (ℋ_shared.erase Hs₀).card = 2 := by
              rw [Finset.card_erase_of_mem hHs0_sh, hc3]
            have hsplit := Finset.add_sum_erase ℋ_shared (fun H => (wallPairsAt c H).card - 1) hHs0_sh
            have hrest : 2 ≤ ∑ H ∈ ℋ_shared.erase Hs₀, ((wallPairsAt c H).card - 1) := by
              calc 2 = ∑ _H ∈ ℋ_shared.erase Hs₀, 1 := by simp [hsum_er]
                _ ≤ ∑ H ∈ ℋ_shared.erase Hs₀, ((wallPairsAt c H).card - 1) := by
                  refine Finset.sum_le_sum fun H hH => ?_
                  have h2 := (Finset.mem_filter.mp (Finset.erase_subset _ _ hH)).2
                  omega
            have h2Hs : 2 ≤ (wallPairsAt c Hs₀).card := (Finset.mem_filter.mp hHs0_sh).2
            omega
          exact he_ne (card2_unique_wedge hdeg_all (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2)
    have hns0_of_le1 : ℋ_shared.card ≤ 1 → ℋ_ns.card = 0 := fun hle1 => by
      by_contra hne0
      obtain ⟨H, hH⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
      obtain ⟨e, _, hwa⟩ := hns_wedge h12 H hH
      have hwa' : (ℋ_shared.filter (fun Hs => HasWedge c Hs e)).card ≤ 1 :=
        (Finset.card_filter_le _ _).trans hle1
      omega
    have hle_sum : ℋ_free.card ≤ ℋ_shared.card + ℋ_ns.card :=
      (Finset.card_le_card hfree_sub).trans (Finset.card_union_le _ _)
    by_cases hc1 : ℋ_shared.card ≤ 1
    · have := hns0_of_le1 hc1
      omega
    · have : 2 ≤ ℋ_shared.card := by omega
      omega
  refine ⟨hmain, fun h15 => ?_⟩
  change ℋ.card = 15 at h15
  have := hmain (by omega)
  rw [h15] at this
  exact Finset.card_eq_zero.mp (by omega)

private lemma hnot_part_15 {c : Fin 6 → Fin 6 → E4}
    (hc_sym : ∀ i j, c j i = -c i j) (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ)
    {F : Fin 6 → Finset (Fin 6)}
    (hF_sub : ∀ i, F i ⊆ Finset.univ.erase i)
    (hF_eq : ∀ i, Kbar c i = {x | ∀ j ∈ F i, 0 ≤ ⟪c i j, x⟫_ℝ})
    (hF_min : ∀ i, ∀ F' ⊂ F i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ})
    (hcard15 : (wallHyperplanes c).card = 15) :
    ∃ H ∈ wallHyperplanes c, ∃ H₁ ∈ wallHyperplanes c, ∃ H₁' ∈ wallHyperplanes c,
      ∃ H₂ ∈ wallHyperplanes c, ∃ H₂' ∈ wallHyperplanes c,
      CoplanarTriple H H₁ H₁' ∧ CoplanarTriple H H₂ H₂' ∧
      H₂ ∉ ({H, H₁, H₁'} : Finset (Submodule ℝ E4)) := by
  classical
  set ℋ := wallHyperplanes c
  have hcard1_all : ∀ H' ∈ ℋ, (wallPairsAt c H').card = 1 := fun H' hH' => by
    have hpos : 1 ≤ (wallPairsAt c H').card := Finset.card_pos.mpr (wallPairsAt_nonempty hH')
    by_contra hne1
    have hge2 : 2 ≤ (wallPairsAt c H').card := by omega
    have hsplit := Finset.add_sum_erase ℋ (fun H'' => (wallPairsAt c H'').card) hH'
    have hrest : 14 ≤ ∑ H'' ∈ ℋ.erase H', (wallPairsAt c H'').card := by
      calc 14 = ∑ _H'' ∈ ℋ.erase H', 1 := by simp [Finset.card_erase_of_mem hH', hcard15]
        _ ≤ ∑ H'' ∈ ℋ.erase H', (wallPairsAt c H'').card :=
          Finset.sum_le_sum fun H'' hH'' =>
            Finset.card_pos.mpr (wallPairsAt_nonempty (Finset.erase_subset _ _ hH''))
    have hle15 := sum_wallPairsAt_le c
    change ∑ H'' ∈ ℋ, (wallPairsAt c H'').card ≤ 15 at hle15
    omega
  obtain ⟨H, hHℋ⟩ := Finset.card_pos.mp (by omega : 0 < ℋ.card)
  obtain ⟨e, he⟩ := wallPairsAt_nonempty hHℋ
  obtain ⟨L, hL_sub, hL_eq, hL_min⟩ := exists_minimal_L hc_sym hc_ne F hF_sub hF_eq he
  have hL2 : 2 ≤ L.card := by
    by_contra hlt
    have hle1 : L.card ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
    · have heq := Finset.card_eq_zero.mp h0
      subst heq
      have h7 := L_empty_card_le_7 hc_sym hc_ne hF_sub hF_eq hHℋ he hL_eq
      change ℋ.card ≤ 7 at h7
      omega
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
      subst hv
      have h12 := L_singleton_card_le_12 hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min
        hHℋ hL_sub hL_eq
      change ℋ.card ≤ 12 at h12
      omega
  obtain ⟨v₁, hv₁, v₂, hv₂, hvne⟩ := Finset.one_lt_card.mp hL2
  have hinf_ne := minimal_L_distinct_hps hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq
    hF_min he hL_sub hL_eq hL_min hv₁ hv₂ hvne
  have ht1 := ridge_trichotomy hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hHℋ
    he hL_sub hL_eq hL_min hv₁
  have ht2 := ridge_trichotomy hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hHℋ
    he hL_sub hL_eq hL_min hv₂
  have hnot2H : ¬ 2 ≤ (wallPairsAt c H).card := by have := hcard1_all H hHℋ; omega
  have hnot_wedge : ∀ (Hs : Submodule ℝ E4) (hHs : Hs ∈ ℋ), ¬ HasWedge c Hs e := by
    intro Hs hHs ⟨k, hki, hkj, hm1, hm2⟩
    have hne_p : mkPair6 e.1.1 k hki.symm ≠ mkPair6 e.1.2 k hkj.symm := fun heq => by
      have hv := congrArg verts6 heq
      rw [verts6_mkPair6, verts6_mkPair6] at hv
      have hm := Finset.mem_insert.mp (hv ▸ Finset.mem_insert_self e.1.1 {k})
      simp only [Finset.mem_singleton] at hm
      exact hm.elim (Fin.ne_of_lt e.2) (fun h => hki h.symm)
    have hc2 : 2 ≤ (wallPairsAt c Hs).card := by
      have hsub : {mkPair6 e.1.1 k hki.symm, mkPair6 e.1.2 k hkj.symm} ⊆ wallPairsAt c Hs := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hm1
        · rw [Finset.mem_singleton.mp hx]; exact hm2
      calc 2 = ({mkPair6 e.1.1 k hki.symm, mkPair6 e.1.2 k hkj.symm} : Finset Pairs6).card :=
            (Finset.card_pair hne_p).symm
        _ ≤ (wallPairsAt c Hs).card := Finset.card_le_card hsub
    have := hcard1_all Hs hHs
    omega
  have hH1_mem : hp v₁ ∈ ℋ := (Finset.mem_erase.mp ht1.1).2
  have hH2_mem : hp v₂ ∈ ℋ := (Finset.mem_erase.mp ht2.1).2
  obtain ⟨H₁', hH1p, hcop1⟩ : ∃ H₁' ∈ ℋ, CoplanarTriple H (hp v₁) H₁' := by
    rcases ht1.2 with htri1 | h2 | hwedge
    · exact htri1
    · exact False.elim (hnot2H h2)
    · exact False.elim (hnot_wedge (hp v₁) hH1_mem hwedge)
  obtain ⟨H₂', hH2p, hcop2⟩ : ∃ H₂' ∈ ℋ, CoplanarTriple H (hp v₂) H₂' := by
    rcases ht2.2 with htri2 | h2 | hwedge
    · exact htri2
    · exact False.elim (hnot2H h2)
    · exact False.elim (hnot_wedge (hp v₂) hH2_mem hwedge)
  have hH2_ne_H : hp v₂ ≠ H := (Finset.mem_erase.mp ht2.1).1
  have hH2_ne_H1 : hp v₂ ≠ hp v₁ := fun heq => hinf_ne (by rw [heq])
  have hH2_ne_H1p : hp v₂ ≠ H₁' := fun heq => by
    have hH_fin := wallHyperplanes_finrank hc_ne hHℋ
    have hH1_fin := wallHyperplanes_finrank hc_ne hH1_mem
    have hH1p_fin := wallHyperplanes_finrank hc_ne hH1p
    have hinf_eq : (H ⊓ hp v₁ : Submodule ℝ E4) = H ⊓ H₁' := by
      refine Submodule.eq_of_le_of_finrank_eq (le_inf inf_le_left hcop1.2.2.2) ?_
      rw [finrank_hp_inf hH_fin hH1_fin hcop1.1, finrank_hp_inf hH_fin hH1p_fin hcop1.2.2.1]
    exact hinf_ne (by rw [hinf_eq, heq])
  refine ⟨H, hHℋ, hp v₁, hH1_mem, H₁', hH1p, hp v₂, hH2_mem, H₂', hH2p, hcop1, hcop2, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hH2_ne_H, hH2_ne_H1, hH2_ne_H1p⟩

private lemma exists_normal_of_finrank3 {H : Submodule ℝ E4} (hH : Module.finrank ℝ H = 3) :
    ∃ v : E4, v ≠ 0 ∧ hp v = H := by
  have hsum := Submodule.finrank_add_finrank_orthogonal H
  rw [hH, finrank_euclideanSpace_fin] at hsum
  have hbot : Hᗮ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨v, hv_mem, hv_ne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨v, hv_ne0, ?_⟩
  refine (hp_eq_of_le hH (finrank_hp hv_ne0) ?_).symm
  intro x hx
  rw [mem_hp_iff, real_inner_comm]
  exact hv_mem x hx

private lemma fin_sum_list_map {α : Type*} (L : List α) (f : α → ℕ) :
    (∑ t : Fin L.length, f L[t.1]) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    dsimp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp [ih]

private lemma evalDagStep_cast {t : ℕ} {op₁ op₂ : DagOp t} (h : op₁ = op₂)
    (prev : Fin t → (Fin 4 → ℝ)) (u : Fin (dagArity op₁) → ℝ) :
    evalDagStep op₂ prev (cast (by rw [h]) u) = evalDagStep op₁ prev u := by
  subst h; rfl

private lemma evalDagNormals_congr_lt {M : ℕ} (steps : (t : Fin M) → DagOp t.1)
    (ψ₁ ψ₂ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ)
    (n : ℕ) (hagree : ∀ s : Fin M, s.1 < n → ψ₁ s = ψ₂ s) :
    ∀ s : Fin M, s.1 < n → evalDagNormals steps ψ₁ s = evalDagNormals steps ψ₂ s := by
  intro ⟨s, hsM⟩ hsn
  induction s using Nat.strong_induction_on with
  | h s ih =>
    rw [evalDagNormals_eq, evalDagNormals_eq, hagree ⟨s, hsM⟩ hsn]
    have hprev : (fun i : Fin s => evalDagNormals steps ψ₁ ⟨i.1, Nat.lt_trans i.2 hsM⟩) =
        (fun i : Fin s => evalDagNormals steps ψ₂ ⟨i.1, Nat.lt_trans i.2 hsM⟩) := by
      funext i
      exact ih i.1 i.2 (Nat.lt_trans i.2 hsM) (lt_trans i.2 hsn)
    rw [hprev]

private lemma exists_dag_of_cones_r4 (c : Fin 6 → Fin 6 → E4)
    (hc_sym : ∀ i j, c j i = -c i j)
    (hc_ne : ∀ i j, i ≠ j → c i j ≠ 0)
    (hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ)
    (hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ) :
    ∃ (M : ℕ) (steps : (t : Fin M) → DagOp t.1)
      (ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ),
      M ≤ 15 ∧
      (∑ t : Fin M, dagArity (steps t)) ≤ 33 ∧
      (∀ t : Fin M, evalDagNormals steps ψ t ≠ 0) ∧
      (∀ H ∈ wallHyperplanes c, ∃ t : Fin M,
        hp (WithLp.toLp 2 (evalDagNormals steps ψ t)) = H) ∧
      (∀ (x : E4) (i : Fin 6), (∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ) →
        (∃ j ≠ i, ⟪c i j, x⟫_ℝ = 0) →
        ∃ t : Fin M, ∑ r : Fin 4, evalDagNormals steps ψ t r * x r = 0) := by
  classical
  have hF_ex : ∀ i : Fin 6, ∃ F_i ⊆ Finset.univ.erase i,
      Kbar c i = {x | ∀ j ∈ F_i, 0 ≤ ⟪c i j, x⟫_ℝ} ∧
      ∀ F' ⊂ F_i, Kbar c i ≠ {x | ∀ j ∈ F', 0 ≤ ⟪c i j, x⟫_ℝ} :=
    fun i => exists_min_facets c i
  choose F hF_sub hF_eq hF_min using hF_ex
  set ℋ := wallHyperplanes c
  set ℋ_free := ℋ.filter (fun H => ¬ hasCoplanarTriple ℋ H)
  set Tset := ℋ.filter (fun H => hasCoplanarTriple ℋ H)
  have hT_fin : ∀ H ∈ Tset, Module.finrank ℝ H = 3 :=
    fun H hH => wallHyperplanes_finrank hc_ne (Finset.mem_filter.mp hH).1
  have hT_tri : ∀ H ∈ Tset, ∃ H₁ ∈ Tset, ∃ H₂ ∈ Tset, CoplanarTriple H H₁ H₂ := by
    intro H hH
    obtain ⟨hHℋ, H₁, hH1ℋ, H₂, hH2ℋ, hcop⟩ := Finset.mem_filter.mp hH
    have perms := coplanarTriple_all_perms (wallHyperplanes_finrank hc_ne hHℋ)
      (wallHyperplanes_finrank hc_ne hH1ℋ) (wallHyperplanes_finrank hc_ne hH2ℋ) hcop
    exact ⟨H₁, Finset.mem_filter.mpr ⟨hH1ℋ, H, hHℋ, H₂, hH2ℋ, perms.2.1⟩,
      H₂, Finset.mem_filter.mpr ⟨hH2ℋ, H, hHℋ, H₁, hH1ℋ, perms.2.2.2.1⟩, hcop⟩
  have hT_card15 : Tset.card = 15 →
      ∃ H ∈ Tset, ∃ H₁ ∈ Tset, ∃ H₁' ∈ Tset, ∃ H₂ ∈ Tset, ∃ H₂' ∈ Tset,
        CoplanarTriple H H₁ H₁' ∧ CoplanarTriple H H₂ H₂' ∧
        H₂ ∉ ({H, H₁, H₁'} : Finset (Submodule ℝ E4)) := by
    intro h15
    have hℋ_le15 := wallHyperplanes_card_le c
    change ℋ.card ≤ 15 at hℋ_le15
    have hT_le : Tset.card ≤ ℋ.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hℋ15 : ℋ.card = 15 := by omega
    have hT_eq_ℋ : Tset = ℋ := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    rw [hT_eq_ℋ]
    exact hnot_part_15 hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min hℋ15
  obtain ⟨L', hL'_valid, hL'_len, hL'_fc, hL'_fc15⟩ :=
    greedy_triples_bound Tset hT_fin hT_tri hT_card15
  let Flist : List (Submodule ℝ E4) := ℋ_free.toList
  let b₀ : ℕ := Flist.length
  let Slist : List TripleSeqItem :=
    Flist.map (fun H => ⟨H, none⟩) ++
    L'.map (fun item => ⟨item.H, item.parents.map fun p => (b₀ + p.1, b₀ + p.2)⟩)
  let M : ℕ := Slist.length
  have hb₀_eq : Flist.length = ℋ_free.card := Finset.length_toList _
  have hsum_cards : ℋ_free.card + Tset.card = ℋ.card := by
    have hdisj : Disjoint ℋ_free Tset := Finset.disjoint_left.mpr fun H ha hb =>
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hun : ℋ_free ∪ Tset = ℋ := by
      ext H
      simp only [ℋ_free, Tset, Finset.mem_union, Finset.mem_filter]
      tauto
    rw [← Finset.card_union_of_disjoint hdisj, hun]
  have hM_eq : M = ℋ.card := by
    dsimp [M, Slist]
    rw [List.length_append, List.length_map, List.length_map, hL'_len, hb₀_eq, hsum_cards]
  have hM_le15 : M ≤ 15 := by
    have := wallHyperplanes_card_le c
    change ℋ.card ≤ 15 at this
    omega
  have hS_in : ∀ t : Fin M, Slist[t.1].H ∈ ℋ := fun ⟨t, ht⟩ => by
    dsimp [M] at ht
    by_cases htb : t < b₀
    · have hget : Slist[t]'ht = ⟨Flist[t]'htb, none⟩ := by
        dsimp [Slist]
        rw [List.getElem_append_left (by simp [b₀, htb]), List.getElem_map]
      rw [hget]
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp (List.getElem_mem htb))).1
    · have htb' : t - b₀ < L'.length := by
        dsimp [Slist, M] at ht
        rw [List.length_append, List.length_map, List.length_map] at ht
        omega
      have hget : Slist[t]'ht = ⟨(L'[t - b₀]'htb').H,
          (L'[t - b₀]'htb').parents.map fun p => (b₀ + p.1, b₀ + p.2)⟩ := by
        dsimp [Slist]
        rw [List.getElem_append_right (by simp; omega), List.getElem_map]
        simp [b₀]
      rw [hget]
      exact (Finset.mem_filter.mp (hL'_valid.2.1 _ (List.getElem_mem htb'))).1
  have hH_mem_S : ∀ H ∈ ℋ, ∃ t : Fin M, Slist[t.1].H = H := fun H hH => by
    by_cases hfree : ¬ hasCoplanarTriple ℋ H
    · have hHF : H ∈ Flist := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hH, hfree⟩)
      obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hHF
      have htM : t < M := by dsimp [M, Slist]; rw [List.length_append, List.length_map]; omega
      refine ⟨⟨t, htM⟩, ?_⟩
      dsimp [Slist]
      rw [List.getElem_append_left (by simp [ht]), List.getElem_map, hteq]
    · have hno : hasCoplanarTriple ℋ H := not_not.mp hfree
      have hHT : H ∈ Tset := Finset.mem_filter.mpr ⟨hH, hno⟩
      have hH_mem_map : H ∈ L'.map (·.H) := by
        have hsub : (L'.map (·.H)).toFinset ⊆ Tset := fun X hX => by
          rw [List.mem_toFinset, List.mem_map] at hX
          obtain ⟨item, hitem, rfl⟩ := hX
          exact hL'_valid.2.1 item hitem
        have hEqFin : (L'.map (·.H)).toFinset = Tset :=
          Finset.eq_of_subset_of_card_le hsub (by rw [List.toFinset_card_of_nodup hL'_valid.1, List.length_map, hL'_len])
        rw [← List.mem_toFinset, hEqFin]
        exact hHT
      obtain ⟨item, hitem, hitem_eq⟩ := List.mem_map.mp hH_mem_map
      obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hitem
      have htM : b₀ + k < M := by
        dsimp [M, Slist, b₀]
        rw [List.length_append, List.length_map, List.length_map]
        omega
      refine ⟨⟨b₀ + k, htM⟩, ?_⟩
      dsimp [Slist]
      rw [List.getElem_append_right (by simp [b₀]), List.getElem_map]
      simp only [b₀, List.length_map, add_tsub_cancel_left]
      rw [hkeq, hitem_eq]
  have hu_ex : ∀ t : Fin M, ∃ u_t : E4, u_t ≠ 0 ∧ hp u_t = Slist[t.1].H :=
    fun t => exists_normal_of_finrank3 (wallHyperplanes_finrank hc_ne (hS_in t))
  choose u hu_ne hu_hp using hu_ex
  have hpiv_ex : ∀ t : Fin M, ∃ piv_t : Fin 4, u t piv_t ≠ 0 := fun t => by
    by_contra hnone
    push Not at hnone
    exact hu_ne t (PiLp.ext hnone)
  choose piv hpiv using hpiv_ex
  have hS_parents : ∀ (t : Fin M) (a b : ℕ), Slist[t.1].parents = some (a, b) →
      a < t.1 ∧ b < t.1 ∧
      ∀ (ha : a < t.1) (hb : b < t.1),
        CoplanarTriple (Slist[a]'(Nat.lt_trans ha t.2)).H (Slist[b]'(Nat.lt_trans hb t.2)).H Slist[t.1].H := by
    intro ⟨t, ht⟩ a b hp_eq
    by_cases htb : t < b₀
    · have hget : Slist[t]'ht = ⟨Flist[t]'htb, none⟩ := by
        dsimp [Slist]
        rw [List.getElem_append_left (by simp [b₀, htb]), List.getElem_map]
      simp [hget] at hp_eq
    · have htb' : t - b₀ < L'.length := by
        dsimp [Slist, M] at ht
        rw [List.length_append, List.length_map, List.length_map] at ht
        omega
      have hget : Slist[t]'ht = ⟨(L'[t - b₀]'htb').H,
          (L'[t - b₀]'htb').parents.map fun p => (b₀ + p.1, b₀ + p.2)⟩ := by
        dsimp [Slist]
        rw [List.getElem_append_right (by simp; omega), List.getElem_map]
        simp [b₀]
      rw [hget] at hp_eq
      dsimp at hp_eq
      cases hlp : (L'[t - b₀]'htb').parents with
      | none => rw [hlp] at hp_eq; simp at hp_eq
      | some ab =>
        rw [hlp] at hp_eq
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp_eq
        rcases hp_eq with ⟨rfl, rfl⟩
        have hspec := hL'_valid.2.2 (t - b₀) htb'
        rw [hlp] at hspec
        obtain ⟨ha', hb', hcop⟩ := hspec
        have ha : b₀ + ab.1 < t := by omega
        have hb : b₀ + ab.2 < t := by omega
        have ha_eq : Slist[b₀ + ab.1].H = (L'[ab.1]'(Nat.lt_trans ha' htb')).H := by
          dsimp [Slist]
          rw [List.getElem_append_right (by simp [b₀]), List.getElem_map]
          simp [b₀]
        have hb_eq : Slist[b₀ + ab.2].H = (L'[ab.2]'(Nat.lt_trans hb' htb')).H := by
          dsimp [Slist]
          rw [List.getElem_append_right (by simp [b₀]), List.getElem_map]
          simp [b₀]
        have ht_eq : Slist[t].H = (L'[t - b₀]'htb').H := by rw [hget]
        refine ⟨ha, hb, fun _ _ => ?_⟩
        rw [ha_eq, hb_eq, ht_eq]
        have perms := coplanarTriple_all_perms
          (wallHyperplanes_finrank hc_ne (by rw [← ht_eq]; exact hS_in ⟨t, ht⟩))
          (wallHyperplanes_finrank hc_ne (by rw [← ha_eq]; exact hS_in ⟨b₀ + ab.1, Nat.lt_trans ha ht⟩))
          (wallHyperplanes_finrank hc_ne (by rw [← hb_eq]; exact hS_in ⟨b₀ + ab.2, Nat.lt_trans hb ht⟩))
          hcop
        exact perms.2.2.1
  let steps : (t : Fin M) → DagOp t.1 := fun t =>
    match Slist[t.1].parents with
    | none => .free (piv t)
    | some (a, b) =>
      if ha : a < t.1 then
        if hb : b < t.1 then .ridge ⟨a, ha⟩ ⟨b, hb⟩
        else .free (piv t)
      else .free (piv t)
  have hsteps_none : ∀ t : Fin M, Slist[t.1].parents = none → steps t = .free (piv t) := by
    intro t h
    dsimp only [steps]
    rw [h]
  have hsteps_some : ∀ (t : Fin M) (a b : ℕ), Slist[t.1].parents = some (a, b) →
      a < t.1 ∧ b < t.1 ∧
      ∀ (ha : a < t.1) (hb : b < t.1),
        steps t = .ridge ⟨a, ha⟩ ⟨b, hb⟩ ∧
        CoplanarTriple (Slist[a]'(Nat.lt_trans ha t.2)).H (Slist[b]'(Nat.lt_trans hb t.2)).H Slist[t.1].H := by
    intro t a b hp_eq
    obtain ⟨ha, hb, hcop⟩ := hS_parents t a b hp_eq
    refine ⟨ha, hb, fun ha' hb' => ⟨?_, hcop ha' hb'⟩⟩
    dsimp only [steps]
    rw [hp_eq]
    simp only [ha', hb', ↓reduceDIte]
  have hpsi_ex : ∀ n : ℕ, n ≤ M →
      ∃ ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ,
        ∀ t : Fin M, t.1 < n →
          WithLp.toLp 2 (evalDagNormals steps ψ t) ≠ 0 ∧
          hp (WithLp.toLp 2 (evalDagNormals steps ψ t)) = Slist[t.1].H := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨fun _ _ => 0, fun t ht => False.elim (Nat.not_lt_zero _ ht)⟩
    | succ n ih =>
      intro hnp1
      have hn : n < M := hnp1
      obtain ⟨ψ₀, hψ₀⟩ := ih hn.le
      let tn : Fin M := ⟨n, hn⟩
      have hex_tn : ∃ ptn : Fin (dagArity (steps tn)) → ℝ,
          let prev : Fin n → Fin 4 → ℝ :=
            fun i => evalDagNormals steps ψ₀ ⟨i.1, Nat.lt_trans i.2 hn⟩
          let vec := evalDagStep (steps tn) prev ptn
          WithLp.toLp 2 vec ≠ 0 ∧ hp (WithLp.toLp 2 vec) = Slist[n].H := by
        cases hp_opt : Slist[n].parents with
        | none =>
          have hst : steps tn = DagOp.free (t := n) (piv tn) := hsteps_none tn hp_opt
          let rawParam : Fin (dagArity (DagOp.free (t := n) (piv tn))) → ℝ :=
            fun k => u tn ((piv tn).succAbove k) / u tn (piv tn)
          refine ⟨cast (by rw [hst.symm]) rawParam, ?_⟩
          dsimp only
          rw [evalDagStep_cast hst.symm]
          change WithLp.toLp 2 (freeVec (piv tn) rawParam) ≠ 0 ∧ _
          have hsm := freeVec_eq_smul (WithLp.ofLp (u tn)) (piv tn) (hpiv tn)
          have hlp : u tn = (u tn (piv tn)) • WithLp.toLp 2 (freeVec (piv tn) rawParam) := by
            apply PiLp.ext
            intro q
            exact congrFun hsm q
          refine ⟨fun h0 => hu_ne tn (by rw [hlp, h0, smul_zero]), ?_⟩
          have hhp : hp (WithLp.toLp 2 (freeVec (piv tn) rawParam)) = hp (u tn) := by
            rw [hlp, hp_smul (hpiv tn)]
          exact hhp.trans (hu_hp tn)
        | some ab =>
          rcases ab with ⟨a, b⟩
          obtain ⟨ha, hb, hsp⟩ := hsteps_some tn a b hp_opt
          obtain ⟨hst, hcop⟩ := hsp ha hb
          have haM : a < M := Nat.lt_trans ha hn
          have hbM : b < M := Nat.lt_trans hb hn
          have hA := hψ₀ ⟨a, haM⟩ ha
          have hB := hψ₀ ⟨b, hbM⟩ hb
          have hcop' : CoplanarTriple (hp (WithLp.toLp 2 (evalDagNormals steps ψ₀ ⟨a, haM⟩)))
              (hp (WithLp.toLp 2 (evalDagNormals steps ψ₀ ⟨b, hbM⟩))) (hp (u tn)) := by
            rw [hA.2, hB.2, hu_hp tn]
            exact hcop
          obtain ⟨s, α, hα0, hu_comb⟩ := exists_ridge_normal_combo (hu_ne tn) hcop'
          let rawParam : Fin (dagArity (DagOp.ridge (t := n) ⟨a, ha⟩ ⟨b, hb⟩)) → ℝ := fun _ => s
          refine ⟨cast (by rw [hst.symm]) rawParam, ?_⟩
          dsimp only
          have hvec_eq : evalDagStep (steps tn)
              (fun i : Fin n => evalDagNormals steps ψ₀ ⟨i.1, Nat.lt_trans i.2 hn⟩)
              (cast (by rw [hst.symm]) rawParam) =
              fun q => evalDagNormals steps ψ₀ ⟨a, haM⟩ q + s * evalDagNormals steps ψ₀ ⟨b, hbM⟩ q :=
            evalDagStep_cast hst.symm _ rawParam
          have hlp : u tn = α • WithLp.toLp 2 (evalDagStep (steps tn)
              (fun i : Fin n => evalDagNormals steps ψ₀ ⟨i.1, Nat.lt_trans i.2 hn⟩)
              (cast (by rw [hst.symm]) rawParam)) := by
            rw [hu_comb]
            apply PiLp.ext
            intro q
            rw [hvec_eq]
            dsimp [rawParam]
          refine ⟨fun h0 => hu_ne tn (by rw [hlp, h0, smul_zero]), ?_⟩
          rw [← hu_hp tn, hlp, hp_smul hα0]
      obtain ⟨ptn, hptn_ne, hptn_hp⟩ := hex_tn
      let ψ : (t : Fin M) → Fin (dagArity (steps t)) → ℝ := fun t =>
        if h : t = tn then cast (by rw [h]) ptn else ψ₀ t
      have hψ_tn : ψ tn = ptn := by simp [ψ]
      have hagree : ∀ s : Fin M, s.1 < n → ψ s = ψ₀ s := fun s hs => by
        have hne : s ≠ tn := fun h => by
          have : s.1 = n := congrArg Fin.val h
          omega
        simp [ψ, hne]
      have heval_lt : ∀ s : Fin M, s.1 < n →
          evalDagNormals steps ψ s = evalDagNormals steps ψ₀ s :=
        evalDagNormals_congr_lt steps ψ ψ₀ n hagree
      refine ⟨ψ, fun t hlt => ?_⟩
      by_cases htn : t.1 < n
      · rw [heval_lt t htn]
        exact hψ₀ t htn
      · have hteq : t = tn := Fin.ext (by dsimp [tn]; omega)
        subst hteq
        have hprev : (fun i : Fin tn.1 => evalDagNormals steps ψ ⟨i.1, Nat.lt_trans i.2 tn.2⟩) =
            (fun i : Fin n => evalDagNormals steps ψ₀ ⟨i.1, Nat.lt_trans i.2 hn⟩) := by
          funext i
          exact heval_lt ⟨i.1, Nat.lt_trans i.2 tn.2⟩ i.2
        have hstep_eq : evalDagNormals steps ψ tn = evalDagStep (steps tn)
            (fun i : Fin n => evalDagNormals steps ψ₀ ⟨i.1, Nat.lt_trans i.2 hn⟩) ptn := by
          rw [evalDagNormals_eq, hψ_tn, hprev]
        rw [hstep_eq]
        exact ⟨hptn_ne, hptn_hp⟩
  obtain ⟨ψ, hψ⟩ := hpsi_ex M le_rfl
  have harity_sum : (∑ t : Fin M, dagArity (steps t)) ≤ 33 := by
    have hsplit : (∑ t : Fin M, dagArity (steps t)) =
        M + 2 * (ℋ_free.card + freeCount L') := by
      have har_item : ∀ t : Fin M, dagArity (steps t) =
          1 + (if Slist[t.1].parents.isNone then 2 else 0) := by
        intro t
        cases hp_opt : Slist[t.1].parents with
        | none =>
          rw [hsteps_none t hp_opt]
          rfl
        | some ab =>
          obtain ⟨ha, hb, hst⟩ := hsteps_some t ab.1 ab.2 hp_opt
          rw [(hst ha hb).1]
          rfl
      rw [Finset.sum_congr rfl fun t _ => har_item t, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
      congr 1
      have hlist_sum : (∑ t : Fin M, if Slist[t.1].parents.isNone then 2 else 0) =
          2 * Slist.countP (fun item : TripleSeqItem => item.parents.isNone) := by
        let f_isNone : TripleSeqItem → ℕ := fun item => if item.parents.isNone then 2 else 0
        have hsum_gen : ∀ L : List TripleSeqItem,
            (L.map f_isNone).sum = 2 * L.countP (fun item => item.parents.isNone) := by
          intro L
          induction L with
          | nil => simp
          | cons x xs ih =>
            rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
            dsimp only [f_isNone]
            cases hx : x.parents with
            | none => simp; omega
            | some _ => simp
        exact (fin_sum_list_map Slist f_isNone).trans (hsum_gen Slist)
      have hcount : Slist.countP (·.parents.isNone) = ℋ_free.card + freeCount L' := by
        dsimp [Slist, freeCount]
        rw [List.countP_append]
        have hc1 : (Flist.map (fun H => (⟨H, none⟩ : TripleSeqItem))).countP (·.parents.isNone) =
            Flist.length := by
          rw [List.countP_eq_length.mpr (by intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨y, _, rfl⟩; simp), List.length_map]
        have hc2 : (L'.map (fun item => (⟨item.H, item.parents.map fun p => (b₀ + p.1, b₀ + p.2)⟩ : TripleSeqItem))).countP
            (·.parents.isNone) = L'.countP (·.parents.isNone) := by
          rw [List.countP_map]
          congr 1; funext item
          cases h : item.parents with
          | none => simp [h]
          | some _ => simp [h]
        rw [hc1, hc2, hb₀_eq]
      rw [hlist_sum, hcount]
    rw [hsplit, hM_eq]
    have hcard_le15 : ℋ.card ≤ 15 := wallHyperplanes_card_le c
    change ℋ.card ≤ 15 at hcard_le15
    by_cases h11 : ℋ.card ≤ 11
    · have hf1 : ℋ_free.card + Tset.card = ℋ.card := hsum_cards
      have hf2 : freeCount L' ≤ L'.length := List.countP_le_length
      rw [hL'_len] at hf2
      omega
    · have h12 : 12 ≤ ℋ.card := by omega
      obtain ⟨htick, h15_empty⟩ := ticket_counting hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq
        hF_min ℋ_free (fun H => Finset.mem_filter)
      have hfree_le := htick h12
      change ℋ_free.card ≤ (15 - ℋ.card) + (15 - ℋ.card) / 2 at hfree_le
      by_cases h15 : ℋ.card = 15
      · have he0 := h15_empty h15
        have hfc0 : ℋ_free.card = 0 := by rw [he0, Finset.card_empty]
        have hT15 : Tset.card = 15 := by omega
        have hfc1 := hL'_fc15 hT15
        omega
      · have h14 : ℋ.card ≤ 14 := by omega
        omega
  refine ⟨M, steps, ψ, hM_le15, harity_sum, fun t => ?_, fun H hH => ?_, fun x i hxK hx0 => ?_⟩
  · intro h0
    apply (hψ t t.2).1
    apply PiLp.ext
    intro q
    exact congrFun h0 q
  · obtain ⟨t, hteq⟩ := hH_mem_S H hH
    exact ⟨t, (hψ t t.2).2.trans hteq⟩
  · have hx_not_open : x ∉ Kopen c i := fun hopen => by
      obtain ⟨j, hj, hj0⟩ := hx0
      exact (hopen j hj).ne' hj0
    obtain ⟨H, hH, hxH⟩ :=
      wall_cover_of_facets hc_sym hc_ne hK_nonempty hK_cover hF_sub hF_eq hF_min x i hxK hx_not_open
    obtain ⟨t, hteq⟩ := hH_mem_S H hH
    have hx_hp : x ∈ hp (WithLp.toLp 2 (evalDagNormals steps ψ t)) := by
      rwa [(hψ t t.2).2.trans hteq]
    have hdot := (mem_hp_iff _ _).mp hx_hp
    refine ⟨t, ?_⟩
    simpa only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
      conj_trivial, WithLp.ofLp_toLp, mul_comm] using hdot

/-! ### Section 5: PlaneDagConfig, differentiability, and dimension bound -/

private structure PlaneDagConfig (d m : ℕ) where
  I : {I : Fin 4 → Fin d // Function.Injective I}
  M : Fin 16
  steps : {steps : (t : Fin M.1) → DagOp t.1 // (∑ t : Fin M.1, dagArity (steps t)) ≤ 33}
  piv : Fin M.1 → Fin 4
  σ : Fin m → Fin M.1

private instance instFinitePlaneDagConfig (d m : ℕ) : Finite (PlaneDagConfig d m) :=
  Finite.of_injective
    (fun c : PlaneDagConfig d m =>
      (⟨c.M, (c.I, c.steps, c.piv, c.σ)⟩ :
        (M : Fin 16) ×
          ({I : Fin 4 → Fin d // Function.Injective I} ×
           {steps : (t : Fin M.1) → DagOp t.1 // (∑ t : Fin M.1, dagArity (steps t)) ≤ 33} ×
           (Fin M.1 → Fin 4) ×
           (Fin m → Fin M.1))))
    (fun c₁ c₂ h => by
      cases c₁; cases c₂
      simp only [Sigma.mk.inj_iff] at h
      rcases h with ⟨rfl, h2⟩
      rw [heq_iff_eq] at h2
      simp only [Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl, rfl, rfl, rfl⟩
      rfl)

private abbrev PlaneDagParamIdx (d m : ℕ) (c : PlaneDagConfig d m) : Type :=
  (Fin 4 × {j : Fin d // ∀ s : Fin 4, c.I.1 s ≠ j}) ⊕
  ((t : Fin c.M.1) × Fin (dagArity (c.steps.1 t))) ⊕
  ((a : Fin m) × {j : Fin d // j ≠ c.I.1 (c.piv (c.σ a))})

private lemma card_planeDagParamIdx {d m : ℕ} (hd : 4 ≤ d) (c : PlaneDagConfig d m) :
    Fintype.card (PlaneDagParamIdx d m c) ≤ 4 * d + 17 + m * (d - 1) := by
  have h1 : Fintype.card {j : Fin d // ∀ s : Fin 4, c.I.1 s ≠ j} = d - 4 := by
    let sRest : Finset (Fin d) := Finset.univ \ Finset.univ.image c.I.1
    have heq : {j : Fin d // ∀ s : Fin 4, c.I.1 s ≠ j} ≃ {j : Fin d // j ∈ sRest} :=
      Equiv.subtypeEquivRight fun j => by simp [sRest, Finset.mem_sdiff, Finset.mem_image]
    rw [Fintype.card_congr heq, Fintype.card_coe]
    have hsub : Finset.univ.image c.I.1 ⊆ (Finset.univ : Finset (Fin d)) := Finset.subset_univ _
    dsimp [sRest]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ c.I.2, Finset.card_univ, Fintype.card_fin]
  have h2 : ∑ t : Fin c.M.1, dagArity (c.steps.1 t) ≤ 33 := c.steps.2
  have h3 : ∀ a : Fin m, Fintype.card {j : Fin d // j ≠ c.I.1 (c.piv (c.σ a))} = d - 1 := fun a => by
    have heq : {j : Fin d // j ≠ c.I.1 (c.piv (c.σ a))} ≃
        {j : Fin d // j ∈ Finset.univ.erase (c.I.1 (c.piv (c.σ a)))} :=
      Equiv.subtypeEquivRight fun j => by simp [Finset.mem_erase]
    rw [Fintype.card_congr heq, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  simp only [PlaneDagParamIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
    Fintype.card_fin, h1, h3, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

private def dagParamU {d m : ℕ} (c : PlaneDagConfig d m)
    (y : PlaneDagParamIdx d m c → ℝ) (r : Fin 4) (j : Fin d) : ℝ :=
  if _h : c.I.1 r = j then 1
  else if h' : ∃ s : Fin 4, c.I.1 s = j then 0
  else y (Sum.inl (r, ⟨j, fun s hs => h' ⟨s, hs⟩⟩))

private def dagParamPsi {d m : ℕ} (c : PlaneDagConfig d m)
    (y : PlaneDagParamIdx d m c → ℝ) (t : Fin c.M.1) :
    Fin (dagArity (c.steps.1 t)) → ℝ :=
  fun k => y (Sum.inr (Sum.inl ⟨t, k⟩))

private def dagParamC {d m : ℕ} (c : PlaneDagConfig d m)
    (y : PlaneDagParamIdx d m c → ℝ) (t : Fin c.M.1) (r : Fin 4) : ℝ :=
  evalDagNormals c.steps.1 (dagParamPsi c y) t r

private def dagParamN {d m : ℕ} (c : PlaneDagConfig d m)
    (y : PlaneDagParamIdx d m c → ℝ) (t : Fin c.M.1) (j : Fin d) : ℝ :=
  ∑ r : Fin 4, dagParamC c y t r * dagParamU c y r j

private def dagParamP0 {d m : ℕ} (c : PlaneDagConfig d m)
    (y : PlaneDagParamIdx d m c → ℝ) (a : Fin m) (j : Fin d) : ℝ :=
  if h : j = c.I.1 (c.piv (c.σ a)) then 0
  else y (Sum.inr (Sum.inr ⟨a, ⟨j, h⟩⟩))

private def planeDagOpen {d m : ℕ} (c : PlaneDagConfig d m) :
    Set (PlaneDagParamIdx d m c → ℝ) :=
  {y | ∀ t : Fin c.M.1, dagParamC c y t (c.piv t) ≠ 0}

private def planeDagMap {d m : ℕ} (c : PlaneDagConfig d m)
    (y : PlaneDagParamIdx d m c → ℝ) : Fin (m * d) → ℝ :=
  fun x =>
    let p := finProdFinEquiv.symm x
    if p.2 = c.I.1 (c.piv (c.σ p.1)) then
      (- ∑ j : Fin d, dagParamN c y (c.σ p.1) j * dagParamP0 c y p.1 j) /
        dagParamC c y (c.σ p.1) (c.piv (c.σ p.1))
    else
      dagParamP0 c y p.1 p.2

private lemma differentiableOn_planeDagMap {d m : ℕ} (c : PlaneDagConfig d m) :
    DifferentiableOn ℝ (planeDagMap c) (planeDagOpen c) := by
  have hu : ∀ r j, Differentiable ℝ fun y => dagParamU c y r j := fun r j => by
    dsimp [dagParamU]
    split_ifs
    · exact differentiable_const 1
    · exact differentiable_const 0
    · exact differentiable_apply _
  have hpsi : Differentiable ℝ fun y : PlaneDagParamIdx d m c → ℝ => dagParamPsi c y :=
    differentiable_pi.mpr fun t => differentiable_pi.mpr fun k => differentiable_apply _
  have hc : ∀ t r, Differentiable ℝ fun y => dagParamC c y t r := fun t r =>
    (differentiable_evalDagNormals c.steps.1 t r).comp hpsi
  have hn : ∀ t j, Differentiable ℝ fun y => dagParamN c y t j := fun t j =>
    Differentiable.fun_sum fun r _ => (hc t r).mul (hu r j)
  have hp0 : ∀ a j, Differentiable ℝ fun y => dagParamP0 c y a j := fun a j => by
    dsimp [dagParamP0]
    split_ifs
    · exact differentiable_const 0
    · exact differentiable_apply _
  refine differentiableOn_pi.mpr fun x => ?_
  dsimp [planeDagMap]
  split_ifs
  · simp_rw [div_eq_mul_inv]
    exact ((Differentiable.fun_sum fun j _ => (hn _ j).mul (hp0 _ j)).neg.differentiableOn).mul
      (((hc _ _).differentiableOn).inv fun y (hy : y ∈ planeDagOpen c) => hy _)
  · exact (hp0 _ _).differentiableOn




private lemma planeDagMap_eq_of_perp {d m : ℕ} (z : Fin (m * d) → ℝ)
    (cfg : PlaneDagConfig d m) (y : PlaneDagParamIdx d m cfg → ℝ)
    (hy_open : y ∈ planeDagOpen cfg)
    (hy_P0 : ∀ a j, dagParamP0 cfg y a j =
      if j = cfg.I.1 (cfg.piv (cfg.σ a)) then 0 else evalPoints z a j)
    (hy_N_piv : ∀ t : Fin cfg.M.1,
      dagParamN cfg y t (cfg.I.1 (cfg.piv t)) = dagParamC cfg y t (cfg.piv t))
    (hy_N_perp : ∀ a : Fin m,
      ∑ q : Fin d, dagParamN cfg y (cfg.σ a) q * evalPoints z a q = 0) :
    planeDagMap cfg y = z := by
  funext x
  obtain ⟨⟨a, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  let p := evalPoints z
  have hp_eq : p a j = z (finProdFinEquiv (a, j)) := rfl
  dsimp [planeDagMap]
  rw [finProdFinEquiv.symm_apply_apply]
  split_ifs with hj
  · have hj_eq : j = cfg.I.1 (cfg.piv (cfg.σ a)) := hj
    simp_rw [hy_P0]
    have hsplit : ∑ q : Fin d, dagParamN cfg y (cfg.σ a) q *
          (if q = cfg.I.1 (cfg.piv (cfg.σ a)) then 0 else p a q) =
        ∑ q ∈ Finset.univ.erase (cfg.I.1 (cfg.piv (cfg.σ a))),
          dagParamN cfg y (cfg.σ a) q * p a q := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (cfg.I.1 (cfg.piv (cfg.σ a))))]
      simp only [↓reduceIte, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun q hq => ?_
      simp [(Finset.mem_erase.mp hq).1]
    have hsplit_full : ∑ q : Fin d, dagParamN cfg y (cfg.σ a) q * p a q =
        dagParamN cfg y (cfg.σ a) (cfg.I.1 (cfg.piv (cfg.σ a))) *
            p a (cfg.I.1 (cfg.piv (cfg.σ a))) +
          ∑ q ∈ Finset.univ.erase (cfg.I.1 (cfg.piv (cfg.σ a))),
            dagParamN cfg y (cfg.σ a) q * p a q :=
      (Finset.add_sum_erase Finset.univ (fun q => dagParamN cfg y (cfg.σ a) q * p a q)
        (Finset.mem_univ (cfg.I.1 (cfg.piv (cfg.σ a))))).symm
    rw [hy_N_perp a, hy_N_piv (cfg.σ a)] at hsplit_full
    have hsum_neg : -(∑ q : Fin d, dagParamN cfg y (cfg.σ a) q *
          (if q = cfg.I.1 (cfg.piv (cfg.σ a)) then 0 else p a q)) =
        dagParamC cfg y (cfg.σ a) (cfg.piv (cfg.σ a)) *
          p a (cfg.I.1 (cfg.piv (cfg.σ a))) := by
      rw [hsplit]; linarith
    have hc0 : dagParamC cfg y (cfg.σ a) (cfg.piv (cfg.σ a)) ≠ 0 := hy_open (cfg.σ a)
    change (-∑ q : Fin d, dagParamN cfg y (cfg.σ a) q *
        (if q = cfg.I.1 (cfg.piv (cfg.σ a)) then 0 else p a q)) /
        dagParamC cfg y (cfg.σ a) (cfg.piv (cfg.σ a)) = z (finProdFinEquiv (a, j))
    rw [hsum_neg, mul_comm, mul_div_cancel_right₀ _ hc0, ← hj_eq, hp_eq]
  · have hj_ne : j ≠ cfg.I.1 (cfg.piv (cfg.σ a)) := hj
    rw [hy_P0, hp_eq]
    simp only [hj_ne, ↓reduceIte]

private lemma mem_range_planeDagMap_of_dag {d m : ℕ}
    (z : Fin (m * d) → ℝ)
    (hz_ball : ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1)
    (C : Fin 6 → Body d)
    (hcov : unitBall d = (⋃ i, (C i : Set (Ambient d))))
    (n : Fin 6 → Fin 6 → Ambient d)
    (hnsym : ∀ i j, n j i = - n i j)
    (hnne : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j → n i j ≠ 0)
    (hnsep : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      (∀ y ∈ (C i : Set (Ambient d)), 0 ≤ ⟪n i j, y⟫_ℝ) ∧
      (∀ x ∈ (C j : Set (Ambient d)), ⟪n i j, x⟫_ℝ ≤ 0))
    (hnint_pos : ∀ i ∈ nonEmptyIntParts C, ∀ j ∈ nonEmptyIntParts C, i ≠ j →
      ∀ y ∈ interior (C i : Set (Ambient d)), 0 < ⟪n i j, y⟫_ℝ)
    (hno_int : ∀ (k₁ : Fin 6) (a : Fin m), evalPoints z a ∉ interior (C k₁ : Set (Ambient d)))
    (I : Fin 4 → Fin d) (u : Fin 4 → Ambient d)
    (hI_inj : Function.Injective I)
    (hu_rref : ∀ r s : Fin 4, u r (I s) = if r = s then 1 else 0)
    (hcoef : ∀ k₁ l : Fin 6, ∀ j : Fin d, n k₁ l j = ∑ r : Fin 4, n k₁ l (I r) * u r j) :
    ∃ c : PlaneDagConfig d m, z ∈ planeDagMap c '' planeDagOpen c := by
  classical
  let p : Fin m → Ambient d := evalPoints z
  let S := nonEmptyIntParts C
  by_cases hfull : ∀ i : Fin 6, i ∈ S
  · let c : Fin 6 → Fin 6 → E4 := fun i j => WithLp.toLp 2 (fun r : Fin 4 => n i j (I r))
    let P_u : Ambient d → E4 := fun w => WithLp.toLp 2 (fun r : Fin 4 => ⟪u r, w⟫_ℝ)
    have hdot_Pu : ∀ (i j : Fin 6) (w : Ambient d), ⟪c i j, P_u w⟫_ℝ = ⟪n i j, w⟫_ℝ := by
      intro i j w
      calc ⟪c i j, P_u w⟫_ℝ
          = ∑ r : Fin 4, ⟪u r, w⟫_ℝ * n i j (I r) := by
              simp [c, P_u, PiLp.inner_apply]
        _ = ∑ r : Fin 4, n i j (I r) * ∑ q : Fin d, u r q * w q := by
              refine Finset.sum_congr rfl fun r _ => ?_
              simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
              rw [mul_comm (∑ q : Fin d, w q * u r q)]
              congr 1
              refine Finset.sum_congr rfl fun q _ => mul_comm _ _
        _ = ∑ r : Fin 4, ∑ q : Fin d, (n i j (I r) * u r q) * w q := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun q _ => by ring
        _ = ∑ q : Fin d, (∑ r : Fin 4, n i j (I r) * u r q) * w q := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun q _ => (Finset.sum_mul ..).symm
        _ = ⟪n i j, w⟫_ℝ := by
              simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [← hcoef i j q, mul_comm]
    have hc_sym : ∀ i j, c j i = -c i j := fun i j => by
      apply PiLp.ext
      intro r
      simp [c, hnsym i j]
    have hc_ne : ∀ i j, i ≠ j → c i j ≠ 0 := fun i j hij h0 => by
      have hne0 := hnne i (hfull i) j (hfull j) hij
      apply hne0
      apply PiLp.ext
      intro q
      rw [hcoef i j q]
      refine Finset.sum_eq_zero fun r _ => ?_
      have hr0 : n i j (I r) = 0 := by
        have := congrFun (congrArg WithLp.ofLp h0) r
        simpa [c] using this
      rw [hr0, zero_mul]
    have hK_nonempty : ∀ i : Fin 6, ∃ x : E4, ∀ j ≠ i, 0 < ⟪c i j, x⟫_ℝ := fun i => by
      have hi_int : (interior (C i : Set (Ambient d))).Nonempty :=
        (mem_nonEmptyIntParts C).mp (hfull i)
      obtain ⟨w₀, hw₀⟩ := hi_int
      refine ⟨P_u w₀, fun j hji => ?_⟩
      rw [hdot_Pu]
      exact hnint_pos i (hfull i) j (hfull j) hji.symm w₀ hw₀
    have hK_cover : ∀ x : E4, ∃ i : Fin 6, ∀ j ≠ i, 0 ≤ ⟪c i j, x⟫_ℝ := fun x => by
      let ιx : Ambient d := WithLp.toLp 2 (fun q : Fin d => ∑ s : Fin 4, if q = I s then x s else 0)
      have hPu_ι : P_u ιx = x := by
        apply PiLp.ext
        intro r
        dsimp [P_u]
        have hsum : ⟪u r, ιx⟫_ℝ = ∑ s : Fin 4, x s * ∑ q : Fin d, if q = I s then u r q else 0 := by
          simp only [ιx, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
          calc ∑ q : Fin d, (∑ s : Fin 4, if q = I s then x s else 0) * u r q
              = ∑ q : Fin d, ∑ s : Fin 4, x s * (if q = I s then u r q else 0) := by
                  refine Finset.sum_congr rfl fun q _ => ?_
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
            _ = ∑ s : Fin 4, ∑ q : Fin d, x s * (if q = I s then u r q else 0) := Finset.sum_comm
            _ = ∑ s : Fin 4, x s * ∑ q : Fin d, if q = I s then u r q else 0 := by
                  refine Finset.sum_congr rfl fun s _ => (Finset.mul_sum ..).symm
        have hinner_q : ∀ s : Fin 4,
            (∑ q : Fin d, if q = I s then u r q else 0) = u r (I s) := fun s => by
          rw [Finset.sum_eq_single (I s)]
          · simp
          · intro q _ hne; simp [hne]
          · intro hs; exact False.elim (hs (Finset.mem_univ _))
        rw [hsum]
        simp_rw [hinner_q, hu_rref]
        rw [Finset.sum_eq_single r]
        · simp
        · intro s _ hrs; simp [hrs.symm]
        · intro hr; exact False.elim (hr (Finset.mem_univ _))
      let δ : ℝ := (2 * (‖ιx‖ + 1))⁻¹
      have hδ_pos : 0 < δ := by positivity
      have hw0_mem : δ • ιx ∈ unitBall d := by
        rw [unitBall, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hδ_pos.le]
        dsimp [δ]
        have hden : 0 < 2 * (‖ιx‖ + 1) := by positivity
        calc (2 * (‖ιx‖ + 1))⁻¹ * ‖ιx‖ = ‖ιx‖ / (2 * (‖ιx‖ + 1)) := by ring
          _ ≤ (‖ιx‖ + 1) / (2 * (‖ιx‖ + 1)) := by
              refine div_le_div_of_nonneg_right (by linarith) hden.le
          _ = 1 / 2 := by
              have h1 : ‖ιx‖ + 1 ≠ 0 := by positivity
              field_simp [h1]
          _ ≤ 1 := by norm_num
      rw [hcov, Set.mem_iUnion] at hw0_mem
      obtain ⟨i, hi_mem⟩ := hw0_mem
      refine ⟨i, fun j hji => ?_⟩
      have hnonneg : 0 ≤ ⟪n i j, δ • ιx⟫_ℝ := (hnsep i (hfull i) j (hfull j) hji.symm).1 _ hi_mem
      rw [real_inner_smul_right] at hnonneg
      have hcx : ⟪c i j, x⟫_ℝ = ⟪n i j, ιx⟫_ℝ := by
        rw [← hPu_ι, hdot_Pu]
      rw [hcx]
      exact nonneg_of_mul_nonneg_right hnonneg hδ_pos
    obtain ⟨M, steps, ψ, hM_le15, harity_le33, hne_ψ, _hwall, hfacet_zero⟩ :=
      exists_dag_of_cones_r4 c hc_sym hc_ne hK_nonempty hK_cover
    have hpiv_ex : ∀ t : Fin M, ∃ r : Fin 4, evalDagNormals steps ψ t r ≠ 0 := fun t => by
      by_contra hnone
      push Not at hnone
      exact hne_ψ t (funext hnone)
    choose piv hpiv using hpiv_ex
    have hsig_ex : ∀ a : Fin m,
        ∃ t : Fin M, ∑ r : Fin 4, evalDagNormals steps ψ t r * P_u (p a) r = 0 := fun a => by
      have hp_unit : p a ∈ unitBall d := Metric.ball_subset_closedBall (hz_ball a)
      rw [hcov, Set.mem_iUnion] at hp_unit
      obtain ⟨i, hpi⟩ := hp_unit
      have hex_j : ∃ j ≠ i, p a ∈ (C j : Set (Ambient d)) := by
        by_contra hnone
        push Not at hnone
        let U₀ : Set (Ambient d) :=
          Metric.ball (0 : Ambient d) 1 \ ⋃ j ∈ Finset.univ.erase i, (C j : Set (Ambient d))
        have hS_closed : IsClosed (⋃ j ∈ Finset.univ.erase i, (C j : Set (Ambient d))) :=
          isClosed_biUnion_finset fun j _ => (C j).isClosed
        have hU₀_open : IsOpen U₀ := Metric.isOpen_ball.sdiff hS_closed
        have hU₀_mem : p a ∈ U₀ := by
          refine ⟨hz_ball a, ?_⟩
          rw [Set.mem_iUnion₂]
          rintro ⟨j, hj, hmem⟩
          exact hnone j (Finset.mem_erase.mp hj).1 hmem
        have hU₀_sub : U₀ ⊆ (C i : Set (Ambient d)) := fun w ⟨hw_ball, hw_not⟩ => by
          have hw_unit : w ∈ unitBall d := Metric.ball_subset_closedBall hw_ball
          rw [hcov, Set.mem_iUnion] at hw_unit
          obtain ⟨k, hwk⟩ := hw_unit
          by_cases hki : k = i
          · exact hki ▸ hwk
          · exfalso
            exact hw_not (Set.mem_iUnion₂.mpr ⟨k, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩, hwk⟩)
        exact hno_int i a (interior_maximal hU₀_sub hU₀_open hU₀_mem)
      obtain ⟨j, hji, hpj⟩ := hex_j
      have hxK : ∀ k ≠ i, 0 ≤ ⟪c i k, P_u (p a)⟫_ℝ := fun k hki => by
        rw [hdot_Pu]
        exact (hnsep i (hfull i) k (hfull k) hki.symm).1 (p a) hpi
      have hx0 : ⟪c i j, P_u (p a)⟫_ℝ = 0 := by
        rw [hdot_Pu]
        have hge : 0 ≤ ⟪n i j, p a⟫_ℝ := (hnsep i (hfull i) j (hfull j) hji.symm).1 (p a) hpi
        have hle : ⟪n i j, p a⟫_ℝ ≤ 0 := (hnsep i (hfull i) j (hfull j) hji.symm).2 (p a) hpj
        exact le_antisymm hle hge
      exact hfacet_zero (P_u (p a)) i hxK ⟨j, hji, hx0⟩
    choose σ hσ using hsig_ex
    let Mfin : Fin 16 := ⟨M, by omega⟩
    let cfg : PlaneDagConfig d m := ⟨⟨I, hI_inj⟩, Mfin, ⟨steps, harity_le33⟩, piv, σ⟩
    let y : PlaneDagParamIdx d m cfg → ℝ
      | Sum.inl (r, j) => u r j.1
      | Sum.inr (Sum.inl ⟨t, k⟩) => ψ t k
      | Sum.inr (Sum.inr ⟨a, j⟩) => p a j.1
    have hy_psi : dagParamPsi cfg y = ψ := rfl
    have hy_C : ∀ t r, dagParamC cfg y t r = evalDagNormals steps ψ t r := fun _ _ => rfl
    have hy_open : y ∈ planeDagOpen cfg := fun t => by
      rw [hy_C]
      exact hpiv t
    have hy_U : ∀ r j, dagParamU cfg y r j = u r j := fun r j => by
      dsimp [dagParamU, cfg]
      split_ifs with h1 h2
      · rw [← h1, hu_rref r r]; simp
      · obtain ⟨s, hs⟩ := h2
        have hrs : r ≠ s := fun h => h1 (h ▸ hs)
        rw [← hs, hu_rref r s]; simp [hrs]
      · rfl
    have hy_P0 : ∀ a j, dagParamP0 cfg y a j =
        if j = cfg.I.1 (cfg.piv (cfg.σ a)) then 0 else p a j := fun a j => by
      dsimp [dagParamP0, cfg]
      split_ifs <;> rfl
    have hy_N_piv : ∀ t : Fin cfg.M.1,
        dagParamN cfg y t (cfg.I.1 (cfg.piv t)) = dagParamC cfg y t (cfg.piv t) := fun t => by
      dsimp [dagParamN]
      simp_rw [hy_U]
      dsimp [cfg]
      simp_rw [hu_rref]
      rw [Finset.sum_eq_single (piv t)]
      · simp
      · intro r _ hr; simp [hr]
      · intro hr; exact False.elim (hr (Finset.mem_univ _))
    have hy_N_perp : ∀ a : Fin m,
        ∑ q : Fin d, dagParamN cfg y (cfg.σ a) q * p a q = 0 := fun a => by
      dsimp [dagParamN]
      simp_rw [hy_U, hy_C]
      calc ∑ q : Fin d, (∑ r : Fin 4, evalDagNormals steps ψ (σ a) r * u r q) * p a q
          = ∑ q : Fin d, ∑ r : Fin 4, evalDagNormals steps ψ (σ a) r * (u r q * p a q) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun r _ => by ring
        _ = ∑ r : Fin 4, ∑ q : Fin d, evalDagNormals steps ψ (σ a) r * (u r q * p a q) :=
              Finset.sum_comm
        _ = ∑ r : Fin 4, evalDagNormals steps ψ (σ a) r * ∑ q : Fin d, u r q * p a q := by
              refine Finset.sum_congr rfl fun r _ => (Finset.mul_sum ..).symm
        _ = ∑ r : Fin 4, evalDagNormals steps ψ (σ a) r * P_u (p a) r := by
              refine Finset.sum_congr rfl fun r _ => ?_
              have hpu : P_u (p a) r = ∑ q : Fin d, u r q * p a q := by
                dsimp [P_u]
                simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
              rw [← hpu]
        _ = 0 := hσ a
    exact ⟨cfg, y, hy_open, planeDagMap_eq_of_perp z cfg y hy_open hy_P0 hy_N_piv hy_N_perp⟩
  · push Not at hfull
    obtain ⟨i₀, hi₀⟩ := hfull
    let Tpairs : Finset Pairs6 := Finset.univ.filter fun e : Pairs6 => e.1.1 ∈ S ∧ e.1.2 ∈ S
    have hT_sub : Tpairs ⊆ Finset.univ.filter fun e : Pairs6 => e.1.1 ≠ i₀ ∧ e.1.2 ≠ i₀ := by
      intro e he
      obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hi₀ (h ▸ h1), fun h => hi₀ (h ▸ h2)⟩
    have hT_le10 : Tpairs.card ≤ 10 :=
      (Finset.card_le_card hT_sub).trans_eq (pairsAvoiding_one_card i₀)
    let Plist : List Pairs6 := Tpairs.toList
    let M : ℕ := Plist.length
    have hM_le10 : M ≤ 10 := by
      simpa [M, Plist] using hT_le10
    let Mfin : Fin 16 := ⟨M, by omega⟩
    have hpiv_ex : ∀ t : Fin Mfin.1, ∃ r : Fin 4,
        n Plist[t.1].1.1 Plist[t.1].1.2 (I r) ≠ 0 := fun t => by
      have hm : Plist[t.1] ∈ Tpairs := Finset.mem_toList.mp (List.getElem_mem t.2)
      obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hm
      have hne0 : n Plist[t.1].1.1 Plist[t.1].1.2 ≠ 0 :=
        hnne _ h1 _ h2 Plist[t.1].2.ne
      by_contra hnone
      push Not at hnone
      apply hne0
      apply PiLp.ext
      intro q
      rw [hcoef Plist[t.1].1.1 Plist[t.1].1.2 q]
      exact Finset.sum_eq_zero fun r _ => by rw [hnone r, zero_mul]
    choose piv hpiv using hpiv_ex
    let steps : (t : Fin Mfin.1) → DagOp t.1 := fun t => .free (piv t)
    have hsum_le33 : (∑ t : Fin Mfin.1, dagArity (steps t)) ≤ 33 := by
      have hsum3 : (∑ t : Fin Mfin.1, dagArity (steps t)) = 3 * Mfin.1 := by
        simp [steps, dagArity]
        ring
      rw [hsum3]
      change 3 * M ≤ 33
      omega
    have hsig_ex : ∀ a : Fin m,
        ∃ t : Fin Mfin.1, ⟪n Plist[t.1].1.1 Plist[t.1].1.2, p a⟫_ℝ = 0 := fun a => by
      obtain ⟨i, hiS, j, hjS, hij, hzero⟩ :=
        skeleton_in_separating_hyperplanes C hcov n hnsep hnsym (hz_ball a)
          (fun q hq => hno_int q a hq)
      have hmT : (⟨(i, j), hij⟩ : Pairs6) ∈ Plist :=
        Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS, hjS⟩)
      obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hmT
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa [hteq] using hzero
    choose σ hσ_zero using hsig_ex
    let cfg : PlaneDagConfig d m := ⟨⟨I, hI_inj⟩, Mfin, ⟨steps, hsum_le33⟩, piv, σ⟩
    let vψ : Fin Mfin.1 → Fin 3 → ℝ := fun t k =>
      n Plist[t.1].1.1 Plist[t.1].1.2 (I ((piv t).succAbove k)) /
        n Plist[t.1].1.1 Plist[t.1].1.2 (I (piv t))
    let y : PlaneDagParamIdx d m cfg → ℝ
      | Sum.inl (r, j) => u r j.1
      | Sum.inr (Sum.inl ⟨t, k⟩) => vψ t k
      | Sum.inr (Sum.inr ⟨a, j⟩) => p a j.1
    have hy_C : ∀ (t : Fin Mfin.1) (r : Fin 4),
        dagParamC cfg y t r = freeVec (piv t) (vψ t) r := fun t r => by
      dsimp [dagParamC]
      rw [evalDagNormals_eq]
      rfl
    have hy_open : y ∈ planeDagOpen cfg := fun t => by
      change dagParamC cfg y t (piv t) ≠ 0
      rw [hy_C, freeVec_self]
      exact one_ne_zero
    have hy_U : ∀ r j, dagParamU cfg y r j = u r j := fun r j => by
      dsimp [dagParamU, cfg]
      split_ifs with h1 h2
      · rw [← h1, hu_rref r r]; simp
      · obtain ⟨s, hs⟩ := h2
        have hrs : r ≠ s := fun h => h1 (h ▸ hs)
        rw [← hs, hu_rref r s]; simp [hrs]
      · rfl
    have hy_P0 : ∀ a j, dagParamP0 cfg y a j =
        if j = cfg.I.1 (cfg.piv (cfg.σ a)) then 0 else p a j := fun a j => by
      dsimp [dagParamP0, cfg]
      split_ifs <;> rfl
    have hy_N_piv : ∀ t : Fin cfg.M.1,
        dagParamN cfg y t (cfg.I.1 (cfg.piv t)) = dagParamC cfg y t (cfg.piv t) := fun t => by
      dsimp [dagParamN]
      simp_rw [hy_U]
      dsimp [cfg]
      simp_rw [hu_rref]
      rw [Finset.sum_eq_single (piv t)]
      · simp
      · intro r _ hr; simp [hr]
      · intro hr; exact False.elim (hr (Finset.mem_univ _))
    have hy_N_eq : ∀ (t : Fin cfg.M.1) (q : Fin d),
        dagParamN cfg y t q =
          (n Plist[t.1].1.1 Plist[t.1].1.2 (I (piv t)))⁻¹ *
            n Plist[t.1].1.1 Plist[t.1].1.2 q := fun t q => by
      dsimp [dagParamN]
      have hsm := freeVec_eq_smul
        (fun r : Fin 4 => n Plist[t.1].1.1 Plist[t.1].1.2 (I r)) (piv t) (hpiv t)
      have hC_eq : ∀ r : Fin 4, dagParamC cfg y t r =
          (n Plist[t.1].1.1 Plist[t.1].1.2 (I (piv t)))⁻¹ *
            n Plist[t.1].1.1 Plist[t.1].1.2 (I r) := fun r => by
        rw [hy_C]
        have h1 : n Plist[t.1].1.1 Plist[t.1].1.2 (I r) =
            n Plist[t.1].1.1 Plist[t.1].1.2 (I (piv t)) *
              freeVec (piv t) (vψ t) r := by
          exact congrFun hsm r
        have hp0 := hpiv t
        rw [h1]
        field_simp [hp0]
      simp_rw [hC_eq, hy_U]
      rw [hcoef Plist[t.1].1.1 Plist[t.1].1.2 q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hy_N_perp : ∀ a : Fin m,
        ∑ q : Fin d, dagParamN cfg y (cfg.σ a) q * p a q = 0 := fun a => by
      have hmul : ∀ q : Fin d, dagParamN cfg y (cfg.σ a) q * p a q =
          (n Plist[(σ a).1].1.1 Plist[(σ a).1].1.2 (I (piv (σ a))))⁻¹ *
            (n Plist[(σ a).1].1.1 Plist[(σ a).1].1.2 q * p a q) := fun q => by
        rw [hy_N_eq (σ a) q, mul_assoc]
      simp_rw [hmul, ← Finset.mul_sum]
      have hdot : ∑ q : Fin d, n Plist[(σ a).1].1.1 Plist[(σ a).1].1.2 q * p a q = 0 := by
        simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using hσ_zero a
      rw [hdot, mul_zero]
    exact ⟨cfg, y, hy_open, planeDagMap_eq_of_perp z cfg y hy_open hy_P0 hy_N_piv hy_N_perp⟩

/-- Unconditional existence of `5 * d` central blocking points in `unitBall d` (`18 ≤ d`). -/
theorem exists_isBlocking_5d (d : ℕ) (hd : 18 ≤ d) :
    ∃ p : Fin (5 * d) → Ambient d, IsBlocking p := by
  let m := 5 * d
  have hmd : 0 < m * d := by positivity
  have hm_prod : m * d = m * (d - 1) + m := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    ring
  let badA : Set (Fin (m * d) → ℝ) :=
    ⋃ c : PlaneDagConfig d m, planeDagMap c '' planeDagOpen c
  have hbadA_vol : (volume : Measure (Fin (m * d) → ℝ)) badA = 0 := by
    refine measure_iUnion_null fun c => ?_
    have hcard : Fintype.card (PlaneDagParamIdx d m c) < m * d := by
      have hle := card_planeDagParamIdx (by omega : 4 ≤ d) c
      rw [hm_prod]
      dsimp [m] at hle ⊢
      omega
    exact volume_image_eq_zero_of_card_lt hmd hcard (differentiableOn_planeDagMap c)
  let badB : Set (Fin (m * d) → ℝ) := ⋃ c : MaxRankConfig d m, maxRankMap c '' maxRankOpen c
  have hbadB_vol : (volume : Measure (Fin (m * d) → ℝ)) badB = 0 := by
    refine measure_iUnion_null fun c => ?_
    have hcard : Fintype.card (MaxRankParamIdx d m c) < m * d := by
      have hle := card_maxRankParamIdx c
      rw [hm_prod]
      dsimp [m] at hle ⊢
      omega
    exact volume_image_eq_zero_of_card_lt hmd hcard (differentiableOn_maxRankMap c)
  let bad : Set (Fin (m * d) → ℝ) := badA ∪ badB
  have hbad_vol : (volume : Measure (Fin (m * d) → ℝ)) bad = 0 := by
    rw [measure_union_null hbadA_vol hbadB_vol]
  let good : Set (Fin (m * d) → ℝ) :=
    {z | ∀ a : Fin m, evalPoints z a ∈ Metric.ball (0 : Ambient d) 1}
  have hgood_open : IsOpen good := by
    have heq : good = ⋂ a : Fin m, (fun z => evalPoints z a) ⁻¹' Metric.ball (0 : Ambient d) 1 := by
      ext z; simp [good]
    rw [heq]
    refine isOpen_iInter_of_finite fun a => Metric.isOpen_ball.preimage ?_
    exact (continuous_apply a).comp continuous_evalPoints
  have hzero_good : (0 : Fin (m * d) → ℝ) ∈ good := fun a => by
    have hev : evalPoints (0 : Fin (m * d) → ℝ) a = 0 := by
      apply PiLp.ext
      intro j
      rfl
    rw [hev]
    exact Metric.mem_ball_self zero_lt_one
  have hgood_pos : 0 < (volume : Measure (Fin (m * d) → ℝ)) good :=
    hgood_open.measure_pos volume ⟨0, hzero_good⟩
  have hnot_sub : ¬ good ⊆ bad := fun hsub => by
    have hle : (volume : Measure (Fin (m * d) → ℝ)) good ≤ volume bad := measure_mono hsub
    rw [hbad_vol] at hle
    exact (lt_of_lt_of_le hgood_pos hle).ne' rfl
  obtain ⟨z, hz_good, hz_not_bad⟩ := Set.not_subset.mp hnot_sub
  refine ⟨evalPoints z, ?_⟩
  by_contra hnot_block
  dsimp [IsBlocking] at hnot_block
  push Not at hnot_block
  obtain ⟨C, hcov, hdisj, h0, hno_int⟩ := hnot_block
  obtain ⟨n, _hnii, hnsym, hnnotS, hsep⟩ := exists_central_separating_normals C hdisj h0
  by_cases hindep : LinearIndependent ℝ (fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)
  · obtain ⟨hS_univ, htri⟩ := rank5_triangle_dependent C hcov n hnnotS
      (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.1,
        (hsep i hi j hj hij).2.2.2.1, (hsep i hi j hj hij).2.2.2.2⟩)
      hnsym hindep
    have hnz : ∀ i j : Fin 6, i ≠ j → n i j ≠ 0 := fun i j hij =>
      (hsep i (hS_univ ▸ Finset.mem_univ i) j (hS_univ ▸ Finset.mem_univ j) hij).1
    have htri' : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
        ∃ c₁ c₂ c₃ : ℝ, (c₁, c₂, c₃) ≠ 0 ∧ c₁ • n i j + c₂ • n j k + c₃ • n k i = 0 :=
        fun i j k hij hjk hik => by
      obtain ⟨c₁, c₂, c₃, hne, hcomb⟩ := htri i j k hij hjk hik
      refine ⟨c₁, c₂, c₃, ?_, hcomb⟩
      intro heq0
      rcases hne with h | h | h
      · exact h (congrArg Prod.fst heq0)
      · exact h (congrArg (fun p => p.2.1) heq0)
      · exact h (congrArg (fun p => p.2.2) heq0)
    have hdim : 5 ≤ Module.finrank ℝ
        (Submodule.span ℝ {x : Ambient d | ∃ i j : Fin 6, x = n i j}) := by
      have hle : Submodule.span ℝ (Set.range fun t : Fin 5 => ∑ j : Fin 6, n t.succ j) ≤
          Submodule.span ℝ {x : Ambient d | ∃ i j : Fin 6, x = n i j} := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨t, rfl⟩
        exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨t.succ, j, rfl⟩
      have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range fun t : Fin 5 => ∑ j : Fin 6, n t.succ j)) = 5 := by
        have h := (linearIndependent_iff_card_eq_finrank_span.mp hindep).symm
        simpa [Set.finrank, Fintype.card_fin] using h
      exact hcard.symm.le.trans (Submodule.finrank_mono hle)
    obtain ⟨sh, hsh_dim, hsh_val, θ, hθ⟩ :=
      exists_treeParam 5 (by norm_num) le_rfl (by omega) n hnsym hnz htri' hdim
    obtain ⟨c, hc⟩ := mem_range_maxRankMap_of_tree z hz_good C hcov n hnsym hS_univ hnz
      (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.2.1⟩)
      hno_int sh hsh_val hsh_dim θ hθ
    exact hz_not_bad (Or.inr (Set.mem_iUnion.mpr ⟨c, hc⟩))
  · obtain ⟨I, u, hI_inj, hu_rref, hcoef⟩ := separating_normals_in_rref4_span (by omega : 4 ≤ d)
      C hcov n hnnotS (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.1⟩)
      hnsym hindep
    obtain ⟨c, hc⟩ := mem_range_planeDagMap_of_dag z hz_good C hcov n
      hnsym (fun i hi j hj hij => (hsep i hi j hj hij).1)
      (fun i hi j hj hij => ⟨(hsep i hi j hj hij).2.1, (hsep i hi j hj hij).2.2.2.1⟩)
      (fun i hi j hj hij => (hsep i hi j hj hij).2.2.1)
      hno_int I u hI_inj hu_rref hcoef
    exact hz_not_bad (Or.inl (Set.mem_iUnion.mpr ⟨c, hc⟩))

private theorem convex_partition_from_base {d₀ d : ℕ} (hd₀ : 2 ≤ d₀) (hd : d₀ ≤ d)
    {g₀ : (Fin (5 * d₀) → ℝ) → (Fin (d₀ - 2) → ℝ)} (hg₀ : IsAlmostSixEmbedding g₀)
    {p : Fin (5 * d) → Ambient d} (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₁, hg₁⟩ := iterated_padding_from (d - d₀) hg₀
  obtain ⟨g, hg⟩ := reindex_almostSixEmbedding (by omega : 5 * d₀ + 5 * (d - d₀) = 5 * d)
    (by omega : (d₀ - 2) + (d - d₀) = d - 2) hg₁
  exact convex_partition_of_embedding_and_blocking (by omega) hg hp

/-- **`d ≥ 24` reduction with `5 * d - 4` central blocking markers**: pads Theorem A
`d - 8` times to `Δ^(5d-5) → ℝ^(d-2)` and transfers any central blocking set `p` via
Blaschke compactness (`exists_eta_of_isBlocking`) and `inwardDist`. -/
theorem convex_partition_counterexample_ge_24 (d : ℕ) (hd : 24 ≤ d)
    (p : Fin (5 * d - 4) → Ambient d) (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₀, hg₀⟩ := tverberg_counterexample
  obtain ⟨g₁, hg₁⟩ := iterated_padding_from (d - 8) hg₀
  obtain ⟨g, hg⟩ := reindex_almostSixEmbedding (by omega : 36 + 5 * (d - 8) = 5 * d - 4)
    (by omega : 6 + (d - 8) = d - 2) hg₁
  exact convex_partition_of_embedding_and_blocking (by omega) hg hp

/-- **Conditional `d ≥ 18` reduction (only `Δ⁸⁹ → ℝ¹⁶` remains open)**: in every
dimension `d ≥ 18`, `exists_isBlocking_5d` unconditionally supplies `5 * d` central
blocking markers, so an almost six-embedding `g₀ : Δ⁸⁹ → ℝ¹⁶` alone yields the
continuous-equipartition counterexample via join-padding `d - 18` times and
inward-distance transfer. -/
theorem convex_partition_counterexample_ge_18 (d : ℕ) (hd : 18 ≤ d)
    (g₀ : (Fin 90 → ℝ) → (Fin 16 → ℝ)) (hg₀ : IsAlmostSixEmbedding g₀) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨p, hp⟩ := exists_isBlocking_5d d hd
  exact convex_partition_from_base (by norm_num : 2 ≤ 18) hd hg₀ hp

/-- **`d ≥ 18` reduction to a safe compatible quadratic height table (`5402` features)**:
uses `exists_isBlocking_5d` unconditionally and `AkopyanResearch.exists_almostSix_of_safe_compatible_quadratic_table`. -/
theorem convex_partition_counterexample_ge_18_of_quadratic_table (d : ℕ) (hd : 18 ≤ d)
    (H : AkopyanResearch.MassSimplex → AkopyanResearch.TableWords → Fin 2 → ℝ)
    (hH : Continuous H)
    (hq : ∀ z t, (fun w => H z w t) ∈ AkopyanQuadratic.quadraticLabelSpace (Fin 15) (Fin 6))
    (hcompat : ∀ z i, z.val i = 0 → ∀ t, AkopyanQuadratic.IgnoresColor (fun w => H z w t) i)
    (hsafe : ∀ z : AkopyanResearch.MassSimplex, ∀ σ : AkopyanResearch.MatchingColumns,
      ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₀, hg_cont, hg_disj⟩ :=
    AkopyanResearch.exists_almostSix_of_safe_compatible_quadratic_table H hH hq hcompat hsafe
  exact convex_partition_counterexample_ge_18 d hd g₀ ⟨hg_cont.continuousOn, fun x hx hdisj =>
    hg_disj x hx hdisj⟩

/-- **`[AKS]`-free Convex Equipartition Transfer (`d ≥ 36`)**: In every dimension `d ≥ 36`,
using the unconditional fivefold join of Theorem A (`fivefold_tverberg_join`), `5 * d`
central blocking markers suffice without any external almost-six-embedding assumption. -/
theorem convex_partition_counterexample_ge_36 (d : ℕ) (hd : 36 ≤ d)
    (p : Fin (5 * d) → Ambient d) (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₀, hg₀⟩ := fivefold_tverberg_join
  exact convex_partition_from_base (by norm_num : 2 ≤ 36) hd hg₀ hp

/-- **Theorem B (completely unconditional, `d ≥ 36`)**: In every dimension `d ≥ 36`,
obtains `5 * d` central blocking markers unconditionally via `exists_isBlocking_5d`
(combining rank-4 RREF reduction and full rank-5 tree parametrization via
`exists_treeParam`), constructs an unconditional almost six-embedding `Δ^(5d-1) → ℝ^(d-2)`
from the fivefold join of Theorem A (`fivefold_tverberg_join`) plus join-padding, and
produces `d - 1` continuous functionals on convex bodies and an absolutely continuous
probability measure without equalizing convex six-partitions. -/
theorem convex_partition_counterexample (d : ℕ) (hd : 36 ≤ d) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨p, hp⟩ := exists_isBlocking_5d d (by omega)
  exact convex_partition_counterexample_ge_36 d hd p hp

end AkopyanSixfold
end
