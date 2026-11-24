module

public import Solution
public import AkopyanResearch.Completion.ConcreteComparison
import all Solution

/-!
# The dimension-eighteen conclusion from the concrete lifting theorem

This module isolates the geometric implication from `RequiredRelativeLifting`.
All its spaces, comparison maps and chosen target sections are concrete.
`DimensionEighteen` applies the proved lifting theorem to obtain the
unconditional conclusion.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace AkopyanSixfold

/-- Conditional on the concrete relative lifting theorem, the required
ninety-vertex almost-six embedding exists. -/
theorem almostSix_ninety_of_relative_lifting
    (hLift : AkopyanResearch.ConcreteComparison.RequiredRelativeLifting) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ, IsAlmostSixEmbedding g := by
  obtain ⟨H, hH, hq, hcompat, hsafe⟩ :=
    AkopyanResearch.ConcreteComparison.exists_safe_table_of_required_lifting hLift
  obtain ⟨g, hg, hsep⟩ :=
    AkopyanResearch.exists_almostSix_of_safe_compatible_quadratic_table
      H hH hq hcompat hsafe
  exact ⟨g, hg.continuousOn, hsep⟩

/-- General convex equipartition transfer with full probability mass on the unit ball
(`mu (unitBall d) = 1`), proved using the existing construction in `Solution.lean`. -/
theorem convex_partition_of_embedding_and_blocking_unitBall_mass_one {d m : ℕ} (hd : 2 ≤ d)
    {g : (Fin m → ℝ) → (Fin (d - 2) → ℝ)} (hg : IsAlmostSixEmbedding g)
    {p : Fin m → Ambient d} (hp : IsBlocking p) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu (unitBall d) = 1 ∧
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
  let S : Set (Ambient d) := Metric.closedBall (0 : Ambient d) eta
  let mu : Measure (Ambient d) := (volume S)⁻¹ • volume.restrict S
  obtain ⟨hprob, hac, hpos, htop, hconc⟩ :=
    normalized_ball_measure_props (d := d) heta0 heta1
  have hS_pos : 0 < volume S :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self heta0⟩)
      (measure_mono Metric.ball_subset_closedBall)
  have hS_top : volume S < ⊤ := (isCompact_closedBall (0 : Ambient d) eta).measure_lt_top
  have hmu_S : mu S = 1 := by
    simp [mu, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self,
      ENNReal.inv_mul_cancel hS_pos.ne' hS_top.ne]
  have hmu_ball : mu (unitBall d) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hprob.measure_univ]
      exact measure_mono (Set.subset_univ _)
    · rw [← hmu_S]
      exact measure_mono (Metric.closedBall_subset_closedBall heta1.le)
  exact ⟨Phi, mu, hPhi_cont, hprob, hmu_ball, hac, fun C hC hfair =>
    hPhi_obstruct C hC (fair_meets_eta_ball heta1 hpos htop hconc hC hfair)⟩

/-- The full conclusion for `d > 17`, with the relative lifting input
displayed as a theorem argument for use by the unconditional wrapper. -/
theorem convex_partition_counterexample_gt_17_of_relative_lifting
    (d : ℕ) (hd : 17 < d)
    (hLift : AkopyanResearch.ConcreteComparison.RequiredRelativeLifting) :
    ∃ (Phi : Body d → Fin (d - 1) → ℝ) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu (unitBall d) = 1 ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d, IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g₀, hg₀⟩ := almostSix_ninety_of_relative_lifting hLift
  obtain ⟨p, hp⟩ := exists_isBlocking_5d d (by omega)
  obtain ⟨g₁, hg₁⟩ := iterated_padding_from (d - 18) hg₀
  obtain ⟨g, hg⟩ := reindex_almostSixEmbedding
    (by omega : 5 * 18 + 5 * (d - 18) = 5 * d)
    (by omega : (18 - 2) + (d - 18) = d - 2) hg₁
  exact convex_partition_of_embedding_and_blocking_unitBall_mass_one (by omega) hg hp

end AkopyanSixfold
