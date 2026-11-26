module

public import RequestProject.Surgery.ShiftGood
public import RequestProject.Surgery.Avoid

@[expose] public section

/-!
# Separating zeros of different kernel classes, and clearing segments
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
variable {ι : Type*}

/-- At `x`, only obstacles with the kernel of `Qs j₀` vanish. -/
def Sep (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)) (G : ℝ × (Fin k → ℝ) → V) (j₀ : ι)
    (x : ℝ × (Fin k → ℝ)) : Prop :=
  ∀ i, LinearMap.ker (Qs i) ≠ LinearMap.ker (Qs j₀) → Qs i (G x) ≠ 0

/-- Shifting in the direction `t • d` for some small `t ≠ 0`. -/
lemma shift_choose [FiniteDimensional ℝ V] [Fintype ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    {U : Set (ℝ × (Fin k → ℝ))} (hU : IsOpen U) {F : ℝ × (Fin k → ℝ) → V}
    (hF : GoodMap Qs U F) {z : ℝ × (Fin k → ℝ)} (hz : z ∈ zeroPts Qs F) (d : V) :
    ∃ r > 0, Metric.closedBall z r ⊆ U ∧ (∀ p ∈ zeroPts Qs F, p ≠ z → r < dist p z) ∧
      ∃ t : ℝ, t ≠ 0 ∧
        GoodMap Qs U (shiftMap F z r (t • d)) ∧
        count Qs (shiftMap F z r (t • d)) = count Qs F ∧
        (∀ x, r / 2 ≤ dist x z → shiftMap F z r (t • d) x = F x) ∧
        (∀ y, dist y z < r / 4 →
          shiftMap F z r (t • d) y = F z + lin (frameAt F z) (y - z) + t • d) ∧
        (∀ j, Qs j (F z) = 0 → dist (z - secB (Qs j) (frameAt F z) (t • d)) z < r / 4) ∧
        (∀ j y, dist y z < r / 2 →
          (Qs j (shiftMap F z r (t • d) y) = 0 ↔
            Qs j (F z) = 0 ∧ y = z - secB (Qs j) (frameAt F z) (t • d))) := by
  obtain ⟨r, hr, hball, hfar, hev⟩ := shift_good hU hF hz
  refine ⟨r, hr, hball, hfar, ?_⟩
  have ht : Tendsto (fun t : ℝ => t • d) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0:ℝ) • d)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, hP, ht0⟩ := ((ht.eventually hev).and self_mem_nhdsWithin).exists
  exact ⟨t, ht0, hP⟩

/-- Common conclusions after a shift at `z`. -/
lemma shift_conclusions [FiniteDimensional ℝ V] [Fintype ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    {U : Set (ℝ × (Fin k → ℝ))} {F G : ℝ × (Fin k → ℝ) → V} (hF : GoodMap Qs U F)
    {z : ℝ × (Fin k → ℝ)} {j₀ : ι} (hz : Qs j₀ (F z) = 0) {r : ℝ} (hr : 0 < r) {u : V}
    (hball : Metric.closedBall z r ⊆ U) (hfar : ∀ p ∈ zeroPts Qs F, p ≠ z → r < dist p z)
    (hGF : ∀ x, r / 2 ≤ dist x z → G x = F x)
    (hG4 : ∀ y, dist y z < r / 4 → G y = F z + lin (frameAt F z) (y - z) + u)
    (hsm : ∀ j, Qs j (F z) = 0 → dist (z - secB (Qs j) (frameAt F z) u) z < r / 4)
    (hiff : ∀ j y, dist y z < r / 2 →
      (Qs j (G y) = 0 ↔ Qs j (F z) = 0 ∧ y = z - secB (Qs j) (frameAt F z) u)) :
    IsCompact (Metric.closedBall z (r / 2)) ∧ Metric.closedBall z (r / 2) ⊆ U ∧
      (∀ x ∉ Metric.closedBall z (r / 2), G x = F x) ∧
      z - secB (Qs j₀) (frameAt F z) u ∈ Metric.closedBall z (r / 2) ∧
      (∀ p ∈ zeroPts Qs F, p ≠ z → p ∉ Metric.closedBall z (r / 2)) ∧
      Qs j₀ (G (z - secB (Qs j₀) (frameAt F z) u)) = 0 ∧
      zsign (Qs j₀) G (z - secB (Qs j₀) (frameAt F z) u) = zsign (Qs j₀) F z := by
  have hd := hsm j₀ hz
  have hGaff : ∀ y, dist y z < r / 4 → G y = (F z + u) + lin (frameAt F z) (y - z) := by
    intro y hy; rw [hG4 y hy]; abel
  have hfr := isFrameAt_of_affine_ball hGaff hd
  refine ⟨isCompact_closedBall _ _, fun x hx => hball (Metric.mem_closedBall.2
      (by linarith [Metric.mem_closedBall.1 hx])), fun x hx => hGF x ?_,
    Metric.mem_closedBall.2 (by linarith), fun p hp hpz hpK => ?_,
    (hiff j₀ _ (by linarith)).2 ⟨hz, rfl⟩, ?_⟩
  · exact le_of_lt (not_le.1 fun h => hx (Metric.mem_closedBall.2 h))
  · have := hfar p hp hpz
    have := Metric.mem_closedBall.1 hpK
    linarith
  · simp only [zsign, frameAt_eq hfr]

/-- **Separation.** After a small shift at `z`, the zero of `Qs j₀` near `z` is separated. -/
theorem separate_good [FiniteDimensional ℝ V] [Fintype ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    (hrank : ∀ i j, LinearMap.ker (Qs i) ≠ LinearMap.ker (Qs j) →
      ∃ u ∈ LinearMap.ker (Qs j), Qs i u ≠ 0)
    {U : Set (ℝ × (Fin k → ℝ))} (hU : IsOpen U) {F : ℝ × (Fin k → ℝ) → V}
    (hF : GoodMap Qs U F) {z : ℝ × (Fin k → ℝ)} {j₀ : ι} (hz : Qs j₀ (F z) = 0) :
    ∃ G K z₁, GoodMap Qs U G ∧ count Qs G = count Qs F ∧ IsCompact K ∧ K ⊆ U ∧
      (∀ x ∉ K, G x = F x) ∧ z₁ ∈ K ∧ (∀ p ∈ zeroPts Qs F, p ≠ z → p ∉ K) ∧
      Qs j₀ (G z₁) = 0 ∧ Sep Qs G j₀ z₁ ∧ zsign (Qs j₀) G z₁ = zsign (Qs j₀) F z := by
  classical
  set a := frameAt F z
  -- the bad submodules
  let p : ι × ι → Submodule ℝ V := fun ii =>
    LinearMap.ker ((Qs ii.2) ∘ₗ (LinearMap.id - (linMap a) ∘ₗ (secBLin (Qs ii.1) a)))
  let s : Finset (ι × ι) := Finset.univ.filter fun ii =>
    Qs ii.1 (F z) = 0 ∧ Qs ii.2 (F z) = 0 ∧
      LinearMap.ker (Qs ii.2) ≠ LinearMap.ker (Qs ii.1)
  have hmem : ∀ ii v, v ∈ p ii ↔ Qs ii.2 (v - lin a (secB (Qs ii.1) a v)) = 0 := by
    intro ii v; rfl
  obtain ⟨d, hd⟩ := exists_not_mem_finset_submodule s p (by
    intro ii hii htop
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hii
    obtain ⟨u, hu, hne⟩ := hrank ii.2 ii.1 hii.2.2
    have : u ∈ p ii := by rw [htop]; exact Submodule.mem_top
    rw [hmem] at this
    have h0 : secB (Qs ii.1) a u = 0 := by
      rw [LinearMap.mem_ker] at hu
      simp [secB, hu, fromVec]; rfl
    rw [h0, lin_zero_right, sub_zero] at this
    exact hne this)
  obtain ⟨r, hr, hball, hfar, t, ht0, hGood, hcount, hGF, hG4, hsm, hiff⟩ :=
    shift_choose hU hF ⟨j₀, hz⟩ d
  obtain ⟨hK1, hK2, hK3, hK4, hK5, hK6, hK7⟩ :=
    shift_conclusions hF hz hr hball hfar hGF hG4 hsm hiff
  refine ⟨_, _, _, hGood, hcount, hK1, hK2, hK3, hK4, hK5, hK6, ?_, hK7⟩
  intro i hi
  by_cases h0 : Qs i (F z) = 0
  · have hii : (j₀, i) ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hz, h0, hi⟩
    have hnd := hd _ hii
    rw [hmem] at hnd
    rw [hG4 _ (hsm j₀ hz), sub_sub_cancel_left, lin_neg, map_add, map_add, h0, zero_add,
      map_neg, secB_smul, lin_smul]
    intro h
    apply hnd
    show Qs i (d - lin a (secB (Qs j₀) a d)) = 0
    have : t • Qs i (d - lin a (secB (Qs j₀) a d)) = 0 := by
      rw [map_sub, smul_sub, ← map_smul, ← map_smul, sub_eq_neg_add]; exact h
    exact (smul_eq_zero.1 this).resolve_left ht0
  · intro h
    exact h0 ((hiff i _ (by linarith [hsm j₀ hz])).1 h).1

end Surgery
