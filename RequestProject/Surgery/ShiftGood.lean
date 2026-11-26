module

public import RequestProject.Surgery.Good

@[expose] public section

/-!
# Shifting a zero of a good map keeps it good
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
variable {ι : Type*}

/-- Frames of affine maps on balls. -/
lemma isFrameAt_of_affine_ball {G : ℝ × (Fin k → ℝ) → V} {z : ℝ × (Fin k → ℝ)} {ρ : ℝ}
    {c : V} {a : Fin (k+1) → V} (hG : ∀ y, dist y z < ρ → G y = c + lin a (y - z))
    {x : ℝ × (Fin k → ℝ)} (hx : dist x z < ρ) : IsFrameAt G x a := by
  refine ⟨ρ - dist x z, by linarith, fun v hv => ?_⟩
  have h1 : dist (x + v) z < ρ := by
    calc dist (x + v) z ≤ dist (x + v) x + dist x z := dist_triangle _ _ _
      _ = ‖v‖ + dist x z := by rw [dist_eq_norm, add_sub_cancel_left]
      _ < ρ := by linarith
  rw [hG _ h1, hG _ hx]
  have : x + v - z = (x - z) + v := by abel
  rw [this, lin_add, add_assoc]

/-- An isolating radius at a point of a finite set. -/
lemma exists_isolating_radius {S : Set (ℝ × (Fin k → ℝ))} (hS : S.Finite) (z : ℝ × (Fin k → ℝ)) :
    ∃ r > 0, ∀ p ∈ S, p ≠ z → r ≤ dist p z := by
  have hc : IsClosed (S \ {z}) := (hS.diff).isClosed
  have hz : z ∈ (S \ {z})ᶜ := by simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hc.isOpen_compl z hz
  refine ⟨r, hr, fun p hp hpz => ?_⟩
  by_contra h
  push_neg at h
  exact hball (Metric.mem_ball.2 h) ⟨hp, hpz⟩

/-- **Shifting a zero point of a good map.** -/
theorem shift_good [FiniteDimensional ℝ V] [Fintype ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    {U : Set (ℝ × (Fin k → ℝ))} (hU : IsOpen U) {F : ℝ × (Fin k → ℝ) → V}
    (hF : GoodMap Qs U F) {z : ℝ × (Fin k → ℝ)} (hz : z ∈ zeroPts Qs F) :
    ∃ r > 0, Metric.closedBall z r ⊆ U ∧ (∀ p ∈ zeroPts Qs F, p ≠ z → r < dist p z) ∧
      ∀ᶠ u in 𝓝 (0:V),
        GoodMap Qs U (shiftMap F z r u) ∧ count Qs (shiftMap F z r u) = count Qs F ∧
        (∀ x, r / 2 ≤ dist x z → shiftMap F z r u x = F x) ∧
        (∀ y, dist y z < r / 4 → shiftMap F z r u y = F z + lin (frameAt F z) (y - z) + u) ∧
        (∀ j, Qs j (F z) = 0 → dist (z - secB (Qs j) (frameAt F z) u) z < r / 4) ∧
        (∀ j y, dist y z < r / 2 →
          (Qs j (shiftMap F z r u y) = 0 ↔
            Qs j (F z) = 0 ∧ y = z - secB (Qs j) (frameAt F z) u)) := by
  obtain ⟨j₀, hj₀⟩ := hz
  set a := frameAt F z with ha_def
  obtain ⟨⟨a', ha'⟩, -⟩ := hF.frame j₀ z hj₀
  have ha : IsFrameAt F z a := by rw [ha_def, frameAt_eq ha']; exact ha'
  obtain ⟨r1, hr1, haff1⟩ := ha
  obtain ⟨r2, hr2, hiso2⟩ := exists_isolating_radius hF.zeroPts_finite z
  obtain ⟨r3, hr3, hU3⟩ := Metric.isOpen_iff.1 hU z (hF.sub j₀ z hj₀)
  set r := min r1 (min r2 r3) / 2 with hr_def
  have hr : 0 < r := by positivity
  have hrr1 : r < r1 := by
    have := min_le_left r1 (min r2 r3); rw [hr_def]; linarith [lt_min hr1 (lt_min hr2 hr3)]
  have hrr2 : r < r2 := by
    have := min_le_right r1 (min r2 r3)
    have := min_le_left r2 r3; rw [hr_def]; linarith [lt_min hr1 (lt_min hr2 hr3)]
  have hrr3 : r < r3 := by
    have := min_le_right r1 (min r2 r3)
    have := min_le_right r2 r3; rw [hr_def]; linarith [lt_min hr1 (lt_min hr2 hr3)]
  have hball : Metric.closedBall z r ⊆ U := fun x hx =>
    hU3 (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hx) hrr3))
  have hfar : ∀ p ∈ zeroPts Qs F, p ≠ z → r < dist p z := fun p hp hpz =>
    lt_of_lt_of_le hrr2 (hiso2 p hp hpz)
  have haff : ∀ x, ‖x‖ < r → F (z + x) = F z + lin a x := fun x hx => haff1 x (by linarith)
  have hiso : ∀ j y, Qs j (F y) = 0 → dist y z < r → y = z := by
    intro j y hy hd
    by_contra hyz
    exact absurd (hfar y ⟨j, hy⟩ hyz) (not_lt.2 hd.le)
  have htr : ∀ j, Qs j (F z) = 0 → (frameMat (Qs j) a).det ≠ 0 := fun j h => (hF.frame j z h).2
  refine ⟨r, hr, hball, hfar, ?_⟩
  refine (shift_spec Qs F hF.cont z a hr haff hiso htr).mono fun u ⟨hG4, hsm, hiff⟩ => ?_
  set G := shiftMap F z r u with hG_def
  set K := Metric.closedBall z (r / 2) with hK_def
  have hGF : ∀ x ∉ K, G x = F x := fun x hx =>
    shiftMap_eq_of_le hr u (le_of_lt (not_le.1 fun h => hx (Metric.mem_closedBall.2 h)))
  have hGF' : ∀ x, r / 2 ≤ dist x z → G x = F x := fun x hx => shiftMap_eq_of_le hr u hx
  have hKU : K ⊆ U := fun x hx =>
    hball (Metric.mem_closedBall.2 (by linarith [Metric.mem_closedBall.1 hx]))
  -- zeros in `K`
  have hGK : ∀ j, zeros Qs G j ∩ K = {x | Qs j (F z) = 0 ∧ x = z - secB (Qs j) a u} := by
    intro j; ext x
    simp only [zeros, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hx, hxK⟩
      have hlt : dist x z < r / 2 := by
        rcases lt_or_eq_of_le (Metric.mem_closedBall.1 hxK) with h | h
        · exact h
        · exfalso
          rw [hGF' x h.ge] at hx
          have := hiso j x hx (by linarith)
          rw [this, dist_self] at h; linarith
      exact (hiff j x hlt).1 hx
    · rintro ⟨h0, rfl⟩
      have hd := hsm j h0
      exact ⟨(hiff j _ (by linarith)).2 ⟨h0, rfl⟩, Metric.mem_closedBall.2 (by linarith)⟩
  have hFK : ∀ j, zeros Qs F j ∩ K = {x | Qs j (F z) = 0 ∧ x = z} := by
    intro j; ext x
    simp only [zeros, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hx, hxK⟩
      have := hiso j x hx (by linarith [Metric.mem_closedBall.1 hxK])
      subst this; exact ⟨hx, rfl⟩
    · rintro ⟨h0, rfl⟩
      exact ⟨h0, Metric.mem_closedBall_self (by linarith)⟩
  have hGaff : ∀ y, dist y z < r / 4 → G y = (F z + u) + lin a (y - z) := by
    intro y hy; rw [hG4 y hy]; abel
  have hframe : ∀ j, Qs j (F z) = 0 → IsFrameAt G (z - secB (Qs j) a u) a := fun j h0 =>
    isFrameAt_of_affine_ball hGaff (hsm j h0)
  have hGc : Continuous G := continuous_shiftMap hF.cont z r u
  have hGood : GoodMap Qs U G := by
    refine hF.transfer hGc Metric.isClosed_closedBall hKU hGF ?_ ?_ ?_
    · intro j
      rw [hGK j]
      exact (Set.finite_singleton (z - secB (Qs j) a u)).subset fun x hx => hx.2
    · intro j x hxK hx
      have hx' : x ∈ zeros Qs G j ∩ K := ⟨hx, hxK⟩
      rw [hGK j] at hx'
      obtain ⟨h0, rfl⟩ := hx'
      exact ⟨⟨a, hframe j h0⟩, by rw [frameAt_eq (hframe j h0)]; exact htr j h0⟩
    · intro j
      rw [hGK j, hFK j]
      by_cases h0 : Qs j (F z) = 0
      · simp only [h0, true_and, setOf_eq_eq_singleton, finsum_mem_singleton]
        simp only [zsign, frameAt_eq (hframe j h0)]
        rfl
      · simp [h0]
  refine ⟨hGood, ?_, hGF', hG4, hsm, hiff⟩
  unfold count
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := ncard_zeros_eq (Qs := Qs) hGF j (hF.fin j) (hGood.fin j)
  rw [hGK j, hFK j] at h
  by_cases h0 : Qs j (F z) = 0
  · simp only [h0, true_and, setOf_eq_eq_singleton, ncard_singleton] at h; omega
  · simp only [h0, false_and, setOf_false, ncard_empty] at h; omega

end Surgery
