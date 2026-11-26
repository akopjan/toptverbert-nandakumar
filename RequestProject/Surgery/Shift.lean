module

public import RequestProject.Surgery.ZeroSet
public import Mathlib.Analysis.Normed.Group.Lemmas
public import RequestProject.Surgery.Cutoff

@[expose] public section

/-!
# Shifting zeros

Near an isolated zero `z` where `F` is affine with frame `a`, adding a small constant vector `u`
(cut off radially) moves the zero of `Q j ∘ F` to `z - secB (Q j) a u` and creates no other zeros.
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- The point `x` with `Q (lin a x) = Q u`. -/
noncomputable def secB (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a : Fin (k+1) → V) (u : V) :
    ℝ × (Fin k → ℝ) :=
  fromVec ((frameMat Q a)⁻¹.mulVec (Q u))

lemma Q_lin_secB {Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)} {a : Fin (k+1) → V}
    (h : (frameMat Q a).det ≠ 0) (u : V) : Q (lin a (secB Q a u)) = Q u := by
  rw [Q_lin, secB, toVec_fromVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit h),
    Matrix.one_mulVec]

lemma eq_secB_of {Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)} {a : Fin (k+1) → V}
    (h : (frameMat Q a).det ≠ 0) {u : V} {x : ℝ × (Fin k → ℝ)} (hx : Q (lin a x) = Q u) :
    x = secB Q a u := by
  have h2 : Q (lin a (x - secB Q a u)) = 0 := by
    have := lin_add a (x - secB Q a u) (secB Q a u)
    rw [sub_add_cancel] at this
    have e : lin a (x - secB Q a u) = lin a x - lin a (secB Q a u) := by
      rw [this]; abel
    rw [e, map_sub, hx, Q_lin_secB h, sub_self]
  rw [Q_lin_eq_zero_iff Q h] at h2
  exact sub_eq_zero.1 h2

lemma secB_smul (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a : Fin (k+1) → V) (c : ℝ) (u : V) :
    secB Q a (c • u) = c • secB Q a u := by
  simp only [secB, map_smul, Matrix.mulVec_smul, fromVec_smul]

lemma secB_add (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a : Fin (k+1) → V) (u v : V) :
    secB Q a (u + v) = secB Q a u + secB Q a v := by
  simp only [secB, map_add, Matrix.mulVec_add, fromVec_add]

/-- `secB` as a linear map. -/
noncomputable def secBLin (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a : Fin (k+1) → V) :
    V →ₗ[ℝ] ℝ × (Fin k → ℝ) where
  toFun := secB Q a
  map_add' := secB_add Q a
  map_smul' := secB_smul Q a

lemma continuous_secB [FiniteDimensional ℝ V] (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ))
    (a : Fin (k+1) → V) : Continuous (secB Q a) :=
  (secBLin Q a).continuous_of_finiteDimensional

lemma lin_neg (a : Fin (k+1) → V) (x : ℝ × (Fin k → ℝ)) : lin a (-x) = -lin a x := by
  have := lin_smul a (-1) x
  simpa using this

/-- The shifted map. -/
noncomputable def shiftMap (F : ℝ × (Fin k → ℝ) → V) (z : ℝ × (Fin k → ℝ)) (r : ℝ) (u : V) :
    ℝ × (Fin k → ℝ) → V :=
  fun y => F y + cutRad (r / 2) (dist y z) • u

lemma continuous_shiftMap {F : ℝ × (Fin k → ℝ) → V} (hF : Continuous F) (z : ℝ × (Fin k → ℝ))
    (r : ℝ) (u : V) : Continuous (shiftMap F z r u) := by
  unfold shiftMap
  exact hF.add (((continuous_cutRad _).comp (continuous_id.dist continuous_const)).smul
    continuous_const)

lemma shiftMap_eq_of_le {F : ℝ × (Fin k → ℝ) → V} {z : ℝ × (Fin k → ℝ)} {r : ℝ} (hr : 0 < r)
    (u : V) {y : ℝ × (Fin k → ℝ)} (hy : r / 2 ≤ dist y z) : shiftMap F z r u y = F y := by
  simp [shiftMap, cutRad_eq_zero (by linarith : (0:ℝ) < r / 2) hy]

/-- **Shift lemma.** -/
theorem shift_spec [FiniteDimensional ℝ V] {ι : Type*} [Finite ι]
    (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)) (F : ℝ × (Fin k → ℝ) → V) (hF : Continuous F)
    (z : ℝ × (Fin k → ℝ)) (a : Fin (k+1) → V) {r : ℝ} (hr : 0 < r)
    (haff : ∀ x, ‖x‖ < r → F (z + x) = F z + lin a x)
    (hiso : ∀ j y, Qs j (F y) = 0 → dist y z < r → y = z)
    (htr : ∀ j, Qs j (F z) = 0 → (frameMat (Qs j) a).det ≠ 0) :
    ∀ᶠ u in 𝓝 (0:V),
      (∀ y, dist y z < r / 4 → shiftMap F z r u y = F z + lin a (y - z) + u) ∧
      (∀ j, Qs j (F z) = 0 → dist (z - secB (Qs j) a u) z < r / 4) ∧
      (∀ j y, dist y z < r / 2 →
        (Qs j (shiftMap F z r u y) = 0 ↔ Qs j (F z) = 0 ∧ y = z - secB (Qs j) a u)) := by
  have hFy : ∀ y, dist y z < r → F y = F z + lin a (y - z) := by
    intro y hy
    have := haff (y - z) (by rwa [← dist_eq_norm])
    rwa [add_sub_cancel] at this
  -- per-obstacle smallness
  have hj : ∀ j, ∀ᶠ u in 𝓝 (0:V),
      (Qs j (F z) = 0 → ‖secB (Qs j) a u‖ < r / 4) ∧
      (Qs j (F z) ≠ 0 → ∀ y, dist y z ≤ r / 2 → ‖Qs j u‖ < ‖Qs j (F y)‖) := by
    intro j
    by_cases h0 : Qs j (F z) = 0
    · have hc : Continuous (secB (Qs j) a) := continuous_secB _ _
      have : ∀ᶠ u in 𝓝 (0:V), ‖secB (Qs j) a u‖ < r / 4 := by
        have h := hc.tendsto 0
        have h00 : secB (Qs j) a 0 = 0 := by simp [secB, fromVec]; rfl
        rw [h00] at h
        exact h.eventually (eventually_norm_sub_lt _ (by linarith : (0:ℝ) < r / 4)
          |>.mono fun x hx => by simpa using hx)
      exact this.mono fun u hu => ⟨fun _ => hu, fun h => absurd h0 h⟩
    · -- minimum of `‖Qs j ∘ F‖` on the closed ball
      have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z _
      have hne : (Metric.closedBall z (r / 2)).Nonempty :=
        ⟨z, Metric.mem_closedBall_self (by linarith)⟩
      have hcont : ContinuousOn (fun y => ‖Qs j (F y)‖) (Metric.closedBall z (r / 2)) :=
        (continuous_norm.comp ((Qs j).continuous_of_finiteDimensional.comp hF)).continuousOn
      obtain ⟨y0, hy0, hmin⟩ := hK.exists_isMinOn hne hcont
      have hm : 0 < ‖Qs j (F y0)‖ := by
        rw [norm_pos_iff]
        intro h
        have := hiso j y0 h (lt_of_le_of_lt (Metric.mem_closedBall.1 hy0) (by linarith))
        rw [this] at h; exact h0 h
      have hcQ : Continuous (Qs j) := (Qs j).continuous_of_finiteDimensional
      have : ∀ᶠ u in 𝓝 (0:V), ‖Qs j u‖ < ‖Qs j (F y0)‖ := by
        have h := hcQ.tendsto 0
        rw [map_zero] at h
        exact h.eventually (eventually_norm_sub_lt _ hm |>.mono fun x hx => by simpa using hx)
      refine this.mono fun u hu => ⟨fun h => absurd h h0, fun _ y hy => ?_⟩
      exact lt_of_lt_of_le hu (hmin (Metric.mem_closedBall.2 hy))
  have hall := (Filter.eventually_all.2 hj)
  refine hall.mono fun u hu => ?_
  have hG : ∀ y, dist y z < r / 4 → shiftMap F z r u y = F z + lin a (y - z) + u := by
    intro y hy
    simp only [shiftMap]
    rw [cutRad_eq_one (by linarith) (by linarith), one_smul, hFy y (by linarith)]
  have hsm : ∀ j, Qs j (F z) = 0 → dist (z - secB (Qs j) a u) z < r / 4 := by
    intro j h0
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact (hu j).1 h0
  refine ⟨hG, hsm, fun j y hy => ?_⟩
  by_cases h0 : Qs j (F z) = 0
  · simp only [h0, true_and]
    constructor
    · intro hzero
      set c := cutRad (r / 2) (dist y z) with hc
      have hc01 := cutRad_mem (r / 2) (dist y z)
      have e : Qs j (lin a (y - z)) = Qs j ((-c) • u) := by
        have := hzero
        simp only [shiftMap, hFy y (by linarith), map_add, h0, zero_add, map_smul] at this
        rw [map_smul, neg_smul, ← eq_neg_iff_add_eq_zero.2 this]
      have hx := eq_secB_of (htr j h0) e
      rw [secB_smul] at hx
      have hn : dist y z < r / 4 := by
        rw [dist_eq_norm, hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hc01.1]
        calc c * ‖secB (Qs j) a u‖ ≤ 1 * ‖secB (Qs j) a u‖ :=
              mul_le_mul_of_nonneg_right hc01.2 (norm_nonneg _)
          _ < r / 4 := by rw [one_mul]; exact (hu j).1 h0
      have hc1 : c = 1 := cutRad_eq_one (by linarith) (by linarith)
      rw [hc1, neg_one_smul] at hx
      rw [sub_eq_iff_eq_add.1 hx]; abel
    · intro hy'
      have hd : dist y z < r / 4 := by rw [hy']; exact hsm j h0
      rw [hG y hd, hy', sub_sub_cancel_left, lin_neg, map_add, map_add, h0, map_neg,
        Q_lin_secB (htr j h0)]
      abel
  · simp only [h0, false_and, iff_false]
    intro hzero
    have hc01 := cutRad_mem (r / 2) (dist y z)
    simp only [shiftMap, map_add, map_smul] at hzero
    have h1 := (hu j).2 h0 y hy.le
    have : ‖Qs j (F y)‖ ≤ ‖Qs j u‖ := by
      rw [eq_neg_of_add_eq_zero_left hzero, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hc01.1]
      calc cutRad (r / 2) (dist y z) * ‖Qs j u‖ ≤ 1 * ‖Qs j u‖ :=
            mul_le_mul_of_nonneg_right hc01.2 (norm_nonneg _)
        _ = ‖Qs j u‖ := one_mul _
    linarith

end Surgery
