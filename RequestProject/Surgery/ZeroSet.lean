module

public import RequestProject.Surgery.Transport

@[expose] public section

/-!
# Local frames and signs of zeros

* `IsFrameAt F z a`: near `z`, `F` is affine with linear part `lin a`;
* `frameAt F z`: the (unique) such frame, if it exists;
* `zsign Q F z`: the sign of `det (Q ∘ lin (frameAt F z))`;
* `exists_factor_of_ker_eq`: maps with the same kernel differ by a matrix.
-/

open Set

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- Near `z`, `F` is affine with linear part `lin a`. -/
def IsFrameAt (F : ℝ × (Fin k → ℝ) → V) (z : ℝ × (Fin k → ℝ)) (a : Fin (k+1) → V) : Prop :=
  ∃ r > 0, ∀ x, ‖x‖ < r → F (z + x) = F z + lin a x

lemma lin_unitE (a : Fin (k+1) → V) (i : Fin (k+1)) : lin a (unitE i) = a i := by
  simp only [lin, unitE, toVec_fromVec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma IsFrameAt.unique {F : ℝ × (Fin k → ℝ) → V} {z : ℝ × (Fin k → ℝ)} {a a' : Fin (k+1) → V}
    (h : IsFrameAt F z a) (h' : IsFrameAt F z a') : a = a' := by
  obtain ⟨r, hr, hF⟩ := h
  obtain ⟨r', hr', hF'⟩ := h'
  funext i
  set c : ℝ := min r r' / (2 * (‖unitE (k := k) i‖ + 1)) with hc
  have hcpos : 0 < c := by positivity
  have hsmall : ‖c • unitE (k := k) i‖ < min r r' := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc]
    have h1 : 0 < ‖unitE (k := k) i‖ + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (unitE (k := k) i), lt_min hr hr']
  have e := (hF _ (lt_of_lt_of_le hsmall (min_le_left _ _))).symm.trans
    (hF' _ (lt_of_lt_of_le hsmall (min_le_right _ _)))
  rw [add_right_inj, lin_smul, lin_smul, lin_unitE, lin_unitE] at e
  exact smul_right_injective V hcpos.ne' e

open Classical in
/-- The local frame of `F` at `z` (junk value `0` if there is none). -/
noncomputable def frameAt (F : ℝ × (Fin k → ℝ) → V) (z : ℝ × (Fin k → ℝ)) : Fin (k+1) → V :=
  if h : ∃ a, IsFrameAt F z a then h.choose else 0

lemma frameAt_eq {F : ℝ × (Fin k → ℝ) → V} {z : ℝ × (Fin k → ℝ)} {a : Fin (k+1) → V}
    (h : IsFrameAt F z a) : frameAt F z = a := by
  have hex : ∃ a, IsFrameAt F z a := ⟨a, h⟩
  rw [frameAt, dif_pos hex]
  exact hex.choose_spec.unique h

lemma IsFrameAt.congr {F G : ℝ × (Fin k → ℝ) → V} {z : ℝ × (Fin k → ℝ)} {a : Fin (k+1) → V}
    (h : IsFrameAt F z a) {ρ : ℝ} (hρ : 0 < ρ) (hFG : ∀ x, ‖x‖ < ρ → G (z + x) = F (z + x)) :
    IsFrameAt G z a := by
  obtain ⟨r, hr, hF⟩ := h
  refine ⟨min r ρ, lt_min hr hρ, fun x hx => ?_⟩
  have h0 := hFG 0 (by simpa using hρ)
  rw [add_zero] at h0
  rw [hFG x (lt_of_lt_of_le hx (min_le_right _ _)), h0, hF x (lt_of_lt_of_le hx (min_le_left _ _))]

/-- The sign of a zero of `Q ∘ F` at `z`. -/
noncomputable def zsign (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (F : ℝ × (Fin k → ℝ) → V)
    (z : ℝ × (Fin k → ℝ)) : ℤ :=
  (SignType.sign (frameMat Q (frameAt F z)).det : ℤ)

/-- Two maps onto `ℝ^n` with the same kernel differ by a matrix (given a right inverse of the
first, here provided by a frame with invertible matrix). -/
lemma exists_factor_of_ker_eq (Q Q' : V →ₗ[ℝ] (Fin (k+1) → ℝ)) {a : Fin (k+1) → V}
    (ha : (frameMat Q a).det ≠ 0) (hker : LinearMap.ker Q = LinearMap.ker Q') :
    ∃ A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ, ∀ v, Q' v = A.mulVec (Q v) := by
  set M := frameMat Q a
  -- section of `Q`
  let sec : (Fin (k+1) → ℝ) → V := fun y => lin a (fromVec (M⁻¹.mulVec y))
  have hsec : ∀ y, Q (sec y) = y := by
    intro y
    simp only [sec]
    rw [Q_lin, toVec_fromVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit ha),
      Matrix.one_mulVec]
  refine ⟨frameMat Q' a * M⁻¹, fun v => ?_⟩
  have hv : v - sec (Q v) ∈ LinearMap.ker Q := by
    rw [LinearMap.mem_ker, map_sub, hsec, sub_self]
  rw [hker, LinearMap.mem_ker, map_sub, sub_eq_zero] at hv
  rw [hv]
  simp only [sec]
  rw [Q_lin, toVec_fromVec, Matrix.mulVec_mulVec]

/-- Same-kernel maps have proportional signs at a zero. -/
lemma sign_det_frameMat_of_ker_eq (Q Q' : V →ₗ[ℝ] (Fin (k+1) → ℝ)) {a : Fin (k+1) → V}
    (ha : (frameMat Q a).det ≠ 0) (hker : LinearMap.ker Q = LinearMap.ker Q') :
    ∃ s : ℝ, ∀ c : Fin (k+1) → V, (frameMat Q' c).det = s * (frameMat Q c).det := by
  obtain ⟨A, hA⟩ := exists_factor_of_ker_eq Q Q' ha hker
  refine ⟨A.det, fun c => ?_⟩
  have : frameMat Q' c = A * frameMat Q c := by
    ext r i
    simp only [frameMat, Matrix.of_apply, hA, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [this, Matrix.det_mul]

end Surgery
