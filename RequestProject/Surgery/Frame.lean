module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Lift
public import RequestProject.Surgery.GLPath

@[expose] public section

/-!
# Frames

A *frame* is a family `c : Fin (k+1) → V`; it acts on `ℝ × ℝ^k` by
`lin c (w, v) = w • c 0 + ∑ v i • c (i+1)`.  For a linear map `Q : V → ℝ^(k+1)` the matrix
`frameMat Q c` records `Q ∘ lin c`.

* `Surgery.exists_frame_path`: two frames whose `Q`-matrices have determinants of the same sign
  can be joined by a continuous family of frames with invertible `Q`-matrices.
-/

open Set

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- `(w, v) ↦ (w, v₀, …, v_{k-1})`. -/
def toVec (x : ℝ × (Fin k → ℝ)) : Fin (k+1) → ℝ := Fin.cons x.1 x.2

lemma toVec_add (x y : ℝ × (Fin k → ℝ)) : toVec (x + y) = toVec x + toVec y := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [toVec]

lemma toVec_smul (a : ℝ) (x : ℝ × (Fin k → ℝ)) : toVec (a • x) = a • toVec x := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [toVec]

lemma toVec_eq_zero_iff (x : ℝ × (Fin k → ℝ)) : toVec x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have hs : ∀ i, x.2 i = 0 := fun i => by simpa [toVec] using congrFun h i.succ
    ext
    · simpa [toVec] using h0
    · exact hs _
  · rintro rfl; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [toVec]

lemma abs_toVec_le (x : ℝ × (Fin k → ℝ)) (i : Fin (k+1)) : |toVec x i| ≤ ‖x‖ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [toVec, Fin.cons_zero]
    exact (Real.norm_eq_abs x.1 ▸ norm_fst_le x)
  · simp only [toVec, Fin.cons_succ]
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm x.2 i).trans (norm_snd_le x)

lemma continuous_toVec : Continuous (toVec (k := k)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [toVec, Fin.cons_zero]; fun_prop
  · simp only [toVec, Fin.cons_succ]; fun_prop

/-- The linear map of a frame. -/
noncomputable def lin (c : Fin (k+1) → V) (x : ℝ × (Fin k → ℝ)) : V := ∑ i, toVec x i • c i

lemma lin_add (c : Fin (k+1) → V) (x y : ℝ × (Fin k → ℝ)) :
    lin c (x + y) = lin c x + lin c y := by
  simp [lin, toVec_add, add_smul, Finset.sum_add_distrib]

lemma lin_smul (c : Fin (k+1) → V) (a : ℝ) (x : ℝ × (Fin k → ℝ)) :
    lin c (a • x) = a • lin c x := by
  simp [lin, toVec_smul, Finset.smul_sum, smul_smul]

lemma lin_mk (c : Fin (k+1) → V) (w : ℝ) (v : Fin k → ℝ) :
    lin c (w, v) = lin c (w, 0) + lin c (0, v) := by
  rw [← lin_add]; simp

lemma lin_zero_right (c : Fin (k+1) → V) : lin c 0 = 0 := by
  simpa using lin_smul c 0 0

lemma norm_lin_le (c : Fin (k+1) → V) (x : ℝ × (Fin k → ℝ)) :
    ‖lin c x‖ ≤ (∑ i, ‖c i‖) * ‖x‖ := by
  unfold lin
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_toVec_le x i) (norm_nonneg _)

lemma continuous_lin :
    Continuous (fun p : (Fin (k+1) → V) × (ℝ × (Fin k → ℝ)) => lin p.1 p.2) := by
  unfold lin
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp (continuous_toVec.comp continuous_snd)).smul
    ((continuous_apply i).comp continuous_fst)

/-- Negating the first frame vector. -/
lemma lin_update_neg (c : Fin (k+1) → V) (w : ℝ) (v : Fin k → ℝ) :
    lin (Function.update c 0 (-c 0)) (w, v) = lin c (-w, v) := by
  simp [lin, Fin.sum_univ_succ, toVec, Function.update_of_ne (Fin.succ_ne_zero _)]

/-- The matrix of `Q ∘ lin c`. -/
def frameMat (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (c : Fin (k+1) → V) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℝ := Matrix.of fun r i => Q (c i) r

lemma Q_lin (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (c : Fin (k+1) → V) (x : ℝ × (Fin k → ℝ)) :
    Q (lin c x) = (frameMat Q c).mulVec (toVec x) := by
  ext r
  simp [lin, frameMat, Matrix.mulVec, dotProduct, mul_comm]

lemma Q_lin_eq_zero_iff (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) {c : Fin (k+1) → V}
    (h : (frameMat Q c).det ≠ 0) (x : ℝ × (Fin k → ℝ)) : Q (lin c x) = 0 ↔ x = 0 := by
  rw [Q_lin, ← toVec_eq_zero_iff]
  constructor
  · intro hx
    have := congrArg (fun y => (frameMat Q c)⁻¹.mulVec y) hx
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit h)] using this
  · intro hx; rw [hx]; simp

lemma frameMat_update_neg (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (c : Fin (k+1) → V) :
    (frameMat Q (Function.update c 0 (-c 0))).det = -(frameMat Q c).det := by
  have : frameMat Q (Function.update c 0 (-c 0)) =
      (frameMat Q c).updateCol 0 ((-1 : ℝ) • (fun r => frameMat Q c r 0)) := by
    ext r i
    by_cases hi : i = 0
    · subst hi; simp [frameMat]
    · simp [frameMat, hi]
  rw [this, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]; ring

lemma frameMat_add (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (c d : Fin (k+1) → V) :
    frameMat Q (c + d) = frameMat Q c + frameMat Q d := by
  ext; simp [frameMat]

lemma frameMat_smul (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a : ℝ) (c : Fin (k+1) → V) :
    frameMat Q (a • c) = a • frameMat Q c := by
  ext; simp [frameMat]

/-- **Frame paths.** -/
lemma exists_frame_path (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a b : Fin (k+1) → V)
    (hdet : 0 < (frameMat Q a).det * (frameMat Q b).det) :
    ∃ J : ℝ → (Fin (k+1) → V), Continuous J ∧ (∀ u ≤ 0, J u = a) ∧ (∀ u, 1 ≤ u → J u = b) ∧
      ∀ u, (frameMat Q (J u)).det ≠ 0 := by
  have ha : (frameMat Q a).det ≠ 0 := by
    intro h; rw [h, zero_mul] at hdet; exact lt_irrefl _ hdet
  -- a right inverse of `Q`
  let sec : (Fin (k+1) → ℝ) → V := fun y => ∑ i, ((frameMat Q a)⁻¹.mulVec y) i • a i
  have hsec : ∀ y, Q (sec y) = y := by
    intro y
    have : Q (sec y) = (frameMat Q a).mulVec ((frameMat Q a)⁻¹.mulVec y) := by
      ext r; simp [sec, frameMat, Matrix.mulVec, dotProduct, mul_comm]
    rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit ha), Matrix.one_mulVec]
  have hsec_cont : Continuous sec := by
    unfold sec
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).smul
      continuous_const
  let lift : Matrix (Fin (k+1)) (Fin (k+1)) ℝ → (Fin (k+1) → V) :=
    fun M i => sec (fun r => M r i)
  have hlift : ∀ M, frameMat Q (lift M) = M := by
    intro M; ext r i; simp [frameMat, lift, hsec]
  have hlift0 : lift 0 = 0 := by
    ext i
    have : (fun r => (0 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) r i) = 0 := rfl
    simp only [lift, sec, this, Matrix.mulVec_zero, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero]
  have hlift_cont : Continuous lift := by
    apply continuous_pi; intro i
    exact hsec_cont.comp (continuous_pi fun r => (continuous_apply i).comp (continuous_apply r))
  obtain hjoin := Surgery.joinedIn_gl_of_det_mul_pos hdet
  let γ := hjoin.somePath
  let θ : ℝ → ℝ := fun u => max 0 (min u 1)
  have hθ : ∀ u, θ u ∈ Icc (0:ℝ) 1 := fun u => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  let J : ℝ → (Fin (k+1) → V) := fun u =>
    (1 - θ u) • a + θ u • b +
      lift (γ.extend (θ u) - (1 - θ u) • frameMat Q a - θ u • frameMat Q b)
  have hJmat : ∀ u, frameMat Q (J u) = γ.extend (θ u) := by
    intro u
    simp only [J, frameMat_add, frameMat_smul, hlift]
    abel
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · have hθc : Continuous θ := by fun_prop
    exact ((continuous_const.sub hθc).smul continuous_const).add (hθc.smul continuous_const) |>.add
      (hlift_cont.comp (((γ.continuous_extend.comp hθc).sub
        ((continuous_const.sub hθc).smul continuous_const)).sub (hθc.smul continuous_const)))
  · intro u hu
    have : θ u = 0 := by simp [θ, min_eq_left (hu.trans zero_le_one), hu]
    simp [J, this, hlift0]
  · intro u hu
    have : θ u = 1 := by simp [θ, min_eq_right hu]
    simp [J, this, hlift0]
  · intro u
    rw [hJmat]
    have hmem : γ.extend (θ u) ∈ glSet k := by
      rw [Path.extend_extends' γ ⟨θ u, hθ u⟩]
      exact hjoin.somePath_mem _
    exact hmem

end Surgery
