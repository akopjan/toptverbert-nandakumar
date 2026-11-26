module

public import RequestProject.Construction.InnerCell

@[expose] public section

/-!
# The pyramid cells: affine coordinates and orientation determinant

`yv k A` is affine with linear part `yvL k A`; at the apex it equals the second unit vector;
the orientation determinant of the cell is `(1/dl)^5 * (∓30)`, with sign
`-(-1)^k` (resp. `(-1)^k` if `|A| = 3`).
-/

open Set Surgery Matrix

namespace Tverberg6R

noncomputable section

@[simp] lemma fcons6_1 {α : Type*} (a : α) (f : Fin 5 → α) : (Fin.cons a f : Fin 6 → α) 1 = f 0 :=
  rfl
@[simp] lemma fcons6_2 {α : Type*} (a : α) (f : Fin 5 → α) : (Fin.cons a f : Fin 6 → α) 2 = f 1 :=
  rfl
@[simp] lemma fcons6_3 {α : Type*} (a : α) (f : Fin 5 → α) : (Fin.cons a f : Fin 6 → α) 3 = f 2 :=
  rfl
@[simp] lemma fcons6_4 {α : Type*} (a : α) (f : Fin 5 → α) : (Fin.cons a f : Fin 6 → α) 4 = f 3 :=
  rfl
@[simp] lemma fcons6_5 {α : Type*} (a : α) (f : Fin 5 → α) : (Fin.cons a f : Fin 6 → α) 5 = f 4 :=
  rfl

/-- The coordinates `yv` in terms of `(alp, gam)`. -/
def ycoef (A : Finset (Fin 6)) (a : ℝ) (g : Fin 5 → ℝ) : Fin 6 → ℝ :=
  Fin.cons (5 * g 0) (fun t => g (tau A t) - g 0 + if t = 0 then a else 0)

lemma yv_eq_ycoef (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) :
    yv k A x = ycoef A (alp k x) (fun t => gam k A t x) := rfl

lemma ycoef_add (A : Finset (Fin 6)) (a a' : ℝ) (g g' : Fin 5 → ℝ) :
    ycoef A (a + a') (g + g') = ycoef A a g + ycoef A a' g' := by
  funext s
  refine Fin.cases ?_ (fun t => ?_) s
  · simp [ycoef]; ring
  · simp only [ycoef, Fin.cons_succ, Pi.add_apply]
    split_ifs <;> ring

lemma ycoef_smul (A : Finset (Fin 6)) (c a : ℝ) (g : Fin 5 → ℝ) :
    ycoef A (c * a) (c • g) = c • ycoef A a g := by
  funext s
  refine Fin.cases ?_ (fun t => ?_) s
  · simp [ycoef]; ring
  · simp only [ycoef, Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring

/-- Linear part of `alp`. -/
def alpL (k : Fin 6) (w : Fin 6 → ℝ) : ℝ := 6 * w k / dl

/-- Linear part of `gam`. -/
def gamL (k : Fin 6) (t : Fin 5) (w : Fin 6 → ℝ) : ℝ := (w (k.succAbove t) - w k) / dl

lemma alp_add (k : Fin 6) (x w : Fin 6 → ℝ) : alp k (x + w) = alp k x + alpL k w := by
  simp only [alp, alpL, Pi.add_apply]; ring

lemma gam_add (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) (x w : Fin 6 → ℝ) :
    gam k A t (x + w) = gam k A t x + gamL k t w := by
  have := dl_pos
  simp only [gam, alp, gamL, Pi.add_apply]
  field_simp
  ring

/-- Linear part of `yv`. -/
def yvL (k : Fin 6) (A : Finset (Fin 6)) : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun w := ycoef A (alpL k w) (fun t => gamL k t w)
  map_add' w w' := by
    rw [← ycoef_add]
    congr 1
    · simp only [alpL, Pi.add_apply]; ring
    · funext t; simp only [gamL, Pi.add_apply]; ring
  map_smul' c w := by
    rw [RingHom.id_apply, ← ycoef_smul]
    congr 1
    · simp only [alpL, Pi.smul_apply, smul_eq_mul]; ring
    · funext t; simp only [gamL, Pi.smul_apply, smul_eq_mul]; ring

lemma yvL_apply (k : Fin 6) (A : Finset (Fin 6)) (w : Fin 6 → ℝ) :
    yvL k A w = ycoef A (alpL k w) (fun t => gamL k t w) := rfl

lemma yv_add (k : Fin 6) (A : Finset (Fin 6)) (x w : Fin 6 → ℝ) :
    yv k A (x + w) = yv k A x + yvL k A w := by
  rw [yv_eq_ycoef, yv_eq_ycoef, yvL_apply, ← ycoef_add]
  congr 1
  · exact alp_add k x w
  · funext t; exact gam_add k A t x w

lemma continuous_yv (k : Fin 6) (A : Finset (Fin 6)) : Continuous (yv k A) := by
  refine continuous_pi fun s => ?_
  refine Fin.cases ?_ (fun t => ?_) s
  · simp only [yv, Fin.cons_zero]
    exact continuous_const.mul (continuous_gam k A 0)
  · simp only [yv, Fin.cons_succ]
    split_ifs
    · exact ((continuous_gam k A _).sub (continuous_gam k A 0)).add (continuous_alp k)
    · exact ((continuous_gam k A _).sub (continuous_gam k A 0)).add continuous_const

/-! ### The apex -/

lemma sum_ctr (k : Fin 6) (A : Finset (Fin 6)) : ∑ i, ctr k A i = 1 := by
  have := sum_succAbove k (ctr k A)
  rw [sum_ctr_succAbove, ctr_self] at this
  linarith

lemma sum_ehat : ∑ i : Fin 6, ehat i = 1 := by norm_num [ehat]

lemma sum_apex (k : Fin 6) (A : Finset (Fin 6)) : ∑ i, apex k A i = 1 := by
  simp only [apex, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ctr, sum_ehat, sum_bJ]
  ring

lemma alp_apex (k : Fin 6) (A : Finset (Fin 6)) : alp k (apex k A) = 1 := by
  have := dl_pos
  simp only [alp, apex, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ctr_self,
    bJ_self, ehat]
  field_simp
  ring

lemma gam_apex (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) : gam k A t (apex k A) = 0 := by
  have := dl_pos
  rw [gam, alp_apex]
  simp only [apex, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    bJ_succAbove, ehat]
  field_simp
  ring

lemma yv_apex (k : Fin 6) (A : Finset (Fin 6)) : yv k A (apex k A) = Pi.single 1 1 := by
  funext s
  refine Fin.cases ?_ (fun t => ?_) s
  · simp [yv, gam_apex]
  · simp only [yv, Fin.cons_succ, gam_apex, alp_apex]
    by_cases ht : t = 0
    · subst ht; simp
    · rw [if_neg ht, Pi.single_apply, if_neg]
      · ring
      · intro h; exact ht (Fin.succ_injective _ (h.trans Fin.succ_zero_eq_one.symm))

/-! ### The orientation determinant -/

/-- The integer frame columns. -/
def D1 (k : Fin 6) (A : Finset (Fin 6)) (i : Fin 5) : Fin 6 → ℝ :=
  ycoef A (6 * (Pi.single i.castSucc 1 - Pi.single 5 1 : Fin 6 → ℝ) k)
    (fun t => (Pi.single i.castSucc 1 - Pi.single 5 1 : Fin 6 → ℝ) (k.succAbove t) -
      (Pi.single i.castSucc 1 - Pi.single 5 1 : Fin 6 → ℝ) k)

lemma yvL_unitE (k : Fin 6) (A : Finset (Fin 6)) (i : Fin 5) :
    yvL k A (toBaryL (unitE i)) = (1 / dl) • D1 k A i := by
  rw [yvL_apply, toBaryL_unitE, D1, ← ycoef_smul]
  congr 1
  · simp only [alpL]; ring
  · funext t; simp only [gamL, Pi.smul_apply, smul_eq_mul]; ring

lemma det_snocMat_smul (c : ℝ) (D : Fin 5 → Fin 6 → ℝ) (v : Fin 6 → ℝ) :
    (snocMat (fun i => c • D i) v).det = c ^ 5 * (snocMat D v).det := by
  have h : snocMat (fun i => c • D i) v =
      snocMat D v * Matrix.diagonal (Fin.snoc (fun _ : Fin 5 => c) 1) := by
    ext s j
    rw [Matrix.mul_diagonal]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [snocMat]
    · simp [snocMat, Fin.snoc_castSucc, mul_comm]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, mul_comm]

lemma tau_of_three {A : Finset (Fin 6)} (h : A.card = 3) : tau A = Equiv.swap 1 2 := by
  simp [tau, h]

lemma tau_of_ne_three {A : Finset (Fin 6)} (h : A.card ≠ 3) : tau A = 1 := by
  simp [tau, h]

set_option maxHeartbeats 8000000 in
lemma det_D1 (k : Fin 6) (A : Finset (Fin 6)) :
    (snocMat (D1 k A) (Pi.single 1 1)).det =
      -(-1) ^ (k : ℕ) * 30 * (if A.card = 3 then -1 else 1) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by fin_cases k <;> simp
  by_cases hA : A.card = 3
  · have ht := tau_of_three hA
    rw [if_pos hA]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · have e : snocMat (D1 0 A) (Pi.single 1 1) = (!![(-5 : ℤ), 5, 0, 0, 0, 0; 6, 0, 0, 0, 0, 1; 0, -1, 0, 1, 0, 0; 0, -1, 1, 0, 0, 0; 0, -1, 0, 0, 1, 0; -1, -2, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(-5 : ℤ), 5, 0, 0, 0, 0; 6, 0, 0, 0, 0, 1; 0, -1, 0, 1, 0, 0; 0, -1, 1, 0, 0, 0; 0, -1, 0, 0, 1, 0; -1, -2, -1, -1, -1, 0]).det = 30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 1 A) (Pi.single 1 1) = (!![(5 : ℤ), -5, 0, 0, 0, 0; 0, 6, 0, 0, 0, 1; -1, 0, 0, 1, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), -5, 0, 0, 0, 0; 0, 6, 0, 0, 0, 1; -1, 0, 0, 1, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).det = -30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 2 A) (Pi.single 1 1) = (!![(5 : ℤ), 0, -5, 0, 0, 0; 0, 0, 6, 0, 0, 1; -1, 0, 0, 1, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), 0, -5, 0, 0, 0; 0, 0, 6, 0, 0, 1; -1, 0, 0, 1, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).det = 30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 3 A) (Pi.single 1 1) = (!![(5 : ℤ), 0, 0, -5, 0, 0; 0, 0, 0, 6, 0, 1; -1, 0, 1, 0, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), 0, 0, -5, 0, 0; 0, 0, 0, 6, 0, 1; -1, 0, 1, 0, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).det = -30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 4 A) (Pi.single 1 1) = (!![(5 : ℤ), 0, 0, 0, -5, 0; 0, 0, 0, 0, 6, 1; -1, 0, 1, 0, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 1, 0, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), 0, 0, 0, -5, 0; 0, 0, 0, 0, 6, 1; -1, 0, 1, 0, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 1, 0, 0; -2, -1, -1, -1, -1, 0]).det = 30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 5 A) (Pi.single 1 1) = (!![(10 : ℤ), 5, 5, 5, 5, 0; -6, -6, -6, -6, -6, 1; -1, 0, 1, 0, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(10 : ℤ), 5, 5, 5, 5, 0; -6, -6, -6, -6, -6, 1; -1, 0, 1, 0, 0, 0; -1, 1, 0, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0]).det = -30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
  · have ht := tau_of_ne_three hA
    rw [if_neg hA]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · have e : snocMat (D1 0 A) (Pi.single 1 1) = (!![(-5 : ℤ), 5, 0, 0, 0, 0; 6, 0, 0, 0, 0, 1; 0, -1, 1, 0, 0, 0; 0, -1, 0, 1, 0, 0; 0, -1, 0, 0, 1, 0; -1, -2, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(-5 : ℤ), 5, 0, 0, 0, 0; 6, 0, 0, 0, 0, 1; 0, -1, 1, 0, 0, 0; 0, -1, 0, 1, 0, 0; 0, -1, 0, 0, 1, 0; -1, -2, -1, -1, -1, 0]).det = -30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 1 A) (Pi.single 1 1) = (!![(5 : ℤ), -5, 0, 0, 0, 0; 0, 6, 0, 0, 0, 1; -1, 0, 1, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), -5, 0, 0, 0, 0; 0, 6, 0, 0, 0, 1; -1, 0, 1, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).det = 30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 2 A) (Pi.single 1 1) = (!![(5 : ℤ), 0, -5, 0, 0, 0; 0, 0, 6, 0, 0, 1; -1, 1, 0, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), 0, -5, 0, 0, 0; 0, 0, 6, 0, 0, 1; -1, 1, 0, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).det = -30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 3 A) (Pi.single 1 1) = (!![(5 : ℤ), 0, 0, -5, 0, 0; 0, 0, 0, 6, 0, 1; -1, 1, 0, 0, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), 0, 0, -5, 0, 0; 0, 0, 0, 6, 0, 1; -1, 1, 0, 0, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 0, 1, 0; -2, -1, -1, -1, -1, 0]).det = 30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 4 A) (Pi.single 1 1) = (!![(5 : ℤ), 0, 0, 0, -5, 0; 0, 0, 0, 0, 6, 1; -1, 1, 0, 0, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 1, 0, 0; -2, -1, -1, -1, -1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(5 : ℤ), 0, 0, 0, -5, 0; 0, 0, 0, 0, 6, 1; -1, 1, 0, 0, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 1, 0, 0; -2, -1, -1, -1, -1, 0]).det = -30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num
    · have e : snocMat (D1 5 A) (Pi.single 1 1) = (!![(10 : ℤ), 5, 5, 5, 5, 0; -6, -6, -6, -6, -6, 1; -1, 1, 0, 0, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0]).map (Int.cast) := by
        ext s j
        fin_cases s <;> fin_cases j <;> simp [snocMat, D1, ycoef, ht, Pi.single_apply,
          Fin.succAbove, Fin.lt_def, Fin.snoc, Equiv.swap_apply_def] <;> norm_num
      rw [e, ← Int.cast_det]
      have : (!![(10 : ℤ), 5, 5, 5, 5, 0; -6, -6, -6, -6, -6, 1; -1, 1, 0, 0, 0, 0; -1, 0, 1, 0, 0, 0; -1, 0, 0, 1, 0, 0; -1, 0, 0, 0, 1, 0]).det = 30 := by
        simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
      rw [this]; norm_num

end

end Tverberg6R
