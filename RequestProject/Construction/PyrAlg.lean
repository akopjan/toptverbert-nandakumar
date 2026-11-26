module

public import RequestProject.Construction.Local
public import RequestProject.Construction.Indep

@[expose] public section

/-!
# `F0` on a pyramid
-/

open Set Surgery

namespace Tverberg6R

noncomputable section

/-! ### Linearity of `H⁰` -/

/-- `H⁰` as a linear map. -/
def H0L (q : Fin 6 → Fin 6 → ℝ) : (Fin 6 → ℝ) →ₗ[ℝ] Table where
  toFun := H0 q
  map_add' a b := by funext w; simp [H0, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by funext w; simp [H0, mul_assoc, Finset.mul_sum]

lemma H0L_apply (q : Fin 6 → Fin 6 → ℝ) (l : Fin 6 → ℝ) : H0L q l = H0 q l := rfl

lemma H0_compat (q : Fin 6 → Fin 6 → ℝ) {y : Fin 6 → ℝ} {i : Fin 6} (hy : y i = 0)
    {u v : Word} (huv : ∀ j, j ≠ i → u j = v j) : H0 q y u = H0 q y v := by
  simp only [H0]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp [hy]
  · rw [huv j hj]

lemma ell_smul (m : Fin 6 → Word) (c : ℝ) (T : Table) : ell m (c • T) = c • ell m T := by
  funext r; simp [ell, mul_sub]

lemma ell_add (m : Fin 6 → Word) (T T' : Table) : ell m (T + T') = ell m T + ell m T' := by
  funext r; simp [ell]; ring

lemma ell_sub (m : Fin 6 → Word) (T T' : Table) : ell m (T - T') = ell m T - ell m T' := by
  funext r; simp [ell]; ring

/-! ### The value permutation on positions -/

/-- Positions permutation (`swap 1 2` for `|A| = 3`). -/
def tau (A : Finset (Fin 6)) : Equiv.Perm (Fin 5) :=
  if A.card = 3 then Equiv.swap 1 2 else 1

lemma sig_succAbove_tau (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) :
    sig k A (k.succAbove (tau A t)) = k.succAbove t := by
  unfold sig tau
  split_ifs with h
  · by_cases h1 : t = 1
    · subst h1; simp
    by_cases h2 : t = 2
    · subst h2; simp
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
    · exact fun e => h1 (Fin.succAbove_right_injective e)
    · exact fun e => h2 (Fin.succAbove_right_injective e)
  · rfl

lemma tau_zero (A : Finset (Fin 6)) : tau A 0 = 0 := by
  unfold tau; split_ifs <;> simp [Equiv.swap_apply_of_ne_of_ne]

/-! ### Coordinates of the zero cell -/

/-- Coefficients of `F0` on the zero cell with respect to `facetPts`. -/
def yv (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  Fin.cons (5 * gam k A 0 x)
    (fun t => gam k A (tau A t) x - gam k A 0 x + (if t = 0 then alp k x else 0))

lemma sum_tau (A : Finset (Fin 6)) (f : Fin 5 → ℝ) : ∑ t, f (tau A t) = ∑ t, f t :=
  Equiv.sum_comp (tau A) f

lemma sum_yv (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) :
    ∑ s, yv k A x s = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [yv, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_tau A (fun t => gam k A t x), Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := sum_alp_gam k A hx
  push_cast
  linarith

lemma yv_nonneg {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : InPyr k A x)
    (hmin : ∀ t, gam k A 0 x ≤ gam k A t x) : ∀ s, 0 ≤ yv k A x s := by
  intro s
  refine Fin.cases ?_ (fun t => ?_) s
  · simp only [yv, Fin.cons_zero]; have := h.2 0; linarith
  · simp only [yv, Fin.cons_succ]
    have := hmin (tau A t)
    split_ifs
    · have := h.1; linarith
    · linarith

/-! ### `F0` on the pyramid -/

/-- `ζ - 5 m b_k`. -/
def lam (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  zetaT k A x - (5 * mhat k A x) • bJ k

lemma F0_inPyr (q : Fin 6 → Fin 6 → ℝ) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex)
    {p : Fin 6 × Finset (Fin 6)} (hp : p ∈ Pyr) (h : InPyr p.1 p.2 x) :
    F0 q x = (5 * mhat p.1 p.2 x) • anc p.1 p.2 + H0 q (lam p.1 p.2 x) := by
  rw [F0_of_near q hx hp (near_of_inPyr hx.2 h), rho_of_near hx hp (near_of_inPyr hx.2 h),
    chi_eq_one h]
  simp only [sub_self, zero_smul, one_smul, zero_add, lam]
  rw [← H0L_apply, ← H0L_apply, ← H0L_apply, map_sub, map_smul]
  simp only [smul_sub]
  abel

lemma sum_bJ (k : Fin 6) : ∑ i, bJ k i = 1 := by
  rw [Fin.sum_univ_succAbove _ k]
  simp [bJ_self, bJ_succAbove]

lemma bJ_eq_sum (k : Fin 6) : bJ k = (1 / 5 : ℝ) • ∑ t, (Pi.single (k.succAbove t) 1 : Fin 6 → ℝ) := by
  funext i
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rcases eq_or_ne i k with rfl | hik
  · simp [bJ_self]
  · obtain ⟨t0, rfl⟩ := Fin.exists_succAbove_eq hik
    rw [bJ_succAbove]
    rw [Finset.sum_eq_single t0]
    · simp
    · intro t _ ht
      exact Pi.single_eq_of_ne (fun e => ht (Fin.succAbove_right_injective e).symm) _
    · simp

lemma ell_H0_single (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (j : Fin 6) :
    ell m (H0 q (Pi.single j 1)) = vvec q m j := by
  rw [ell_H0]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

lemma ell_H0_sum (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (j : ι → Fin 6) :
    ell m (H0 q (∑ t ∈ s, c t • (Pi.single (j t) 1 : Fin 6 → ℝ))) = ∑ t ∈ s, c t • vvec q m (j t) := by
  rw [← H0L_apply, map_sum]
  induction s using Finset.cons_induction with
  | empty => funext r; simp [ell]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ell_add, ih, map_smul, H0L_apply, ell_smul,
      ell_H0_single]

/-- **`F0` on the zero cell.** -/
theorem ell_F0_zeroCell (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (hm : IsMatching m)
    {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {p : Fin 6 × Finset (Fin 6)} (hp : p ∈ Pyr)
    (h : InPyr p.1 p.2 x) (hmin : ∀ t, gam p.1 p.2 0 x ≤ gam p.1 p.2 t x) :
    ell m (F0 q x) = ∑ s, yv p.1 p.2 x s •
      facetPts q m (rowSet m (p.1.succAbove 0) p.2) p.1 s := by
  obtain ⟨k, A⟩ := p
  simp only at h hmin ⊢
  have hm0 : mhat k A x = gam k A 0 x := by
    unfold mhat
    have : (mn5 fun t => gam k A t x) = gam k A 0 x :=
      le_antisymm (mn5_le _ 0) (le_mn5 hmin)
    rw [this, pp_of_nonneg (h.2 0)]
  rw [F0_inPyr q hx hp h, ell_add, ell_smul]
  simp only at hm0 ⊢
  rw [hm0, anc, ell_anchorTable, lam, zetaT_of_inPyr hx.2 h, bJ_eq_sum, smul_smul]
  rw [show (5 * mhat k A x * (1 / 5)) = gam k A 0 x by rw [hm0]; ring, Finset.smul_sum]
  rw [← H0L_apply, map_sub, map_add, map_smul, ell_sub, ell_add, ell_smul, H0L_apply,
    ell_H0_single, H0L_apply, H0L_apply, ell_H0_sum, ell_H0_sum]
  have hre : ∑ t, gam k A t x • vvec q m (sig k A (k.succAbove t)) =
      ∑ t, gam k A (tau A t) x • vvec q m (k.succAbove t) := by
    rw [← Equiv.sum_comp (tau A)]
    simp only [sig_succAbove_tau]
  rw [hre]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [yv, facetPts, Fin.cons_zero, Fin.cons_succ]
  simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

end

end Tverberg6R
