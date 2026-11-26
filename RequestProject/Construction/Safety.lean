module

public import RequestProject.Construction.PyrAlg

@[expose] public section

/-!
# Where `F0` can fail to be safe; compatibility of `F0`
-/

open Set Surgery

namespace Tverberg6R

noncomputable section

lemma mem_Pyr {p : Fin 6 × Finset (Fin 6)} (hp : p ∈ Pyr) : 1 ≤ p.2.card ∧ p.2.card ≤ 3 := by
  simp only [Pyr, anchors, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at hp
  exact hp

lemma lam_self (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : lam k A x k = 0 := by
  simp [lam, zetaT_self, bJ_self]

lemma sum_lam (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) :
    5 * mhat k A x + ∑ i, lam k A x i = 1 := by
  simp only [lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_bJ, zetaT_sum k A hx]
  ring

lemma zetaT_sig {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1)
    (h : InPyr k A x) {t1 : Fin 5} (ht1 : t1 ≠ 0) :
    zetaT k A x (sig k A (k.succAbove t1)) = gam k A t1 x := by
  rw [zetaT_of_inPyr hx h]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have h0 : sig k A (k.succAbove t1) ≠ k.succAbove 0 := by
    rw [← sig_zero k A]
    intro e
    exact ht1 (Fin.succAbove_right_injective ((sig k A).injective e))
  rw [Pi.single_eq_of_ne h0, mul_zero, zero_add, Finset.sum_eq_single t1]
  · simp
  · intro t _ ht
    rw [Pi.single_eq_of_ne, mul_zero]
    intro e
    exact ht (Fin.succAbove_right_injective ((sig k A).injective e)).symm
  · simp

/-- Off the zero cell, the pyramid is safe. -/
theorem ell_F0_ne_zero_of_not_min {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {p : Fin 6 × Finset (Fin 6)}
    (hp : p ∈ Pyr) (h : InPyr p.1 p.2 x) (hnm : ∃ t, gam p.1 p.2 t x < gam p.1 p.2 0 x) :
    ell m (F0 q x) ≠ 0 := by
  obtain ⟨k, A⟩ := p
  simp only at h hnm ⊢
  obtain ⟨t1, ht1⟩ := exists_mn5_eq (fun t => gam k A t x)
  have ht10 : t1 ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hnm
    have := mn5_le (fun t => gam k A t x) t
    linarith
  have hmh : mhat k A x = gam k A t1 x := by
    unfold mhat; rw [ht1, pp_of_nonneg (h.2 t1)]
  have hl2 : lam k A x (sig k A (k.succAbove t1)) = 0 := by
    simp only [lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zetaT_sig hx.2 h ht10]
    have hb : bJ k (sig k A (k.succAbove t1)) = 1 / 5 := by
      simp [bJ, sig_ne_self]
    rw [hb, hmh]; ring
  rw [F0_inPyr q hx hp h]
  have := ell_anchor_H0_ne_zero hq hm (k.succAbove 0) (A := A) (mem_Pyr hp).1
    (by have := (mem_Pyr hp).2; simp only at this; omega) (sum_lam k A hx.2)
    (sig_ne_self k A t1).symm (lam_self k A x) hl2
  convert this using 2
  rfl

/-- **Where zeros can occur.** -/
theorem zero_cases {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) (h0 : ell m (F0 q x) = 0) :
    1 / 12 < min6 x ∨ ∃ p ∈ Pyr, InPyr p.1 p.2 x ∧ ∀ t, gam p.1 p.2 0 x ≤ gam p.1 p.2 t x := by
  by_cases hn : ∃ p ∈ Pyr, Near p.1 p.2 x
  · obtain ⟨p0, hp0, hnear⟩ := hn
    by_cases hin : InPyr p0.1 p0.2 x
    · by_cases hmin : ∀ t, gam p0.1 p0.2 0 x ≤ gam p0.1 p0.2 t x
      · exact Or.inr ⟨p0, hp0, hin, hmin⟩
      · push_neg at hmin
        exact absurd h0 (ell_F0_ne_zero_of_not_min hq hm hx hp0 hin hmin)
    · exfalso
      have hmh : mhat p0.1 p0.2 x = 0 := by
        rcases (pp_nonneg (mn5 fun t => gam p0.1 p0.2 t x)).lt_or_eq with h' | h'
        · exact absurd (inPyr_of_mhat_pos (hx.1 _) h').1 hin
        · exact h'.symm
      rw [F0_of_near q hx hp0 hnear, hmh, mul_zero, zero_smul, add_zero] at h0
      have hmin : min6 x ≤ 1 / 12 := (min6_le x p0.1).trans (near_self_lt hnear).le
      obtain ⟨i, hi⟩ := exists_rho_eq_zero hx hmin
      exact ell_H0_ne_zero_of_boundary hq (rho_mem hx) hi hm h0
  · push_neg at hn
    by_contra hc
    push_neg at hc
    rw [F0_of_far q hx hn] at h0
    obtain ⟨i, hi⟩ := exists_min6_eq x
    exact ell_H0_ne_zero_of_boundary hq (thetaT_mem hx)
      (thetaT_eq_zero_of_min hi.symm hc.1) hm h0

/-- **Compatibility of `F0`.** -/
theorem compat_F0 (q : Fin 6 → Fin 6 → ℝ) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {i : Fin 6}
    (hi : x i = 0) {u v : Word} (huv : ∀ j, j ≠ i → u j = v j) : F0 q x u = F0 q x v := by
  by_cases hn : ∃ p ∈ Pyr, Near p.1 p.2 x
  · obtain ⟨p0, hp0, hnear⟩ := hn
    have hik : i = p0.1 := by
      by_contra hne
      have := (near_lt hnear hne).2
      linarith
    subst hik
    rw [F0_of_near q hx hp0 hnear]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [H0_compat q (rho_eq_zero_of_eq_zero hx hi) huv, H0_compat q (bJ_self _) huv]
    congr 2
    simp only [anc, anchorTable]
    rw [huv _ (Fin.succAbove_ne _ 0)]
  · push_neg at hn
    rw [F0_of_far q hx hn]
    exact H0_compat q (thetaT_eq_zero_of_eq_zero hx hi) huv

end

end Tverberg6R
