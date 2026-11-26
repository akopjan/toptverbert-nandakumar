module

public import RequestProject.Construction.Map

@[expose] public section

/-!
# Local description of `F0`
-/

open Set Surgery

namespace Tverberg6R

noncomputable section

/-- The closed pyramid `(k, A)` (in barycentric coordinates). -/
def InPyr (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : Prop :=
  0 ≤ alp k x ∧ ∀ t, 0 ≤ gam k A t x

lemma near_of_chi_pos {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1)
    (h : 0 < chi k A x) : Near k A x := by
  have hm : -1 / 10 < min (alp k x) (mn5 fun t => gam k A t x) := by
    by_contra hc
    push_neg at hc
    have : chi k A x = 0 := clamp01_of_nonpos (by linarith)
    linarith
  refine near_of_coords k A hx (le_of_lt (lt_of_lt_of_le hm (min_le_left _ _))) fun t => ?_
  exact le_of_lt (lt_of_lt_of_le hm ((min_le_right _ _).trans (mn5_le _ t)))

lemma chi_eq_zero_of_not_near {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ}
    (hx : ∑ i, x i = 1) (h : ¬ Near k A x) : chi k A x = 0 := by
  rcases (clamp01_mem (1 + 10 * min (alp k x) (mn5 fun t => gam k A t x))).1.lt_or_eq with h' | h'
  · exact absurd (near_of_chi_pos hx h') h
  · exact h'.symm

lemma chi_eq_one {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : InPyr k A x) :
    chi k A x = 1 := by
  apply clamp01_of_one_le
  have : 0 ≤ min (alp k x) (mn5 fun t => gam k A t x) := le_min h.1 (le_mn5 h.2)
  linarith

lemma near_of_inPyr {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1)
    (h : InPyr k A x) : Near k A x :=
  near_of_chi_pos hx (by rw [chi_eq_one h]; exact one_pos)

lemma alp_nonneg {k : Fin 6} {x : Fin 6 → ℝ} (h : 0 ≤ x k) : 0 ≤ alp k x := by
  unfold alp; have := dl_pos; positivity

lemma inPyr_of_mhat_pos {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (hx0 : 0 ≤ x k)
    (h : 0 < mhat k A x) : InPyr k A x ∧ ∀ t, 0 < gam k A t x := by
  have hm : 0 < mn5 fun t => gam k A t x := by
    by_contra hc; push_neg at hc
    have : mhat k A x = 0 := max_eq_right hc
    linarith
  have hg : ∀ t, 0 < gam k A t x := fun t => lt_of_lt_of_le hm (mn5_le _ t)
  exact ⟨⟨alp_nonneg hx0, fun t => (hg t).le⟩, hg⟩

lemma mhat_eq_zero_of_not_near {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ}
    (hx : x ∈ massSimplex) (h : ¬ Near k A x) : mhat k A x = 0 := by
  rcases (pp_nonneg (mn5 fun t => gam k A t x)).lt_or_eq with h' | h'
  · exact absurd (near_of_inPyr hx.2 (inPyr_of_mhat_pos (hx.1 k) h').1) h
  · exact h'.symm

/-! ### The two cases -/

lemma rho_of_far {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) (h : ∀ p ∈ Pyr, ¬ Near p.1 p.2 x) :
    rho x = thetaT x := by
  unfold rho
  rw [Finset.sum_eq_zero (fun p hp => chi_eq_zero_of_not_near hx.2 (h p hp)),
    Finset.sum_eq_zero (fun p hp => by rw [chi_eq_zero_of_not_near hx.2 (h p hp), zero_smul])]
  simp

lemma F0_of_far (q : Fin 6 → Fin 6 → ℝ) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex)
    (h : ∀ p ∈ Pyr, ¬ Near p.1 p.2 x) : F0 q x = H0 q (thetaT x) := by
  unfold F0
  rw [rho_of_far hx h, Finset.sum_eq_zero (fun p hp => by
    rw [mhat_eq_zero_of_not_near hx (h p hp), mul_zero, zero_smul]), add_zero]

lemma not_near_of_ne {p p0 : Fin 6 × Finset (Fin 6)} {x : Fin 6 → ℝ}
    (h0 : Near p0.1 p0.2 x) (hne : p ≠ p0) : ¬ Near p.1 p.2 x := by
  intro h
  obtain ⟨e1, e2⟩ := near_unique h h0
  exact hne (Prod.ext e1 e2)

lemma rho_of_near {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {p0 : Fin 6 × Finset (Fin 6)}
    (hp0 : p0 ∈ Pyr) (h0 : Near p0.1 p0.2 x) :
    rho x = (1 - chi p0.1 p0.2 x) • thetaT x + chi p0.1 p0.2 x • zetaT p0.1 p0.2 x := by
  unfold rho
  rw [Finset.sum_eq_single p0 (fun p _ hne => chi_eq_zero_of_not_near hx.2 (not_near_of_ne h0 hne))
    (fun h => absurd hp0 h),
    Finset.sum_eq_single p0 (fun p _ hne => by
      rw [chi_eq_zero_of_not_near hx.2 (not_near_of_ne h0 hne), zero_smul]) (fun h => absurd hp0 h)]

lemma F0_of_near (q : Fin 6 → Fin 6 → ℝ) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex)
    {p0 : Fin 6 × Finset (Fin 6)} (hp0 : p0 ∈ Pyr) (h0 : Near p0.1 p0.2 x) :
    F0 q x = H0 q (rho x) + (5 * mhat p0.1 p0.2 x) • (anc p0.1 p0.2 - H0 q (bJ p0.1)) := by
  unfold F0
  rw [Finset.sum_eq_single p0 (fun p _ hne => by
      rw [mhat_eq_zero_of_not_near hx (not_near_of_ne h0 hne), mul_zero, zero_smul])
    (fun h => absurd hp0 h)]

/-! ### `thetaT` -/

lemma muC_le_x (x : Fin 6 → ℝ) (i : Fin 6) : muC x ≤ x i :=
  (min_le_left _ _).trans (min6_le x i)

lemma thetaT_mem {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) : thetaT x ∈ massSimplex := by
  have hpos := one_sub_six_muC_pos x
  refine ⟨fun i => div_nonneg (sub_nonneg.2 (muC_le_x x i)) hpos.le, ?_⟩
  unfold thetaT
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hx.2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((6:ℕ):ℝ) * muC x = 6 * muC x by norm_num, div_self hpos.ne']

lemma thetaT_eq_zero_of_eq_zero {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {i : Fin 6}
    (hi : x i = 0) : thetaT x i = 0 := by
  have hmu : muC x = 0 := by
    have h1 := muC_le_x x i
    have h2 : 0 ≤ muC x := le_min (le_min6 hx.1) (by norm_num)
    linarith
  simp [thetaT, hmu, hi]

lemma thetaT_eq_zero_of_min {x : Fin 6 → ℝ} {i : Fin 6} (hi : x i = min6 x)
    (h : min6 x ≤ 1 / 12) : thetaT x i = 0 := by
  have hmu : muC x = x i := by rw [muC, min_eq_left h, hi]
  simp [thetaT, hmu]

lemma thetaT_inner {x : Fin 6 → ℝ} (h : 1 / 12 ≤ min6 x) :
    thetaT x = fun i => 2 * x i - 1 / 6 := by
  have hmu : muC x = 1 / 12 := min_eq_right h
  funext i
  simp only [thetaT, hmu]
  ring

/-! ### `zetaT` -/

lemma sig_self (k : Fin 6) (A : Finset (Fin 6)) : sig k A k = k := by
  unfold sig
  split_ifs
  · exact Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne k 1).symm (Fin.succAbove_ne k 2).symm
  · rfl

lemma sig_ne_self (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) :
    sig k A (k.succAbove t) ≠ k := by
  intro h
  have := (sig k A).injective (h.trans (sig_self k A).symm)
  exact Fin.succAbove_ne k t this

lemma sig_zero (k : Fin 6) (A : Finset (Fin 6)) : sig k A (k.succAbove 0) = k.succAbove 0 := by
  unfold sig
  split_ifs
  · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · exact fun h => absurd (Fin.succAbove_right_injective h) (by decide)
    · exact fun h => absurd (Fin.succAbove_right_injective h) (by decide)
  · rfl

lemma zetaT_self (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : zetaT k A x k = 0 := by
  simp only [zetaT, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  rw [Pi.single_eq_of_ne (Fin.succAbove_ne k 0).symm]
  simp [Pi.single_eq_of_ne (sig_ne_self k A _).symm]

lemma zetaT_nonneg (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) (i : Fin 6) :
    0 ≤ zetaT k A x i := by
  simp only [zetaT, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  refine mul_nonneg (by have := zden_pos k A x; positivity) (add_nonneg ?_ ?_)
  · exact mul_nonneg (pp_nonneg _) (by simp [Pi.single_apply]; split_ifs <;> norm_num)
  · exact Finset.sum_nonneg fun t _ =>
      mul_nonneg (pp_nonneg _) (by simp [Pi.single_apply]; split_ifs <;> norm_num)

lemma sum_single (j : Fin 6) : ∑ i, (Pi.single j (1:ℝ) : Fin 6 → ℝ) i = 1 := by
  simp [Pi.single_apply]

lemma zetaT_sum (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) :
    ∑ i, zetaT k A x i = 1 := by
  have hge : 1 ≤ pp (alp k x) + ∑ t, pp (gam k A t x) := by
    have := sum_alp_gam k A hx
    have h1 := le_pp (alp k x)
    have h2 : ∑ t, gam k A t x ≤ ∑ t, pp (gam k A t x) :=
      Finset.sum_le_sum fun t _ => le_pp _
    linarith
  have hz : zden k A x = pp (alp k x) + ∑ t, pp (gam k A t x) := max_eq_right hge
  simp only [zetaT, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_single, Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_single, mul_one]
  rw [← hz, one_div, inv_mul_cancel₀ (zden_pos k A x).ne']

lemma zetaT_mem (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) :
    zetaT k A x ∈ massSimplex :=
  ⟨zetaT_nonneg k A x, zetaT_sum k A hx⟩

lemma zetaT_of_inPyr {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1)
    (h : InPyr k A x) :
    zetaT k A x = alp k x • (Pi.single (k.succAbove 0) 1 : Fin 6 → ℝ) +
      ∑ t, gam k A t x • (Pi.single (sig k A (k.succAbove t)) 1 : Fin 6 → ℝ) := by
  have hpa : pp (alp k x) = alp k x := pp_of_nonneg h.1
  have hpg : ∀ t, pp (gam k A t x) = gam k A t x := fun t => pp_of_nonneg (h.2 t)
  have hz : zden k A x = 1 := by
    unfold zden; rw [hpa]; simp only [hpg]; rw [sum_alp_gam k A hx]; simp
  unfold zetaT
  simp only [hz, hpa, hpg, div_one, one_smul]

/-! ### `rho` -/

lemma chi_mem (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : chi k A x ∈ Icc (0:ℝ) 1 :=
  clamp01_mem _

lemma convex_massSimplex {a b : Fin 6 → ℝ} (ha : a ∈ massSimplex) (hb : b ∈ massSimplex)
    {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) : (1 - c) • a + c • b ∈ massSimplex := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := ha.1 i; have := hb.1 i; have := hc.1; have := hc.2
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, ha.2, hb.2]
    ring

lemma rho_mem {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) : rho x ∈ massSimplex := by
  by_cases h : ∃ p ∈ Pyr, Near p.1 p.2 x
  · obtain ⟨p0, hp0, h0⟩ := h
    rw [rho_of_near hx hp0 h0]
    exact convex_massSimplex (thetaT_mem hx) (zetaT_mem _ _ hx.2) (chi_mem _ _ _)
  · push_neg at h
    rw [rho_of_far hx h]; exact thetaT_mem hx

lemma rho_eq_zero_of_eq_zero {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {i : Fin 6} (hi : x i = 0) :
    rho x i = 0 := by
  by_cases h : ∃ p ∈ Pyr, Near p.1 p.2 x
  · obtain ⟨p0, hp0, h0⟩ := h
    have hik : i = p0.1 := by
      by_contra hne
      have := (near_lt h0 hne).2
      linarith
    subst hik
    rw [rho_of_near hx hp0 h0]
    simp [thetaT_eq_zero_of_eq_zero hx hi, zetaT_self]
  · push_neg at h
    rw [rho_of_far hx h]; exact thetaT_eq_zero_of_eq_zero hx hi

lemma exists_rho_eq_zero {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) (hmin : min6 x ≤ 1 / 12) :
    ∃ i, rho x i = 0 := by
  by_cases h : ∃ p ∈ Pyr, Near p.1 p.2 x
  · obtain ⟨p0, hp0, h0⟩ := h
    refine ⟨p0.1, ?_⟩
    have hmin' : x p0.1 = min6 x := by
      obtain ⟨i, hi⟩ := exists_min6_eq x
      by_cases hik : i = p0.1
      · rw [hi, hik]
      · have := (near_lt h0 hik).1
        have := min6_le x p0.1
        linarith
    rw [rho_of_near hx hp0 h0]
    simp [thetaT_eq_zero_of_min hmin' hmin, zetaT_self]
  · push_neg at h
    obtain ⟨i, hi⟩ := exists_min6_eq x
    exact ⟨i, by rw [rho_of_far hx h]; exact thetaT_eq_zero_of_min hi.symm hmin⟩

lemma far_of_inner {x : Fin 6 → ℝ} (hmin : 1 / 12 ≤ min6 x) : ∀ p ∈ Pyr, ¬ Near p.1 p.2 x := by
  intro p _ h
  have := near_self_lt h
  have := min6_le x p.1
  linarith

lemma F0_inner (q : Fin 6 → Fin 6 → ℝ) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex)
    (hmin : 1 / 12 ≤ min6 x) : F0 q x = H0 q (fun i => 2 * x i - 1 / 6) := by
  rw [F0_of_far q hx (far_of_inner hmin), thetaT_inner hmin]

end

end Tverberg6R
