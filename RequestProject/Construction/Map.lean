module

public import RequestProject.Construction.Layout
public import RequestProject.Boundary
public import RequestProject.Surgery.Core

@[expose] public section

/-!
# The initial height table `F0`

`F0 q x = H⁰(ρ x) + ∑_{(k,A)} 5 m̂_{k,A}(x) (anchor_{k,A} - H⁰(b_k))`, where `ρ` is the
radial projection `θ̃` modified near the pyramids, and `m̂` is the bump of the pyramid.
-/

open Set Surgery

namespace Tverberg6R

noncomputable section

/-! ### Minima -/

/-- Minimum of five reals. -/
def mn5 (f : Fin 5 → ℝ) : ℝ := min (f 0) (min (f 1) (min (f 2) (min (f 3) (f 4))))

lemma mn5_le (f : Fin 5 → ℝ) (t : Fin 5) : mn5 f ≤ f t := by
  unfold mn5
  fin_cases t <;> simp

lemma le_mn5 {f : Fin 5 → ℝ} {c : ℝ} (h : ∀ t, c ≤ f t) : c ≤ mn5 f := by
  unfold mn5
  simp only [le_min_iff]
  exact ⟨h 0, h 1, h 2, h 3, h 4⟩

lemma lt_mn5 {f : Fin 5 → ℝ} {c : ℝ} (h : ∀ t, c < f t) : c < mn5 f := by
  unfold mn5
  simp only [lt_min_iff]
  exact ⟨h 0, h 1, h 2, h 3, h 4⟩

lemma exists_mn5_eq (f : Fin 5 → ℝ) : ∃ t, mn5 f = f t := by
  unfold mn5
  rcases min_choice (f 3) (f 4) with h3 | h3 <;> rw [h3] <;>
  rcases min_choice (f 2) _ with h2 | h2 <;> rw [h2] <;>
  rcases min_choice (f 1) _ with h1 | h1 <;> rw [h1] <;>
  rcases min_choice (f 0) _ with h0 | h0 <;> rw [h0] <;>
  first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩

lemma continuous_mn5 {X : Type*} [TopologicalSpace X] {g : Fin 5 → X → ℝ}
    (hg : ∀ t, Continuous (g t)) : Continuous fun x => mn5 (fun t => g t x) := by
  unfold mn5
  exact (hg 0).min ((hg 1).min ((hg 2).min ((hg 3).min (hg 4))))

/-- Minimum of six reals. -/
def min6 (x : Fin 6 → ℝ) : ℝ := min (x 0) (mn5 fun t => x t.succ)

lemma min6_le (x : Fin 6 → ℝ) (i : Fin 6) : min6 x ≤ x i := by
  unfold min6
  refine Fin.cases ?_ (fun t => ?_) i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (mn5_le _ t)

lemma exists_min6_eq (x : Fin 6 → ℝ) : ∃ i, min6 x = x i := by
  unfold min6
  rcases min_choice (x 0) (mn5 fun t => x t.succ) with h | h
  · exact ⟨0, h⟩
  · obtain ⟨t, ht⟩ := exists_mn5_eq (fun t => x t.succ)
    exact ⟨t.succ, h.trans ht⟩

lemma le_min6 {x : Fin 6 → ℝ} {c : ℝ} (h : ∀ i, c ≤ x i) : c ≤ min6 x := by
  obtain ⟨i, hi⟩ := exists_min6_eq x; rw [hi]; exact h i

lemma continuous_min6 : Continuous min6 := by
  unfold min6
  exact (continuous_apply 0).min (continuous_mn5 fun t => continuous_apply _)

/-! ### Ingredients -/

/-- Positive part. -/
def pp (t : ℝ) : ℝ := max t 0

lemma pp_nonneg (t : ℝ) : 0 ≤ pp t := le_max_right _ _
lemma le_pp (t : ℝ) : t ≤ pp t := le_max_left _ _
lemma pp_of_nonneg {t : ℝ} (h : 0 ≤ t) : pp t = t := max_eq_left h
lemma continuous_pp : Continuous pp := continuous_id.max continuous_const

/-- Truncated minimum. -/
def muC (x : Fin 6 → ℝ) : ℝ := min (min6 x) (1 / 12)

lemma muC_le (x : Fin 6 → ℝ) : muC x ≤ 1 / 12 := min_le_right _ _

lemma one_sub_six_muC_pos (x : Fin 6 → ℝ) : 0 < 1 - 6 * muC x := by
  have := muC_le x; linarith

/-- Radial projection (truncated near the centre). -/
def thetaT (x : Fin 6 → ℝ) : Fin 6 → ℝ := fun i => (x i - muC x) / (1 - 6 * muC x)

/-- Cut-off of the pyramid `(k, A)`. -/
def chi (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : ℝ :=
  clamp01 (1 + 10 * min (alp k x) (mn5 fun t => gam k A t x))

/-- The value permutation (orientation reversal for `|A| = 3`). -/
def sig (k : Fin 6) (A : Finset (Fin 6)) : Equiv.Perm (Fin 6) :=
  if A.card = 3 then Equiv.swap (k.succAbove 1) (k.succAbove 2) else 1

/-- Denominator of `zetaT`. -/
def zden (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : ℝ :=
  max 1 (pp (alp k x) + ∑ t, pp (gam k A t x))

/-- The facet point attached to a point of the pyramid. -/
def zetaT (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  (1 / zden k A x) • (pp (alp k x) • (Pi.single (k.succAbove 0) 1 : Fin 6 → ℝ) +
    ∑ t, pp (gam k A t x) • (Pi.single (sig k A (k.succAbove t)) 1 : Fin 6 → ℝ))

/-- The pyramids. -/
def Pyr : Finset (Fin 6 × Finset (Fin 6)) := Finset.univ ×ˢ anchors

/-- The modified radial projection. -/
def rho (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  (1 - ∑ p ∈ Pyr, chi p.1 p.2 x) • thetaT x + ∑ p ∈ Pyr, chi p.1 p.2 x • zetaT p.1 p.2 x

/-- The bump of the pyramid. -/
def mhat (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : ℝ := pp (mn5 fun t => gam k A t x)

/-- The anchor of the pyramid `(k, A)`. -/
def anc (k : Fin 6) (A : Finset (Fin 6)) : Table := anchorTable (k.succAbove 0) A

/-- **The initial height table.** -/
def F0 (q : Fin 6 → Fin 6 → ℝ) (x : Fin 6 → ℝ) : Table :=
  H0 q (rho x) + ∑ p ∈ Pyr, (5 * mhat p.1 p.2 x) • (anc p.1 p.2 - H0 q (bJ p.1))

/-! ### Continuity -/

lemma continuous_alp (k : Fin 6) : Continuous (alp k) := by
  unfold alp; fun_prop

lemma continuous_gam (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) : Continuous (gam k A t) := by
  unfold gam alp; fun_prop

lemma continuous_muC : Continuous muC := continuous_min6.min continuous_const

lemma continuous_thetaT : Continuous thetaT := by
  refine continuous_pi fun i => ?_
  unfold thetaT
  exact ((continuous_apply i).sub continuous_muC).div (continuous_const.sub
    (continuous_const.mul continuous_muC)) fun x => (one_sub_six_muC_pos x).ne'

lemma continuous_chi (k : Fin 6) (A : Finset (Fin 6)) : Continuous (chi k A) := by
  unfold chi
  exact continuous_clamp01.comp (continuous_const.add (continuous_const.mul
    ((continuous_alp k).min (continuous_mn5 fun t => continuous_gam k A t))))

lemma zden_pos (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : 0 < zden k A x :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

lemma continuous_zetaT (k : Fin 6) (A : Finset (Fin 6)) : Continuous (zetaT k A) := by
  unfold zetaT
  have h_scalar : Continuous (fun x => 1 / zden k A x) := by
    refine continuous_const.div ?_ (fun x => (zden_pos k A x).ne')
    unfold zden
    exact continuous_const.max ((continuous_pp.comp (continuous_alp k)).add
      (continuous_finsetSum _ fun t _ => continuous_pp.comp (continuous_gam k A t)))
  have h_vec : Continuous (fun x =>
      pp (alp k x) • (Pi.single (k.succAbove 0) 1 : Fin 6 → ℝ) +
      ∑ t, pp (gam k A t x) • (Pi.single (sig k A (k.succAbove t)) 1 : Fin 6 → ℝ)) :=
    ((continuous_pp.comp (continuous_alp k)).smul continuous_const).add
      (continuous_finsetSum _ fun t _ =>
        (continuous_pp.comp (continuous_gam k A t)).smul continuous_const)
  exact h_scalar.smul h_vec

lemma continuous_rho : Continuous rho := by
  unfold rho
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub (continuous_finsetSum _ fun p _ => continuous_chi _ _)).smul
      continuous_thetaT
  · exact continuous_finsetSum _ fun p _ => (continuous_chi _ _).smul (continuous_zetaT _ _)

lemma continuous_mhat (k : Fin 6) (A : Finset (Fin 6)) : Continuous (mhat k A) :=
  continuous_pp.comp (continuous_mn5 fun t => continuous_gam k A t)

lemma continuous_F0 (q : Fin 6 → Fin 6 → ℝ) : Continuous (F0 q) := by
  unfold F0
  exact ((continuous_H0 q).comp continuous_rho).add (continuous_finsetSum _ fun p _ =>
    (continuous_const.mul (continuous_mhat _ _)).smul continuous_const)

end

end Tverberg6R
