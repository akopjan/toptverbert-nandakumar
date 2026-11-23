module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity


@[expose] public section

/-!
# The local geometry of two matching constraints

For two matchings sharing four words, the joint normal quotient is
`U × V × W`, with real dimensions 4, 4, and 6. The individual normals are
`V × W` and `U × W`. The lemmas below are dimension independent.

The equations `UnitPair` use the Euclidean sum of squared norms rather than
the supremum norm on Lean's product type. No homotopy lifting or surgery
theorem is asserted here.
-/

noncomputable section

namespace AkopyanResearch.PairGeometry

set_option linter.unusedSectionVars false

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def UnitPair (v : V) (w : W) : Prop := ‖v‖ ^ 2 + ‖w‖ ^ 2 = 1

def AntipodalCommon (v : V) (u : U) (w₁ w₂ : W) : Prop :=
  v = 0 ∧ u = 0 ∧ w₁ + w₂ = 0

def AvoidsBothAxes (u : U) (v : V) (w : W) : Prop :=
  (v ≠ 0 ∨ w ≠ 0) ∧ (u ≠ 0 ∨ w ≠ 0)

lemma norm_snd_le_one {v : V} {w : W} (h : UnitPair v w) : ‖w‖ ≤ 1 := by
  have hv := sq_nonneg ‖v‖
  have hw := norm_nonneg w
  dsimp [UnitPair] at h
  nlinarith

lemma norm_snd_eq_one_of_fst_zero {v : V} {w : W}
    (h : UnitPair v w) (hv : v = 0) : ‖w‖ = 1 := by
  have hw := norm_nonneg w
  simp only [UnitPair, hv, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  nlinarith

lemma fst_eq_zero_of_norm_snd_eq_one {v : V} {w : W}
    (h : UnitPair v w) (hw : ‖w‖ = 1) : v = 0 := by
  apply norm_eq_zero.mp
  dsimp [UnitPair] at h
  rw [hw] at h
  nlinarith [sq_nonneg ‖v‖]

/-- The sum section fails exactly on the common antipodal sphere. -/
theorem sum_section_avoids_iff {v : V} {u : U} {w₁ w₂ : W}
    (h₁ : UnitPair v w₁) (h₂ : UnitPair u w₂) :
    AvoidsBothAxes u v (w₁ + w₂) ↔ ¬ AntipodalCommon v u w₁ w₂ := by
  constructor
  · rintro h ⟨hv, hu, hw⟩
    rcases h.1 with hv' | hw'
    · exact hv' hv
    · exact hw' hw
  · intro h
    have hleft : v ≠ 0 ∨ w₁ + w₂ ≠ 0 := by
      by_cases hv : v = 0
      · right
        intro hw
        have hw₁ := norm_snd_eq_one_of_fst_zero h₁ hv
        have heq : w₁ = -w₂ := eq_neg_of_add_eq_zero_left hw
        have hw₂ : ‖w₂‖ = 1 := by simpa only [heq, norm_neg] using hw₁
        exact h ⟨hv, fst_eq_zero_of_norm_snd_eq_one h₂ hw₂, hw⟩
      · exact Or.inl hv
    have hright : u ≠ 0 ∨ w₁ + w₂ ≠ 0 := by
      by_cases hu : u = 0
      · right
        intro hw
        have hw₂ := norm_snd_eq_one_of_fst_zero h₂ hu
        have heq : w₁ = -w₂ := eq_neg_of_add_eq_zero_left hw
        have hw₁ : ‖w₁‖ = 1 := by simpa only [heq, norm_neg] using hw₂
        exact h ⟨fst_eq_zero_of_norm_snd_eq_one h₁ hw₁, hu, hw⟩
      · exact Or.inl hu
    exact ⟨hleft, hright⟩

/-- For a parameter strictly below one, the first interpolated normal never
vanishes. This follows only from the two unit equations. -/
theorem left_interpolation_nonzero {v : V} {u : U} {w₁ w₂ : W} {t : ℝ}
    (h₁ : UnitPair v w₁) (h₂ : UnitPair u w₂) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    v ≠ 0 ∨ w₁ + t • w₂ ≠ 0 := by
  by_cases hv : v = 0
  · right
    intro hz
    have hw₁ := norm_snd_eq_one_of_fst_zero h₁ hv
    have hw₂ := norm_snd_le_one h₂
    have heq : w₁ = -(t • w₂) := eq_neg_of_add_eq_zero_left hz
    have hnorm : 1 = t * ‖w₂‖ := by
      calc
        1 = ‖w₁‖ := hw₁.symm
        _ = t * ‖w₂‖ := by rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hle : t * ‖w₂‖ ≤ t := by simpa using mul_le_mul_of_nonneg_left hw₂ ht0
    linarith
  · exact Or.inl hv

theorem right_interpolation_nonzero {v : V} {u : U} {w₁ w₂ : W} {t : ℝ}
    (h₁ : UnitPair v w₁) (h₂ : UnitPair u w₂) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    u ≠ 0 ∨ t • w₁ + w₂ ≠ 0 := by
  simpa only [add_comm] using left_interpolation_nonzero h₂ h₁ ht0 ht1

/-- Positive multiples of a common vector cannot lie on the antipodal locus
when the two full normals have unit length. -/
theorem positive_common_not_antipodal {v : V} {u : U} {w : W} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h₁ : UnitPair v (a • w)) (_h₂ : UnitPair u (b • w)) :
    ¬ AntipodalCommon v u (a • w) (b • w) := by
  rintro ⟨hv, hu, hw⟩
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hw0 : w = 0 := by
    have hs : (a + b) • w = 0 := by simpa only [add_smul] using hw
    exact (smul_eq_zero.mp hs).resolve_left hab
  have hn := norm_snd_eq_one_of_fst_zero h₁ hv
  simp only [hw0, smul_zero, norm_zero] at hn
  norm_num at hn

end AkopyanResearch.PairGeometry
