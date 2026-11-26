module

public import RequestProject.Surgery.Core

@[expose] public section

/-!
# Cut-off functions used in the zero-pair cancellation
-/

open Set

namespace Surgery

/-- `1` on `[-ζ, 1 + ζ]`, `0` outside `(-2ζ, 1 + 2ζ)`. -/
noncomputable def cutChi (ζ t : ℝ) : ℝ := clamp01 ((t + 2 * ζ) / ζ) * clamp01 ((1 + 2 * ζ - t) / ζ)

/-- `2ζ` on `[0, 1]`, `0` outside `(-ζ, 1 + ζ)`. -/
noncomputable def bump (ζ t : ℝ) : ℝ := 2 * ζ * (clamp01 ((t + ζ) / ζ) * clamp01 ((1 + ζ - t) / ζ))

/-- Radial cut-off: `1` for `‖v‖ ≤ ε/2`, `0` for `‖v‖ ≥ ε`. -/
noncomputable def cutRad (ε r : ℝ) : ℝ := clamp01 (2 - 2 * r / ε)

/-- Radial bump: `1` at `0`, `0` for `‖v‖ ≥ ε/2`. -/
noncomputable def bumpRad (ε r : ℝ) : ℝ := clamp01 (1 - 2 * r / ε)

lemma continuous_cutChi (ζ : ℝ) : Continuous (cutChi ζ) := by
  unfold cutChi; have := continuous_clamp01; fun_prop

lemma continuous_bump (ζ : ℝ) : Continuous (bump ζ) := by
  unfold bump; have := continuous_clamp01; fun_prop

lemma continuous_cutRad (ε : ℝ) : Continuous (cutRad ε) := by
  unfold cutRad; have := continuous_clamp01; fun_prop

lemma continuous_bumpRad (ε : ℝ) : Continuous (bumpRad ε) := by
  unfold bumpRad; have := continuous_clamp01; fun_prop

lemma clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := (clamp01_mem x).1
lemma clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := (clamp01_mem x).2

lemma cutChi_mem (ζ t : ℝ) : cutChi ζ t ∈ Icc (0:ℝ) 1 :=
  ⟨mul_nonneg (clamp01_nonneg _) (clamp01_nonneg _),
    mul_le_one₀ (clamp01_le_one _) (clamp01_nonneg _) (clamp01_le_one _)⟩

lemma cutRad_mem (ε r : ℝ) : cutRad ε r ∈ Icc (0:ℝ) 1 := clamp01_mem _
lemma bumpRad_mem (ε r : ℝ) : bumpRad ε r ∈ Icc (0:ℝ) 1 := clamp01_mem _

lemma bump_nonneg {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) : 0 ≤ bump ζ t :=
  mul_nonneg (by linarith) (mul_nonneg (clamp01_nonneg _) (clamp01_nonneg _))

lemma bump_le {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) : bump ζ t ≤ 2 * ζ := by
  unfold bump
  have := mul_le_one₀ (clamp01_le_one ((t + ζ) / ζ)) (clamp01_nonneg _)
    (clamp01_le_one ((1 + ζ - t) / ζ))
  nlinarith

lemma cutChi_eq_zero {ζ t : ℝ} (hζ : 0 < ζ) (ht : t ∉ Ioo (-2 * ζ) (1 + 2 * ζ)) :
    cutChi ζ t = 0 := by
  unfold cutChi
  rcases not_and_or.1 ht with h | h
  · rw [clamp01_of_nonpos (x := (t + 2 * ζ) / ζ) (by
      rw [div_nonpos_iff]; right; constructor <;> linarith [not_lt.1 h]), zero_mul]
  · rw [clamp01_of_nonpos (x := (1 + 2 * ζ - t) / ζ) (by
      rw [div_nonpos_iff]; right; constructor <;> linarith [not_lt.1 h]), mul_zero]

lemma cutChi_eq_one {ζ t : ℝ} (hζ : 0 < ζ) (h1 : -ζ ≤ t) (h2 : t ≤ 1 + ζ) : cutChi ζ t = 1 := by
  unfold cutChi
  rw [clamp01_of_one_le, clamp01_of_one_le, mul_one]
  · rw [le_div_iff₀ hζ]; linarith
  · rw [le_div_iff₀ hζ]; linarith

lemma bump_eq {ζ t : ℝ} (hζ : 0 < ζ) (h1 : 0 ≤ t) (h2 : t ≤ 1) : bump ζ t = 2 * ζ := by
  unfold bump
  rw [clamp01_of_one_le, clamp01_of_one_le, mul_one, mul_one]
  · rw [le_div_iff₀ hζ]; linarith
  · rw [le_div_iff₀ hζ]; linarith

lemma cutRad_eq_zero {ε r : ℝ} (hε : 0 < ε) (hr : ε ≤ r) : cutRad ε r = 0 := by
  unfold cutRad
  apply clamp01_of_nonpos
  have : 2 * ε ≤ 2 * r := by linarith
  have : 2 ≤ 2 * r / ε := by rw [le_div_iff₀ hε]; linarith
  linarith

lemma cutRad_eq_one {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ ε / 2) : cutRad ε r = 1 := by
  unfold cutRad
  apply clamp01_of_one_le
  have : 2 * r / ε ≤ 1 := by rw [div_le_iff₀ hε]; linarith
  linarith

lemma bumpRad_eq_zero {ε r : ℝ} (hε : 0 < ε) (hr : ε / 2 ≤ r) : bumpRad ε r = 0 := by
  unfold bumpRad
  apply clamp01_of_nonpos
  have : 1 ≤ 2 * r / ε := by rw [le_div_iff₀ hε]; linarith
  linarith

lemma bumpRad_zero (ε : ℝ) : bumpRad ε 0 = 1 := by
  simp [bumpRad, clamp01_of_one_le]

lemma cutRad_zero {ε : ℝ} (hε : 0 < ε) : cutRad ε 0 = 1 := cutRad_eq_one hε (by linarith)

end Surgery
