module

public import AkopyanResearch.Completion.PairCollapsedLocus

/-!
# Continuous alignment of two common vectors

The weighted sum `‖z‖/(‖z‖+‖w‖) • (z+w)` is continuous even where both
vectors vanish. Together with its symmetric version it retracts pairs of
common vectors onto their positively proportional locus. The formulas below
also control interpolation on the two unit spheres.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairCommonAlignment

open PairDeformation Set Filter Topology
open scoped InnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def align (z w : W) : W := (‖z‖ / (‖z‖ + ‖w‖)) • (z + w)

theorem nonneg_smul_relation (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (z : W) :
    ‖s • z‖ • (r • z) = ‖r • z‖ • (s • z) := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hs, smul_smul]
  congr 1
  ring

theorem norm_align_le (z w : W) : ‖align z w‖ ≤ ‖z‖ := by
  by_cases hz : z = 0
  · simp [align, hz]
  · have hd : 0 < ‖z‖ + ‖w‖ := add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hz) (norm_nonneg _)
    rw [align, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) hd.le)]
    calc
      _ ≤ (‖z‖ / (‖z‖ + ‖w‖)) * (‖z‖ + ‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (div_nonneg (norm_nonneg _) hd.le)
      _ = ‖z‖ := div_mul_cancel₀ _ hd.ne'

theorem continuous_align : Continuous (fun p : W × W => align p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.1 = 0
  · change Tendsto (fun q : W × W => align q.1 q.2) (𝓝 p) (𝓝 (align p.1 p.2))
    rw [hp]
    simp only [align, norm_zero, zero_div, zero_smul]
    apply squeeze_zero_norm (fun q : W × W => norm_align_le q.1 q.2)
    simpa only [hp, norm_zero] using continuous_fst.norm.continuousAt.tendsto (x := p)
  · exact ((continuous_fst.norm.continuousAt.div
      (continuous_fst.norm.add continuous_snd.norm).continuousAt
      (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hp) (norm_nonneg _)).ne').smul
      (continuous_fst.add continuous_snd).continuousAt)

theorem align_eq_of_proportional (z w : W) (h : ‖w‖ • z = ‖z‖ • w) : align z w = z := by
  by_cases hz : z = 0
  · simp [align, hz]
  · have hd : ‖z‖ + ‖w‖ ≠ 0 :=
      (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hz) (norm_nonneg _)).ne'
    have he : ‖z‖ • (z + w) = (‖z‖ + ‖w‖) • z := by
      rw [smul_add, ← h, add_smul]
    calc
      align z w = (‖z‖ + ‖w‖)⁻¹ • (‖z‖ • (z + w)) := by
        rw [align, smul_smul]
        congr 1
        ring
      _ = (‖z‖ + ‖w‖)⁻¹ • ((‖z‖ + ‖w‖) • z) := by rw [he]
      _ = z := by rw [smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem align_add_swap (z w : W) : align z w + align w z = z + w := by
  by_cases hd : ‖z‖ + ‖w‖ = 0
  · have hz : z = 0 := norm_eq_zero.mp (by linarith [norm_nonneg z, norm_nonneg w])
    have hw : w = 0 := norm_eq_zero.mp (by linarith [norm_nonneg z, norm_nonneg w])
    simp [hz, hw, align]
  · rw [align, align, add_comm w z, add_comm ‖w‖ ‖z‖, ← add_smul]
    have he : ‖z‖ / (‖z‖ + ‖w‖) + ‖w‖ / (‖z‖ + ‖w‖) = 1 := by
      rw [← add_div, div_self hd]
    rw [he, one_smul]

def interpolate (t : Time) (z w : W) : W := (1 - t.val) • z + t.val • align z w

theorem continuous_interpolate :
    Continuous (fun p : Time × (W × W) => interpolate p.1 p.2.1 p.2.2) := by
  have ht : Continuous (fun p : Time × (W × W) => p.1.val) := by fun_prop
  exact ((continuous_const.sub ht).smul (by fun_prop)).add
    (ht.smul (continuous_align.comp continuous_snd))

theorem interpolate_add_swap (t : Time) (z w : W) :
    interpolate t z w + interpolate t w z = z + w := by
  calc
    _ = (1 - t.val) • (z + w) + t.val • (align z w + align w z) := by
      simp only [interpolate, smul_add]
      abel
    _ = z + w := by rw [align_add_swap, ← add_smul, sub_add_cancel, one_smul]

theorem interpolate_fixes (t : Time) (z w : W) (h : ‖w‖ • z = ‖z‖ • w) :
    interpolate t z w = z := by
  rw [interpolate, align_eq_of_proportional z w h, ← add_smul, sub_add_cancel, one_smul]

theorem interpolate_ne_zero_of_unit (t : Time) (z w : W)
    (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) (hsum : z + w ≠ 0) :
    interpolate t z w ≠ 0 := by
  intro hzero
  have hs : 0 ≤ ‖w‖ := norm_nonneg _
  have hd : 0 < 1 + ‖w‖ := by linarith
  have ha : 0 ≤ (1 - t.val) + t.val * (1 / (1 + ‖w‖)) :=
    add_nonneg (sub_nonneg.mpr t.property.2)
      (mul_nonneg t.property.1 (div_nonneg zero_le_one hd.le))
  have hb : 0 ≤ t.val * (1 / (1 + ‖w‖)) :=
    mul_nonneg t.property.1 (div_nonneg zero_le_one hd.le)
  have hv : ((1 - t.val) + t.val * (1 / (1 + ‖w‖))) • z =
      -((t.val * (1 / (1 + ‖w‖))) • w) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [interpolate, align, hz, smul_add, smul_smul, add_smul, add_assoc] using hzero
  have hn := congrArg norm hv
  rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb, hz, mul_one] at hn
  have he : 1 + ‖w‖ = 2 * t.val * ‖w‖ := by
    field_simp [hd.ne'] at hn
    nlinarith
  have hts : t.val * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left hs t.property.2
  have hwu : ‖w‖ = 1 := by nlinarith
  have htu : t.val = 1 := by rw [hwu] at he; nlinarith
  have hh : ((1 / 2 : ℝ) • (z + w)) = 0 := by
    simpa only [interpolate, htu, sub_self, zero_smul, one_smul, zero_add,
      align, hz, hwu, one_add_one_eq_two] using hzero
  exact hsum ((smul_eq_zero.mp hh).resolve_left (by norm_num))

theorem norm_interpolate_eq_of_unit (t : Time) (z w : W) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖interpolate t z w‖ = ‖interpolate t w z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [interpolate, align, hz, hw, one_add_one_eq_two, smul_add, smul_smul]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq z, real_inner_self_eq_norm_sq w, hz, hw,
    real_inner_comm w z]

end AkopyanResearch.PairCommonAlignment
