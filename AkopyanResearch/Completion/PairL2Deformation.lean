module

public import AkopyanResearch.Completion.PairDeformation
public import Mathlib.Analysis.Real.Sqrt

/-!
# A strong deformation onto the exact quadratic-norm balanced locus

The normal pair complement consists of triples `(z,a,b)` with both `(z,a)`
and `(z,b)` nonzero. The retraction shortens the private vectors to their
smaller norm, then divides all three coordinates by the common Euclidean
radius. Straight-line interpolation remains in the complement and fixes
the locus `‖z‖²+‖a‖²=‖z‖²+‖b‖²=1` pointwise.

This is an explicit local deformation, not a connectivity theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairL2Deformation

open PairDeformation

variable {Z A B : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def radius2 (v : Raw (Z := Z) (A := A) (B := B)) : ℝ :=
  Real.sqrt (‖v.1‖ ^ 2 + (min ‖v.2.1‖ ‖v.2.2‖) ^ 2)

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem radius2_sq (v : Raw (Z := Z) (A := A) (B := B)) :
    radius2 v ^ 2 = ‖v.1‖ ^ 2 + (min ‖v.2.1‖ ‖v.2.2‖) ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem radius2_pos (v : Complement (Z := Z) (A := A) (B := B)) : 0 < radius2 v.val := by
  apply Real.sqrt_pos.mpr
  by_cases hz : v.val.1 = 0
  · have ha : v.val.2.1 ≠ 0 := v.property.1.resolve_left (not_not.mpr hz)
    have hb : v.val.2.2 ≠ 0 := v.property.2.resolve_left (not_not.mpr hz)
    have hm : 0 < min ‖v.val.2.1‖ ‖v.val.2.2‖ :=
      lt_min (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
    simpa only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] using pow_pos hm 2
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hz) 2) (sq_nonneg _)

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem continuous_radius2 : Continuous (radius2 (Z := Z) (A := A) (B := B)) :=
  Real.continuous_sqrt.comp ((continuous_fst.norm.pow 2).add
    (((continuous_fst.comp continuous_snd).norm.min
      (continuous_snd.comp continuous_snd).norm).pow 2))

abbrev Balanced2 := {v : Raw (Z := Z) (A := A) (B := B) //
  ‖v.1‖ ^ 2 + ‖v.2.1‖ ^ 2 = 1 ∧ ‖v.1‖ ^ 2 + ‖v.2.2‖ ^ 2 = 1}

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem balanced2_norms (v : Balanced2 (Z := Z) (A := A) (B := B)) :
    ‖v.val.2.1‖ = ‖v.val.2.2‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith [v.property.1, v.property.2]

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem balanced2_safe (v : Balanced2 (Z := Z) (A := A) (B := B)) : Safe v.val := by
  by_cases hz : v.val.1 = 0
  · constructor
    · right
      intro ha
      have h := v.property.1
      simp [hz, ha] at h
    · right
      intro hb
      have h := v.property.2
      simp [hz, hb] at h
  · exact ⟨Or.inl hz, Or.inl hz⟩

def inclusion (v : Balanced2 (Z := Z) (A := A) (B := B)) :
    Complement (Z := Z) (A := A) (B := B) :=
  ⟨v.val, balanced2_safe v⟩

def retractionRaw (v : Complement (Z := Z) (A := A) (B := B)) :
    Raw (Z := Z) (A := A) (B := B) :=
  ((radius2 v.val)⁻¹ • v.val.1,
    (radius2 v.val)⁻¹ • shorten v.val.2.1 v.val.2.2,
    (radius2 v.val)⁻¹ • shorten v.val.2.2 v.val.2.1)

theorem retractionRaw_balanced (v : Complement (Z := Z) (A := A) (B := B)) :
    ‖(retractionRaw v).1‖ ^ 2 + ‖(retractionRaw v).2.1‖ ^ 2 = 1 ∧
      ‖(retractionRaw v).1‖ ^ 2 + ‖(retractionRaw v).2.2‖ ^ 2 = 1 := by
  have hr : 0 < radius2 v.val := radius2_pos v
  have hi : |(radius2 v.val)⁻¹| = (radius2 v.val)⁻¹ := abs_of_pos (inv_pos.mpr hr)
  have hn : ((radius2 v.val)⁻¹ * ‖v.val.1‖) ^ 2 +
      ((radius2 v.val)⁻¹ * min ‖v.val.2.1‖ ‖v.val.2.2‖) ^ 2 = 1 := by
    calc
      _ = (radius2 v.val)⁻¹ ^ 2 *
          (‖v.val.1‖ ^ 2 + (min ‖v.val.2.1‖ ‖v.val.2.2‖) ^ 2) := by ring
      _ = (radius2 v.val)⁻¹ ^ 2 * radius2 v.val ^ 2 := by rw [radius2_sq]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  simp only [retractionRaw, norm_smul, Real.norm_eq_abs, hi, norm_shorten]
  exact ⟨hn, by simpa only [min_comm] using hn⟩

def retraction (v : Complement (Z := Z) (A := A) (B := B)) :
    Balanced2 (Z := Z) (A := A) (B := B) :=
  ⟨retractionRaw v, retractionRaw_balanced v⟩

theorem continuous_retractionRaw :
    Continuous (retractionRaw (Z := Z) (A := A) (B := B)) := by
  have hr : Continuous (fun v : Complement (Z := Z) (A := A) (B := B) =>
      (radius2 v.val)⁻¹) :=
    (continuous_radius2.comp continuous_subtype_val).inv₀ (fun v => (radius2_pos v).ne')
  have hz := continuous_fst.comp (continuous_subtype_val (p := Safe (Z := Z) (A := A) (B := B)))
  have ha := (continuous_fst.comp continuous_snd).comp
    (continuous_subtype_val (p := Safe (Z := Z) (A := A) (B := B)))
  have hb := (continuous_snd.comp continuous_snd).comp
    (continuous_subtype_val (p := Safe (Z := Z) (A := A) (B := B)))
  exact (hr.smul hz).prodMk ((hr.smul (continuous_shorten.comp (ha.prodMk hb))).prodMk
    (hr.smul (continuous_shorten.comp (hb.prodMk ha))))

theorem continuous_retraction :
    Continuous (retraction (Z := Z) (A := A) (B := B)) :=
  continuous_retractionRaw.subtype_mk _

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem continuous_inclusion : Continuous (inclusion (Z := Z) (A := A) (B := B)) :=
  continuous_subtype_val.subtype_mk _

theorem retraction_inclusion (v : Balanced2 (Z := Z) (A := A) (B := B)) :
    retraction (inclusion v) = v := by
  have he := balanced2_norms v
  have hr : radius2 v.val = 1 := by
    rw [radius2, min_eq_left he.le, v.property.1, Real.sqrt_one]
  apply Subtype.ext
  change ((radius2 v.val)⁻¹ • v.val.1,
    (radius2 v.val)⁻¹ • shorten v.val.2.1 v.val.2.2,
    (radius2 v.val)⁻¹ • shorten v.val.2.2 v.val.2.1) = v.val
  rw [hr, inv_one, one_smul, one_smul, one_smul,
    shorten_eq_left _ _ he.le, shorten_eq_left _ _ he.symm.le]

private theorem interpolate_positive (t : Time) (a : ℝ) (ha : 0 < a) :
    0 < (1 - t.val) + t.val * a := by
  by_cases ht : t.val = 0
  · simp [ht]
  · have htp : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2) (mul_pos htp ha)

def deformationRaw (p : Time × Complement (Z := Z) (A := A) (B := B)) :
    Raw (Z := Z) (A := A) (B := B) :=
  (1 - p.1.val) • p.2.val + p.1.val • retractionRaw p.2

theorem deformationRaw_safe (t : Time)
    (v : Complement (Z := Z) (A := A) (B := B)) : Safe (deformationRaw (t, v)) := by
  have hr : 0 < (radius2 v.val)⁻¹ := inv_pos.mpr (radius2_pos v)
  by_cases hz : v.val.1 = 0
  · have ha : v.val.2.1 ≠ 0 := v.property.1.resolve_left (not_not.mpr hz)
    have hb : v.val.2.2 ≠ 0 := v.property.2.resolve_left (not_not.mpr hz)
    have hna : 0 < ‖v.val.2.1‖ := norm_pos_iff.mpr ha
    have hnb : 0 < ‖v.val.2.2‖ := norm_pos_iff.mpr hb
    have hca : 0 < (radius2 v.val)⁻¹ * (min ‖v.val.2.1‖ ‖v.val.2.2‖ / ‖v.val.2.1‖) :=
      mul_pos hr (div_pos (lt_min hna hnb) hna)
    have hcb : 0 < (radius2 v.val)⁻¹ * (min ‖v.val.2.2‖ ‖v.val.2.1‖ / ‖v.val.2.2‖) :=
      mul_pos hr (div_pos (lt_min hnb hna) hnb)
    constructor
    · right
      change (1 - t.val) • v.val.2.1 +
        t.val • ((radius2 v.val)⁻¹ • ((min ‖v.val.2.1‖ ‖v.val.2.2‖ / ‖v.val.2.1‖) • v.val.2.1)) ≠ 0
      rw [smul_smul, smul_smul, mul_assoc, ← add_smul]
      exact smul_ne_zero (ne_of_gt (interpolate_positive t _ hca)) ha
    · right
      change (1 - t.val) • v.val.2.2 +
        t.val • ((radius2 v.val)⁻¹ • ((min ‖v.val.2.2‖ ‖v.val.2.1‖ / ‖v.val.2.2‖) • v.val.2.2)) ≠ 0
      rw [smul_smul, smul_smul, mul_assoc, ← add_smul]
      exact smul_ne_zero (ne_of_gt (interpolate_positive t _ hcb)) hb
  · have h : (deformationRaw (t, v)).1 ≠ 0 := by
      change (1 - t.val) • v.val.1 + t.val • ((radius2 v.val)⁻¹ • v.val.1) ≠ 0
      rw [smul_smul, ← add_smul]
      exact smul_ne_zero (ne_of_gt (interpolate_positive t _ hr)) hz
    exact ⟨Or.inl h, Or.inl h⟩

def deformation (p : Time × Complement (Z := Z) (A := A) (B := B)) :
    Complement (Z := Z) (A := A) (B := B) :=
  ⟨deformationRaw p, deformationRaw_safe p.1 p.2⟩

theorem continuous_deformation : Continuous (deformation (Z := Z) (A := A) (B := B)) := by
  apply Continuous.subtype_mk
  have ht : Continuous (fun p : Time × Complement (Z := Z) (A := A) (B := B) => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub ht).smul (continuous_subtype_val.comp continuous_snd)).add
    (ht.smul (continuous_retractionRaw.comp continuous_snd))

theorem deformation_start (v : Complement (Z := Z) (A := A) (B := B)) :
    deformation (⟨0, by simp⟩, v) = v := by
  apply Subtype.ext
  simp [deformation, deformationRaw]

theorem deformation_end (v : Complement (Z := Z) (A := A) (B := B)) :
    deformation (⟨1, by simp⟩, v) = inclusion (retraction v) := by
  apply Subtype.ext
  simp [deformation, deformationRaw, inclusion, retraction]

theorem deformation_fixes_balanced (t : Time)
    (v : Balanced2 (Z := Z) (A := A) (B := B)) :
    deformation (t, inclusion v) = inclusion v := by
  have hr : retractionRaw (inclusion v) = v.val :=
    congrArg Subtype.val (retraction_inclusion v)
  apply Subtype.ext
  change (1 - t.val) • v.val + t.val • retractionRaw (inclusion v) = v.val
  rw [hr, ← add_smul, sub_add_cancel, one_smul]

/-- All continuity, endpoint, and relative-fixing assertions for the actual
displayed retraction and homotopy, bundled for independent verification. -/
theorem strong_deformation_retraction :
    Continuous (inclusion (Z := Z) (A := A) (B := B)) ∧
    Continuous (retraction (Z := Z) (A := A) (B := B)) ∧
    (∀ v : Balanced2 (Z := Z) (A := A) (B := B), retraction (inclusion v) = v) ∧
    Continuous (deformation (Z := Z) (A := A) (B := B)) ∧
    (∀ v : Complement (Z := Z) (A := A) (B := B), deformation (⟨0, by simp⟩, v) = v) ∧
    (∀ v : Complement (Z := Z) (A := A) (B := B),
      deformation (⟨1, by simp⟩, v) = inclusion (retraction v)) ∧
    (∀ (t : Time) (v : Balanced2 (Z := Z) (A := A) (B := B)),
      deformation (t, inclusion v) = inclusion v) :=
  ⟨continuous_inclusion, continuous_retraction, retraction_inclusion,
    continuous_deformation, deformation_start, deformation_end, deformation_fixes_balanced⟩


end AkopyanResearch.PairL2Deformation
