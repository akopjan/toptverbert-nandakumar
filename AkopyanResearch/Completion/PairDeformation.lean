module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Tactic.NormNum

/-!
# A concrete retraction of the pair complement

For normed real spaces `Z`, `A`, `B`, the complement of the two coordinate
subspaces `(z,a)=0` and `(z,b)=0` retracts onto the locus
`‖z‖ + ‖a‖ = 1`, `‖a‖ = ‖b‖`.

The formulas remain continuous when one of `a,b` is zero. In particular, they
do not assume that division by a vanishing norm is a continuous operation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AkopyanResearch.PairDeformation

open Set Filter Topology

variable {Z A B : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Shorten the first vector to the smaller of the two norms. -/
def shorten (a : A) (b : B) : A := (min ‖a‖ ‖b‖ / ‖a‖) • a

omit [NormedSpace ℝ B] in
theorem norm_shorten (a : A) (b : B) : ‖shorten a b‖ = min ‖a‖ ‖b‖ := by
  by_cases ha : a = 0
  · simp [ha, shorten, norm_nonneg]
  · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    rw [shorten, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (le_min (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)),
      div_mul_cancel₀ _ hn]

omit [NormedSpace ℝ B] in
theorem norm_shorten_le (a : A) (b : B) : ‖shorten a b‖ ≤ ‖a‖ := by
  rw [norm_shorten]
  exact min_le_left _ _

omit [NormedSpace ℝ B] in
theorem shorten_eq_left (a : A) (b : B) (h : ‖a‖ ≤ ‖b‖) : shorten a b = a := by
  by_cases ha : a = 0
  · simp [ha, shorten]
  · simp [shorten, min_eq_left h, norm_ne_zero_iff.mpr ha]

omit [NormedSpace ℝ B] in
theorem continuous_shorten : Continuous (fun p : A × B => shorten p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.1 = 0
  · change Tendsto (fun p : A × B => shorten p.1 p.2) (𝓝 p) (𝓝 (shorten p.1 p.2))
    rw [hp]
    simp only [shorten, norm_zero, div_zero, zero_smul]
    apply squeeze_zero_norm (fun q : A × B => norm_shorten_le q.1 q.2)
    simpa only [hp, norm_zero] using continuous_fst.norm.continuousAt.tendsto (x := p)
  · exact (((continuous_fst.norm.min continuous_snd.norm).continuousAt.div
      continuous_fst.norm.continuousAt (norm_ne_zero_iff.mpr hp)).smul
      continuous_fst.continuousAt)

abbrev Raw := Z × A × B

/-- Both matching tests must be nonzero. -/
def Safe (v : Raw (Z := Z) (A := A) (B := B)) : Prop :=
  (v.1 ≠ 0 ∨ v.2.1 ≠ 0) ∧ (v.1 ≠ 0 ∨ v.2.2 ≠ 0)

abbrev Complement := {v : Raw (Z := Z) (A := A) (B := B) // Safe v}

def radius (v : Raw (Z := Z) (A := A) (B := B)) : ℝ :=
  ‖v.1‖ + min ‖v.2.1‖ ‖v.2.2‖

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem radius_pos (v : Complement (Z := Z) (A := A) (B := B)) : 0 < radius v.val := by
  rcases v with ⟨v, h⟩
  by_cases hz : v.1 = 0
  · have ha : v.2.1 ≠ 0 := h.1.resolve_left (not_not.mpr hz)
    have hb : v.2.2 ≠ 0 := h.2.resolve_left (not_not.mpr hz)
    simp only [radius, hz, norm_zero, zero_add]
    exact lt_min (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
  · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hz)
      (le_min (norm_nonneg _) (norm_nonneg _))

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem continuous_radius : Continuous (radius (Z := Z) (A := A) (B := B)) :=
  continuous_fst.norm.add ((continuous_fst.comp continuous_snd).norm.min
    (continuous_snd.comp continuous_snd).norm)

/-- The balanced norm locus is an embedded model of the required join. -/
abbrev Balanced := {v : Raw (Z := Z) (A := A) (B := B) //
  ‖v.1‖ + ‖v.2.1‖ = 1 ∧ ‖v.2.1‖ = ‖v.2.2‖}

omit [NormedSpace ℝ Z] [NormedSpace ℝ A] [NormedSpace ℝ B] in
theorem balanced_safe (v : Balanced (Z := Z) (A := A) (B := B)) : Safe v.val := by
  by_cases hz : v.val.1 = 0
  · have ha : ‖v.val.2.1‖ = 1 := by simpa [hz] using v.property.1
    have hb : ‖v.val.2.2‖ = 1 := v.property.2.symm.trans ha
    exact ⟨Or.inr (norm_ne_zero_iff.mp (by rw [ha]; norm_num)),
      Or.inr (norm_ne_zero_iff.mp (by rw [hb]; norm_num))⟩
  · exact ⟨Or.inl hz, Or.inl hz⟩

def inclusion (v : Balanced (Z := Z) (A := A) (B := B)) :
    Complement (Z := Z) (A := A) (B := B) :=
  ⟨v.val, balanced_safe v⟩

def retractionRaw (v : Complement (Z := Z) (A := A) (B := B)) :
    Raw (Z := Z) (A := A) (B := B) :=
  ((radius v.val)⁻¹ • v.val.1,
    (radius v.val)⁻¹ • shorten v.val.2.1 v.val.2.2,
    (radius v.val)⁻¹ • shorten v.val.2.2 v.val.2.1)

theorem retractionRaw_balanced (v : Complement (Z := Z) (A := A) (B := B)) :
    ‖(retractionRaw v).1‖ + ‖(retractionRaw v).2.1‖ = 1 ∧
      ‖(retractionRaw v).2.1‖ = ‖(retractionRaw v).2.2‖ := by
  have hr : 0 < radius v.val := radius_pos v
  have hi : |(radius v.val)⁻¹| = (radius v.val)⁻¹ := abs_of_pos (inv_pos.mpr hr)
  simp only [retractionRaw, norm_smul, Real.norm_eq_abs, hi, norm_shorten]
  constructor
  · rw [← mul_add]
    exact inv_mul_cancel₀ (ne_of_gt hr)
  · rw [min_comm]

def retraction (v : Complement (Z := Z) (A := A) (B := B)) :
    Balanced (Z := Z) (A := A) (B := B) :=
  ⟨retractionRaw v, retractionRaw_balanced v⟩

theorem continuous_retractionRaw :
    Continuous (retractionRaw (Z := Z) (A := A) (B := B)) := by
  have hr : Continuous (fun v : Complement (Z := Z) (A := A) (B := B) =>
      (radius v.val)⁻¹) :=
    (continuous_radius.comp continuous_subtype_val).inv₀ (fun v => ne_of_gt (radius_pos v))
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

theorem retraction_inclusion (v : Balanced (Z := Z) (A := A) (B := B)) :
    retraction (inclusion v) = v := by
  have hr : radius v.val = 1 := by
    simp only [radius, ← v.property.2, min_self]
    exact v.property.1
  apply Subtype.ext
  change ((radius v.val)⁻¹ • v.val.1,
    (radius v.val)⁻¹ • shorten v.val.2.1 v.val.2.2,
    (radius v.val)⁻¹ • shorten v.val.2.2 v.val.2.1) = v.val
  rw [hr, inv_one, one_smul, one_smul, one_smul,
    shorten_eq_left _ _ (le_of_eq v.property.2),
    shorten_eq_left _ _ (le_of_eq v.property.2.symm)]

abbrev Time := Set.Icc (0 : ℝ) 1

private theorem interpolate_positive (t : Time) (a : ℝ) (ha : 0 < a) :
    0 < (1 - t.val) + t.val * a := by
  by_cases ht : t.val = 0
  · simp [ht]
  · have htp : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2) (mul_pos htp ha)

/-- Straight-line motion to the retraction, before recording its safety. -/
def deformationRaw (p : Time × Complement (Z := Z) (A := A) (B := B)) :
    Raw (Z := Z) (A := A) (B := B) :=
  (1 - p.1.val) • p.2.val + p.1.val • retractionRaw p.2

theorem deformationRaw_safe (t : Time)
    (v : Complement (Z := Z) (A := A) (B := B)) : Safe (deformationRaw (t, v)) := by
  have hr : 0 < (radius v.val)⁻¹ := inv_pos.mpr (radius_pos v)
  by_cases hz : v.val.1 = 0
  · have ha : v.val.2.1 ≠ 0 := v.property.1.resolve_left (not_not.mpr hz)
    have hb : v.val.2.2 ≠ 0 := v.property.2.resolve_left (not_not.mpr hz)
    have hna : 0 < ‖v.val.2.1‖ := norm_pos_iff.mpr ha
    have hnb : 0 < ‖v.val.2.2‖ := norm_pos_iff.mpr hb
    have hca : 0 < (radius v.val)⁻¹ * (min ‖v.val.2.1‖ ‖v.val.2.2‖ / ‖v.val.2.1‖) :=
      mul_pos hr (div_pos (lt_min hna hnb) hna)
    have hcb : 0 < (radius v.val)⁻¹ * (min ‖v.val.2.2‖ ‖v.val.2.1‖ / ‖v.val.2.2‖) :=
      mul_pos hr (div_pos (lt_min hnb hna) hnb)
    constructor
    · right
      change (1 - t.val) • v.val.2.1 +
        t.val • ((radius v.val)⁻¹ • ((min ‖v.val.2.1‖ ‖v.val.2.2‖ / ‖v.val.2.1‖) • v.val.2.1)) ≠ 0
      rw [smul_smul, smul_smul, mul_assoc, ← add_smul]
      exact smul_ne_zero (ne_of_gt (interpolate_positive t _ hca)) ha
    · right
      change (1 - t.val) • v.val.2.2 +
        t.val • ((radius v.val)⁻¹ • ((min ‖v.val.2.2‖ ‖v.val.2.1‖ / ‖v.val.2.2‖) • v.val.2.2)) ≠ 0
      rw [smul_smul, smul_smul, mul_assoc, ← add_smul]
      exact smul_ne_zero (ne_of_gt (interpolate_positive t _ hcb)) hb
  · have h : (deformationRaw (t, v)).1 ≠ 0 := by
      change (1 - t.val) • v.val.1 + t.val • ((radius v.val)⁻¹ • v.val.1) ≠ 0
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
    (v : Balanced (Z := Z) (A := A) (B := B)) :
    deformation (t, inclusion v) = inclusion v := by
  have hr : retractionRaw (inclusion v) = v.val :=
    congrArg Subtype.val (retraction_inclusion v)
  apply Subtype.ext
  change (1 - t.val) • v.val + t.val • retractionRaw (inclusion v) = v.val
  rw [hr, ← add_smul, sub_add_cancel, one_smul]

end AkopyanResearch.PairDeformation

