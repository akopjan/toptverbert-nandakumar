module

public import AkopyanResearch.PairNormalChart


@[expose] public section

/-!
# A sphere chart preserving a nonzero common component

For real inner-product spaces `F` and `E`, the open part of the unit sphere
of `F ⊕ E` with nonzero `E`-component is explicitly homeomorphic to
`F × sphere(E)`. We use the squared-norm equation rather than a choice of
norm on the ordinary product type.
-/

noncomputable section

namespace AkopyanResearch.SplitSphereChart

open PairNormalChart

set_option linter.unusedSectionVars false

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

abbrev UnitDirections (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

abbrev UnitSplit (F E : Type*) [NormedAddCommGroup F] [NormedAddCommGroup E] :=
  {vw : F × E // ‖vw.1‖ ^ 2 + ‖vw.2‖ ^ 2 = 1 ∧ vw.2 ≠ 0}

def normalizedDirection (w : E) : E := ‖w‖⁻¹ • w

lemma normalizedDirection_unit {w : E} (hw : w ≠ 0) : ‖normalizedDirection w‖ = 1 := by
  simp [normalizedDirection, norm_smul, norm_ne_zero_iff.mpr hw]

lemma common_norm {r : F} {w : E} (hw : ‖w‖ = 1) :
    ‖(sharedScale r)⁻¹ • w‖ = (sharedScale r)⁻¹ := by
  rw [norm_smul, hw, mul_one, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sharedScale_pos r))]

lemma scaled_pair_unit (r : F) {w : E} (hw : ‖w‖ = 1) :
    ‖(sharedScale r)⁻¹ • r‖ ^ 2 + ‖(sharedScale r)⁻¹ • w‖ ^ 2 = 1 := by
  rw [norm_sq_smul, norm_sq_smul, hw]
  have hd := sharedScale_sq r
  have hn := ne_of_gt (sharedScale_pos r)
  field_simp
  nlinarith

def toSplit (x : F × UnitDirections E) : UnitSplit F E :=
  ⟨((sharedScale x.1)⁻¹ • x.1, (sharedScale x.1)⁻¹ • x.2.val),
    scaled_pair_unit x.1 x.2.property, by
      have hnorm := common_norm (r := x.1) x.2.property
      intro h
      change (sharedScale x.1)⁻¹ • x.2.val = 0 at h
      rw [h, norm_zero] at hnorm
      exact (ne_of_gt (inv_pos.mpr (sharedScale_pos x.1))) hnorm.symm⟩

def fromSplit (x : UnitSplit F E) : F × UnitDirections E :=
  (‖x.val.2‖⁻¹ • x.val.1,
    ⟨normalizedDirection x.val.2, normalizedDirection_unit x.property.2⟩)

theorem fromSplit_toSplit (x : F × UnitDirections E) : fromSplit (toSplit x) = x := by
  apply Prod.ext
  · change ‖(sharedScale x.1)⁻¹ • x.2.val‖⁻¹ •
      ((sharedScale x.1)⁻¹ • x.1) = x.1
    rw [common_norm x.2.property, inv_inv, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (sharedScale_pos x.1)), one_smul]
  · apply Subtype.ext
    change ‖(sharedScale x.1)⁻¹ • x.2.val‖⁻¹ •
      ((sharedScale x.1)⁻¹ • x.2.val) = x.2.val
    rw [common_norm x.2.property, inv_inv, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (sharedScale_pos x.1)), one_smul]

lemma scale_fromSplit (x : UnitSplit F E) :
    sharedScale (‖x.val.2‖⁻¹ • x.val.1) = ‖x.val.2‖⁻¹ := by
  have hb : 0 < ‖x.val.2‖ := norm_pos_iff.mpr x.property.2
  have hu := x.property.1
  have hs := sharedScale_sq (‖x.val.2‖⁻¹ • x.val.1)
  rw [norm_sq_smul] at hs
  have heq : sharedScale (‖x.val.2‖⁻¹ • x.val.1) ^ 2 = (‖x.val.2‖⁻¹) ^ 2 := by
    rw [hs]
    field_simp
    nlinarith
  have hp := sharedScale_pos (‖x.val.2‖⁻¹ • x.val.1)
  have hi := inv_pos.mpr hb
  nlinarith

theorem toSplit_fromSplit (x : UnitSplit F E) : toSplit (fromSplit x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · change (sharedScale (‖x.val.2‖⁻¹ • x.val.1))⁻¹ •
      (‖x.val.2‖⁻¹ • x.val.1) = x.val.1
    rw [scale_fromSplit x, inv_inv, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property.2), one_smul]
  · change (sharedScale (‖x.val.2‖⁻¹ • x.val.1))⁻¹ •
      (‖x.val.2‖⁻¹ • x.val.2) = x.val.2
    rw [scale_fromSplit x, inv_inv, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property.2), one_smul]

theorem continuous_toSplit : Continuous (toSplit (E := E) (F := F)) := by
  have hr : Continuous (fun x : F × UnitDirections E => x.1) := continuous_fst
  have hw : Continuous (fun x : F × UnitDirections E => x.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hs : Continuous (fun x : F × UnitDirections E => sharedScale x.1) := by
    unfold sharedScale
    fun_prop
  have hi := hs.inv₀ (fun x => ne_of_gt (sharedScale_pos x.1))
  apply Continuous.subtype_mk
  exact (hi.smul hr).prodMk (hi.smul hw)

theorem continuous_fromSplit : Continuous (fromSplit (E := E) (F := F)) := by
  have hv : Continuous (fun x : UnitSplit F E => x.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hw : Continuous (fun x : UnitSplit F E => x.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hi := hw.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property.2)
  exact (hi.smul hv).prodMk ((hi.smul hw).subtype_mk _)

/-- The common component's unit direction and the residual/common ratio are
global coordinates on this open part of the sphere. -/
def splitHomeomorph : (F × UnitDirections E) ≃ₜ UnitSplit F E where
  toFun := toSplit
  invFun := fromSplit
  left_inv := fromSplit_toSplit
  right_inv := toSplit_fromSplit
  continuous_toFun := continuous_toSplit
  continuous_invFun := continuous_fromSplit

end AkopyanResearch.SplitSphereChart
