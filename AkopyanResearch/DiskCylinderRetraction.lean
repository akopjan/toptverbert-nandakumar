module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp


@[expose] public section

/-!
# An explicit retraction used for disk homotopy extension

The closed unit disk times `[0,1]` retracts onto its bottom and side.
Projection is along rays starting at `(0,2)`. The denominator is at least
`1/2` on the cylinder. Thus no general cofibration or homotopy-extension
theorem is needed for this particular geometric ingredient.
-/

noncomputable section

namespace AkopyanResearch

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cylinderDenominator (p : E × ℝ) : ℝ := max (1 - p.2 / 2) ‖p.1‖

def diskCylinderRetraction (p : E × ℝ) : E × ℝ :=
  ((cylinderDenominator p)⁻¹ • p.1, 2 + (p.2 - 2) / cylinderDenominator p)

def closedDiskCylinder : Set (E × ℝ) :=
  {p | ‖p.1‖ ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

lemma cylinderDenominator_pos {p : E × ℝ} (ht : p.2 ≤ 1) :
    0 < cylinderDenominator p := by
  have hleft : 0 < 1 - p.2 / 2 := by linarith
  exact lt_of_lt_of_le hleft (le_max_left _ _)

lemma cylinderDenominator_le_one {p : E × ℝ} (hp : p ∈ closedDiskCylinder) :
    cylinderDenominator p ≤ 1 := by
  exact max_le (by linarith [hp.2.1]) hp.1

lemma diskCylinderRetraction_norm {p : E × ℝ} (ht : p.2 ≤ 1) :
    ‖(diskCylinderRetraction p).1‖ = ‖p.1‖ / cylinderDenominator p := by
  have hd := cylinderDenominator_pos ht
  simp only [diskCylinderRetraction, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hd)]
  exact inv_mul_eq_div _ _

theorem diskCylinderRetraction_mem {p : E × ℝ} (hp : p ∈ closedDiskCylinder) :
    diskCylinderRetraction p ∈ closedDiskCylinder := by
  have hd := cylinderDenominator_pos hp.2.2
  have hd1 := cylinderDenominator_le_one hp
  have hbottom : 1 - p.2 / 2 ≤ cylinderDenominator p := le_max_left _ _
  have hnorm : ‖p.1‖ ≤ cylinderDenominator p := le_max_right _ _
  constructor
  · rw [diskCylinderRetraction_norm hp.2.2]
    exact (div_le_one hd).mpr hnorm
  · change 0 ≤ 2 + (p.2 - 2) / cylinderDenominator p ∧
      2 + (p.2 - 2) / cylinderDenominator p ≤ 1
    have hlow : -2 ≤ (p.2 - 2) / cylinderDenominator p := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hhigh : (p.2 - 2) / cylinderDenominator p ≤ -1 := by
      apply (div_le_iff₀ hd).mpr
      linarith [hp.2.2]
    constructor <;> linarith

/-- Every image point belongs to the bottom or the side of the cylinder. -/
theorem diskCylinderRetraction_bottom_or_side {p : E × ℝ}
    (hp : p ∈ closedDiskCylinder) :
    (diskCylinderRetraction p).2 = 0 ∨ ‖(diskCylinderRetraction p).1‖ = 1 := by
  have hd := cylinderDenominator_pos hp.2.2
  rcases le_total ‖p.1‖ (1 - p.2 / 2) with h | h
  · left
    have heq : cylinderDenominator p = 1 - p.2 / 2 := max_eq_left h
    have hquot : (p.2 - 2) / cylinderDenominator p = -2 := by
      apply (div_eq_iff (ne_of_gt hd)).mpr
      rw [heq]
      ring
    change 2 + (p.2 - 2) / cylinderDenominator p = 0
    rw [hquot]
    norm_num
  · right
    have heq : cylinderDenominator p = ‖p.1‖ := max_eq_right h
    rw [diskCylinderRetraction_norm hp.2.2, ← heq]
    exact div_self (ne_of_gt hd)

theorem diskCylinderRetraction_fixes_bottom (x : E) (hx : ‖x‖ ≤ 1) :
    diskCylinderRetraction (x, 0) = (x, 0) := by
  have hd : cylinderDenominator (x, 0) = 1 := by
    simpa only [cylinderDenominator, zero_div, sub_zero] using max_eq_left hx
  simp [diskCylinderRetraction, hd]

theorem diskCylinderRetraction_fixes_side (x : E) (t : ℝ)
    (hx : ‖x‖ = 1) (ht : 0 ≤ t) :
    diskCylinderRetraction (x, t) = (x, t) := by
  have hd : cylinderDenominator (x, t) = 1 := by
    simp only [cylinderDenominator, hx]
    exact max_eq_right (by linarith)
  simp [diskCylinderRetraction, hd]

theorem continuousOn_diskCylinderRetraction :
    ContinuousOn (diskCylinderRetraction (E := E)) closedDiskCylinder := by
  have hden : Continuous (cylinderDenominator (E := E)) := by
    unfold cylinderDenominator
    fun_prop
  have hne : ∀ p ∈ closedDiskCylinder (E := E), cylinderDenominator p ≠ 0 :=
    fun _ hp => ne_of_gt (cylinderDenominator_pos hp.2.2)
  exact ((hden.continuousOn.inv₀ hne).smul continuous_fst.continuousOn).prodMk
    (continuous_const.continuousOn.add
      ((continuous_snd.sub continuous_const).continuousOn.div hden.continuousOn hne))

end AkopyanResearch
