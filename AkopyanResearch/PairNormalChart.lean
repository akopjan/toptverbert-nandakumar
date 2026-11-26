module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
# Algebra of the explicit normal chart of the pair anti-diagonal

The two directions `p` and `q` are unit vectors with `p ≠ q`.
Their normalized difference is the base point on the anti-diagonal, and
their normalized sum is its perpendicular normal coordinate.

These formulas replace the local linear-algebra part of a tubular-neighborhood
argument. The complete open-chart homeomorphism is not asserted in this file.
-/

noncomputable section

namespace AkopyanResearch.PairNormalChart

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def base (p q : E) : E := ‖p - q‖⁻¹ • (p - q)

def offset (p q : E) : E := ‖p - q‖⁻¹ • (p + q)

lemma direction_distance_pos {p q : E} (hne : p ≠ q) : 0 < ‖p - q‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr hne)

lemma norm_sq_smul (a : ℝ) (v : E) : ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem base_unit {p q : E} (hne : p ≠ q) : ‖base p q‖ = 1 := by
  have hd := direction_distance_pos hne
  simp [base, norm_smul, ne_of_gt hd]

theorem offset_perpendicular {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ⟪base p q, offset p q⟫_ℝ = 0 := by
  simp [base, offset, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_add_right, real_inner_comm q p, hp, hq]
  ring

theorem direction_parallelogram {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p - q‖ ^ 2 + ‖p + q‖ ^ 2 = 4 := by
  rw [norm_sub_sq_real, norm_add_sq_real, hp, hq]
  ring

theorem offset_norm_identity {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hne : p ≠ q) :
    1 + ‖offset p q‖ ^ 2 = 4 / ‖p - q‖ ^ 2 := by
  have hd := ne_of_gt (direction_distance_pos hne)
  have hpar := direction_parallelogram hp hq
  rw [offset, norm_sq_smul]
  field_simp
  nlinarith

theorem base_add_offset (p q : E) :
    base p q + offset p q = (2 / ‖p - q‖) • p := by
  simp only [base, offset, ← smul_add, sub_add_add_cancel, div_eq_mul_inv]
  module

theorem neg_base_add_offset (p q : E) :
    -base p q + offset p q = (2 / ‖p - q‖) • q := by
  simp only [base, offset, ← smul_neg, ← smul_add, div_eq_mul_inv]
  module

def sharedScale (z : E) : ℝ := Real.sqrt (1 + ‖z‖ ^ 2)

theorem sharedScale_pos (z : E) : 0 < sharedScale z := by
  exact Real.sqrt_pos.2 (by positivity)

theorem sharedScale_sq (z : E) : sharedScale z ^ 2 = 1 + ‖z‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

def directionPlus (w z : E) : E := (sharedScale z)⁻¹ • (w + z)

def directionMinus (w z : E) : E := (sharedScale z)⁻¹ • (-w + z)

theorem directionPlus_unit {w z : E} (hw : ‖w‖ = 1)
    (hz : ⟪w, z⟫_ℝ = 0) : ‖directionPlus w z‖ = 1 := by
  have hsq : ‖directionPlus w z‖ ^ 2 = 1 := by
    rw [directionPlus, norm_sq_smul, norm_add_sq_real, hw, hz]
    have hd := sharedScale_sq z
    have hn := ne_of_gt (sharedScale_pos z)
    field_simp
    nlinarith
  nlinarith [norm_nonneg (directionPlus w z)]

theorem directionMinus_unit {w z : E} (hw : ‖w‖ = 1)
    (hz : ⟪w, z⟫_ℝ = 0) : ‖directionMinus w z‖ = 1 := by
  exact directionPlus_unit (w := -w) (by simpa using hw) (by simp [hz])

theorem directions_sub (w z : E) :
    directionPlus w z - directionMinus w z = (2 / sharedScale z) • w := by
  simp only [directionPlus, directionMinus, div_eq_mul_inv]
  module

theorem directions_add (w z : E) :
    directionPlus w z + directionMinus w z = (2 / sharedScale z) • z := by
  simp only [directionPlus, directionMinus, div_eq_mul_inv]
  module

theorem directions_distance {w z : E} (hw : ‖w‖ = 1) :
    ‖directionPlus w z - directionMinus w z‖ = 2 / sharedScale z := by
  rw [directions_sub, norm_smul, hw, mul_one, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) (sharedScale_pos z))]

theorem directions_ne {w z : E} (hw : ‖w‖ = 1) :
    directionPlus w z ≠ directionMinus w z := by
  intro h
  have hp := div_pos (by norm_num : (0 : ℝ) < 2) (sharedScale_pos z)
  have heq := directions_distance (z := z) hw
  simp [h] at heq
  linarith

theorem base_directions {w z : E} (hw : ‖w‖ = 1) :
    base (directionPlus w z) (directionMinus w z) = w := by
  rw [base, directions_distance hw, directions_sub, smul_smul]
  have hn : 2 / sharedScale z ≠ 0 := ne_of_gt (div_pos (by norm_num) (sharedScale_pos z))
  rw [inv_mul_cancel₀ hn, one_smul]

theorem offset_directions {w z : E} (hw : ‖w‖ = 1) :
    offset (directionPlus w z) (directionMinus w z) = z := by
  rw [offset, directions_distance hw, directions_add, smul_smul]
  have hn : 2 / sharedScale z ≠ 0 := ne_of_gt (div_pos (by norm_num) (sharedScale_pos z))
  rw [inv_mul_cancel₀ hn, one_smul]

theorem sharedScale_offset {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hne : p ≠ q) : sharedScale (offset p q) = 2 / ‖p - q‖ := by
  have hs := sharedScale_sq (offset p q)
  rw [offset_norm_identity hp hq hne] at hs
  have hd := direction_distance_pos hne
  have hright : (2 / ‖p - q‖) ^ 2 = 4 / ‖p - q‖ ^ 2 := by ring
  have hp' := sharedScale_pos (offset p q)
  have hq' := div_pos (by norm_num : (0 : ℝ) < 2) hd
  nlinarith

theorem directionPlus_base_offset {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hne : p ≠ q) : directionPlus (base p q) (offset p q) = p := by
  rw [directionPlus, sharedScale_offset hp hq hne, base_add_offset, smul_smul]
  have hn : 2 / ‖p - q‖ ≠ 0 := ne_of_gt (div_pos (by norm_num) (direction_distance_pos hne))
  rw [inv_mul_cancel₀ hn, one_smul]

theorem directionMinus_base_offset {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hne : p ≠ q) : directionMinus (base p q) (offset p q) = q := by
  rw [directionMinus, sharedScale_offset hp hq hne, neg_base_add_offset, smul_smul]
  have hn : 2 / ‖p - q‖ ≠ 0 := ne_of_gt (div_pos (by norm_num) (direction_distance_pos hne))
  rw [inv_mul_cancel₀ hn, one_smul]

/-- The elementary tangent-bundle model; no manifold structure is needed. -/
abbrev UnitTangent (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {wz : E × E // ‖wz.1‖ = 1 ∧ ⟪wz.1, wz.2⟫_ℝ = 0}

/-- Ordered distinct unit directions. -/
abbrev DistinctDirections (E : Type*) [NormedAddCommGroup E] :=
  {pq : E × E // ‖pq.1‖ = 1 ∧ ‖pq.2‖ = 1 ∧ pq.1 ≠ pq.2}

def directionsMap (x : UnitTangent E) : DistinctDirections E :=
  ⟨(directionPlus x.val.1 x.val.2, directionMinus x.val.1 x.val.2),
    directionPlus_unit x.property.1 x.property.2,
    directionMinus_unit x.property.1 x.property.2, directions_ne x.property.1⟩

def tangentMap (x : DistinctDirections E) : UnitTangent E :=
  ⟨(base x.val.1 x.val.2, offset x.val.1 x.val.2),
    base_unit x.property.2.2, offset_perpendicular x.property.1 x.property.2.1⟩

theorem tangent_directionsMap (x : UnitTangent E) : tangentMap (directionsMap x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · exact base_directions x.property.1
  · exact offset_directions x.property.1

theorem directions_tangentMap (x : DistinctDirections E) : directionsMap (tangentMap x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · exact directionPlus_base_offset x.property.1 x.property.2.1 x.property.2.2
  · exact directionMinus_base_offset x.property.1 x.property.2.1 x.property.2.2

theorem continuous_directionsMap : Continuous (directionsMap (E := E)) := by
  have hw : Continuous (fun x : UnitTangent E => x.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hz : Continuous (fun x : UnitTangent E => x.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hs : Continuous (fun x : UnitTangent E => sharedScale x.val.2) := by
    unfold sharedScale
    fun_prop
  have hi := hs.inv₀ (fun x => ne_of_gt (sharedScale_pos x.val.2))
  apply Continuous.subtype_mk
  exact (hi.smul (hw.add hz)).prodMk (hi.smul (hw.neg.add hz))

theorem continuous_tangentMap : Continuous (tangentMap (E := E)) := by
  have hp : Continuous (fun x : DistinctDirections E => x.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hq : Continuous (fun x : DistinctDirections E => x.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hi := (hp.sub hq).norm.inv₀
    (fun x => ne_of_gt (direction_distance_pos x.property.2.2))
  apply Continuous.subtype_mk
  exact (hi.smul (hp.sub hq)).prodMk (hi.smul (hp.add hq))

/-- An explicit global normal chart for the two common unit directions. -/
def directionsHomeomorph : UnitTangent E ≃ₜ DistinctDirections E where
  toFun := directionsMap
  invFun := tangentMap
  left_inv := tangent_directionsMap
  right_inv := directions_tangentMap
  continuous_toFun := continuous_directionsMap
  continuous_invFun := continuous_tangentMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def denominator (v : F) (z : E) : ℝ := Real.sqrt (1 + ‖v‖ ^ 2 + ‖z‖ ^ 2)

theorem denominator_pos (v : F) (z : E) : 0 < denominator v z := by
  unfold denominator
  exact Real.sqrt_pos.2 (by positivity)

theorem denominator_sq (v : F) (z : E) : denominator v z ^ 2 = 1 + ‖v‖ ^ 2 + ‖z‖ ^ 2 := by
  unfold denominator
  exact Real.sq_sqrt (by positivity)

theorem norm_add_orthogonal_unit {w z : E} (hw : ‖w‖ = 1)
    (hz : ⟪w, z⟫_ℝ = 0) : ‖w + z‖ ^ 2 = 1 + ‖z‖ ^ 2 := by
  rw [norm_add_sq_real, hw, hz]
  ring

theorem normalize_chart_unit {w z : E} {v : F} (hw : ‖w‖ = 1)
    (hz : ⟪w, z⟫_ℝ = 0) :
    ‖(denominator v z)⁻¹ • v‖ ^ 2 +
      ‖(denominator v z)⁻¹ • (w + z)‖ ^ 2 = 1 := by
  rw [norm_sq_smul, norm_sq_smul, norm_add_orthogonal_unit hw hz]
  have hd := denominator_sq v z
  have hn := ne_of_gt (denominator_pos v z)
  field_simp
  nlinarith

end AkopyanResearch.PairNormalChart
