module

public import Mathlib

/-!
# Explicit normal spheres in a subspace-arrangement complement

Near a point of one forbidden subspace which belongs to no other forbidden
subspace, a small normal sphere lies in the arrangement complement. Normalized
linear projection is a retraction onto this sphere. The construction below is
given for an arbitrary open neighbourhood of that point, so it applies after
removing all the other subspaces.

This is an actual section and retraction, with both continuity proofs. It does
not identify the homotopy type of an arrangement complement.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LocalLink

open Metric

variable {E N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

abbrev UnitSphere (N : Type*) [NormedAddCommGroup N] := Metric.sphere (0 : N) 1

abbrev PuncturedNeighbourhood (Q : E →L[ℝ] N) (U : Set E) :=
  {x : E // x ∈ U ∧ Q x ≠ 0}

/-- Normalized projection from the complement of a kernel to its normal
unit sphere. -/
def normalProjection (Q : E →L[ℝ] N) (U : Set E)
    (x : PuncturedNeighbourhood Q U) : UnitSphere N :=
  ⟨‖Q x.1‖⁻¹ • Q x.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr x.2.2⟩

theorem continuous_normalProjection (Q : E →L[ℝ] N) (U : Set E) :
    Continuous (normalProjection Q U) := by
  have hQ : Continuous (fun x : PuncturedNeighbourhood Q U => Q x.1) :=
    Q.continuous.comp continuous_subtype_val
  exact ((hQ.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.2.2)).smul hQ).subtype_mk _

/-- A continuous linear right inverse provides a small linking sphere inside
any open neighbourhood of a point of the kernel. -/
theorem exists_linking_sphere_retract
    (Q : E →L[ℝ] N) (L : N →L[ℝ] E) (hL : Function.LeftInverse Q L)
    (U : Set E) (hU : IsOpen U) (a : E) (ha : a ∈ U) (hQa : Q a = 0) :
    ∃ s : UnitSphere N → PuncturedNeighbourhood Q U,
      Continuous s ∧ Function.LeftInverse (normalProjection Q U) s := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let ε : ℝ := r / (‖L‖ + 1)
  have hden : 0 < ‖L‖ + 1 := by positivity
  have hε : 0 < ε := div_pos hr hden
  have hscale : ε * ‖L‖ < r := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  let link : UnitSphere N → E := fun y => a + ε • L y.1
  have hlink : Continuous link :=
    continuous_const.add (continuous_const.smul (L.continuous.comp continuous_subtype_val))
  have hlink_mem (y : UnitSphere N) : link y ∈ U := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    change ‖a + ε • L y.1 - a‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
    have hy : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
    have hbound : ‖L y.1‖ ≤ ‖L‖ := by
      simpa [hy] using L.le_opNorm y.1
    exact (mul_le_mul_of_nonneg_left hbound hε.le).trans_lt hscale
  have hQlink (y : UnitSphere N) : Q (link y) = ε • y.1 := by
    simp only [link, map_add, map_smul, hQa, zero_add]
    rw [hL]
  have hlink_ne (y : UnitSphere N) : Q (link y) ≠ 0 := by
    rw [hQlink]
    apply smul_ne_zero hε.ne'
    intro hy
    have hn := mem_sphere_zero_iff_norm.mp y.2
    rw [hy, norm_zero] at hn
    exact zero_ne_one hn
  let s : UnitSphere N → PuncturedNeighbourhood Q U :=
    fun y => ⟨link y, hlink_mem y, hlink_ne y⟩
  refine ⟨s, hlink.subtype_mk _, ?_⟩
  intro y
  apply Subtype.ext
  change ‖Q (link y)‖⁻¹ • Q (link y) = y.1
  rw [hQlink, norm_smul, Real.norm_of_nonneg hε.le,
    mem_sphere_zero_iff_norm.mp y.2, mul_one, smul_smul,
    inv_mul_cancel₀ hε.ne', one_smul]

end AkopyanResearch.LocalLink
