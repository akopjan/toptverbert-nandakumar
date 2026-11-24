module

public import AkopyanResearch.Completion.SphereConnectivity
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Linarith

/-!
# Explicit radial equivalence of a punctured vector space and its sphere

The radial homotopy scales by a strictly positive real number at every
time. A finite-dimensional continuous linear equivalence then identifies
the punctured space with the corresponding ordinary Euclidean sphere.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PuncturedSpace

open ContinuousMap

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Space := {x : E // x ≠ 0}
abbrev Sphere := Metric.sphere (0 : E) 1

def inclusion : C(Sphere E, Space E) where
  toFun x := ⟨x.val, fun hx => by
    have hn := mem_sphere_zero_iff_norm.mp x.property
    rw [hx, norm_zero] at hn
    exact zero_ne_one hn⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def normalized (x : Space E) : E := ‖x.val‖⁻¹ • x.val

theorem normalized_mem (x : Space E) : normalized E x ∈ Sphere E := by
  rw [mem_sphere_zero_iff_norm]
  change ‖‖x.val‖⁻¹ • x.val‖ = 1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.property)]

def normalization : C(Space E, Sphere E) where
  toFun x := ⟨normalized E x, normalized_mem E x⟩
  continuous_toFun :=
    (((continuous_subtype_val.norm).inv₀
      (fun x : Space E => norm_ne_zero_iff.mpr x.property)).smul
      continuous_subtype_val).subtype_mk _

def factor (t : unitInterval) (x : Space E) : ℝ := 1 - t.val + t.val * ‖x.val‖⁻¹

theorem factor_pos (t : unitInterval) (x : Space E) : 0 < factor E t x := by
  have hinv : 0 < ‖x.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr x.property)
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · have hp := mul_nonneg t.property.1 hinv.le
    unfold factor
    linarith
  · unfold factor
    rw [ht, sub_self, one_mul, zero_add]
    exact hinv

def radialHomotopy : (ContinuousMap.id (Space E)).Homotopy
    ((inclusion E).comp (normalization E)) where
  toFun p := ⟨factor E p.1 p.2 • p.2.val,
    smul_ne_zero (factor_pos E p.1 p.2).ne' p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have ht : Continuous (fun p : unitInterval × Space E => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : unitInterval × Space E => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub ht).add (ht.mul
      (hx.norm.inv₀ (fun p => norm_ne_zero_iff.mpr p.2.property)))).smul hx
  map_zero_left x := by
    apply Subtype.ext
    change (1 - (0 : ℝ) + 0 * ‖x.val‖⁻¹) • x.val = x.val
    simp
  map_one_left x := by
    apply Subtype.ext
    change (1 - (1 : ℝ) + 1 * ‖x.val‖⁻¹) • x.val = ‖x.val‖⁻¹ • x.val
    simp

theorem normalization_inclusion :
    (normalization E).comp (inclusion E) = ContinuousMap.id (Sphere E) := by
  ext x
  change ‖x.val‖⁻¹ • x.val = x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

def radialEquiv : Space E ≃ₕ Sphere E where
  toFun := normalization E
  invFun := inclusion E
  left_inv := ⟨(radialHomotopy E).symm⟩
  right_inv := by rw [normalization_inclusion]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def linearHomeomorph (e : E ≃L[ℝ] F) : Space E ≃ₜ Space F :=
  e.toHomeomorph.subtype (fun x => by
    change x ≠ 0 ↔ e x ≠ 0
    exact (not_congr e.map_eq_zero_iff).symm)

/-- A punctured real vector space of dimension `n+1` has the ordinary
`n`-sphere as an explicit homotopy-equivalent model. -/
def sphereEquiv [FiniteDimensional ℝ E] (n : ℕ)
    (hdim : Module.finrank ℝ E = n + 1) : Space E ≃ₕ TopCat.sphere.{0} n := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
      rw [finrank_euclideanSpace_fin]
      exact hdim)).some
  exact (linearHomeomorph E e).toHomotopyEquiv.trans
    ((radialEquiv (EuclideanSpace ℝ (Fin (n + 1)))).trans
      (Homeomorph.ulift.symm.toHomotopyEquiv))

end AkopyanResearch.PuncturedSpace
