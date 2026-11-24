module

public import AkopyanResearch.Completion.ArrangementConnectivity
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Connectivity of the ordinary representation spheres

Radial normalization is a retraction from the complement of the origin to
the unit sphere. The proved finite-arrangement connectivity theorem thus
gives the usual vanishing range for its actual Mathlib homotopy groups.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.SphereConnectivity

open ContinuousMap
open scoped Topology.Homotopy

theorem pi_subsingleton_of_retract {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (s : C(Y, X)) (r : C(X, Y)) (hrs : r.comp s = ContinuousMap.id Y)
    (n : ℕ) (b : Y) (hX : Subsingleton (HomotopyGroup.Pi n X (s b))) :
    Subsingleton (HomotopyGroup.Pi n Y b) := by
  have hb : r (s b) = b := DFunLike.congr_fun hrs b
  refine ⟨fun a c => ?_⟩
  have heq := hX.elim
    (Submission.HomotopyGroup.map s (rfl : s b = s b) a)
    (Submission.HomotopyGroup.map s (rfl : s b = s b) c)
  have h := congrArg (Submission.HomotopyGroup.map r hb) heq
  simpa only [Submission.HomotopyGroup.map_map_of_comp_eq_id r s rfl hb hrs] using h

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev Sphere := Metric.sphere (0 : E) 1
abbrev Punctured := ArrangementConnectivity.Complement (fun _ : PUnit.{1} => (⊥ : Submodule ℝ E))

def sphereInclusion : C(Sphere E, Punctured E) :=
  ⟨fun x => ⟨x.val, fun _ h => by
      have hzero : x.val = 0 := h
      have hn := mem_sphere_zero_iff_norm.mp x.property
      rw [hzero, norm_zero] at hn
      exact zero_ne_one hn⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [FiniteDimensional ℝ E] in
theorem punctured_ne_zero (x : Punctured E) : x.val ≠ 0 :=
  fun h => x.property PUnit.unit h

def normalized (x : Punctured E) : E := ‖x.val‖⁻¹ • x.val

theorem normalized_mem_sphere (x : Punctured E) : normalized E x ∈ Sphere E := by
  rw [mem_sphere_zero_iff_norm]
  change ‖‖x.val‖⁻¹ • x.val‖ = 1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (punctured_ne_zero E x))]

theorem continuous_normalized : Continuous (normalized E) :=
  (((continuous_subtype_val.norm).inv₀
    (fun x => norm_ne_zero_iff.mpr (punctured_ne_zero E x))).smul
    continuous_subtype_val)

def normalization : C(Punctured E, Sphere E) where
  toFun x := ⟨normalized E x, normalized_mem_sphere E x⟩
  continuous_toFun := (continuous_normalized E).subtype_mk _

theorem normalization_inclusion :
    (normalization E).comp (sphereInclusion E) = ContinuousMap.id (Sphere E) := by
  ext x
  change ‖x.val‖⁻¹ • x.val = x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

theorem sphere_pi_vanish (n : ℕ) (hn : n + 2 ≤ Module.finrank ℝ E) (b : Sphere E) :
    Subsingleton (HomotopyGroup.Pi n (Sphere E) b) := by
  apply pi_subsingleton_of_retract (sphereInclusion E) (normalization E)
    (normalization_inclusion E)
  apply ArrangementConnectivity.subsingleton_homotopyGroup_of_codim
  intro _
  have hq := (⊥ : Submodule ℝ E).finrank_quotient_add_finrank
  simp only [finrank_bot, add_zero] at hq
  omega

theorem sphere_pathConnected (hn : 2 ≤ Module.finrank ℝ E) :
    PathConnectedSpace (Sphere E) := by
  let : PathConnectedSpace (Punctured E) :=
    ArrangementConnectivity.pathConnectedSpace_complement _ (fun _ => by
      simp only [finrank_bot]
      omega)
  have hsurj : Function.Surjective (normalization E) := by
    intro x
    exact ⟨sphereInclusion E x, DFunLike.congr_fun (normalization_inclusion E) x⟩
  exact hsurj.pathConnectedSpace (normalization E).continuous

end AkopyanResearch.SphereConnectivity
