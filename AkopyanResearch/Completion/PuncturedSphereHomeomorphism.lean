module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Finite punctures and a stereographic chart

After choosing one of the deleted sphere points, stereographic projection
identifies the remaining complement with Euclidean space minus finitely
many points. Repeated punctures are allowed; indices equal to the chart
pole are omitted from the finite target family.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PuncturedSphereHomeomorphism

universe u v w
variable {X : Type u} {Y : Type v} {ι : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual complement of a family of points. -/
abbrev PointComplement (p : ι → X) := {x : X // ∀ i, x ≠ p i}

/-- Transport a point complement along an actual homeomorphism. -/
def transport (e : X ≃ₜ Y) (p : ι → X) :
    PointComplement p ≃ₜ PointComplement (fun i => e (p i)) where
  toFun x := ⟨e x.val, fun i h => x.property i (e.injective h)⟩
  invFun y := ⟨e.symm y.val, fun i h => y.property i (by
    have he := congrArg e h
    simpa only [Homeomorph.apply_symm_apply] using he)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.continuous_symm.comp continuous_subtype_val).subtype_mk _

/-- The indices whose deleted point differs from the chosen chart pole. -/
def OtherIndex (p : ι → X) (i₀ : ι) := {i : ι // p i ≠ p i₀}

instance [Fintype ι] (p : ι → X) (i₀ : ι) : Fintype (OtherIndex p i₀) := by
  classical
  unfold OtherIndex
  infer_instance

/-- A chart with one deleted source point and full target gives a global
homeomorphism after removing the remaining finite family. -/
def deletedChart (e : OpenPartialHomeomorph X Y) (p : ι → X) (i₀ : ι)
    (hs : e.source = {p i₀}ᶜ) (ht : e.target = Set.univ) :
    PointComplement p ≃ₜ PointComplement (fun i : OtherIndex p i₀ => e (p i.val)) := by
  have hsource (x : X) : x ∈ e.source ↔ x ≠ p i₀ := by
    rw [hs]
    rfl
  have htarget (y : Y) : y ∈ e.target := by rw [ht]; trivial
  let f : PointComplement p → PointComplement
      (fun i : OtherIndex p i₀ => e (p i.val)) := fun x =>
    ⟨e x.val, fun i hi => x.property i.val
      (e.injOn ((hsource x.val).mpr (x.property i₀))
        ((hsource (p i.val)).mpr i.property) hi)⟩
  let g : PointComplement (fun i : OtherIndex p i₀ => e (p i.val)) →
      PointComplement p := fun y => ⟨e.symm y.val, by
    intro i hi
    have hn := (hsource (e.symm y.val)).mp (e.map_target (htarget y.val))
    by_cases he : p i = p i₀
    · exact hn (hi.trans he)
    · apply y.property ⟨i, he⟩
      have hr := e.right_inv (htarget y.val)
      rw [hi] at hr
      exact hr.symm⟩
  exact {
    toFun := f
    invFun := g
    left_inv := fun x => Subtype.ext (e.left_inv ((hsource x.val).mpr (x.property i₀)))
    right_inv := fun y => Subtype.ext (e.right_inv (htarget y.val))
    continuous_toFun :=
      (e.continuousOn.comp_continuous continuous_subtype_val
        (fun x : PointComplement p => (hsource x.val).mpr (x.property i₀))).subtype_mk _
    continuous_invFun :=
      (e.continuousOn_symm.comp_continuous continuous_subtype_val
        (fun y : PointComplement (fun i : OtherIndex p i₀ => e (p i.val)) => htarget y.val)).subtype_mk _ }

section Sphere
open Metric Module
variable {n : ℕ}

instance euclideanDimensionFact :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Stereographic images of the punctures other than the chosen pole. -/
def projectedPoints (p : ι → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i₀ : ι) :
    OtherIndex p i₀ → EuclideanSpace ℝ (Fin n) :=
  fun i => stereographic' n (p i₀) (p i.val)

/-- A finitely punctured sphere is a finitely punctured Euclidean space. -/
def sphereComplementHomeomorph
    (p : ι → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (i₀ : ι) :
    PointComplement p ≃ₜ PointComplement (projectedPoints p i₀) :=
  deletedChart (stereographic' n (p i₀)) p i₀
    (stereographic'_source _) (stereographic'_target _)

end Sphere
end AkopyanResearch.PuncturedSphereHomeomorphism
