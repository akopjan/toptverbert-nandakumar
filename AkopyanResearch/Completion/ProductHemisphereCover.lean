module

public import Hatcher.Sphere.HemisphereNeighborhoodCover
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Product hemisphere covers with specified projection and section

The two hemispheres of an actual sphere give a neighborhood-retract cover
after taking the product with any topological space. Their retractions to
the base are the literal first projections. Both inverse maps use the same
point of the equator, so the two maps from the base into the whole product
agree exactly. These are the geometric maps needed for the relative Thom
calculation from ordinary Mayer--Vietoris.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ProductHemisphereCover

open Set ContinuousMap
open scoped Topology unitInterval ContinuousMap
open Hatcher.MayerVietoris

universe u v w

def productSubtypeHomeomorph {X : Type u} [TopologicalSpace X]
    (Z : Type v) [TopologicalSpace Z] (A : Set X) :
    (Set.univ ×ˢ A : Set (Z × X)) ≃ₜ Z × A where
  toFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
  invFun p := ⟨(p.1, p.2.val), Set.mem_univ _, p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def productIntersectionHomeomorph {X : Type u} [TopologicalSpace X]
    (Z : Type v) [TopologicalSpace Z] (A B : Set X) :
    ((Set.univ ×ˢ A) ∩ (Set.univ ×ˢ B) : Set (Z × X)) ≃ₜ Z × ↑(A ∩ B) where
  toFun p := (p.val.1, ⟨p.val.2, p.property.1.2, p.property.2.2⟩)
  invFun p := ⟨(p.1, p.2.val),
    ⟨Set.mem_univ _, p.2.property.1⟩, ⟨Set.mem_univ _, p.2.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def productMap {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
    (Z : Type w) [TopologicalSpace Z] (i : C(A, Y)) : C(Z × A, Z × Y) :=
  ⟨fun p => (p.1, i p.2), continuous_fst.prodMk (i.continuous.comp continuous_snd)⟩

def productStrongDeformationRetract {A : Type u} {Y : Type v}
    [TopologicalSpace A] [TopologicalSpace Y]
    (Z : Type w) [TopologicalSpace Z] {i : C(A, Y)}
    (h : Hatcher.StrongDeformationRetract i) :
    Hatcher.StrongDeformationRetract (productMap Z i) where
  retract := productMap Z h.retract
  retract_inclusion := by
    apply ContinuousMap.ext
    intro p
    apply Prod.ext
    · rfl
    · exact congrArg (fun f : C(A, A) => f p.2) h.retract_inclusion
  deformation := {
    toFun := fun p => (p.2.1, h.deformation (p.1, p.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (h.deformation.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    map_zero_left := by
      intro p
      change (p.1, h.deformation (0, p.2)) = p
      rw [h.deformation.apply_zero]
      rfl
    map_one_left := by
      intro p
      change (p.1, h.deformation (1, p.2)) = (p.1, i (h.retract p.2))
      rw [h.deformation.apply_one]
      rfl
    prop' := by
      intro t p hp
      obtain ⟨a, rfl⟩ := hp
      apply Prod.ext
      · rfl
      · exact h.deformation.eq_fst t ⟨a.2, rfl⟩ }

def productSubsetStrongDeformationRetract {X : TopCat.{u}}
    (Z : Type u) [TopologicalSpace Z] {A U : Set X} (hAU : A ⊆ U)
    (h : Hatcher.StrongDeformationRetract (inclusionOfSubset hAU)) :
    Hatcher.StrongDeformationRetract
      (inclusionOfSubset (X := TopCat.of (Z × X))
        (show Set.univ ×ˢ A ⊆ Set.univ ×ˢ U from fun _ hp => ⟨hp.1, hAU hp.2⟩)) :=
  Hatcher.Sphere.strongDeformationRetractOfHomeomorphSquare
    (inclusionOfSubset _)
    (productMap Z (inclusionOfSubset hAU))
    (productSubtypeHomeomorph Z A) (productSubtypeHomeomorph Z U)
    (fun _ => rfl) (productStrongDeformationRetract Z h)

def productNeighborhoodCover {X : TopCat.{u}}
    (Z : Type u) [TopologicalSpace Z] {A B : Set X} (h : NeighborhoodCover A B) :
    NeighborhoodCover (X := TopCat.of (Z × X)) (Set.univ ×ˢ A) (Set.univ ×ˢ B) where
  U := Set.univ ×ˢ h.U
  V := Set.univ ×ˢ h.V
  union_eq_univ := by
    ext p
    simpa only [Set.mem_union, Set.mem_prod, Set.mem_univ, true_and] using
      Set.ext_iff.mp h.union_eq_univ p.2
  left_subset_interior := by
    intro p hp
    rw [interior_prod_eq, interior_univ]
    exact ⟨hp.1, h.left_subset_interior hp.2⟩
  right_subset_interior := by
    intro p hp
    rw [interior_prod_eq, interior_univ]
    exact ⟨hp.1, h.right_subset_interior hp.2⟩
  leftRetract := productSubsetStrongDeformationRetract Z _ h.leftRetract
  rightRetract := productSubsetStrongDeformationRetract Z _ h.rightRetract
  intersectionRetract :=
    Hatcher.Sphere.strongDeformationRetractOfHomeomorphSquare
      (inclusionOfSubset _)
      (productMap Z h.intersectionInclusion)
      (productIntersectionHomeomorph Z A B)
      (productIntersectionHomeomorph Z h.U h.V)
      (fun _ => rfl) (productStrongDeformationRetract Z h.intersectionRetract)

def hemisphereProductCover (Z : Type u) [TopologicalSpace Z] (n : ℕ) :
    NeighborhoodCover (X := TopCat.of (Z × (TopCat.sphere.{u} (n + 1) : Type u)))
      (Set.univ ×ˢ Hatcher.Sphere.northHemisphere n)
      (Set.univ ×ˢ Hatcher.Sphere.southHemisphere n) :=
  productNeighborhoodCover Z (Hatcher.Sphere.hemisphereNeighborhoodCover n)

def intersectionSphereHomeomorph (Z : Type u) [TopologicalSpace Z] (n : ℕ) :
    ((Set.univ ×ˢ Hatcher.Sphere.northHemisphere n) ∩
        (Set.univ ×ˢ Hatcher.Sphere.southHemisphere n) :
      Set (Z × (TopCat.sphere.{u} (n + 1) : Type u))) ≃ₜ
      Z × (TopCat.sphere.{u} n : Type u) :=
  (productIntersectionHomeomorph Z _ _).trans
    ((Homeomorph.refl Z).prodCongr
      ((Homeomorph.setCongr (Hatcher.Sphere.hemisphere_intersection n)).trans
        (Hatcher.Sphere.equatorSphereHomeomorph n)))

theorem contraction_to {A : Type u} [TopologicalSpace A] [ContractibleSpace A] (a : A) :
    (ContinuousMap.id A).Homotopic (ContinuousMap.const A a) := by
  obtain ⟨a₀, h⟩ := id_nullhomotopic A
  have hc := h.comp (Homotopic.refl (ContinuousMap.const A a))
  exact h.trans hc.symm

/-- Projection along a contractible factor, with a prescribed section. -/
def projectionHomotopyEquiv {A : Type u} [TopologicalSpace A] [ContractibleSpace A]
    (Z : Type v) [TopologicalSpace Z] (a : A) : (Z × A) ≃ₕ Z where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := ⟨fun z => (z, a), continuous_id.prodMk continuous_const⟩
  left_inv := (Homotopic.refl (ContinuousMap.id Z)).prodMap (contraction_to a).symm
  right_inv := Homotopic.refl (ContinuousMap.id Z)

def productSubsetProjectionHomotopyEquiv {X : Type u} [TopologicalSpace X]
    (Z : Type v) [TopologicalSpace Z] (A : Set X) [ContractibleSpace A] (a : A) :
    (Set.univ ×ˢ A : Set (Z × X)) ≃ₕ Z :=
  (productSubtypeHomeomorph Z A).toHomotopyEquiv.trans (projectionHomotopyEquiv Z a)

def commonPoint (n : ℕ) : (TopCat.sphere.{u} (n + 1) : Type u) :=
  (Hatcher.Sphere.hemisphereIntersectionPoint.{u} n).val

def northPoint (n : ℕ) : Hatcher.Sphere.northHemisphere.{u} n :=
  ⟨commonPoint.{u} n, (Hatcher.Sphere.hemisphereIntersectionPoint.{u} n).property.1⟩

def southPoint (n : ℕ) : Hatcher.Sphere.southHemisphere.{u} n :=
  ⟨commonPoint.{u} n, (Hatcher.Sphere.hemisphereIntersectionPoint.{u} n).property.2⟩

def northProjectionEquiv (Z : Type u) [TopologicalSpace Z] (n : ℕ) :
    (Set.univ ×ˢ Hatcher.Sphere.northHemisphere n :
      Set (Z × (TopCat.sphere.{u} (n + 1) : Type u))) ≃ₕ Z := by
  let : ContractibleSpace (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 2) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  let : ContractibleSpace (Hatcher.Sphere.northHemisphere.{u} n) :=
    (Hatcher.Sphere.northHemisphereHomeomorph n).contractibleSpace
  exact productSubsetProjectionHomotopyEquiv Z _ (northPoint n)

def southProjectionEquiv (Z : Type u) [TopologicalSpace Z] (n : ℕ) :
    (Set.univ ×ˢ Hatcher.Sphere.southHemisphere n :
      Set (Z × (TopCat.sphere.{u} (n + 1) : Type u))) ≃ₕ Z := by
  let : ContractibleSpace (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 2) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  let : ContractibleSpace (Hatcher.Sphere.southHemisphere.{u} n) :=
    (Hatcher.Sphere.southHemisphereHomeomorph n).contractibleSpace
  exact productSubsetProjectionHomotopyEquiv Z _ (southPoint n)

theorem northProjectionEquiv_apply (Z : Type u) [TopologicalSpace Z] (n : ℕ)
    (x : (Set.univ ×ˢ Hatcher.Sphere.northHemisphere n :
      Set (Z × (TopCat.sphere.{u} (n + 1) : Type u)))) :
    northProjectionEquiv Z n x = x.val.1 := rfl

theorem southProjectionEquiv_apply (Z : Type u) [TopologicalSpace Z] (n : ℕ)
    (x : (Set.univ ×ˢ Hatcher.Sphere.southHemisphere n :
      Set (Z × (TopCat.sphere.{u} (n + 1) : Type u)))) :
    southProjectionEquiv Z n x = x.val.1 := rfl

theorem northProjectionEquiv_symm_apply (Z : Type u) [TopologicalSpace Z]
    (n : ℕ) (z : Z) : ((northProjectionEquiv Z n).symm z).val = (z, commonPoint n) := rfl

theorem southProjectionEquiv_symm_apply (Z : Type u) [TopologicalSpace Z]
    (n : ℕ) (z : Z) : ((southProjectionEquiv Z n).symm z).val = (z, commonPoint n) := rfl

end AkopyanResearch.ProductHemisphereCover
