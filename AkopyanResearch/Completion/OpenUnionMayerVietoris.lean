module

public import AkopyanResearch.Completion.ComplementMayerVietoris

/-!
# Mayer--Vietoris in the actual union of two open subsets

This supplies the explicit subspace homeomorphisms needed when the union
is a proper subset of the ambient arrangement complement.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.OpenUnionMayerVietoris

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel ComplementMayerVietoris

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X : TopCat.{w}} (A B : Set X)

abbrev unionSpace : TopCat.{w} := TopCat.of ↥(A ∪ B)
def leftSet : Set (unionSpace A B) := {x | x.val ∈ A}
def rightSet : Set (unionSpace A B) := {x | x.val ∈ B}

theorem cover (hA : IsOpen A) (hB : IsOpen B) :
    Hatcher.Excision.CoverCondition (leftSet A B) (rightSet A B) where
  union_interior := by
    have hl : IsOpen (leftSet A B) := hA.preimage continuous_subtype_val
    have hr : IsOpen (rightSet A B) := hB.preimage continuous_subtype_val
    rw [hl.interior_eq, hr.interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    exact x.property

def leftHomeomorph : ↥(leftSet A B) ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def rightHomeomorph : ↥(rightSet A B) ≃ₜ B where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, Or.inr x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def intersectionHomeomorph : ↥(leftSet A B ∩ rightSet A B) ≃ₜ ↥(A ∩ B) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, Or.inl x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def leftHomologyIso (R : C) (i : ℕ) :
    homology R i (TopCat.of ↥(leftSet A B)) ≅ homology R i (TopCat.of ↥A) :=
  (homologyFunctor R i).mapIso (TopCat.isoOfHomeo (leftHomeomorph A B))

def rightHomologyIso (R : C) (i : ℕ) :
    homology R i (TopCat.of ↥(rightSet A B)) ≅ homology R i (TopCat.of ↥B) :=
  (homologyFunctor R i).mapIso (TopCat.isoOfHomeo (rightHomeomorph A B))

def intersectionHomologyIso (R : C) (i : ℕ) :
    homology R i (TopCat.of ↥(leftSet A B ∩ rightSet A B)) ≅
      homology R i (TopCat.of ↥(A ∩ B)) :=
  (homologyFunctor R i).mapIso (TopCat.isoOfHomeo (intersectionHomeomorph A B))

theorem isZero_intersection_of_zero_union (hA : IsOpen A) (hB : IsOpen B)
    (R : C) (i : ℕ)
    (hU : IsZero (homology R (i + 1) (unionSpace A B)))
    (hHA : IsZero (homology R i (TopCat.of ↥A)))
    (hHB : IsZero (homology R i (TopCat.of ↥B))) :
    IsZero (homology R i (TopCat.of ↥(A ∩ B))) := by
  have h := ComplementMayerVietoris.isZero_intersection_of_zero (cover A B hA hB) R i hU
    (hHA.of_iso (leftHomologyIso A B R i)) (hHB.of_iso (rightHomologyIso A B R i))
  exact h.of_iso (intersectionHomologyIso A B R i).symm

/-- The direct-sum isomorphism for the original intersection and original
cover members; all subspace-coordinate changes are explicit. -/
def homologyBiprodIso (hA : IsOpen A) (hB : IsOpen B) (R : C) (i : ℕ)
    (hU₁ : IsZero (homology R (i + 1) (unionSpace A B)))
    (hU₀ : IsZero (homology R i (unionSpace A B))) :
    homology R i (TopCat.of ↥(A ∩ B)) ≅
      homology R i (TopCat.of ↥A) ⊞ homology R i (TopCat.of ↥B) :=
  (intersectionHomologyIso A B R i).symm ≪≫
    ComplementMayerVietoris.intersectionHomologyIso (cover A B hA hB) R i hU₁ hU₀ ≪≫
      biprod.mapIso (leftHomologyIso A B R i) (rightHomologyIso A B R i)

end AkopyanResearch.OpenUnionMayerVietoris
