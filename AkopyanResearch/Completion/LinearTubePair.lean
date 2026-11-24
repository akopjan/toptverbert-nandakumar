module

public import AkopyanResearch.Completion.LinearTube
public import Mathlib.Topology.Category.TopPair

/-!
# The actual pairs in the normal-tube excision argument

The product normal pair is identified with the pair formed by the tube
and its punctured part. Its map to the exceptional-set complement is the
literal geometric inclusion. All spaces have their usual subspace topologies.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearTubePair

open Set CategoryTheory Topology
open LinearTube

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℝ E) (Z : Set E)

abbrev Ambient := {x : E // x ∉ Z}
def Punctured : Set (Ambient Z) := {x | x.val ∉ L}
def Neighborhood : Set (Ambient Z) := {x | x.val ∈ Tube L Z}

theorem isOpen_punctured : IsOpen (Punctured L Z) :=
  L.closed_of_finiteDimensional.isOpen_compl.preimage continuous_subtype_val

theorem isOpen_neighborhood (hZ : IsClosed Z) : IsOpen (Neighborhood L Z) :=
  (isOpen_tube L Z hZ).preimage continuous_subtype_val

theorem punctured_union_neighborhood (hZ : IsClosed Z) (hne : Z.Nonempty) :
    Punctured L Z ∪ Neighborhood L Z = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hx : x.val ∈ L
  · right
    exact base_mem_tube L Z hZ hne ⟨⟨x.val, hx⟩, x.property⟩
  · exact Or.inl hx

def tubeAmbientHomeomorph : Tube L Z ≃ₜ Neighborhood L Z where
  toFun x := ⟨⟨x.val, tube_disjoint_exceptional L Z x.val x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable (hZ : IsClosed Z) (hne : Z.Nonempty)

def normalCoordinates : (Base L Z × NormalBall L) ≃ₜ Neighborhood L Z :=
  (LinearTube.homeomorph L Z hZ hne).trans (tubeAmbientHomeomorph L Z)

theorem normalCoordinates_punctured_iff (p : Base L Z × NormalBall L) :
    (normalCoordinates L Z hZ hne p).val ∈ Punctured L Z ↔ p.2.val ≠ 0 :=
  not_congr (homeomorph_mem_submodule_iff L Z hZ hne p)

def intersectionHomeomorph :
    {x : Neighborhood L Z // x.val ∈ Punctured L Z} ≃ₜ
      ↥(Punctured L Z ∩ Neighborhood L Z) where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def puncturedCoordinates :
    {p : Base L Z × NormalBall L // p.2.val ≠ 0} ≃ₜ
      ↥(Punctured L Z ∩ Neighborhood L Z) :=
  ((normalCoordinates L Z hZ hne).subtype
    (fun p => (normalCoordinates_punctured_iff L Z hZ hne p).symm)).trans
      (intersectionHomeomorph L Z)

abbrev NormalPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (Base L Z × NormalBall L)) {p | p.2.val ≠ 0}

abbrev AmbientPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (Ambient Z)) (Punctured L Z)

abbrev TubePair : TopPair.{u} :=
  TopPair.of
    (TopCat.ofHom (ContinuousMap.inclusion
      (Set.inter_subset_right : Punctured L Z ∩ Neighborhood L Z ⊆ Neighborhood L Z)))
    (IsEmbedding.inclusion Set.inter_subset_right)

def normalPairIso : NormalPair L Z ≅ TubePair L Z :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (puncturedCoordinates L Z hZ hne))
    (TopCat.isoOfHomeo (normalCoordinates L Z hZ hne)) (by ext p; rfl)

def tubeInclusion : TubePair L Z ⟶ AmbientPair L Z :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)) rfl

/-- The normal product is included using `a + radius(a) • v`. -/
def normalInclusion : NormalPair L Z ⟶ AmbientPair L Z :=
  (normalPairIso L Z hZ hne).hom ≫ tubeInclusion L Z

theorem normalInclusion_apply (p : Base L Z × NormalBall L) :
    (TopPair.Hom.fst (normalInclusion L Z hZ hne) p).val =
      p.1.val.val + radius L Z p.1.val • p.2.val.val := rfl

theorem normalInclusion_zero (a : Base L Z) :
    (TopPair.Hom.fst (normalInclusion L Z hZ hne) (a, ⟨0, by simp⟩)).val = a.val.val := by
  rw [normalInclusion_apply]
  simp

end AkopyanResearch.LinearTubePair
