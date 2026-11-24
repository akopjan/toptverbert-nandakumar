module

public import AkopyanResearch.Completion.SphereSourceCover
public import AkopyanResearch.Completion.ProductProjectionIsomorphism
public import AkopyanResearch.Completion.ExactCommonSection

/-!
# Homology under adjoining a sphere factor to the source

Ordinary Mayer--Vietoris for the actual lifted sphere cover identifies
the map induced by the common-base inclusion. If the two adjacent
product-sphere projections are homology isomorphisms, that actual
inclusion is a homology isomorphism as well.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.SphereSourceHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open ContinuousMap SphereSourceCover ProductSphereKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

local instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
local instance : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {n : ℕ} (f : C(X × LoopSphereCover.Sphere.{w} n, Y)) (y₀ : Y) (R : C)

def northIso (i : ℕ) :
    homology R i (TopCat.of (SphereSourceCover.North f y₀)) ≅
      homology R i (TopCat.of (BaseSpace f y₀)) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (SphereSourceCover.northEquiv f y₀) R i

def southIso (i : ℕ) :
    homology R i (TopCat.of (SphereSourceCover.South f y₀)) ≅
      homology R i (TopCat.of (BaseSpace f y₀)) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (SphereSourceCover.southEquiv f y₀) R i

def overlapIso (i : ℕ) :
    homology R i (TopCat.of ↑(SphereSourceCover.North f y₀ ∩ SphereSourceCover.South f y₀)) ≅
      homology R i (sphereProduct (BaseSpace f y₀) n) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (overlapEquiv f y₀) R i

def baseInclusionMap (i : ℕ) :
    homology R i (TopCat.of (BaseSpace f y₀)) ⟶ homology R i (TopCat.of (Total f y₀)) :=
  (homologyFunctor R i).map (TopCat.ofHom (SphereSourceCover.baseInclusion f y₀))

def northOverlapMap (i : ℕ) :
    homology R i (TopCat.of ↑(SphereSourceCover.North f y₀ ∩ SphereSourceCover.South f y₀)) ⟶
      homology R i (TopCat.of (SphereSourceCover.North f y₀)) :=
  (homologyFunctor R i).map
    (Hatcher.MayerVietoris.intersectionToLeft (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀))

def southOverlapMap (i : ℕ) :
    homology R i (TopCat.of ↑(SphereSourceCover.North f y₀ ∩ SphereSourceCover.South f y₀)) ⟶
      homology R i (TopCat.of (SphereSourceCover.South f y₀)) :=
  (homologyFunctor R i).map
    (Hatcher.MayerVietoris.intersectionToRight (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀))

def overlapSectionMap (i : ℕ) :
    homology R i (TopCat.of (BaseSpace f y₀)) ⟶
      homology R i (TopCat.of ↑(SphereSourceCover.North f y₀ ∩ SphereSourceCover.South f y₀)) :=
  (homologyFunctor R i).map (TopCat.ofHom (overlapInclusion f y₀))

theorem north_section (i : ℕ) :
    (homologyFunctor R i).map (TopCat.ofHom (northInclusion f y₀)) ≫
      (northIso f y₀ R i).hom = 𝟙 _ := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  calc
    _ = (homologyFunctor R i).map (𝟙 (TopCat.of (BaseSpace f y₀))) :=
      TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        (northEquiv_inclusion f y₀).some R i
    _ = _ := (homologyFunctor R i).map_id _

theorem south_section (i : ℕ) :
    (homologyFunctor R i).map (TopCat.ofHom (southInclusion f y₀)) ≫
      (southIso f y₀ R i).hom = 𝟙 _ := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  calc
    _ = (homologyFunctor R i).map (𝟙 (TopCat.of (BaseSpace f y₀))) :=
      TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        (southEquiv_inclusion f y₀).some R i
    _ = _ := (homologyFunctor R i).map_id _

theorem northIso_inv (i : ℕ) :
    (northIso f y₀ R i).inv =
      (homologyFunctor R i).map (TopCat.ofHom (northInclusion f y₀)) := by
  apply (cancel_mono (northIso f y₀ R i).hom).mp
  rw [Iso.inv_hom_id, north_section]

theorem southIso_inv (i : ℕ) :
    (southIso f y₀ R i).inv =
      (homologyFunctor R i).map (TopCat.ofHom (southInclusion f y₀)) := by
  apply (cancel_mono (southIso f y₀ R i).hom).mp
  rw [Iso.inv_hom_id, south_section]

theorem overlapSection_north (i : ℕ) :
    overlapSectionMap f y₀ R i ≫ northOverlapMap f y₀ R i ≫
      (northIso f y₀ R i).hom = 𝟙 _ := by
  rw [← Category.assoc]
  change ((homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _) ≫ _ = _
  rw [← Functor.map_comp]
  exact north_section f y₀ R i

theorem overlapSection_south (i : ℕ) :
    overlapSectionMap f y₀ R i ≫ southOverlapMap f y₀ R i ≫
      (southIso f y₀ R i).hom = 𝟙 _ := by
  rw [← Category.assoc]
  change ((homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _) ≫ _ = _
  rw [← Functor.map_comp]
  exact south_section f y₀ R i

theorem north_projection (i : ℕ) :
    northOverlapMap f y₀ R i ≫ (northIso f y₀ R i).hom =
      (overlapIso f y₀ R i).hom ≫ projectionMap (BaseSpace f y₀) R n i := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ =
    (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

theorem isIso_northOverlapMap (i : ℕ)
    (hp : IsIso (projectionMap (BaseSpace f y₀) R n i)) :
    IsIso (northOverlapMap f y₀ R i) := by
  have := hp
  have heq : northOverlapMap f y₀ R i =
      (overlapIso f y₀ R i).hom ≫ projectionMap (BaseSpace f y₀) R n i ≫
        (northIso f y₀ R i).inv := by
    apply (cancel_mono (northIso f y₀ R i).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact north_projection f y₀ R i
  rw [heq]
  infer_instance

theorem normalizedOverlap_eq (i : ℕ)
    (hp : IsIso (projectionMap (BaseSpace f y₀) R n i)) :
    northOverlapMap f y₀ R i ≫ (northIso f y₀ R i).hom =
      southOverlapMap f y₀ R i ≫ (southIso f y₀ R i).hom := by
  have := isIso_northOverlapMap f y₀ R i hp
  let e := (asIso (northOverlapMap f y₀ R i)).trans (northIso f y₀ R i)
  have hs : overlapSectionMap f y₀ R i = e.inv := by
    apply (cancel_mono e.hom).mp
    exact (overlapSection_north f y₀ R i).trans e.inv_hom_id.symm
  have : IsIso (overlapSectionMap f y₀ R i) := by rw [hs]; infer_instance
  apply (cancel_epi (overlapSectionMap f y₀ R i)).mp
  exact (overlapSection_north f y₀ R i).trans (overlapSection_south f y₀ R i).symm

def plusMap (i : ℕ) :
    homology R i (TopCat.of (SphereSourceCover.North f y₀)) ⊞
        homology R i (TopCat.of (SphereSourceCover.South f y₀)) ⟶
      homology R i (TopCat.of (BaseSpace f y₀)) :=
  biprod.desc (northIso f y₀ R i).hom (southIso f y₀ R i).hom

theorem epi_plusMap (i : ℕ) : Epi (plusMap f y₀ R i) :=
  epi_of_epi_fac (biprod.inl_desc (northIso f y₀ R i).hom (southIso f y₀ R i).hom)

theorem signedLift_desc_zero {I A B D : C}
    (p : I ⟶ A) (q : I ⟶ B) (a : A ⟶ D) (b : B ⟶ D)
    (h : p ≫ a = q ≫ b) : biprod.lift p (-q) ≫ biprod.desc a b = 0 := by
  simp only [biprod.lift_desc, neg_comp, h, add_neg_cancel]

theorem intersection_plus_zero (i : ℕ)
    (hp : IsIso (projectionMap (BaseSpace f y₀) R n i)) :
    Hatcher.MayerVietoris.intersectionMap (X := TopCat.of (Total f y₀))
        (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R i ≫
      plusMap f y₀ R i = 0 :=
  signedLift_desc_zero (northOverlapMap f y₀ R i) (southOverlapMap f y₀ R i)
    (northIso f y₀ R i).hom (southIso f y₀ R i).hom (normalizedOverlap_eq f y₀ R i hp)

theorem union_factor (i : ℕ) :
    Hatcher.MayerVietoris.unionMap (X := TopCat.of (Total f y₀))
        (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R i =
      plusMap f y₀ R i ≫ baseInclusionMap f y₀ R i := by
  apply biprod.hom_ext'
  · simp only [Hatcher.MayerVietoris.unionMap, biprod.inl_desc,
      plusMap, biprod.inl_desc_assoc]
    apply (cancel_epi (northIso f y₀ R i).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, northIso_inv]
    change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
    rw [← Functor.map_comp]
    rfl
  · simp only [Hatcher.MayerVietoris.unionMap, biprod.inr_desc,
      plusMap, biprod.inr_desc_assoc]
    apply (cancel_epi (southIso f y₀ R i).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, southIso_inv]
    change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
    rw [← Functor.map_comp]
    rfl

/-- If the overlap projections are isomorphisms in two adjacent degrees,
the actual common-base inclusion is an isomorphism in the higher degree. -/
theorem baseInclusion_isIso (i : ℕ)
    (hlo : IsIso (projectionMap (BaseSpace f y₀) R n i))
    (hhi : IsIso (projectionMap (BaseSpace f y₀) R n (i + 1))) :
    IsIso (baseInclusionMap f y₀ R (i + 1)) := by
  let hs := Hatcher.MayerVietoris.sequence_exact (cover f y₀) R (i + 1) i rfl
  have := isIso_northOverlapMap f y₀ R i hlo
  have hm : Mono (Hatcher.MayerVietoris.intersectionMap
      (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R i) :=
    mono_of_mono_fac (biprod.lift_fst (northOverlapMap f y₀ R i) (-southOverlapMap f y₀ R i))
  have hz : Hatcher.MayerVietoris.connecting (cover f y₀) R (i + 1) i rfl ≫
      Hatcher.MayerVietoris.intersectionMap (X := TopCat.of (Total f y₀))
        (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R i = 0 :=
    hs.toIsComplex.zero 2
  have hδ : Hatcher.MayerVietoris.connecting (cover f y₀) R (i + 1) i rfl = 0 :=
    zero_of_comp_mono _ hz
  have he : Epi (Hatcher.MayerVietoris.unionMap (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R (i + 1)) :=
    (hs.exact 1).epi_f hδ
  have := epi_plusMap f y₀ R (i + 1)
  let S : ShortComplex C := ShortComplex.mk
    (Hatcher.MayerVietoris.intersectionMap (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R (i + 1))
    (Hatcher.MayerVietoris.unionMap (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R (i + 1))
    (hs.toIsComplex.zero 0)
  have hS : S.Exact := hs.exact 0
  exact ExactCommonSection.isIso_factor S hS
    (plusMap f y₀ R (i + 1)) (baseInclusionMap f y₀ R (i + 1))
    (intersection_plus_zero f y₀ R (i + 1) hhi) (union_factor f y₀ R (i + 1)).symm

theorem baseInclusion_isIso_of_base_vanish (i : ℕ) (hni : n ≤ i)
    (hlo : IsZero (homology R (i - n) (TopCat.of (BaseSpace f y₀))))
    (hhi : IsZero (homology R (i + 1 - n) (TopCat.of (BaseSpace f y₀)))) :
    IsIso (baseInclusionMap f y₀ R (i + 1)) :=
  baseInclusion_isIso f y₀ R i
    (ProductProjectionIsomorphism.isIso_of_base_vanish _ R n i hni hlo)
    (ProductProjectionIsomorphism.isIso_of_base_vanish _ R n (i + 1) (by omega) hhi)

end AkopyanResearch.SphereSourceHomology
