module

public import AkopyanResearch.Completion.ProductSphereProjection
public import AkopyanResearch.Completion.ProductHemisphereCover
public import AkopyanResearch.Completion.SplitExactKernel

/-!
# Mayer--Vietoris recurrence for the kernel of product projection

The connecting map for the actual product hemisphere cover restricts to an
isomorphism between the kernels of projection in adjacent sphere dimensions
and adjacent homology degrees. Both endpoint maps of Mayer--Vietoris are
identified using the actual projections and the common equatorial section.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.ProductSphereKernel

open AlgebraicTopology CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Hatcher.MayerVietoris

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

local instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
local instance : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts

variable (Z : Type w) [TopologicalSpace Z] (R : C)

abbrev North (n : ℕ) : Set (sphereProduct Z (n + 1)) :=
  Set.univ ×ˢ Hatcher.Sphere.northHemisphere n

abbrev South (n : ℕ) : Set (sphereProduct Z (n + 1)) :=
  Set.univ ×ˢ Hatcher.Sphere.southHemisphere n

def northIso (n i : ℕ) :
    homology R i (TopCat.of (North Z n)) ≅ homology R i (TopCat.of Z) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    (ProductHemisphereCover.northProjectionEquiv Z n) R i

def southIso (n i : ℕ) :
    homology R i (TopCat.of (South Z n)) ≅ homology R i (TopCat.of Z) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    (ProductHemisphereCover.southProjectionEquiv Z n) R i

def intersectionIso (n i : ℕ) :
    homology R i (TopCat.of ↑(North Z n ∩ South Z n)) ≅
      homology R i (sphereProduct Z n) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    (ProductHemisphereCover.intersectionSphereHomeomorph Z n).toHomotopyEquiv R i

def equatorSection (n : ℕ) : TopCat.of Z ⟶ sphereProduct Z (n + 1) :=
  TopCat.ofHom ⟨fun z => (z, ProductHemisphereCover.commonPoint n),
    continuous_id.prodMk continuous_const⟩

def sectionMap (n i : ℕ) : homology R i (TopCat.of Z) ⟶
    homology R i (sphereProduct Z (n + 1)) :=
  (homologyFunctor R i).map (equatorSection Z n)

theorem section_projection (n i : ℕ) :
    sectionMap Z R n i ≫ projectionMap Z R (n + 1) i = 𝟙 _ := by
  change (homologyFunctor R i).map (equatorSection Z n) ≫
    (homologyFunctor R i).map (projection Z (n + 1)) = _
  rw [← Functor.map_comp]
  have he : equatorSection Z n ≫ projection Z (n + 1) = 𝟙 (TopCat.of Z) := rfl
  rw [he]
  exact (homologyFunctor R i).map_id _

theorem north_section (n i : ℕ) :
    (northIso Z R n i).inv ≫ homologyMapToAmbient (North Z n) R i =
      sectionMap Z R n i := by
  change (homologyFunctor R i).map
      (TopCat.ofHom (ProductHemisphereCover.northProjectionEquiv Z n).invFun) ≫
    (homologyFunctor R i).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) =
    (homologyFunctor R i).map (equatorSection Z n)
  rw [← Functor.map_comp]
  rfl

theorem south_section (n i : ℕ) :
    (southIso Z R n i).inv ≫ homologyMapToAmbient (South Z n) R i =
      sectionMap Z R n i := by
  change (homologyFunctor R i).map
      (TopCat.ofHom (ProductHemisphereCover.southProjectionEquiv Z n).invFun) ≫
    (homologyFunctor R i).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) =
    (homologyFunctor R i).map (equatorSection Z n)
  rw [← Functor.map_comp]
  rfl

theorem north_intersection_projection (n i : ℕ) :
    homologyMapOfSubset (Set.inter_subset_left : North Z n ∩ South Z n ⊆ North Z n) R i ≫
        (northIso Z R n i).hom =
      (intersectionIso Z R n i).hom ≫ projectionMap Z R n i := by
  change (homologyFunctor R i).map
      (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)) ≫
    (homologyFunctor R i).map
      (TopCat.ofHom (ProductHemisphereCover.northProjectionEquiv Z n).toFun) =
    (homologyFunctor R i).map
      (TopCat.ofHom (ProductHemisphereCover.intersectionSphereHomeomorph Z n).toHomotopyEquiv.toFun) ≫
    (homologyFunctor R i).map (projection Z n)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem south_intersection_projection (n i : ℕ) :
    homologyMapOfSubset (Set.inter_subset_right : North Z n ∩ South Z n ⊆ South Z n) R i ≫
        (southIso Z R n i).hom =
      (intersectionIso Z R n i).hom ≫ projectionMap Z R n i := by
  change (homologyFunctor R i).map
      (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right)) ≫
    (homologyFunctor R i).map
      (TopCat.ofHom (ProductHemisphereCover.southProjectionEquiv Z n).toFun) =
    (homologyFunctor R i).map
      (TopCat.ofHom (ProductHemisphereCover.intersectionSphereHomeomorph Z n).toHomotopyEquiv.toFun) ≫
    (homologyFunctor R i).map (projection Z n)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

def plusMap (n i : ℕ) :
    homology R i (TopCat.of (North Z n)) ⊞ homology R i (TopCat.of (South Z n)) ⟶
      homology R i (TopCat.of Z) :=
  biprod.desc (northIso Z R n i).hom (southIso Z R n i).hom

theorem epi_plusMap (n i : ℕ) : Epi (plusMap Z R n i) :=
  epi_of_epi_fac (biprod.inl_desc (northIso Z R n i).hom (southIso Z R n i).hom)

def antiMap (n i : ℕ) : homology R i (TopCat.of Z) ⟶
    homology R i (TopCat.of (North Z n)) ⊞ homology R i (TopCat.of (South Z n)) :=
  biprod.lift (northIso Z R n i).inv (-(southIso Z R n i).inv)

theorem mono_antiMap (n i : ℕ) : Mono (antiMap Z R n i) :=
  mono_of_mono_fac (biprod.lift_fst (northIso Z R n i).inv (-(southIso Z R n i).inv))

theorem union_factor (n i : ℕ) :
    unionMap (North Z n) (South Z n) R i = plusMap Z R n i ≫ sectionMap Z R n i := by
  apply biprod.hom_ext'
  · rw [unionMap, biprod.inl_desc, ← Category.assoc, plusMap, biprod.inl_desc]
    change homologyMapToAmbient (North Z n) R i =
      (northIso Z R n i).hom ≫ sectionMap Z R n i
    apply (cancel_epi (northIso Z R n i).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, north_section]
  · rw [unionMap, biprod.inr_desc, ← Category.assoc, plusMap, biprod.inr_desc]
    change homologyMapToAmbient (South Z n) R i =
      (southIso Z R n i).hom ≫ sectionMap Z R n i
    apply (cancel_epi (southIso Z R n i).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, south_section]

theorem signedLiftFactor {X A B D Y : C}
    (f : X ⟶ A) (g : X ⟶ B) (a : A ≅ D) (b : B ≅ D)
    (k : X ⟶ Y) (p : Y ⟶ D)
    (hf : f ≫ a.hom = k ≫ p) (hg : g ≫ b.hom = k ≫ p) :
    biprod.lift f (-g) = k ≫ p ≫ biprod.lift a.inv (-b.inv) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    apply (cancel_mono a.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hf]
  · simp only [Category.assoc, biprod.lift_snd, comp_neg]
    congr 1
    apply (cancel_mono b.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hg]

theorem intersection_factor (n i : ℕ) :
    intersectionMap (North Z n) (South Z n) R i =
      (intersectionIso Z R n i).hom ≫ projectionMap Z R n i ≫ antiMap Z R n i :=
  signedLiftFactor
    (homologyMapOfSubset
      (Set.inter_subset_left : North Z n ∩ South Z n ⊆ North Z n) R i)
    (homologyMapOfSubset
      (Set.inter_subset_right : North Z n ∩ South Z n ⊆ South Z n) R i)
    (northIso Z R n i) (southIso Z R n i) (intersectionIso Z R n i).hom
    (projectionMap Z R n i)
    (north_intersection_projection Z R n i) (south_intersection_projection Z R n i)

def connecting (n i : ℕ) :
    homology R (i + 1) (sphereProduct Z (n + 1)) ⟶ homology R i (sphereProduct Z n) :=
  neighborhoodConnecting (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl ≫
    (intersectionIso Z R n i).hom

theorem section_connecting (n i : ℕ) :
    sectionMap Z R n (i + 1) ≫ connecting Z R n i = 0 := by
  have := epi_plusMap Z R n (i + 1)
  apply (cancel_epi (plusMap Z R n (i + 1))).mp
  rw [comp_zero, ← Category.assoc, ← union_factor]
  unfold connecting
  rw [← Category.assoc]
  have hz := (neighborhoodSequence_exact
    (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl).toIsComplex.zero 1
  change unionMap (North Z n) (South Z n) R (i + 1) ≫
    neighborhoodConnecting (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl = 0 at hz
  rw [hz, zero_comp]

theorem connecting_projection (n i : ℕ) :
    connecting Z R n i ≫ projectionMap Z R n i = 0 := by
  have := mono_antiMap Z R n i
  apply (cancel_mono (antiMap Z R n i)).mp
  rw [zero_comp, connecting, Category.assoc, Category.assoc, ← intersection_factor]
  exact (neighborhoodSequence_exact
    (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl).toIsComplex.zero 2

theorem exact_section_connecting (n i : ℕ) :
    (ShortComplex.mk (sectionMap Z R n (i + 1)) (connecting Z R n i)
      (section_connecting Z R n i)).Exact := by
  have h := neighborhoodSequence_exact
    (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl
  let S := (neighborhoodSequence
    (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl).sc h.toIsComplex 1
  have := epi_plusMap Z R n (i + 1)
  let φ : S ⟶
      ShortComplex.mk (sectionMap Z R n (i + 1)) (connecting Z R n i)
        (section_connecting Z R n i) := {
    τ₁ := plusMap Z R n (i + 1)
    τ₂ := 𝟙 _
    τ₃ := (intersectionIso Z R n i).hom
    comm₁₂ := by
      change plusMap Z R n (i + 1) ≫ sectionMap Z R n (i + 1) =
        unionMap (North Z n) (South Z n) R (i + 1) ≫ 𝟙 _
      rw [Category.comp_id, union_factor]
    comm₂₃ := by
      change 𝟙 _ ≫ connecting Z R n i =
        neighborhoodConnecting (ProductHemisphereCover.hemisphereProductCover Z n)
          R (i + 1) i rfl ≫ (intersectionIso Z R n i).hom
      rw [Category.id_comp]
      rfl }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp (h.exact 1)

theorem exact_connecting_projection (n i : ℕ) :
    (ShortComplex.mk (connecting Z R n i) (projectionMap Z R n i)
      (connecting_projection Z R n i)).Exact := by
  have h := neighborhoodSequence_exact
    (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl
  let S := (neighborhoodSequence
    (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl).sc h.toIsComplex 2
  have := mono_antiMap Z R n i
  let φ : ShortComplex.mk (connecting Z R n i) (projectionMap Z R n i)
      (connecting_projection Z R n i) ⟶ S := {
    τ₁ := 𝟙 _
    τ₂ := (intersectionIso Z R n i).inv
    τ₃ := antiMap Z R n i
    comm₁₂ := by
      change 𝟙 _ ≫ neighborhoodConnecting
        (ProductHemisphereCover.hemisphereProductCover Z n) R (i + 1) i rfl =
        connecting Z R n i ≫ (intersectionIso Z R n i).inv
      simp only [connecting, Category.id_comp, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    comm₂₃ := by
      change (intersectionIso Z R n i).inv ≫
        intersectionMap (North Z n) (South Z n) R i =
        projectionMap Z R n i ≫ antiMap Z R n i
      rw [intersection_factor, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr (h.exact 2)

/-- The actual Mayer--Vietoris boundary induces the suspension recurrence
for the kernel of projection, with no homology vanishing assumed for `Z`. -/
def recurrenceIso (n i : ℕ) : Kernel Z R (n + 1) (i + 1) ≅ Kernel Z R n i :=
  SplitExactKernel.kernelIso
    (projectionMap Z R (n + 1) (i + 1)) (sectionMap Z R n (i + 1))
    (connecting Z R n i) (projectionMap Z R n i)
    (section_projection Z R n (i + 1))
    (section_connecting Z R n i) (connecting_projection Z R n i)
    (exact_section_connecting Z R n i) (exact_connecting_projection Z R n i)

theorem recurrenceIso_hom_ι (n i : ℕ) :
    (recurrenceIso Z R n i).hom ≫ kernel.ι (projectionMap Z R n i) =
      kernel.ι (projectionMap Z R (n + 1) (i + 1)) ≫ connecting Z R n i :=
  SplitExactKernel.kernelIso_hom_ι _ _ _ _ _ _ _ _ _

/-- Projection from a product with a positive-dimensional sphere is an
isomorphism on degree-zero homology, even when the base is disconnected. -/
theorem isZero_kernel_zero (n : ℕ) : IsZero (Kernel Z R (n + 1) 0) := by
  have := neighborhoodUnionMap_zero_epi
    (ProductHemisphereCover.hemisphereProductCover Z n) R
  have : Epi (sectionMap Z R n 0) := epi_of_epi_fac (union_factor Z R n 0).symm
  have hps : projectionMap Z R (n + 1) 0 ≫ sectionMap Z R n 0 = 𝟙 _ := by
    apply (cancel_epi (sectionMap Z R n 0)).mp
    rw [← Category.assoc, section_projection, Category.id_comp, Category.comp_id]
  have : Mono (projectionMap Z R (n + 1) 0) := mono_of_mono_fac hps
  exact isZero_kernel_of_mono _

end AkopyanResearch.ProductSphereKernel
