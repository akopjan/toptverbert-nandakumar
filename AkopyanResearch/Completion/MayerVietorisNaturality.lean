module

public import AkopyanResearch.Completion.ProductSphereProjection
public import Hatcher.MayerVietoris.Sequence

/-!
# Naturality of the actual Mayer--Vietoris connecting morphism

A map preserving the two cover members induces a map of the genuine
small-chain short exact sequences. Its third component is obtained by the
cokernel universal property, and is proved to commute with the actual
small-chain inclusions. Naturality of the chain-complex connecting map
therefore gives naturality for singular homology of the original spaces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MayerVietorisNaturality

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open Hatcher.MayerVietoris Hatcher.Excision ProductSphereKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X Y : TopCat.{w}} {A B : Set X} {U V : Set Y}

def restriction (f : X ⟶ Y) (h : Set.MapsTo f A U) :
    TopCat.of ↥A ⟶ TopCat.of ↥U :=
  TopCat.ofHom ⟨fun x => ⟨f x, h x.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def intersectionRestriction (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) :
    TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥(U ∩ V) :=
  restriction f (fun _ hx => ⟨hA hx.1, hB hx.2⟩)

@[reassoc] theorem intersectionRestriction_comp_left (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) :
    intersectionRestriction f hA hB ≫ intersectionToLeft U V =
      intersectionToLeft A B ≫ restriction f hA := by ext x; rfl

@[reassoc] theorem intersectionRestriction_comp_right (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) :
    intersectionRestriction f hA hB ≫ intersectionToRight U V =
      intersectionToRight A B ≫ restriction f hB := by ext x; rfl

@[reassoc] theorem restriction_comp_inclusion (f : X ⟶ Y) (hA : Set.MapsTo f A U) :
    restriction f hA ≫ subspaceInclusion U = subspaceInclusion A ≫ f := by ext x; rfl

def membersChainMap (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) (R : C) :
    subspaceChains A R ⊞ subspaceChains B R ⟶ subspaceChains U R ⊞ subspaceChains V R :=
  biprod.map (singularChainMap (restriction f hA) R) (singularChainMap (restriction f hB) R)

theorem intersectionChainMap_naturality (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) (R : C) :
    singularChainMap (intersectionRestriction f hA hB) R ≫
        singularChainComplexIntersectionMap U V R =
      singularChainComplexIntersectionMap A B R ≫ membersChainMap f hA hB R := by
  rw [singularChainComplexIntersectionMap_eq, singularChainComplexIntersectionMap_eq]
  apply biprod.hom_ext
  · simp only [membersChainMap, Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc]
    change ((singularChainComplexFunctor C).obj R).map _ ≫
      ((singularChainComplexFunctor C).obj R).map _ =
      ((singularChainComplexFunctor C).obj R).map _ ≫
        ((singularChainComplexFunctor C).obj R).map _
    rw [← Functor.map_comp, ← Functor.map_comp, intersectionRestriction_comp_left]
  · simp only [membersChainMap, Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    congr 1
    change ((singularChainComplexFunctor C).obj R).map _ ≫
      ((singularChainComplexFunctor C).obj R).map _ =
      ((singularChainComplexFunctor C).obj R).map _ ≫
        ((singularChainComplexFunctor C).obj R).map _
    rw [← Functor.map_comp, ← Functor.map_comp, intersectionRestriction_comp_right]

def smallChainMap (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) (R : C) :
    smallCoverChains A B R ⟶ smallCoverChains U V R := by
  have := (singularChainComplexShortComplex_shortExact A B R).epi_g
  exact (singularChainComplexShortComplex_shortExact A B R).exact.desc
    (membersChainMap f hA hB R ≫ singularChainComplexUnionMap U V R) (by
      change singularChainComplexIntersectionMap A B R ≫ _ = 0
      rw [← Category.assoc, ← intersectionChainMap_naturality]
      simp)

@[reassoc] theorem unionChainMap_naturality (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) (R : C) :
    singularChainComplexUnionMap A B R ≫ smallChainMap f hA hB R =
      membersChainMap f hA hB R ≫ singularChainComplexUnionMap U V R := by
  have := (singularChainComplexShortComplex_shortExact A B R).epi_g
  unfold smallChainMap
  exact (singularChainComplexShortComplex_shortExact A B R).exact.g_desc _ _

def shortComplexMap (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V) (R : C) :
    singularChainComplexShortComplex A B R ⟶ singularChainComplexShortComplex U V R where
  τ₁ := singularChainMap (intersectionRestriction f hA hB) R
  τ₂ := membersChainMap f hA hB R
  τ₃ := smallChainMap f hA hB R
  comm₁₂ := intersectionChainMap_naturality f hA hB R
  comm₂₃ := (unionChainMap_naturality f hA hB R).symm

/-- The cokernel-defined small-chain map induces the original ambient
chain map under the actual inclusion of small chains. -/
theorem smallChainMap_comp_inclusion (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V)
    (hX : CoverCondition A B) (hY : CoverCondition U V) (R : C) :
    smallChainMap f hA hB R ≫
        (smallChainInclusionHomotopyEquiv hY.smallSimplicesCondition R).hom =
      (smallChainInclusionHomotopyEquiv hX.smallSimplicesCondition R).hom ≫
        singularChainMap f R := by
  have : Epi (singularChainComplexUnionMap A B R) :=
    (singularChainComplexShortComplex_shortExact A B R).epi_g
  apply (cancel_epi (singularChainComplexUnionMap A B R)).1
  rw [← Category.assoc, unionChainMap_naturality, Category.assoc,
    singularChainComplexUnionMap_comp_inclusion hY R]
  rw [← Category.assoc, singularChainComplexUnionMap_comp_inclusion hX R]
  apply biprod.hom_ext'
  · simp only [membersChainMap, biprod.inl_map_assoc, biprod.inl_desc_assoc,
      biprod.inl_desc]
    change ((singularChainComplexFunctor C).obj R).map _ ≫
      ((singularChainComplexFunctor C).obj R).map _ =
      ((singularChainComplexFunctor C).obj R).map _ ≫
        ((singularChainComplexFunctor C).obj R).map _
    rw [← Functor.map_comp, ← Functor.map_comp, restriction_comp_inclusion]
  · simp only [membersChainMap, biprod.inr_map_assoc, biprod.inr_desc_assoc,
      biprod.inr_desc]
    change ((singularChainComplexFunctor C).obj R).map _ ≫
      ((singularChainComplexFunctor C).obj R).map _ =
      ((singularChainComplexFunctor C).obj R).map _ ≫
        ((singularChainComplexFunctor C).obj R).map _
    rw [← Functor.map_comp, ← Functor.map_comp, restriction_comp_inclusion]

theorem smallCoverHomologyIso_naturality (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V)
    (hX : CoverCondition A B) (hY : CoverCondition U V) (R : C) (n : ℕ) :
    (smallCoverHomologyIso hX R n).hom ≫ (homologyFunctor R n).map f =
      HomologicalComplex.homologyMap (smallChainMap f hA hB R) n ≫
        (smallCoverHomologyIso hY R n).hom := by
  change HomologicalComplex.homologyMap
      (smallChainInclusionHomotopyEquiv hX.smallSimplicesCondition R).hom n ≫
      HomologicalComplex.homologyMap (singularChainMap f R) n =
    HomologicalComplex.homologyMap (smallChainMap f hA hB R) n ≫
      HomologicalComplex.homologyMap
        (smallChainInclusionHomotopyEquiv hY.smallSimplicesCondition R).hom n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    smallChainMap_comp_inclusion f hA hB hX hY R]

/-- Naturality for the actual singular-homology connecting maps of the
two original cover spaces. -/
theorem connecting_naturality (f : X ⟶ Y)
    (hA : Set.MapsTo f A U) (hB : Set.MapsTo f B V)
    (hX : CoverCondition A B) (hY : CoverCondition U V)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    connecting hX R n m hnm ≫ (homologyFunctor R m).map (intersectionRestriction f hA hB) =
      (homologyFunctor R n).map f ≫ connecting hY R n m hnm := by
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (shortComplexMap f hA hB R)
    (singularChainComplexShortComplex_shortExact A B R)
    (singularChainComplexShortComplex_shortExact U V R) n m (by simpa using hnm)
  have hI : (smallCoverHomologyIso hX R n).inv ≫
        HomologicalComplex.homologyMap (smallChainMap f hA hB R) n =
      (homologyFunctor R n).map f ≫ (smallCoverHomologyIso hY R n).inv := by
    apply (cancel_mono (smallCoverHomologyIso hY R n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← smallCoverHomologyIso_naturality f hA hB hX hY R n]
    simp
  unfold connecting
  rw [Category.assoc]
  change (smallCoverHomologyIso hX R n).inv ≫
      (singularChainComplexShortComplex_shortExact A B R).δ n m _ ≫
        HomologicalComplex.homologyMap (shortComplexMap f hA hB R).τ₁ m = _
  rw [hδ, ← Category.assoc]
  dsimp only [shortComplexMap]
  erw [hI]
  rw [Category.assoc]

end AkopyanResearch.MayerVietorisNaturality
