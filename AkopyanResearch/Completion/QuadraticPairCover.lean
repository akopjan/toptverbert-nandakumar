module

public import AkopyanResearch.Completion.QuadraticPairCoordinates
public import AkopyanResearch.Completion.QuadraticBoundaryExtension
public import AkopyanResearch.Completion.MayerVietorisNaturality

/-!
# Actual maps from an atom-addition cover to each new pair cover

The map of ambient unions is the original critical joint evaluation.
The order of the target cover is chosen by the old atom. Its restriction
to the intersection is the original pair-coordinate map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticPairCover

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets
open QuadraticComplementHomology QuadraticBoundaryExtension QuadraticPairCoordinates
open QuadraticMeridians DisjointComplementHomology DisjointComplementCoordinates
open PairNormalModel PairConcreteLocalModel ProductSphereKernel Submission
open QuadraticStratumHomology

variable {S : Finset (Fin 15)}

abbrev Ambient (F : Finset (MatchingIndex S)) (m : MatchingIndex S) : TopCat :=
  OpenUnionMayerVietoris.unionSpace (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ

abbrev leftRegion (F : Finset (MatchingIndex S)) (m : MatchingIndex S) : Set (Ambient F m) :=
  OpenUnionMayerVietoris.leftSet (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ

abbrev rightRegion (F : Finset (MatchingIndex S)) (m : MatchingIndex S) : Set (Ambient F m) :=
  OpenUnionMayerVietoris.rightSet (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ

theorem cover (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    Hatcher.Excision.CoverCondition (leftRegion F m) (rightRegion F m) :=
  OpenUnionMayerVietoris.cover (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ
    (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl

theorem critical_nonzero_on_union (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) (x : Ambient F m) :
    criticalTest e.val x.val.val ≠ 0 := by
  intro hz
  have hx : x.val ∈ pairComplementSet S (newPairs S F m) := by
    change x.val ∈ (⋃ e ∈ newPairs S F m, criticalPairSet S e)ᶜ
    rw [← actual_atom_cover_union hS F m hm]
    exact x.property
  have havoid := complementSet_subset_single (X := TopCat.of (OpenAmbient S))
    (criticalPairSet S) (newPairs S F m) e.val e.property hx
  apply havoid
  rw [criticalPairSet_eq_subspace]
  exact (criticalTest_zero_iff hS e.val x.val.val).mp hz

def unionMap (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    C(Ambient F m, PuncturedSpace.Space commonEquality) :=
  ⟨fun x => ⟨criticalTest e.val x.val.val, critical_nonzero_on_union hS F m hm e x⟩,
    ((criticalTest e.val).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

theorem unionMap_left (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    Set.MapsTo (TopCat.ofHom (unionMap hS F m hm e)) (leftRegion F m)
      (LinearPairComplementHomology.nonzeroSet
        (CommonPairHomology.test (oldSide hS F m e))) := by
  intro x hx
  change CommonPairHomology.test (oldSide hS F m e) (criticalTest e.val x.val.val) ≠ 0
  intro hz
  exact hx (testAtom hS e.val (oldSide hS F m e)) (oldSide_mem hS F m hm e)
    ((test_zero_iff hS e.val (oldSide hS F m e) x.val.val).mp hz)

theorem unionMap_right (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    Set.MapsTo (TopCat.ofHom (unionMap hS F m hm e)) (rightRegion F m)
      (LinearPairComplementHomology.nonzeroSet
        (CommonPairHomology.test (!(oldSide hS F m e)))) := by
  intro x hx
  change CommonPairHomology.test (!(oldSide hS F m e)) (criticalTest e.val x.val.val) ≠ 0
  intro hz
  have hmem := (test_zero_iff hS e.val (!(oldSide hS F m e)) x.val.val).mp hz
  rw [newSide_eq hS F m hm e] at hmem
  exact hx hmem

def sourceIntersectionHomeomorph (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    ↥(leftRegion F m ∩ rightRegion F m) ≃ₜ ↥(partialComplementSet S (insert m F)) :=
  (OpenUnionMayerVietoris.intersectionHomeomorph (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ).trans
      (Homeomorph.setCongr (partialComplementSet_insert F m).symm)

theorem intersectionSquare (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    (TopCat.isoOfHomeo (sourceIntersectionHomeomorph F m)).hom ≫
        TopCat.ofHom (pairMap hS (insert m F) (newPairInAll hS F m e)) =
      MayerVietorisNaturality.intersectionRestriction (TopCat.ofHom (unionMap hS F m hm e))
        (unionMap_left hS F m hm e) (unionMap_right hS F m hm e) ≫
          (TopCat.isoOfHomeo
            (CommonPairHomology.orderedIntersectionHomeomorph (oldSide hS F m e)).symm).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem rawBoundary_naturality (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    ((rawSequence hS F m).f ≫ (intersectionIso hS F m).hom) ≫
        (HgrpFunctor 12).map (TopCat.ofHom (pairMap hS (insert m F) (newPairInAll hS F m e))) =
      (HgrpFunctor 13).map (TopCat.ofHom (unionMap hS F m hm e)) ≫
        (CommonPairHomology.boundaryIso (oldSide hS F m e) coefficients).hom := by
  have hsource : (rawSequence hS F m).f ≫ (intersectionIso hS F m).hom =
      Hatcher.MayerVietoris.connecting (cover F m) coefficients 13 12 rfl ≫
        (HgrpFunctor 12).map (TopCat.isoOfHomeo (sourceIntersectionHomeomorph F m)).hom := by
    rw [rawSequence_f, intersectionIso_hom, Category.assoc, ← Functor.map_comp]
    rfl
  rw [hsource, Category.assoc, ← Functor.map_comp,
    intersectionSquare hS F m hm e, Functor.map_comp]
  have hn := MayerVietorisNaturality.connecting_naturality
    (TopCat.ofHom (unionMap hS F m hm e)) (unionMap_left hS F m hm e)
    (unionMap_right hS F m hm e) (cover F m)
    (CommonPairHomology.orderedCover (oldSide hS F m e)) coefficients 13 12 rfl
  rw [← Category.assoc, hn, Category.assoc]
  rfl

/-- The new pair component on the actual kernel generator is the local
boundary of the actual joint linear meridian. -/
theorem additionBoundary_naturality (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    (additionSequence hS F m hm).f ≫
        (HgrpFunctor 12).map (TopCat.ofHom (pairMap hS (insert m F) (newPairInAll hS F m e))) =
      (unionCoordinatesIso hS F m hm).inv ≫
        (HgrpFunctor 13).map (TopCat.ofHom (unionMap hS F m hm e)) ≫
          (CommonPairHomology.boundaryIso (oldSide hS F m e) coefficients).hom := by
  simpa only [additionSequence_f, Category.assoc] using
    congrArg (fun f => (unionCoordinatesIso hS F m hm).inv ≫ f)
      (rawBoundary_naturality hS F m hm e)

end AkopyanResearch.QuadraticPairCover
