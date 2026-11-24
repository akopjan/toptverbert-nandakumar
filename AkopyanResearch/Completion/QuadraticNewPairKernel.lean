module

public import AkopyanResearch.Completion.QuadraticPairCover
public import AkopyanResearch.Completion.ShortExactCoordinates

/-!
# The actual new pair coordinates detect the entire Mayer--Vietoris kernel

The single critical meridian maps are proved isomorphisms. Together with
the canonical restriction coordinates and the proved map-of-covers square,
this identifies the new-coordinate map on the exact kernel. No matrix
coefficient, Thom naturality, or splitting hypothesis is introduced.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticNewPairKernel

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets QuadraticDeletedPairs
open QuadraticStratumHomology QuadraticComplementHomology QuadraticComplementCoordinates
open QuadraticBoundaryExtension QuadraticPairCoordinates QuadraticPairCover QuadraticMeridians
open DisjointComplementHomology DisjointComplementCoordinates
open PairPathCoordinates PairNormalModel ProductSphereKernel Submission

variable {S : Finset (Fin 15)}

def criticalSetHomeomorph (e : CriticalPairIndex S) :
    ↥((criticalPairSet S e)ᶜ) ≃ₜ (deletionPair (criticalFlat e)).snd :=
  Homeomorph.setCongr (by rw [criticalPairSet_eq_subspace]; rfl)

def criticalSetMap (hS : S.Nonempty) (e : CriticalPairIndex S) :
    C(↥((criticalPairSet S e)ᶜ), PuncturedSpace.Space commonEquality) :=
  (criticalMeridian hS e).comp ⟨criticalSetHomeomorph e, (criticalSetHomeomorph e).continuous⟩

theorem criticalSetMap_factor (hS : S.Nonempty) (e : CriticalPairIndex S) :
    TopCat.ofHom (criticalSetMap hS e) =
      (TopCat.isoOfHomeo (criticalSetHomeomorph e)).hom ≫
        TopCat.ofHom (criticalMeridian hS e) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem criticalSetMap_isIso (hS : S.Nonempty) (e : CriticalPairIndex S) :
    IsIso ((HgrpFunctor 13).map (TopCat.ofHom (criticalSetMap hS e))) := by
  have := criticalMeridian_isIso hS e
  rw [criticalSetMap_factor hS e, Functor.map_comp]
  infer_instance

theorem unionToSet_safe (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) (x : Ambient F m) :
    x.val ∈ (criticalPairSet S e.val)ᶜ := by
  intro hx
  rw [criticalPairSet_eq_subspace] at hx
  exact critical_nonzero_on_union hS F m hm e x
    ((criticalTest_zero_iff hS e.val x.val.val).mpr hx)

def unionToSet (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    Ambient F m ⟶ TopCat.of ↥((criticalPairSet S e.val)ᶜ) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, unionToSet_safe hS F m hm e x⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem unionMap_factor (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    TopCat.ofHom (QuadraticPairCover.unionMap hS F m hm e) =
      unionToSet hS F m hm e ≫ TopCat.ofHom (criticalSetMap hS e.val) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

def unionRestrictionIso (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    Hgrp 13 (Ambient F m) ≅ AddCommGrpCat.of
      (∀ e : newPairs S F m, ↥(Hgrp 13 (TopCat.of ↥((criticalPairSet S e.val)ᶜ)))) :=
  (HgrpFunctor 13).mapIso (TopCat.isoOfHomeo
    (Homeomorph.setCongr (actual_atom_cover_union hS F m hm))) ≪≫
      pairRestrictionIso hS (newPairs S F m)

theorem unionRestrictionIso_apply (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (z : Hgrp 13 (Ambient F m)) (e : newPairs S F m) :
    (unionRestrictionIso hS F m hm).hom z e =
      (HgrpFunctor 13).map (unionToSet hS F m hm e) z := by
  change ((HgrpFunctor 13).map
      (TopCat.isoOfHomeo (Homeomorph.setCongr (actual_atom_cover_union hS F m hm))).hom ≫
    (HgrpFunctor 13).map (inclusion (X := TopCat.of (OpenAmbient S))
      (complementSet_subset_single (X := TopCat.of (OpenAmbient S))
        (criticalPairSet S) (newPairs S F m) e.val e.property))) z = _
  rw [← Functor.map_comp]
  rfl

def newLocalIso (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (e : newPairs S F m) :
    Hgrp 13 (TopCat.of ↥((criticalPairSet S e.val)ᶜ)) ≅ LocalHomology := by
  have := criticalSetMap_isIso hS e.val
  exact asIso ((HgrpFunctor 13).map (TopCat.ofHom (criticalSetMap hS e.val))) ≪≫
    CommonPairHomology.boundaryIso (oldSide hS F m e) coefficients

abbrev NewHomologyProduct (S : Finset (Fin 15)) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) : AddCommGrpCat :=
  AddCommGrpCat.of (↥(newPairs S F m) → ↥LocalHomology)

def newBoundaryIso (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    Hgrp 13 (Ambient F m) ≅ NewHomologyProduct S F m :=
  unionRestrictionIso hS F m hm ≪≫ piIso (fun e : newPairs S F m => newLocalIso hS F m e)

theorem newBoundaryIso_apply (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (z : Hgrp 13 (Ambient F m)) (e : newPairs S F m) :
    (newBoundaryIso hS F m hm).hom z e =
      (CommonPairHomology.boundaryIso (oldSide hS F m e) coefficients).hom
        ((HgrpFunctor 13).map (TopCat.ofHom (QuadraticPairCover.unionMap hS F m hm e)) z) := by
  change (CommonPairHomology.boundaryIso (oldSide hS F m e) coefficients).hom
      (((HgrpFunctor 13).map (TopCat.ofHom (criticalSetMap hS e.val)))
        ((unionRestrictionIso hS F m hm).hom z e)) = _
  rw [unionRestrictionIso_apply hS F m hm z e]
  change (CommonPairHomology.boundaryIso (oldSide hS F m e) coefficients).hom
      (((HgrpFunctor 13).map (unionToSet hS F m hm e) ≫
        (HgrpFunctor 13).map (TopCat.ofHom (criticalSetMap hS e.val))) z) = _
  rw [← Functor.map_comp, ← unionMap_factor hS F m hm e]

def newCoordinates (hS : S.Nonempty) (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    Hgrp 12 (TopCat.of ↥(partialComplementSet S (insert m F))) ⟶ NewHomologyProduct S F m :=
  AddCommGrpCat.ofHom
    { toFun := fun z e => (HgrpFunctor 12).map
        (TopCat.ofHom (pairMap hS (insert m F) (newPairInAll hS F m e))) z
      map_zero' := by funext e; exact map_zero _
      map_add' := by intro x y; funext e; exact map_add _ _ _ }

theorem addition_comp_newCoordinates (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    (additionSequence hS F m hm).f ≫ newCoordinates hS F m =
      (unionCoordinatesIso hS F m hm).inv ≫ (newBoundaryIso hS F m hm).hom := by
  ext z e
  change (HgrpFunctor 12).map
      (TopCat.ofHom (pairMap hS (insert m F) (newPairInAll hS F m e)))
        ((additionSequence hS F m hm).f z) =
    (newBoundaryIso hS F m hm).hom ((unionCoordinatesIso hS F m hm).inv z) e
  rw [newBoundaryIso_apply hS F m hm]
  exact ConcreteCategory.congr_hom (additionBoundary_naturality hS F m hm e) z

theorem isIso_addition_comp_newCoordinates (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    IsIso ((additionSequence hS F m hm).f ≫ newCoordinates hS F m) := by
  rw [addition_comp_newCoordinates hS F m hm]
  infer_instance

theorem isIso_new_and_old (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    IsIso (biprod.lift (newCoordinates hS F m) (additionSequence hS F m hm).g) := by
  have := isIso_addition_comp_newCoordinates hS F m hm
  exact ShortExactCoordinates.isIso_lift_of_kernel_iso (additionSequence hS F m hm)
    (additionSequence_shortExact hS F m hm) (newCoordinates hS F m)

end AkopyanResearch.QuadraticNewPairKernel
