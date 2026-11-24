module

public import AkopyanResearch.Completion.QuadraticComplementHomology
public import AkopyanResearch.Completion.FiniteComplementCoordinates

/-!
# Canonical atom and critical-stratum integral homology coordinates

The isomorphisms below retain the actual maps: first restrict a class to
each single-deletion complement, then use its pair boundary and normal
orientation. Thus these are coordinates for meridian calculations, not
merely abstract rank computations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticComplementCoordinates

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets QuadraticDeletedPairs
open QuadraticStratumHomology QuadraticComplementHomology ProductSphereKernel Submission
open DisjointComplementHomology DisjointComplementCoordinates ComplementMayerVietoris
open PairPathCoordinates

variable {S : Finset (Fin 15)}

def piIso {ι : Type} {A B : ι → AddCommGrpCat} (e : ∀ j, A j ≅ B j) :
    AddCommGrpCat.of (∀ j, ↥(A j)) ≅ AddCommGrpCat.of (∀ j, ↥(B j)) :=
  (AddEquiv.piCongrRight fun j => (e j).addCommGroupIsoToAddEquiv).toAddCommGrpIso

def criticalComplementThirteenIso (hS : S.Nonempty) (e : CriticalPairIndex S) :
    Hgrp 13 (TopCat.of ↥((criticalPairSet S e)ᶜ)) ≅ coefficients := by
  let P := TopPair.ofSubset (X := TopCat.of (OpenAmbient S)) (criticalPairSet S e)ᶜ
  have := isIso_pairConnecting_of_ambient_zero P coefficients 13
    (openAmbient_homology_zero 14 (by norm_num) (by norm_num))
    (openAmbient_homology_zero 13 (by norm_num) (by norm_num))
  exact (asIso (Hatcher.Relative.pairConnecting P coefficients 14 13 rfl)).symm ≪≫
    (Hatcher.Relative.homologyFunctor coefficients 14).mapIso (criticalDeletionPairIso e) ≪≫
    criticalRelativeThomIso hS e 0 ≪≫ criticalBaseZeroIso hS e

/-- These coordinates are literally the maps induced by inclusions into
the individual critical-stratum complements. -/
def pairRestrictionIso (hS : S.Nonempty) (F : Finset (CriticalPairIndex S)) :
    Hgrp 13 (TopCat.of ↥(pairComplementSet S F)) ≅
      AddCommGrpCat.of (∀ e : F, ↥(Hgrp 13 (TopCat.of ↥((criticalPairSet S e.val)ᶜ)))) :=
  restrictionIso (X := TopCat.of (OpenAmbient S)) (criticalPairSet S) F coefficients 13
    (fun e _ => criticalPairSet_isClosed hS e)
    (fun e _ f _ hef => criticalPairSet_disjoint hS e f hef)
    (openAmbient_homology_zero 14 (by norm_num) (by norm_num))
    (openAmbient_homology_zero 13 (by norm_num) (by norm_num))

def pairIntegralCoordinatesIso (hS : S.Nonempty) (F : Finset (CriticalPairIndex S)) :
    Hgrp 13 (TopCat.of ↥(pairComplementSet S F)) ≅ AddCommGrpCat.of (↥F → ℤ) :=
  pairRestrictionIso hS F ≪≫ piIso (fun e : F => criticalComplementThirteenIso hS e.val)

theorem pairIntegralCoordinatesIso_apply (hS : S.Nonempty)
    (F : Finset (CriticalPairIndex S)) (x : Hgrp 13 (TopCat.of ↥(pairComplementSet S F)))
    (e : F) :
    (pairIntegralCoordinatesIso hS F).hom x e =
      (criticalComplementThirteenIso hS e.val).hom
        ((HgrpFunctor 13).map (inclusion (X := TopCat.of (OpenAmbient S))
          (complementSet_subset_single (X := TopCat.of (OpenAmbient S))
            (criticalPairSet S) F e e.property)) x) := rfl

theorem atomBinaryRestriction_isIso (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) (m : MatchingIndex S) (hm : m ∉ F) :
    IsIso (binaryRestriction (X := TopCat.of (OpenAmbient S))
      (complementSet (X := TopCat.of (OpenAmbient S)) (atomSet S) F)
      (atomSet S m)ᶜ coefficients 9) := by
  have hc : complementSet (X := TopCat.of (OpenAmbient S)) (atomSet S) F =
      partialComplementSet S F :=
    (partialComplementSet_eq_compl_union F).symm
  rw [hc]
  exact FiniteComplementCoordinates.isIso_binaryRestriction_of_union_zero
    (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ
    (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl coefficients 9
    (atomCoverUnion_homology_zero hS F m hm 10 (by norm_num) (by norm_num) (by norm_num))
    (atomCoverUnion_homology_zero hS F m hm 9 (by norm_num) (by norm_num) (by norm_num))

def atomRestrictionIso (hS : S.Nonempty) (F : Finset (MatchingIndex S)) :
    Hgrp 9 (TopCat.of ↥(partialComplementSet S F)) ≅
      AddCommGrpCat.of (∀ m : F, ↥(Hgrp 9 (TopCat.of ↥((atomSet S m.val)ᶜ)))) :=
  (HgrpFunctor 9).mapIso (TopCat.isoOfHomeo
    (Homeomorph.setCongr (partialComplementSet_eq_compl_union F))) ≪≫
    FiniteComplementCoordinates.restrictionIsoOfBinary (X := TopCat.of (OpenAmbient S))
      (atomSet S) F coefficients 9
      (openAmbient_homology_zero 9 (by norm_num) (by norm_num))
      (fun G m hm => atomBinaryRestriction_isIso hS G m hm)

def atomIntegralCoordinatesIso (hS : S.Nonempty) (F : Finset (MatchingIndex S)) :
    Hgrp 9 (TopCat.of ↥(partialComplementSet S F)) ≅ AddCommGrpCat.of (↥F → ℤ) :=
  atomRestrictionIso hS F ≪≫ piIso (fun m : F => atomComplementNineIso hS m.val)

def originalNineIso (hS : S.Nonempty) :
    Hgrp 9 (TopCat.of (QuadComplement S)) ≅
      AddCommGrpCat.of (↥(Finset.univ : Finset (MatchingIndex S)) → ℤ) :=
  (HgrpFunctor 9).mapIso (TopCat.isoOfHomeo (fullComplementHomeomorph (S := S))) ≪≫
    atomIntegralCoordinatesIso hS Finset.univ

end AkopyanResearch.QuadraticComplementCoordinates
