module

public import AkopyanResearch.Completion.QuadraticPairHomology

/-!
# Homology coordinates of the original quadratic complement

The degree-nine coordinates are the original normalized matching tests.
The degree-twelve coordinates are the original normalized pair tests,
with values in the original collapsed locus. Every component formula
identifies the forward isomorphism with the induced map of the actual
continuous coordinate map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticSourceCoordinates

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets
open QuadraticStratumHomology QuadraticComplementHomology QuadraticComplementCoordinates
open QuadraticPairHomology QuadraticPairCoordinates QuadraticMeridians
open DisjointComplementCoordinates DisjointComplementHomology
open PairNormalModel PairConcreteLocalModel PairPathCoordinates ProductSphereKernel Submission
open OriginalJoinBridge

variable {S : Finset (Fin 15)}

def matchingUnivEquiv : (Finset.univ : Finset (MatchingIndex S)) ≃ MatchingIndex S where
  toFun := Subtype.val
  invFun m := ⟨m, Finset.mem_univ m⟩
  left_inv _ := rfl
  right_inv _ := rfl

def singleLocalIso (hS : S.Nonempty) (m : MatchingIndex S) :
    Hgrp 9 (TopCat.of ↥((atomSet S m)ᶜ)) ≅ Hgrp 9 (TopCat.of Target) := by
  have := matchingSphereMap_isIso hS m
  exact asIso ((HgrpFunctor 9).map (TopCat.ofHom (QuadraticMeridians.matchingSphereMap m)))

def singleCoordinatesIso (hS : S.Nonempty) :
    Hgrp 9 (TopCat.of (QuadComplement S)) ≅
      AddCommGrpCat.of (MatchingIndex S → ↥(Hgrp 9 (TopCat.of Target))) :=
  (HgrpFunctor 9).mapIso (TopCat.isoOfHomeo fullComplementHomeomorph) ≪≫
    atomRestrictionIso hS Finset.univ ≪≫
      piIso (fun m : (Finset.univ : Finset (MatchingIndex S)) => singleLocalIso hS m.val) ≪≫
        (AddEquiv.arrowCongr matchingUnivEquiv
          (AddEquiv.refl ↥(Hgrp 9 (TopCat.of Target)))).toAddCommGrpIso

def singleMap (hS : S.Nonempty) (m : MatchingIndex S) : C(QuadComplement S, Target) :=
  ⟨fun x => MatchingSphereMap.matchingSphere hS x (SingleCoordinateModel.enumeration m),
    MatchingSphereMap.continuous_matchingSphere hS _⟩

def partialToAtom (F : Finset (MatchingIndex S)) (m : F) :
    TopCat.of ↥(partialComplementSet S F) ⟶ TopCat.of ↥((atomSet S m.val)ᶜ) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, x.property m.val m.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem atomRestrictionIso_apply (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (z : Hgrp 9 (TopCat.of ↥(partialComplementSet S F))) (m : F) :
    (atomRestrictionIso hS F).hom z m = (HgrpFunctor 9).map (partialToAtom F m) z := by
  change ((HgrpFunctor 9).map (TopCat.isoOfHomeo
      (Homeomorph.setCongr (partialComplementSet_eq_compl_union F))).hom ≫
    (HgrpFunctor 9).map (inclusion (X := TopCat.of (OpenAmbient S))
      (complementSet_subset_single (X := TopCat.of (OpenAmbient S))
        (atomSet S) F m.val m.property))) z = _
  rw [← Functor.map_comp]
  rfl

theorem singleMap_factor (hS : S.Nonempty) (m : MatchingIndex S) :
    (TopCat.isoOfHomeo fullComplementHomeomorph).hom ≫
      partialToAtom Finset.univ ⟨m, Finset.mem_univ m⟩ ≫
        TopCat.ofHom (QuadraticMeridians.matchingSphereMap m) =
      TopCat.ofHom (singleMap hS m) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem singleCoordinatesIso_apply (hS : S.Nonempty)
    (z : Hgrp 9 (TopCat.of (QuadComplement S))) (m : MatchingIndex S) :
    (singleCoordinatesIso hS).hom z m =
      (HgrpFunctor 9).map (TopCat.ofHom (singleMap hS m)) z := by
  change (HgrpFunctor 9).map (TopCat.ofHom (QuadraticMeridians.matchingSphereMap m))
    ((atomRestrictionIso hS Finset.univ).hom
      ((HgrpFunctor 9).map (TopCat.isoOfHomeo fullComplementHomeomorph).hom z)
      ⟨m, Finset.mem_univ m⟩) = _
  rw [atomRestrictionIso_apply]
  change ((HgrpFunctor 9).map (TopCat.isoOfHomeo fullComplementHomeomorph).hom ≫
    (HgrpFunctor 9).map (partialToAtom Finset.univ ⟨m, Finset.mem_univ m⟩) ≫
    (HgrpFunctor 9).map (TopCat.ofHom (QuadraticMeridians.matchingSphereMap m))) z = _
  rw [← Functor.map_comp, ← Functor.map_comp, singleMap_factor hS m]

def collapsedMap (hS : S.Nonempty) (e : CriticalPairIndex S) :
    C(QuadComplement S, Collapsed) :=
  commonNormalizationHomotopyEquiv.toFun.comp (originalPairMap hS e)

theorem collapsedMap_apply (hS : S.Nonempty) (e : CriticalPairIndex S)
    (x : QuadComplement S) :
    (collapsedMap hS e x).val = spherePairEquiv
      (MatchingSphereMap.matchingSphere hS x (PairSourceProjections.firstVertex ∘ representative e),
        MatchingSphereMap.matchingSphere hS x (PairSourceProjections.secondVertex ∘ representative e)) := by
  exact PairEvaluationEquivalence.pairComparison_on_global hS (representative e)
    (representative_critical e) x

def collapsedCoordinatesIso (hS : S.Nonempty) :
    Hgrp 12 (TopCat.of (QuadComplement S)) ≅
      AddCommGrpCat.of (CriticalPairIndex S → ↥(Hgrp 12 (TopCat.of Collapsed))) :=
  originalPairCoordinatesIso hS ≪≫
    piIso (fun _ : CriticalPairIndex S => Hatcher.Singular.homologyIsoOfHomotopyEquiv
      commonNormalizationHomotopyEquiv coefficients 12)

theorem collapsedCoordinatesIso_apply (hS : S.Nonempty)
    (z : Hgrp 12 (TopCat.of (QuadComplement S))) (e : CriticalPairIndex S) :
    (collapsedCoordinatesIso hS).hom z e =
      (HgrpFunctor 12).map (TopCat.ofHom (collapsedMap hS e)) z := by
  change (HgrpFunctor 12).map (TopCat.ofHom commonNormalizationHomotopyEquiv.toFun)
    ((originalPairCoordinatesIso hS).hom z e) = _
  rw [originalPairCoordinatesIso_apply]
  change ((HgrpFunctor 12).map (TopCat.ofHom (originalPairMap hS e)) ≫
    (HgrpFunctor 12).map (TopCat.ofHom commonNormalizationHomotopyEquiv.toFun)) z = _
  rw [← Functor.map_comp]
  rfl

end AkopyanResearch.QuadraticSourceCoordinates
