module

public import AkopyanResearch.Completion.FiniteSphereSourceHomology
public import AkopyanResearch.Completion.Sphere13FibreHomology
public import AkopyanResearch.Completion.TargetConnectivity

/-!
# Degree-twelve homology and degree-thirteen/fourteen vanishing of the actual target

The original comparison target is identified with its actual path-fibration
pullback. The literal fiber inclusion induces homology isomorphisms in
degrees ten through fourteen. Its degree-twelve coordinate isomorphism is
then computed by the actual critical-pair path coordinates.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.TargetHighHomology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel
open TargetFiberModel
open scoped Classical OnePoint

abbrev Coefficients := AddCommGrpCat.of ℤ

variable (S : Finset (Fin 15))

def sourceHomeomorph : SingleProduct S ≃ₜ
    FiniteSphereSourceHomology.Source (Fintype.card (MatchingIndex S)) :=
  (Homeomorph.piCongrRight fun _ : MatchingIndex S =>
    RepresentationSphereInvariants.singleHomeomorph).trans
      (FiniteProductTopology.reindex (TopCat.sphere.{0} 9) (MatchingIndex S))

def sourcePoint : SingleProduct S :=
  (sourceHomeomorph S).symm (FiniteSphereSourceHomology.sourcePoint (Fintype.card (MatchingIndex S)))

variable {S} (hS : S.Nonempty)

def standardCollapse :
    C(FiniteSphereSourceHomology.Source (Fintype.card (MatchingIndex S)), PairProduct S) :=
  (TargetFibration.collapse hS).comp ⟨(sourceHomeomorph S).symm, (sourceHomeomorph S).symm.continuous⟩

def sourceValue : PairProduct S := TargetFibration.collapse hS (sourcePoint S)

abbrev Fibre := Submission.PathFibre (PairProduct S) (fun _ => ∞) (sourceValue hS)

def targetHomeomorph : ConcreteComparisonTarget.Space S ≃ₜ
    HomotopyPullback.Space (standardCollapse hS) (fun _ => ∞) :=
  (TargetFiberModel.homotopyFiberHomeomorph hS).trans
    ((HomotopyFiberFibration.pullbackHomeomorph (TargetFibration.collapse hS) (fun _ => ∞)).trans
      (HomotopyPullbackCoordinates.sourceHomeomorph (sourceHomeomorph S).symm
        (TargetFibration.collapse hS) (fun _ => ∞)).symm)

def fibreInclusion : C(Fibre hS, ConcreteComparisonTarget.Space S) :=
  (⟨(targetHomeomorph hS).symm, (targetHomeomorph hS).symm.continuous⟩ : C(_, _)).comp
    (HomotopyPullbackCoordinates.fibreInclusion (standardCollapse hS)
      (FiniteSphereSourceHomology.sourcePoint (Fintype.card (MatchingIndex S))) (fun _ => ∞))

def fibreInclusionIso (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    homology Coefficients i (TopCat.of (Fibre hS)) ≅
      homology Coefficients i (TopCat.of (ConcreteComparisonTarget.Space S)) :=
  FiniteSphereSourceHomology.fibreInclusionIso
    (Fintype.card (MatchingIndex S)) (standardCollapse hS) (fun _ => ∞)
    ((TargetConnectivity.pairProduct_isNConnected S).mono (by decide : 9 ≤ 12)) i hi hi' ≪≫
    (homologyFunctor Coefficients i).mapIso
      (show TopCat.of (HomotopyPullback.Space (standardCollapse hS) (fun _ => ∞)) ≅
        TopCat.of (ConcreteComparisonTarget.Space S) from
          TopCat.isoOfHomeo (targetHomeomorph hS).symm)

theorem fibreInclusionIso_hom (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    (fibreInclusionIso hS i hi hi').hom =
      (homologyFunctor Coefficients i).map (TopCat.ofHom (fibreInclusion hS)) := by
  change (homologyFunctor Coefficients i).map _ ≫ (homologyFunctor Coefficients i).map _ = _
  rw [← Functor.map_comp]
  rfl

theorem fibreInclusion_isIso (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    IsIso ((homologyFunctor Coefficients i).map (TopCat.ofHom (fibreInclusion hS))) := by
  rw [← fibreInclusionIso_hom hS i hi hi']
  exact (fibreInclusionIso hS i hi hi').isIso_hom

include hS in
theorem homology_vanish (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) (hne : i ≠ 12) :
    IsZero (homology Coefficients i (TopCat.of (ConcreteComparisonTarget.Space S))) :=
  (Sphere13FibreHomology.homology_vanish
    (fun _ : PairPathCoordinates.CriticalPairIndex S => RepresentationSphereInvariants.pairHomeomorph)
    (fun _ => ∞) (sourceValue hS) i (by omega) hi' hne).of_iso
      (fibreInclusionIso hS i hi hi').symm

def degreeTwelveCoordinatesIso :
    homology Coefficients 12 (TopCat.of (ConcreteComparisonTarget.Space S)) ≅
      AddCommGrpCat.of (∀ j : PairPathCoordinates.CriticalPairIndex S,
        ↥(homology Coefficients 12
          (TopCat.of (Submission.PathFibre (OnePoint PairTarget) ∞ (sourceValue hS j))))) :=
  (fibreInclusionIso hS 12 (by decide) (by decide)).symm ≪≫
    Sphere13FibreHomology.coordinatesIso
      (fun _ : PairPathCoordinates.CriticalPairIndex S => RepresentationSphereInvariants.pairHomeomorph)
      (fun _ => ∞) (sourceValue hS)

theorem fibreInclusion_coordinates :
    (homologyFunctor Coefficients 12).map (TopCat.ofHom (fibreInclusion hS)) ≫
      (degreeTwelveCoordinatesIso hS).hom =
      (Sphere13FibreHomology.coordinatesIso
        (fun _ : PairPathCoordinates.CriticalPairIndex S => RepresentationSphereInvariants.pairHomeomorph)
        (fun _ => ∞) (sourceValue hS)).hom := by
  rw [← fibreInclusionIso_hom hS 12 (by decide) (by decide)]
  exact (fibreInclusionIso hS 12 (by decide) (by decide)).hom_inv_id_assoc _

def componentHomologyIso (j : PairPathCoordinates.CriticalPairIndex S) :
    homology Coefficients 12
        (TopCat.of (Submission.PathFibre (OnePoint PairTarget) ∞ (sourceValue hS j))) ≅
      AddCommGrpCat.of ℤ :=
  Sphere13FibreHomology.componentHomologyIso
    (fun _ : PairPathCoordinates.CriticalPairIndex S => RepresentationSphereInvariants.pairHomeomorph)
    (fun _ => ∞) (sourceValue hS) j

end AkopyanResearch.TargetHighHomology
