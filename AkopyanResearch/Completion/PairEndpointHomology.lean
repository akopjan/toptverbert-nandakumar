module

public import AkopyanResearch.Completion.LocalPairPathHomology
public import AkopyanResearch.Completion.RelativeHomologyBridge
public import AkopyanResearch.Completion.FibrationRelativeHomology

/-!
# The actual based-path endpoint map has primitive relative degree

Surjectivity comes from the genuine Serre fibration and absolute Hurewicz
map of the thirteen-sphere. Both relative groups are the checked infinite
cyclic groups. The natural cokernel comparison transfers this result to
the actual map of Hatcher pairs, closing the local comparison obligation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairEndpointHomology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel
open LocalPairPathHomology
open scoped OnePoint

abbrev Target := OnePoint PairTarget
abbrev Total := Submission.PathSpace Target (collapse sourcePoint)
abbrev endpoint : C(Total, Target) := Submission.ev₁ Target (collapse sourcePoint)
abbrev Fibre : Set Total := ⇑endpoint ⁻¹' {∞}

theorem target_connected : Submission.IsNConnected 12 Target :=
  ConnectivityTransport.homeomorph RepresentationSphereInvariants.pairHomeomorph.symm
    (ConnectivityTransport.sphere 12)

def fibrePoint : Fibre := by
  let : PathConnectedSpace Target := target_connected.pathConnected
  let p := (PathConnectedSpace.joined (collapse sourcePoint) (∞ : Target)).somePath
  exact ⟨⟨p.toContinuousMap, p.source⟩, p.target⟩

def sourceHomologyIso : Submission.HrelSet (Y := TopCat.of Total) 13 Fibre ≅ Coefficients :=
  RelativeHomologyBridge.subsetHomologyIso Fibre 13 ≪≫ basedRelativeHomologyIso

def targetHomologyIso : Submission.HrelSet (Y := TopCat.of Target) 13 ({∞} : Set Target) ≅
    Coefficients :=
  RelativeHomologyBridge.subsetHomologyIso ({∞} : Set Target) 13 ≪≫
    (Hatcher.Relative.homologyFunctor Coefficients 13).mapIso
      (RelativeHomologyBridge.singletonPairIso (∞ : Target)) ≪≫
    PairCollapseHomology.targetHomologyIso Coefficients

theorem endpoint_submission_isIso :
    IsIso ((FibrationRelativeHomology.fibrePairMap endpoint ∞ fibrePoint).hrelMap 13) :=
  FibrationRelativeHomology.fibrePairMap_homology_isIso endpoint ∞ fibrePoint 11
    (Submission.isSerreFibration_ev₁ Target (collapse sourcePoint)) target_connected
    sourceHomologyIso targetHomologyIso

theorem endpoint_pair_factor :
    RelativeHomologyBridge.basedPairMap
        (FibrationRelativeHomology.fibrePairMap endpoint ∞ fibrePoint) ≫
      (RelativeHomologyBridge.singletonPairIso (∞ : Target)).hom =
        MappingPathPair.basedEndpointPair collapse ∞ sourcePoint := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · rfl

theorem basedEndpoint_isIso :
    IsIso ((Hatcher.Relative.homologyFunctor Coefficients 13).map
      (MappingPathPair.basedEndpointPair collapse ∞ sourcePoint)) := by
  rw [← endpoint_pair_factor, Functor.map_comp]
  have h := RelativeHomologyBridge.basedPairMap_isIso
    (FibrationRelativeHomology.fibrePairMap endpoint ∞ fibrePoint) 13 endpoint_submission_isIso
  exact IsIso.comp_isIso' h
    (((Hatcher.Relative.homologyFunctor Coefficients 13).mapIso
      (RelativeHomologyBridge.singletonPairIso (∞ : Target))).isIso_hom)

/-- The original collapsed-locus inclusion into the actual mapping-path
fibre induces an isomorphism in degree twelve. -/
theorem collapsedInclusion_isIso :
    IsIso ((homologyFunctor Coefficients 12).map (TopCat.ofHom
      (MappingPathPair.sourceFibreInclusion collapse ∞ PairCofiberModel.ClosedLocus collapse_closed))) :=
  collapsedInclusion_isIso_of_basedEndpoint basedEndpoint_isIso

end AkopyanResearch.PairEndpointHomology
