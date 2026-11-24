module

public import AkopyanResearch.Completion.FiniteSphereSourceHomology
public import AkopyanResearch.Completion.Sphere13FibreHomology
public import AkopyanResearch.Completion.MappingPathHomology
public import AkopyanResearch.Completion.PairCollapseHomology

/-!
# Actual path-pair homology for the original pair collapse

The fixed-source path-pair inclusion is an isomorphism in relative degree
thirteen. This uses the proved sphere-source fiber inclusion and the actual
pair boundaries. The final endpoint comparison is kept as its precise
remaining map obligation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.LocalPairPathHomology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel
open PairCofiberModel
open scoped OnePoint

abbrev Coefficients := AddCommGrpCat.of ℤ

def collapse : C(PairSpace, OnePoint PairTarget) := ⟨pairCollapseMap, continuous_pairCollapseMap⟩

def sourceHomeomorph : PairSpace ≃ₜ FiniteSphereSourceHomology.Source 2 :=
  spherePairEquiv.symm.trans
    ((Homeomorph.prodCongr RepresentationSphereInvariants.singleHomeomorph
      RepresentationSphereInvariants.singleHomeomorph).trans
        (Homeomorph.finTwoArrow (X := TopCat.sphere.{0} 9)).symm)

def sourcePoint : PairSpace := sourceHomeomorph.symm (FiniteSphereSourceHomology.sourcePoint 2)

theorem target_isNConnected : Submission.IsNConnected 9 (OnePoint PairTarget) :=
  ConnectivityTransport.homeomorph RepresentationSphereInvariants.pairHomeomorph.symm
    ((ConnectivityTransport.sphere 12).mono (by decide : 9 ≤ 12))

theorem fibreInclusion_isIso (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    IsIso ((homologyFunctor Coefficients i).map (TopCat.ofHom
      (HomotopyPullbackCoordinates.fibreInclusion collapse sourcePoint ∞))) :=
  FiniteSphereSourceHomology.fibreInclusion_isIso_of_homeomorph 2 sourceHomeomorph
    collapse ∞ target_isNConnected i hi hi'

theorem basedPairInclusion_isIso :
    IsIso ((Hatcher.Relative.homologyFunctor Coefficients 13).map
      (MappingPathPair.basedPairInclusion collapse ∞ sourcePoint)) :=
  MappingPathHomology.basedPairInclusion_isIso collapse ∞ Coefficients sourcePoint 12 (by decide)
    (PairRelativeHomology.ambient_homology_vanish Coefficients 13 (by decide) (by decide))
    (PairRelativeHomology.ambient_homology_vanish Coefficients 12 (by decide) (by decide))
    (fibreInclusion_isIso 12 (by decide) (by decide))

def basedRelativeHomologyIso :
    (Hatcher.Relative.homologyFunctor Coefficients 13).obj
      (MappingPathPair.basedPair collapse ∞ sourcePoint) ≅ Coefficients :=
  PairBoundaryComparison.boundaryIso (MappingPathPair.basedPair collapse ∞ sourcePoint)
      Coefficients 12
      (MappingPathHomology.based_ambient_homology_vanish collapse ∞ Coefficients sourcePoint 13 (by decide))
      (MappingPathHomology.based_ambient_homology_vanish collapse ∞ Coefficients sourcePoint 12 (by decide)) ≪≫
    (homologyFunctor Coefficients 12).mapIso
      (TopCat.isoOfHomeo (MappingPathPair.basedFibreHomeomorph collapse ∞ sourcePoint)) ≪≫
    Hatcher.Singular.homologyIsoOfHomotopyEquiv
      (Sphere13FibreHomology.fibreModel RepresentationSphereInvariants.pairHomeomorph
        (collapse sourcePoint) ∞) Coefficients 12 ≪≫
    LoopSphereHomology.fibreDiagonalIso Coefficients 12 (by decide)

def replacementRelativeHomologyIso :
    (Hatcher.Relative.homologyFunctor Coefficients 13).obj
      (MappingPathPair.pair collapse ∞) ≅ Coefficients := by
  letI := basedPairInclusion_isIso
  exact (asIso ((Hatcher.Relative.homologyFunctor Coefficients 13).map
    (MappingPathPair.basedPairInclusion collapse ∞ sourcePoint))).symm ≪≫ basedRelativeHomologyIso

theorem collapse_closed (x : PairSpace) (hx : x ∈ ClosedLocus) : collapse x = ∞ := by
  change pairCollapseMap x = ∞
  rw [← PairCofiberSection.quotientCollapse_quotientMap x,
    PairCollapseHomology.quotientMap_closed ⟨x, hx⟩, PairCollapseHomology.quotientCollapse_point]

theorem originalPairMap_eq :
    MappingPathPair.originalPairMap collapse ∞ ClosedLocus collapse_closed =
      PairCollapseHomology.originalPairMap := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · ext x
    exact (PairCollapseHomology.originalPairMap_apply x).symm

theorem originalPairMap_isIso :
    IsIso ((Hatcher.Relative.homologyFunctor Coefficients 13).map
      (MappingPathPair.originalPairMap collapse ∞ ClosedLocus collapse_closed)) := by
  rw [originalPairMap_eq]
  exact PairCollapseHomology.originalPairMap_homology_isIso

/-- Once the endpoint map of the contractible based-path pair is shown
to be an isomorphism, the actual inclusion of the collapsed locus into
the homotopy-fiber subspace is an isomorphism in degree twelve. -/
theorem collapsedInclusion_isIso_of_basedEndpoint
    (hE : IsIso ((Hatcher.Relative.homologyFunctor Coefficients 13).map
      (MappingPathPair.basedEndpointPair collapse ∞ sourcePoint))) :
    IsIso ((homologyFunctor Coefficients 12).map (TopCat.ofHom
      (MappingPathPair.sourceFibreInclusion collapse ∞ ClosedLocus collapse_closed))) := by
  have hEnd := MappingPathHomology.endpointPair_isIso collapse ∞ Coefficients sourcePoint 13
    basedPairInclusion_isIso hE
  exact MappingPathHomology.sourceFibreInclusion_isIso collapse ∞ Coefficients ClosedLocus collapse_closed 12
    (PairRelativeHomology.ambient_homology_vanish Coefficients 13 (by decide) (by decide))
    (PairRelativeHomology.ambient_homology_vanish Coefficients 12 (by decide) (by decide))
    originalPairMap_isIso hEnd

end AkopyanResearch.LocalPairPathHomology
