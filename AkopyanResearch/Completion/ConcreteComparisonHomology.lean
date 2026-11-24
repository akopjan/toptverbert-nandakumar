module

public import AkopyanResearch.Completion.ConcreteComparisonCoordinates
public import AkopyanResearch.Completion.FirstHomologyComparison
public import AkopyanResearch.Completion.PairEndpointHomology
public import AkopyanResearch.Completion.MappingCylinderHomology
public import AkopyanResearch.Completion.QuadraticHomology

/-!
# Low-degree homology of the original comparison

The single and pair coordinate squares identify the actual comparison
homomorphisms in degrees nine and twelve. All remaining low degrees are
settled by the proved vanishing theorems. The genuine mapping-cylinder
pair consequently has zero relative integral homology through degree
fourteen. No assertion about degree fourteen of the source is needed.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.ConcreteComparisonHomology

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic ConcreteComparisonCoordinates QuadraticSourceCoordinates
open QuadraticComplementCoordinates QuadraticComplementHomology
open PairConcreteLocalModel PairPathCoordinates TargetPairCoordinates
open OriginalJoinBridge ProductSphereKernel Submission
open scoped OnePoint

variable {S : Finset (Fin 15)}

theorem singleProduct_coordinates_isIso :
    IsIso (FirstHomologyComparison.productCoordinates
      (fun _ : MatchingIndex S => Target) 7) := by
  exact FirstHomologyComparison.productCoordinates_isIso
    (fun _ : MatchingIndex S => Target) 7 (TargetHighHomology.sourcePoint S)
    (fun _ => ConnectivityTransport.homeomorph RepresentationSphereInvariants.singleHomeomorph.symm
      (ConnectivityTransport.sphere 8))

theorem nine_square (hS : S.Nonempty) :
    HgrpMap 9 (TopCat.ofHom (comparison hS)) ≫
      HgrpMap 9 (TopCat.ofHom (TargetFibration.projection hS)) ≫
        FirstHomologyComparison.productCoordinates (fun _ : MatchingIndex S => Target) 7 =
      (singleCoordinatesIso hS).hom := by
  ext z m
  change HgrpMap 9 (TopCat.ofHom (ContinuousMap.eval m))
      (HgrpMap 9 (TopCat.ofHom (TargetFibration.projection hS))
        (HgrpMap 9 (TopCat.ofHom (comparison hS)) z)) = (singleCoordinatesIso hS).hom z m
  rw [singleCoordinatesIso_apply hS z m]
  change (HgrpMap 9 (TopCat.ofHom (comparison hS)) ≫
    HgrpMap 9 (TopCat.ofHom (TargetFibration.projection hS)) ≫
    HgrpMap 9 (TopCat.ofHom (ContinuousMap.eval m))) z = _
  rw [← HgrpMap_comp, ← HgrpMap_comp, single_square hS m]

theorem degreeNine_isIso (hS : S.Nonempty) :
    IsIso (HgrpMap 9 (TopCat.ofHom (comparison hS))) := by
  have hP := FirstHomologyComparison.targetProjection_isIso hS
  have hC := singleProduct_coordinates_isIso (S := S)
  have hcomp : IsIso (HgrpMap 9 (TopCat.ofHom (comparison hS)) ≫
      HgrpMap 9 (TopCat.ofHom (TargetFibration.projection hS)) ≫
      FirstHomologyComparison.productCoordinates (fun _ : MatchingIndex S => Target) 7) := by
    rw [nine_square hS]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (HgrpMap 9 (TopCat.ofHom (TargetFibration.projection hS)) ≫
      FirstHomologyComparison.productCoordinates (fun _ : MatchingIndex S => Target) 7)

theorem collapsedInclusion_isIso :
    IsIso (HgrpMap 12 (TopCat.ofHom collapsedInclusion)) := by
  have h := PairEndpointHomology.collapsedInclusion_isIso
  rw [collapsedInclusion_factor, HgrpMap_comp]
  infer_instance

theorem localCoordinatesMap_isIso (S : Finset (Fin 15)) :
    IsIso (localCoordinatesMap S) := by
  have h : IsIso localHomologyMap := collapsedInclusion_isIso
  exact (piIso (fun _ : CriticalPairIndex S => asIso localHomologyMap)).isIso_hom

theorem degreeTwelve_isIso (hS : S.Nonempty) :
    IsIso (HgrpMap 12 (TopCat.ofHom (comparison hS))) := by
  have hT : IsIso (TargetPairCoordinates.homologyCoordinates (S := S)) :=
    (TargetPairCoordinates.homologyCoordinatesIso hS).isIso_hom
  have hL := localCoordinatesMap_isIso S
  have hcomp : IsIso (HgrpMap 12 (TopCat.ofHom (comparison hS)) ≫
      TargetPairCoordinates.homologyCoordinates) := by
    rw [twelve_square hS]
    infer_instance
  exact IsIso.of_isIso_comp_right _ TargetPairCoordinates.homologyCoordinates

theorem degreeZero_isIso (hS : S.Nonempty) :
    IsIso (HgrpMap 0 (TopCat.ofHom (comparison hS))) :=
  MappingCylinderHomology.homologyMap_zero_isIso (comparison hS)
    ((isNConnected_quadComplement S hS).mono (by decide : 1 ≤ 8))
    ((TargetConnectivity.isNConnected S hS).mono (by decide : 1 ≤ 8))

/-- The literal comparison induces isomorphisms in all degrees below
fourteen, with integral coefficients. -/
theorem homology_isIso (hS : S.Nonempty) (i : ℕ) (hi : i ≤ 13) :
    IsIso (HgrpMap i (TopCat.ofHom (comparison hS))) := by
  by_cases h0 : i = 0
  · subst i; exact degreeZero_isIso hS
  by_cases h9 : i = 9
  · subst i; exact degreeNine_isIso hS
  by_cases h12 : i = 12
  · subst i; exact degreeTwelve_isIso hS
  have hsource : IsZero (Hgrp i (TopCat.of (QuadComplement S))) :=
    originalComplement_homology_zero hS i hi h0 h9 h12
  have htarget : IsZero (Hgrp i (TopCat.of (ConcreteComparisonTarget.Space S))) := by
    by_cases hlow : i ≤ 8
    · exact TargetConnectivity.homology_vanish S hS i hlow h0
    · exact TargetHighHomology.homology_vanish hS i (by omega) (by omega) h12
  exact hsource.isIso htarget _

/-- Surjectivity in degree fourteen uses only vanishing of the target. -/
theorem homology_epi (hS : S.Nonempty) (i : ℕ) (hi : i ≤ 14) :
    Epi (HgrpMap i (TopCat.ofHom (comparison hS))) := by
  by_cases hlow : i ≤ 13
  · have h := homology_isIso hS i hlow
    infer_instance
  · have heq : i = 14 := by omega
    subst i
    exact (TargetHighHomology.homology_vanish hS 14 (by decide) (by decide) (by decide)).epi _

abbrev cylinderPair (hS : S.Nonempty) : TopPair :=
  MappingCylinderHomology.topPair (TopCat.ofHom (comparison hS))

/-- The actual top of the actual mapping cylinder has zero relative
homology through degree fourteen. -/
theorem cylinder_relative_homology_zero (hS : S.Nonempty) (i : ℕ)
    (hi : i ≤ 14) (hi0 : i ≠ 0) :
    IsZero ((Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) i).obj (cylinderPair hS)) := by
  rcases i with _ | i
  · exact (hi0 rfl).elim
  have hE := homology_epi hS (i + 1) hi
  have hI := homology_isIso hS i (by omega)
  exact MappingCylinderHomology.topPair_homology_zero (TopCat.ofHom (comparison hS)) i

/-- The same vanishing in the genuine relative homology used by the
relative Hurewicz construction, through the checked natural chain iso. -/
theorem cylinder_hrelSet_zero (hS : S.Nonempty) (i : ℕ)
    (hi : i ≤ 14) (hi0 : i ≠ 0) :
    IsZero (Submission.HrelSet (Y := TopCat.MapCyl (TopCat.ofHom (comparison hS))) i
      (TopCat.MapCyl.top (TopCat.ofHom (comparison hS)))) :=
  (cylinder_relative_homology_zero hS i hi hi0).of_iso
    (RelativeHomologyBridge.subsetHomologyIso
      (TopCat.MapCyl.top (TopCat.ofHom (comparison hS))) i)

end AkopyanResearch.ConcreteComparisonHomology
