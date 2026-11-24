module

public import AkopyanResearch.Completion.TargetHighHomology
public import AkopyanResearch.Completion.LocalPairPathHomology
public import AkopyanResearch.Completion.FibreInclusionTransport

/-!
# Actual critical-pair projections of the concrete comparison target

Each coordinate retains the two original row evaluations and reverses the
original critical-pair path. Its square with the literal global fibre
inclusion commutes. The degree-twelve homology coordinates are induced by
these projections, with no choice of cycles or meridians.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.TargetPairCoordinates

open ContinuousMap CategoryTheory CategoryTheory.Limits ProductSphereKernel
open TargetFiberModel PairPathCoordinates PairCofiberModel
open PairSourceProjections
open scoped Classical OnePoint

abbrev Coefficients := AddCommGrpCat.of ℤ
abbrev LocalTarget := HomotopyPullback.Space LocalPairPathHomology.collapse ∞

variable {S : Finset (Fin 15)} (hS : S.Nonempty)

def sourceCoordinate (j : CriticalPairIndex S) : C(SingleProduct S, PairSpace) where
  toFun x := spherePairEquiv
    ((SingleCoordinateModel.decode hS x).val (firstVertex ∘ representative j),
      (SingleCoordinateModel.decode hS x).val (secondVertex ∘ representative j))
  continuous_toFun := spherePairEquiv.continuous.comp
    (((continuous_apply _).comp (continuous_subtype_val.comp
      (SingleCoordinateModel.continuous_decode hS))).prodMk
      ((continuous_apply _).comp (continuous_subtype_val.comp
        (SingleCoordinateModel.continuous_decode hS))))

def fibreSourcePoint (j : CriticalPairIndex S) : PairSpace :=
  sourceCoordinate hS j (TargetHighHomology.sourcePoint S)

theorem collapse_sourceCoordinate (j : CriticalPairIndex S) (x : SingleProduct S) :
    LocalPairPathHomology.collapse (sourceCoordinate hS j x) = TargetFibration.collapse hS x j := rfl

def rawSourceCoordinate (j : CriticalPairIndex S) :
    C(ConcreteComparisonTarget.Space S, PairSpace) where
  toFun p := spherePairEquiv
    (p.val.1 (firstVertex ∘ representative j), p.val.1 (secondVertex ∘ representative j))
  continuous_toFun := spherePairEquiv.continuous.comp
    (((continuous_apply _).comp (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_apply _).comp (continuous_fst.comp continuous_subtype_val)))

def reversedCoordinatePath (j : CriticalPairIndex S) :
    C(ConcreteComparisonTarget.Space S, C(unitInterval, OnePoint PairTarget)) where
  toFun p := (p.val.2 (representative j)).comp
    ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  continuous_toFun := (ContinuousMap.continuous_precomp
      (⟨unitInterval.symm, unitInterval.continuous_symm⟩ : C(unitInterval, unitInterval))).comp
    ((continuous_apply _).comp (continuous_snd.comp continuous_subtype_val))

theorem reversedCoordinatePath_source (j : CriticalPairIndex S)
    (p : ConcreteComparisonTarget.Space S) : reversedCoordinatePath j p 0 = ∞ := by
  change p.val.2 (representative j) (unitInterval.symm 0) = ∞
  rw [unitInterval.symm_zero]
  exact p.property.finish _

theorem reversedCoordinatePath_target (j : CriticalPairIndex S)
    (p : ConcreteComparisonTarget.Space S) :
    reversedCoordinatePath j p 1 = LocalPairPathHomology.collapse (rawSourceCoordinate j p) := by
  change p.val.2 (representative j) (unitInterval.symm 1) = _
  rw [unitInterval.symm_one]
  exact p.property.start _

def coordinate (j : CriticalPairIndex S) : C(ConcreteComparisonTarget.Space S, LocalTarget) where
  toFun p := ⟨(rawSourceCoordinate j p,
    ⟨reversedCoordinatePath j p, reversedCoordinatePath_source j p⟩),
      (reversedCoordinatePath_target j p).symm⟩
  continuous_toFun := ((rawSourceCoordinate j).continuous.prodMk
    ((reversedCoordinatePath j).continuous.subtype_mk _)).subtype_mk _

def localFibreInclusion (j : CriticalPairIndex S) :
    C(Submission.PathFibre (OnePoint PairTarget) ∞ (TargetHighHomology.sourceValue hS j), LocalTarget) :=
  HomotopyPullbackCoordinates.fibreInclusion LocalPairPathHomology.collapse (fibreSourcePoint hS j) ∞

theorem localFibreInclusion_isIso (j : CriticalPairIndex S) :
    IsIso ((homologyFunctor Coefficients 12).map (TopCat.ofHom (localFibreInclusion hS j))) := by
  let : PathConnectedSpace PairSpace :=
    (ConnectivityTransport.homeomorph LocalPairPathHomology.sourceHomeomorph.symm
      (FiniteSphereSourceHomology.source_isNConnected 2)).pathConnected
  exact FibreInclusionTransport.fibreInclusion_isIso_of_pathConnected
    LocalPairPathHomology.collapse ∞ Coefficients 12 LocalPairPathHomology.sourcePoint
    (fibreSourcePoint hS j) (LocalPairPathHomology.fibreInclusion_isIso 12 (by decide) (by decide))

def localFibreInclusionIso (j : CriticalPairIndex S) :
    homology Coefficients 12
      (TopCat.of (Submission.PathFibre (OnePoint PairTarget) ∞ (TargetHighHomology.sourceValue hS j))) ≅
        homology Coefficients 12 (TopCat.of LocalTarget) := by
  letI := localFibreInclusion_isIso hS j
  exact asIso ((homologyFunctor Coefficients 12).map (TopCat.ofHom (localFibreInclusion hS j)))


theorem coordinate_fibreInclusion (j : CriticalPairIndex S) :
    (coordinate j).comp (TargetHighHomology.fibreInclusion hS) =
      (localFibreInclusion hS j).comp
        (Sphere13FibreHomology.projection (fun _ => ∞) (TargetHighHomology.sourceValue hS) j) := by
  ext γ
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  ext t
  change PairPathCoordinates.decodeRaw hS _ (representative j) (unitInterval.symm t) = _
  rw [PairPathCoordinates.decodeRaw, dite_eq_left (representative_critical j),
    shift_representative, classOf_representative, actPath_one]
  change γ.val.val (unitInterval.symm (unitInterval.symm t)) j = γ.val.val t j
  rw [unitInterval.symm_symm]

def homologyCoordinates : homology Coefficients 12 (TopCat.of (ConcreteComparisonTarget.Space S)) ⟶
    AddCommGrpCat.of (CriticalPairIndex S → ↥(homology Coefficients 12 (TopCat.of LocalTarget))) :=
  AddCommGrpCat.ofHom {
    toFun x j := (homologyFunctor Coefficients 12).map (TopCat.ofHom (coordinate j)) x
    map_zero' := by funext j; exact map_zero _
    map_add' := by intro x y; funext j; exact map_add _ x y }

theorem homologyCoordinates_fibreInclusion
    (x : ↥(homology Coefficients 12 (TopCat.of (TargetHighHomology.Fibre hS))))
    (j : CriticalPairIndex S) :
    homologyCoordinates ((TargetHighHomology.fibreInclusionIso hS 12 (by decide) (by decide)).hom x) j =
      (localFibreInclusionIso hS j).hom
        ((Sphere13FibreHomology.coordinatesIso
          (fun _ : CriticalPairIndex S => RepresentationSphereInvariants.pairHomeomorph)
          (fun _ => ∞) (TargetHighHomology.sourceValue hS)).hom x j) := by
  rw [TargetHighHomology.fibreInclusionIso_hom, Sphere13FibreHomology.coordinatesIso_apply]
  have heq : (homologyFunctor Coefficients 12).map (TopCat.ofHom (TargetHighHomology.fibreInclusion hS)) ≫
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (coordinate j)) =
      (homologyFunctor Coefficients 12).map
        (TopCat.ofHom (Sphere13FibreHomology.projection (fun _ => ∞)
          (TargetHighHomology.sourceValue hS) j)) ≫
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (localFibreInclusion hS j)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((homologyFunctor Coefficients 12).map ∘ TopCat.ofHom)
      (coordinate_fibreInclusion hS j)
  exact ConcreteCategory.congr_hom heq x

include hS in
theorem homologyCoordinates_bijective : Function.Bijective (homologyCoordinates (S := S)) := by
  let e := TargetHighHomology.fibreInclusionIso hS 12 (by decide) (by decide)
  let d := Sphere13FibreHomology.coordinatesIso
    (fun _ : CriticalPairIndex S => RepresentationSphereInvariants.pairHomeomorph)
    (fun _ => ∞) (TargetHighHomology.sourceValue hS)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso _
  have hd : Function.Bijective d.hom := ConcreteCategory.bijective_of_isIso _
  have hj (j : CriticalPairIndex S) : Function.Bijective (localFibreInclusionIso hS j).hom :=
    ConcreteCategory.bijective_of_isIso _
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := he.2 x
    obtain ⟨b, rfl⟩ := he.2 y
    congr 1
    apply hd.1
    funext j
    apply (hj j).1
    rw [← homologyCoordinates_fibreInclusion, ← homologyCoordinates_fibreInclusion]
    exact congrFun hxy j
  · intro z
    obtain ⟨a, ha⟩ := hd.2 (fun j => (localFibreInclusionIso hS j).inv (z j))
    refine ⟨e.hom a, funext fun j => ?_⟩
    rw [homologyCoordinates_fibreInclusion, show d.hom a = _ from ha]
    exact ConcreteCategory.congr_hom (localFibreInclusionIso hS j).inv_hom_id (z j)

def homologyCoordinatesIso :
    homology Coefficients 12 (TopCat.of (ConcreteComparisonTarget.Space S)) ≅
      AddCommGrpCat.of (CriticalPairIndex S → ↥(homology Coefficients 12 (TopCat.of LocalTarget))) := by
  letI := (ConcreteCategory.isIso_iff_bijective (homologyCoordinates (S := S))).mpr
    (homologyCoordinates_bijective hS)
  exact asIso homologyCoordinates

end AkopyanResearch.TargetPairCoordinates
