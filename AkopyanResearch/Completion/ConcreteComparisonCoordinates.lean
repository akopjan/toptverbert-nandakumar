module

public import AkopyanResearch.Completion.QuadraticSourceCoordinates
public import AkopyanResearch.Completion.TargetPairCoordinates

/-!
# Strict coordinate squares for the original comparison map

The single coordinates are the original matching spheres. Each critical
pair coordinate is the original normalized pair evaluation followed by
the constant-path inclusion of the collapsed locus into the local
homotopy fibre. These are equalities of continuous maps, not homotopy
classes or choices of homology generators.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.ConcreteComparisonCoordinates

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticSourceCoordinates QuadraticComplementCoordinates
open PairConcreteLocalModel PairPathCoordinates TargetPairCoordinates
open ProductSphereKernel Submission
open scoped OnePoint

variable {S : Finset (Fin 15)}

abbrev comparison (hS : S.Nonempty) : C(QuadComplement S, ConcreteComparisonTarget.Space S) :=
  ConcreteComparison.comparison.comp S hS

theorem single_square (hS : S.Nonempty) (m : MatchingIndex S) :
    TopCat.ofHom (comparison hS) ≫ TopCat.ofHom (TargetFibration.projection hS) ≫
      TopCat.ofHom (ContinuousMap.eval m) = TopCat.ofHom (singleMap hS m) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- The literal constant-path inclusion at infinity. -/
def collapsedInclusion : C(Collapsed, LocalTarget) where
  toFun d := ⟨(d.val, ⟨ContinuousMap.const unitInterval ∞, rfl⟩),
    LocalPairPathHomology.collapse_closed d.val d.property⟩
  continuous_toFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _

theorem collapsedInclusion_factor :
    TopCat.ofHom collapsedInclusion =
      TopCat.ofHom (MappingPathPair.sourceFibreInclusion LocalPairPathHomology.collapse ∞
        PairCofiberModel.ClosedLocus LocalPairPathHomology.collapse_closed) ≫
      (TopCat.isoOfHomeo
        (MappingPathHomology.fibrePullbackHomeomorph LocalPairPathHomology.collapse ∞)).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro d
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact (LocalPairPathHomology.collapse_closed d.val d.property).symm

theorem pair_square (hS : S.Nonempty) (j : CriticalPairIndex S) :
    (TargetPairCoordinates.coordinate j).comp (comparison hS) =
      collapsedInclusion.comp (collapsedMap hS j) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · exact (collapsedMap_apply hS j x).symm
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    rfl

def localHomologyMap : Hgrp 12 (TopCat.of Collapsed) ⟶ Hgrp 12 (TopCat.of LocalTarget) :=
  HgrpMap 12 (TopCat.ofHom collapsedInclusion)

def localCoordinatesMap (S : Finset (Fin 15)) :
    AddCommGrpCat.of (CriticalPairIndex S → ↥(Hgrp 12 (TopCat.of Collapsed))) ⟶
      AddCommGrpCat.of (CriticalPairIndex S → ↥(Hgrp 12 (TopCat.of LocalTarget))) :=
  AddCommGrpCat.ofHom {
    toFun z j := localHomologyMap (z j)
    map_zero' := by funext j; exact map_zero _
    map_add' := by intro x y; funext j; exact map_add _ _ _ }

/-- The full degree-twelve comparison square uses the literal source and
target coordinate homomorphisms. -/
theorem twelve_square (hS : S.Nonempty) :
    HgrpMap 12 (TopCat.ofHom (comparison hS)) ≫ TargetPairCoordinates.homologyCoordinates =
      (collapsedCoordinatesIso hS).hom ≫ localCoordinatesMap S := by
  ext z j
  change (HgrpFunctor 12).map (TopCat.ofHom (TargetPairCoordinates.coordinate j))
      ((HgrpFunctor 12).map (TopCat.ofHom (comparison hS)) z) =
    (HgrpFunctor 12).map (TopCat.ofHom collapsedInclusion)
      ((collapsedCoordinatesIso hS).hom z j)
  rw [collapsedCoordinatesIso_apply hS z j]
  change ((HgrpFunctor 12).map (TopCat.ofHom (comparison hS)) ≫
    (HgrpFunctor 12).map (TopCat.ofHom (TargetPairCoordinates.coordinate j))) z =
      ((HgrpFunctor 12).map (TopCat.ofHom (collapsedMap hS j)) ≫
        (HgrpFunctor 12).map (TopCat.ofHom collapsedInclusion)) z
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg ((HgrpFunctor 12).map ∘ TopCat.ofHom) (pair_square hS j)) z

end AkopyanResearch.ConcreteComparisonCoordinates
