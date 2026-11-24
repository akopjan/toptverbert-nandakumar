module

public import AkopyanResearch.Completion.TargetFiberModel
public import AkopyanResearch.Completion.HomotopyFiberFibration

/-!
# The fibration of the actual comparison target

The projection retains all original single-matching sphere coordinates.
Its homotopy lifting property is transferred through the already proved
homeomorphism with the path-space homotopy fiber of the actual collapse.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.TargetFibration

open TargetFiberModel
open scoped OnePoint

variable {S : Finset (Fin 15)} (hS : S.Nonempty)

def collapse : C(SingleProduct S, PairProduct S) :=
  ⟨collapseCoordinates hS, continuous_collapseCoordinates hS⟩

def projection : C(ConcreteComparisonTarget.Space S, SingleProduct S) :=
  (HomotopyFiberFibration.projection (collapse hS) (fun _ => ∞)).comp
    ⟨homotopyFiberHomeomorph hS, (homotopyFiberHomeomorph hS).continuous⟩

theorem projection_apply (p : ConcreteComparisonTarget.Space S) (m : MatchingIndex S) :
    projection hS p m = p.val.1 (SingleCoordinateModel.enumeration m) := rfl

theorem hasHLP_projection (A : Type*) [TopologicalSpace A] :
    Submission.HasHLP (projection hS) A :=
  (Submission.HasHLP.of_homeomorph (homotopyFiberHomeomorph hS)).comp
    (HomotopyFiberFibration.hasHLP_projection (collapse hS) (fun _ => ∞) A)

theorem isSerreFibration_projection : Submission.IsSerreFibration (projection hS) :=
  fun _ => hasHLP_projection hS _

theorem projection_comparison (H : QuadComplement S)
    (m : MatchingIndex S) :
    projection hS (ConcreteComparison.comparisonMap S hS H) m =
      MatchingSphereMap.matchingSphere hS H (SingleCoordinateModel.enumeration m) := rfl

end AkopyanResearch.TargetFibration
