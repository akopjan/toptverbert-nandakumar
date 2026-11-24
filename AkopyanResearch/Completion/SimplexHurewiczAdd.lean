module

public import AkopyanResearch.Completion.RelativeSimplexBoundary
public import Submission.Hurewicz.SimplexCubeOrientation
public import Submission.Hurewicz.RelativeAdditivity

/-! # The simplex-oriented relative Hurewicz homomorphism -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

namespace AkopyanResearch.RelativeSimplexBoundary
open Submission RelativeHurewiczDescent

/-- The explicit-simplex Hurewicz evaluator as an additive homomorphism. -/
def simplexHurewiczAdd {Y : Type} [TopologicalSpace Y] (B : Set Y) (b : B) (n : ℕ) :
    Additive (π_rel (n + 2) Y B b) →+ HrelSet (Y := TopCat.of Y) (n + 2) B :=
  cubeSimplexOrientationDegree n • relativeHurewiczAdd n B b

theorem simplexHurewiczAdd_apply {Y : Type} [TopologicalSpace Y]
    (B : Set Y) (b : B) (n : ℕ) (z : Additive (π_rel (n + 2) Y B b)) :
    simplexHurewiczAdd B b n z = simplexRelativeHurewicz n B b z.toMul := by
  exact (simplexRelativeHurewicz_eq_degree_smul_relativeHurewicz n z.toMul).symm

/-- The explicit simplex orientation changes the canonical map by a unit. -/
theorem simplexHurewiczAdd_injective_of_relativeHurewiczAdd_injective
    {Y : Type} [TopologicalSpace Y] (B : Set Y) (b : B) (n : ℕ)
    (hi : Function.Injective (relativeHurewiczAdd n B b)) :
    Function.Injective (simplexHurewiczAdd B b n) := by
  intro z w h
  apply hi
  change cubeSimplexOrientationDegree n • relativeHurewiczAdd n B b z =
    cubeSimplexOrientationDegree n • relativeHurewiczAdd n B b w at h
  rcases cubeSimplexOrientationDegree_eq_one_or_neg_one n with hu | hu
  · simpa [hu] using h
  · simpa [hu] using h

end AkopyanResearch.RelativeSimplexBoundary
