module

public import AkopyanResearch.Completion.SimplexHurewiczAdd
public import Submission.Hurewicz.CubicalCollapse

/-!
# Homotopy addition in a contractible ambient space

The genuine relative Hurewicz isomorphism transfers the singular-chain
face relation to the relative homotopy group. The explicit simplex
orientation differs from the canonical cube orientation by a unit.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

namespace AkopyanResearch.RelativeSimplexBoundary
open Submission RelativeHurewiczDescent
variable {n : ℕ} {X : TopCat.{0}} {A : Set X}

theorem simplexHurewiczAdd_injective {Y : Type} [TopologicalSpace Y]
    [ContractibleSpace Y] {B : Set Y} (b : B)
    (hB : IsNConnected (n + 1) B) :
    Function.Injective (simplexHurewiczAdd B b (n + 1)) := by
  exact simplexHurewiczAdd_injective_of_relativeHurewiczAdd_injective B b (n + 1)
    (hB.relativeHurewiczAdd_bijective_of_contractibleAmbient b).injective

/-- The actual relative homotopy addition relation for a boundary in a
contractible ambient space, obtained from the genuine Hurewicz map. -/
theorem alternating_class_eq_zero_of_contractible [ContractibleSpace X]
    (a : A) (hA : IsNConnected (n + 1) A) (s : Boundary (n + 1) X A) :
    letI : PathConnectedSpace A := hA.pathConnected
    ∑ i : Fin (n + 5), ((-1 : ℤ) ^ (i : ℕ)) •
      Additive.ofMul (simplexClass a (s.face i)) = 0 := by
  let : PathConnectedSpace A := hA.pathConnected
  apply simplexHurewiczAdd_injective a hA
  rw [map_sum, map_zero]
  simp only [map_zsmul, simplexHurewiczAdd_apply, toMul_ofMul,
    simplexRelativeHurewicz_simplexClass]
  exact alternating_relativeClass_eq_zero s

end AkopyanResearch.RelativeSimplexBoundary
