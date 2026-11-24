module

public import AkopyanResearch.Completion.MappingCylinderFaceLifting
public import AkopyanResearch.Completion.ConcreteComparisonConnectivity

/-!
# The proved relative lifting property of the original comparison

This discharges the original concrete lifting obligation. Its input is the
actual fourteen-connected mapping-cylinder pair, and the face dimension
is at most fourteen. The prescribed boundary homotopy is extended exactly.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.ConcreteComparisonLifting

open CategoryTheory AkopyanQuadratic
open ConcreteComparisonCoordinates ConcreteComparisonConnectivity

/-- The genuine relative lifting property, without additional topological
or homological assumptions. -/
theorem requiredRelativeLifting : ConcreteComparison.RequiredRelativeLifting := by
  constructor
  intro S hS g eta h₀ h₁
  let : PathConnectedSpace (QuadComplement S) :=
    pathConnectedSpace_quadComplement S hS
  have hc : S.card - 1 ≤ 14 := by
    have hcard := Finset.card_le_univ S
    simp only [Fintype.card_fin] at hcard
    omega
  exact MappingCylinderFaceLifting.extend (TopCat.ofHom (comparison hS)) S hS
    (cylinder_pair_fourteen hS) hc g (ConcreteComparison.chosenSection.value S hS)
    eta h₀ h₁

end AkopyanResearch.ConcreteComparisonLifting
