module

public import Submission.Homotopy.FibrationLES
public import Submission.Hurewicz.AbsoluteComparison
public import AkopyanResearch.Completion.RankOneSplit

/-!
# The homology map of a fibration and its fibre

For a Serre fibration `p : E → B`, the actual pair map
`(E, p⁻¹{b}) → (B, {b})` is onto in the first potentially nonzero
homology degree of the base. Lift a homotopy class by the fibration,
then apply naturality of the relative Hurewicz homomorphism.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FibrationRelativeHomology

open CategoryTheory AlgebraicTopology Submission
open scoped Topology Topology.Homotopy

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (b : B) (e : (⇑p ⁻¹' {b} : Set E))

/-- The canonical map from a fibration pair to the singleton pair. -/
def fibrePairMap :
    BasedPairMap (⇑p ⁻¹' {b}) ({b} : Set B) e (⟨b, rfl⟩ : ({b} : Set B)) where
  toContinuousMap := p
  mapsTo' _ hx := hx
  map_basepoint' := e.property

theorem fibrePairMap_homotopy (n : ℕ)
    (z : π_rel n E (⇑p ⁻¹' {b}) e) :
    RelHomotopyGroup.map (fibrePairMap p b e) z =
      RelHomotopyGroup.jStar n B ({b} : Set B) (⟨b, rfl⟩ : ({b} : Set B))
        (Submission.pStar e n z) := by
  refine Quotient.inductionOn z ?_
  intro q
  rfl

/-- Surjectivity in degree `n+2` follows from `(n+1)`-connectedness
of the base. No homotopy or homology condition on the total space is used. -/
theorem fibrePairMap_homology_surjective (n : ℕ)
    (hp : IsSerreFibration p) (hB : IsNConnected (n + 1) B) :
    Function.Surjective ((fibrePairMap p b e).hrelMap (n + 2)) := by
  intro w
  let j := subIncl (Y := TopCat.of B) ({b} : Set B)
  letI : IsIso (relJ (n + 2) j) := isIso_relJ_singleton n b
  obtain ⟨v, hv⟩ := ((ConcreteCategory.isIso_iff_bijective
    (relJ (n + 2) j)).mp inferInstance).surjective w
  obtain ⟨z, hz⟩ := hB.absoluteHurewiczAdd_surjective b v
  obtain ⟨q, hq⟩ := Submission.surjective_pStar e hp (n + 1) z.toMul
  refine ⟨relativeHurewicz n (⇑p ⁻¹' {b}) e q, ?_⟩
  rw [relativeHurewicz_naturality, fibrePairMap_homotopy, hq,
    relativeHurewicz_jStar]
  change relJ (n + 2) j (absoluteHurewiczAdd n b z) = w
  rw [hz, hv]

/-- For infinite cyclic relative homology groups, this surjectivity
identifies the actual fibration pair map as an isomorphism. -/
theorem fibrePairMap_homology_isIso (n : ℕ)
    (hp : IsSerreFibration p) (hB : IsNConnected (n + 1) B)
    (eE : HrelSet (Y := TopCat.of E) (n + 2) (⇑p ⁻¹' {b}) ≅
      RankOneSplit.IntegerGroup)
    (eB : HrelSet (Y := TopCat.of B) (n + 2) ({b} : Set B) ≅
      RankOneSplit.IntegerGroup) :
    IsIso ((fibrePairMap p b e).hrelMap (n + 2)) :=
  RankOneSplit.isIso_of_surjective eE eB _
    (fibrePairMap_homology_surjective p b e n hp hB)

end AkopyanResearch.FibrationRelativeHomology
