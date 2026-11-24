module

public import AkopyanResearch.Completion.ConcreteComparisonTarget
public import AkopyanResearch.Completion.MatchingSphereMap
public import AkopyanResearch.Completion.MatchingPairCollapse
public import AkopyanResearch.Completion.RelativeComparison

/-!
# The actual natural comparison and its precise relative lifting interface

The complement is mapped to the concrete target by centered normalized
matching evaluations. For a pair, the first four evaluated rows agree, so
the original pair collapse is infinity; its path is chosen constantly infinity.
Both this comparison and the chosen target section commute with every face lift.

`RequiredRelativeLifting` below is an explicit proposition about these concrete
maps. `ConcreteComparisonLifting.requiredRelativeLifting` proves it in a later
module. The last theorem here records the resulting finite table construction
as a separate implication.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ConcreteComparison

open scoped OnePoint
open EquivariantJoinStep OriginalJoinBridge PairSourceProjections
  ConcreteComparisonTarget MatchingSphereMap MatchingPairCollapse

theorem matching_pair_collapse {S : Finset (Fin 15)} (hS : S.Nonempty)
    (H : QuadComplement S) (ω : PairLabels S) :
    pairCollapseMap (spherePairEquiv
      (matchingSphere hS H (firstVertex ∘ ω),
        matchingSphere hS H (secondVertex ∘ ω))) = ∞ := by
  let a : Rows := matchingRows H.1 (firstVertex ∘ ω)
  let b : Rows := matchingRows H.1 (secondVertex ∘ ω)
  apply collapse_of_initial_differences (centered a) (centered b)
    (mean b 0 - mean a 0) (mean b 1 - mean a 1)
    (r := ‖vector a‖⁻¹) (s := ‖vector b‖⁻¹)
  · intro i
    rw [centered_castAdd, centered_castAdd]
    have hi : a (i.castAdd 2) 0 = b (i.castAdd 2) 0 := pair_rows_common H.1 ω i 0
    rw [hi]
    ring
  · intro i
    rw [centered_natAdd, centered_natAdd]
    have hi : a (i.castAdd 2) 1 = b (i.castAdd 2) 1 := pair_rows_common H.1 ω i 1
    rw [hi]
    ring
  · exact inv_nonneg.mpr (norm_nonneg _)
  · exact inv_nonneg.mpr (norm_nonneg _)
  · rfl
  · rfl

/-- All path coordinates of the genuine comparison are constant infinity. -/
def comparisonMap (S : Finset (Fin 15)) (hS : S.Nonempty)
    (H : QuadComplement S) : Space S :=
  ⟨(fun σ => matchingSphere hS H σ, fun _ => ContinuousMap.const Time ∞), by
    constructor
    · exact matchingSphere_enumeration_change hS H
    · intro ω
      exact (matching_pair_collapse hS H ω).symm
    · intro ω
      rfl
    · intro h ω s
      simp [actOnePoint]
    · intro ω b hω s
      rfl⟩

theorem continuous_comparisonMap (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Continuous (comparisonMap S hS) := by
  apply Continuous.subtype_mk
  exact (continuous_pi (continuous_matchingSphere hS)).prodMk continuous_const

theorem comparisonMap_natural {T S : Finset (Fin 15)}
    (hT : T.Nonempty) (hS : S.Nonempty) (hTS : T ⊆ S) (H : QuadComplement T) :
    comparisonMap S hS (liftFaceCompl hT hTS H) =
      lift hTS (comparisonMap T hT H) := rfl

def comparison : RelativeComparison.Comparison diagram where
  comp S hS := ⟨comparisonMap S hS, continuous_comparisonMap S hS⟩
  natural := comparisonMap_natural

def chosenSection : RelativeComparison.ChosenSection diagram where
  value S _ := ⟨sectionMap S, continuous_sectionMap S⟩
  natural _ _ hTS z := sectionMap_natural hTS z

/-- The concrete relative extension statement proved in
`ConcreteComparisonLifting`. This abbreviation introduces no axiom. -/
abbrev RequiredRelativeLifting : Prop :=
  RelativeComparison.RelativeLifting diagram comparison chosenSection

theorem exists_safe_table_of_required_lifting (hLift : RequiredRelativeLifting) :
    ∃ H : MassSimplex → TableWords → Fin 2 → ℝ,
      Continuous H ∧
      (∀ z t, (fun w => H z w t) ∈ AkopyanQuadratic.quadraticLabelSpace (Fin 15) (Fin 6)) ∧
      (∀ z i, z.val i = 0 → ∀ t, AkopyanQuadratic.IgnoresColor (fun w => H z w t) i) ∧
      (∀ z : MassSimplex, ∀ σ : MatchingColumns,
        ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) :=
  RelativeComparison.exists_safe_table_of_relative_lifting
    diagram comparison chosenSection hLift

end AkopyanResearch.ConcreteComparison
