module

public import Solution
public import AkopyanResearch.Completion.ConcreteComparison

/-!
# The dimension-eighteen conclusion from the concrete lifting theorem

This module isolates the geometric implication from `RequiredRelativeLifting`.
All its spaces, comparison maps and chosen target sections are concrete.
`DimensionEighteen` applies the proved lifting theorem to obtain the
unconditional conclusion.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace AkopyanSixfold

/-- Conditional on the concrete relative lifting theorem, the required
ninety-vertex almost-six embedding exists. -/
theorem almostSix_ninety_of_relative_lifting
    (hLift : AkopyanResearch.ConcreteComparison.RequiredRelativeLifting) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ, IsAlmostSixEmbedding g := by
  obtain ⟨H, hH, hq, hcompat, hsafe⟩ :=
    AkopyanResearch.ConcreteComparison.exists_safe_table_of_required_lifting hLift
  obtain ⟨g, hg, hsep⟩ :=
    AkopyanResearch.exists_almostSix_of_safe_compatible_quadratic_table
      H hH hq hcompat hsafe
  exact ⟨g, hg.continuousOn, hsep⟩

/-- The full conclusion for `d > 17`, with the relative lifting input
displayed as a theorem argument for use by the unconditional wrapper. -/
theorem convex_partition_counterexample_gt_17_of_relative_lifting
    (d : ℕ) (hd : 17 < d)
    (hLift : AkopyanResearch.ConcreteComparison.RequiredRelativeLifting) :
    ∃ (Phi : Body d → Fin (d - 1) → ℝ) (mu : Measure (Ambient d)),
      Continuous Phi ∧ IsProbabilityMeasure mu ∧ mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d, IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g, hg⟩ := almostSix_ninety_of_relative_lifting hLift
  exact convex_partition_counterexample_ge_18 d hd g hg

end AkopyanSixfold
