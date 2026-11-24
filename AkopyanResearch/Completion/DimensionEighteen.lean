module

public import AkopyanResearch.Completion.ConcreteReduction
public import AkopyanResearch.Completion.ConcreteComparisonLifting

/-!
# The unconditional dimension-eighteen conclusion

The concrete relative lifting theorem supplies the last input to the
fifteen-color construction. The original convex-geometric reduction then
applies in every dimension strictly larger than seventeen.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace AkopyanSixfold

/-- The ninety-vertex almost-six embedding supplied by the concrete
comparison and the compatible safe planar table. -/
theorem almostSix_ninety :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ, IsAlmostSixEmbedding g := by
  exact almostSix_ninety_of_relative_lifting
    AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting

/-- In every dimension strictly larger than seventeen, a continuous
functional and an absolutely continuous probability measure obstruct
simultaneous convex six-equipartition. -/
theorem convex_partition_counterexample_gt_17 (d : ℕ) (hd : 17 < d) :
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  exact convex_partition_counterexample_gt_17_of_relative_lifting d hd
    AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting

end AkopyanSixfold
