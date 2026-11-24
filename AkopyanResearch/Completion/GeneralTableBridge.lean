module

public import Solution
public import AkopyanResearch.Completion.TableToEmbedding

/-!
# The dimension-eighteen reduction for arbitrary continuous height tables

The original quadratic reduction is sufficient but unnecessarily restrictive
for the analytic realization. Here the table may be any continuous compatible
safe table. Its existence is an explicit hypothesis, not a proved conclusion.

The central blocking theorem, the measure, and the body functionals are supplied
by the original, independently checked geometric construction in `Solution`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace AkopyanSixfold

/-- A continuous compatible safe planar table gives the precise ninety-vertex
almost-six embedding required by the dimension-eighteen transfer. -/
theorem almostSix_ninety_of_continuous_table
    (H : AkopyanResearch.TableToEmbedding.PlanarTable)
    (hH : Continuous H)
    (hcompat : AkopyanResearch.TableRealization.Compatible H)
    (hsafe : AkopyanResearch.TableRealization.Safe 0 H) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ, IsAlmostSixEmbedding g := by
  obtain ⟨g, hg, hsep⟩ :=
    AkopyanResearch.TableToEmbedding.exists_almostSix_of_continuous_table
      H hH hcompat hsafe
  exact ⟨g, hg, hsep⟩

/-- The full convex-partition conclusion for every `d > 17`, conditional only
on an actual continuous compatible safe planar table. No quadratic-degree
restriction and no additional geometric hypothesis appear. -/
theorem convex_partition_counterexample_gt_17_of_continuous_table
    (d : ℕ) (hd : 17 < d)
    (H : AkopyanResearch.TableToEmbedding.PlanarTable)
    (hH : Continuous H)
    (hcompat : AkopyanResearch.TableRealization.Compatible H)
    (hsafe : AkopyanResearch.TableRealization.Safe 0 H) :
    ∃ (Phi : Body d → Fin (d - 1) → ℝ) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  obtain ⟨g, hg⟩ := almostSix_ninety_of_continuous_table H hH hcompat hsafe
  exact convex_partition_counterexample_ge_18 d hd g hg

end AkopyanSixfold
