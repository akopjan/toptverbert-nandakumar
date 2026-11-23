module

public import Solution
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false

/-!
# Kernel-dependency audit for the two required theorems

`lake build Audit` checks that both comparator theorems exist, are genuine
Lean theorem declarations, and transitively depend only on the permitted
foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

This command does not replace kernel elaboration. It runs only *after* all
imported proof modules have compiled successfully.
-/

open Lean MeasureTheory

/-!
The following two examples restate the original `Challenge.lean` interfaces.
Their proofs invoke the public declarations of `Solution.lean`, so the kernel
checks the entire statements, not merely that theorem names exist.
-/

example :
    ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
      AkopyanSixfold.IsAlmostSixEmbedding f :=
  AkopyanSixfold.tverberg_counterexample

example (d : ℕ) (hd : 36 ≤ d) :
    ∃ (Phi : AkopyanSixfold.Body d → (Fin (d - 1) → ℝ))
      (mu : Measure (AkopyanSixfold.Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      mu.AbsolutelyContinuous volume ∧
      ∀ C : Fin 6 → AkopyanSixfold.Body d,
        AkopyanSixfold.IsSixPartition C →
        (∀ i, mu (C i : Set (AkopyanSixfold.Ambient d)) =
          mu (AkopyanSixfold.unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) :=
  AkopyanSixfold.convex_partition_counterexample d hd

run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- Check the main milestones as well as the two published results. When the
  -- audit fails, this helps locate the first problematic proof dependency.
  let targets : Array Name :=
    #[``Tverberg6R.exists_height,
      ``Tverberg6R.heightExtension,
      ``AkopyanSixfold.tverberg_counterexample,
      ``AkopyanSixfold.fivefold_tverberg_join,
      ``AkopyanSixfold.exists_isBlocking_5d,
      ``AkopyanSixfold.convex_partition_counterexample_ge_36,
      ``AkopyanSixfold.convex_partition_counterexample]
  for name in targets do
    unless (← getEnv).contains name do
      throwError "Missing theorem declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    logInfo m!"Axiom audit passed for {name}"

-- Print the two public theorem certificates for a human-readable build log.
#print axioms AkopyanSixfold.tverberg_counterexample
#print axioms AkopyanSixfold.convex_partition_counterexample

end
