module
public import Lean
import all Audit
import all Solution
import all AkopyanResearch.Completion.DimensionEighteen
import all AkopyanResearch.Completion.ConcreteComparisonLifting

open Lean
set_option pp.universes true
set_option pp.explicit true
set_option format.width 120
set_option pp.proofs false

#print AkopyanSixfold.IsAlmostSixEmbedding

#print AkopyanSixfold.IsSixPartition

#check @AkopyanSixfold.tverberg_counterexample
#print axioms AkopyanSixfold.tverberg_counterexample

#check @AkopyanSixfold.almostSix_ninety
#print axioms AkopyanSixfold.almostSix_ninety

#check @AkopyanSixfold.convex_partition_counterexample_gt_17
#print axioms AkopyanSixfold.convex_partition_counterexample_gt_17

#check @AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting
#print axioms AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting

run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let privateEnv := (← getEnv).setExporting false
  for name in #[``AkopyanSixfold.tverberg_counterexample, ``AkopyanSixfold.almostSix_ninety, ``AkopyanSixfold.convex_partition_counterexample_gt_17, ``AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting] do
    match privateEnv.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Selected declaration is not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
    logInfo m!"Axiom whitelist passed for {name}: {axioms}"
