module
public import Lean
import all Audit
import all AkopyanResearch.Completion.ConcreteReduction
import all AkopyanResearch.Completion.GeneralTableBridge
import all AkopyanResearch.Completion.QuadraticFlatRank
import all AkopyanResearch.Completion.QuadraticLink

open Lean
set_option pp.universes true
set_option pp.explicit true
set_option format.width 120
set_option pp.proofs false

#print AkopyanResearch.ConcreteComparison.RequiredRelativeLifting

#print AkopyanResearch.RelativeComparison.RelativeLifting

#print AkopyanResearch.ConcreteComparisonTarget.diagram

#print AkopyanResearch.ConcreteComparison.comparison

#print AkopyanResearch.ConcreteComparison.chosenSection

#print AkopyanResearch.TableToEmbedding.PlanarTable

#print AkopyanResearch.TableRealization.Compatible

#print AkopyanResearch.TableRealization.Safe

#check @AkopyanSixfold.convex_partition_counterexample_gt_17_of_relative_lifting
#print axioms AkopyanSixfold.convex_partition_counterexample_gt_17_of_relative_lifting

#check @AkopyanSixfold.almostSix_ninety_of_continuous_table
#print axioms AkopyanSixfold.almostSix_ninety_of_continuous_table

#check @AkopyanResearch.QuadraticFlatRank.strict_flat_chain_length_bound
#print axioms AkopyanResearch.QuadraticFlatRank.strict_flat_chain_length_bound

#check @AkopyanResearch.exists_matching_sphere_retract
#print axioms AkopyanResearch.exists_matching_sphere_retract

run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let privateEnv := (← getEnv).setExporting false
  for name in #[``AkopyanSixfold.convex_partition_counterexample_gt_17_of_relative_lifting, ``AkopyanSixfold.almostSix_ninety_of_continuous_table, ``AkopyanResearch.QuadraticFlatRank.strict_flat_chain_length_bound, ``AkopyanResearch.exists_matching_sphere_retract] do
    match privateEnv.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Selected declaration is not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
    logInfo m!"Axiom whitelist passed for {name}: {axioms}"
