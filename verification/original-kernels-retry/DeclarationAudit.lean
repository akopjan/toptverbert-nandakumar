module
public import Lean
import all Solution

open Lean
set_option pp.universes true
set_option format.width 120
set_option pp.proofs false

#print AkopyanSixfold.simplex

#print AkopyanSixfold.DisjointSupports

#print AkopyanSixfold.IsAlmostSixEmbedding

#print AkopyanSixfold.Ambient

#print AkopyanSixfold.Body

#print AkopyanSixfold.unitBall

#print AkopyanSixfold.IsSixPartition

#check @AkopyanSixfold.tverberg_counterexample
#print axioms AkopyanSixfold.tverberg_counterexample

#check @AkopyanSixfold.convex_partition_counterexample
#print axioms AkopyanSixfold.convex_partition_counterexample

run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let privateEnv := (← getEnv).setExporting false
  for name in #[``AkopyanSixfold.tverberg_counterexample, ``AkopyanSixfold.convex_partition_counterexample] do
    match privateEnv.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Selected declaration is not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
    logInfo m!"Axiom whitelist passed for {name}: {axioms}"
