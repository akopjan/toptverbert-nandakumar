module
public import Lean
import all Audit
import all AkopyanResearch.Completion.PairOrbit
import all AkopyanResearch.Completion.PairL2Deformation
import all AkopyanResearch.Completion.TargetFiberModel
import all AkopyanResearch.Completion.PairNormalModel
import all AkopyanResearch.Completion.SingleCoordinateModel
import all AkopyanResearch.Completion.PairPathCoordinates
import all AkopyanResearch.Completion.TargetCollapseModel

open Lean
set_option pp.universes true
set_option pp.explicit true
set_option format.width 120
set_option pp.proofs false

#print AkopyanResearch.TargetFiberModel.HomotopyFiber

#print AkopyanResearch.PairNormalModel.commonEquality

#print AkopyanResearch.PairL2Deformation.Balanced2

#check @AkopyanResearch.PairOrbit.card_labelsOverPair
#print axioms AkopyanResearch.PairOrbit.card_labelsOverPair

#check @AkopyanResearch.PairL2Deformation.strong_deformation_retraction
#print axioms AkopyanResearch.PairL2Deformation.strong_deformation_retraction

#check @AkopyanResearch.TargetFiberModel.homotopyFiberHomeomorph
#print axioms AkopyanResearch.TargetFiberModel.homotopyFiberHomeomorph

#check @AkopyanResearch.PairNormalModel.jointQuotientContinuousEquiv
#print axioms AkopyanResearch.PairNormalModel.jointQuotientContinuousEquiv

#check @AkopyanResearch.SingleCoordinateModel.coordinatesHomeomorph
#print axioms AkopyanResearch.SingleCoordinateModel.coordinatesHomeomorph

#check @AkopyanResearch.PairPathCoordinates.homeomorph
#print axioms AkopyanResearch.PairPathCoordinates.homeomorph

#check @AkopyanResearch.TargetCollapseModel.pairTargetSphereHomeomorph
#print axioms AkopyanResearch.TargetCollapseModel.pairTargetSphereHomeomorph

run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let privateEnv := (← getEnv).setExporting false
  for name in #[``AkopyanResearch.PairOrbit.card_labelsOverPair, ``AkopyanResearch.PairL2Deformation.strong_deformation_retraction] do
    match privateEnv.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Selected declaration is not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
    logInfo m!"Axiom whitelist passed for {name}: {axioms}"
  for name in #[``AkopyanResearch.TargetFiberModel.homotopyFiberHomeomorph, ``AkopyanResearch.PairNormalModel.jointQuotientContinuousEquiv, ``AkopyanResearch.SingleCoordinateModel.coordinatesHomeomorph, ``AkopyanResearch.PairPathCoordinates.homeomorph, ``AkopyanResearch.TargetCollapseModel.pairTargetSphereHomeomorph] do
    match privateEnv.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Selected declaration is not a definition: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
    logInfo m!"Definition axiom whitelist passed for {name}: {axioms}"
