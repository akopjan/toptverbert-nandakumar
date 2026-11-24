module

public import Lean.Util.CollectAxioms
public import AkopyanResearch.Completion.RankOneSplit
import all AkopyanResearch.Completion.RankOneSplit
public import AkopyanResearch.Completion.LinearMeridian
import all AkopyanResearch.Completion.LinearMeridian
public import AkopyanResearch.Completion.QuadraticMeridians
import all AkopyanResearch.Completion.QuadraticMeridians
public import AkopyanResearch.Completion.RelativeHomotopyBasepoint
import all AkopyanResearch.Completion.RelativeHomotopyBasepoint
public import AkopyanResearch.Completion.FreeRelativeClass
import all AkopyanResearch.Completion.FreeRelativeClass
public import AkopyanResearch.Completion.TargetProjectionHomotopy
import all AkopyanResearch.Completion.TargetProjectionHomotopy
public import AkopyanResearch.Completion.CubicalCut
import all AkopyanResearch.Completion.CubicalCut
public import AkopyanResearch.Completion.CubicalPasting
import all AkopyanResearch.Completion.CubicalPasting
public import AkopyanResearch.Completion.FreeRelativeOperations
import all AkopyanResearch.Completion.FreeRelativeOperations
public import AkopyanResearch.Completion.SimplexSkeletonRetraction
import all AkopyanResearch.Completion.SimplexSkeletonRetraction
public import AkopyanResearch.Completion.ConnectivityTransport
import all AkopyanResearch.Completion.ConnectivityTransport

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`AkopyanResearch.Completion.RankOneSplit, `AkopyanResearch.Completion.LinearMeridian, `AkopyanResearch.Completion.QuadraticMeridians, `AkopyanResearch.Completion.RelativeHomotopyBasepoint, `AkopyanResearch.Completion.FreeRelativeClass, `AkopyanResearch.Completion.TargetProjectionHomotopy, `AkopyanResearch.Completion.CubicalCut, `AkopyanResearch.Completion.CubicalPasting, `AkopyanResearch.Completion.FreeRelativeOperations, `AkopyanResearch.Completion.SimplexSkeletonRetraction, `AkopyanResearch.Completion.ConnectivityTransport]
  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let mut total : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants do
    let owner := match env.getModuleIdxFor? name with
      | some index => moduleNames[index]!
      | none => env.mainModule
    if ownedModules.contains owner then
      total := total + 1
      match info with
      | .axiomInfo _ => throwError "New axiom: {name}"
      | .thmInfo _ => theorems := theorems + 1
      | _ => pure ()
      let axioms ← Lean.collectAxioms name
      let bad := axioms.toList.filter fun a => !permitted.contains a
      unless bad.isEmpty do
        throwError "Forbidden dependencies in {name}: {bad}"
  if total == 0 then throwError "Empty audit"
  logInfo m!"ROOT TOPOLOGY AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"


