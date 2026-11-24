module

public import Lean.Util.CollectAxioms
public import AkopyanResearch.Completion.PuncturedSphereHomeomorphism
import all AkopyanResearch.Completion.PuncturedSphereHomeomorphism
public import AkopyanResearch.Completion.SimplexSkeletonConnectivity
import all AkopyanResearch.Completion.SimplexSkeletonConnectivity

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`AkopyanResearch.Completion.PuncturedSphereHomeomorphism,`AkopyanResearch.Completion.SimplexSkeletonConnectivity]
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
  logInfo m!"SKELETONCONNECTIVITY AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

