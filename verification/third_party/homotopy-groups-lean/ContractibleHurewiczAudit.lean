module

public import Lean.Util.CollectAxioms
public import Submission.Hurewicz.RelativeBoundary
import all Submission.Hurewicz.RelativeBoundary
public import Submission.WhiteheadTheorem.Shapes.CubeBoundaryMap
import all Submission.WhiteheadTheorem.Shapes.CubeBoundaryMap
public import Submission.Hurewicz.CubicalBoundary
import all Submission.Hurewicz.CubicalBoundary
public import Submission.Hurewicz.AbsoluteNaturality
import all Submission.Hurewicz.AbsoluteNaturality
public import Submission.SphereHomologicalDegree
import all Submission.SphereHomologicalDegree
public import Submission.Hurewicz.CubicalCollapse
import all Submission.Hurewicz.CubicalCollapse

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Submission.Hurewicz.RelativeBoundary,`Submission.WhiteheadTheorem.Shapes.CubeBoundaryMap,`Submission.Hurewicz.CubicalBoundary,`Submission.Hurewicz.AbsoluteNaturality,`Submission.SphereHomologicalDegree,`Submission.Hurewicz.CubicalCollapse]
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
  logInfo m!"CONTRACTIBLEHUREWICZ AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

