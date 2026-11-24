module

public import Lean.Util.CollectAxioms
public import Submission.Hurewicz.SphereLoopBridge
import all Submission.Hurewicz.SphereLoopBridge
public import Submission.Hurewicz.StickSimplex
import all Submission.Hurewicz.StickSimplex
public import Submission.Hurewicz.CubicalShell
import all Submission.Hurewicz.CubicalShell
public import Submission.Hurewicz.NormalizedBoundary
import all Submission.Hurewicz.NormalizedBoundary
public import Submission.Hurewicz.StickBoundary
import all Submission.Hurewicz.StickBoundary
public import Submission.Hurewicz.StickSphere
import all Submission.Hurewicz.StickSphere
public import Submission.Hurewicz.DeformationClass
import all Submission.Hurewicz.DeformationClass
public import Submission.Hurewicz.SimplexHorn
import all Submission.Hurewicz.SimplexHorn
public import Submission.Hurewicz.SingularKan
import all Submission.Hurewicz.SingularKan
public import Submission.Hurewicz.SimplicialAddition
import all Submission.Hurewicz.SimplicialAddition
public import Submission.Hurewicz.SimplicialRelation
import all Submission.Hurewicz.SimplicialRelation
public import Submission.Hurewicz.SimplicialIndexShift
import all Submission.Hurewicz.SimplicialIndexShift
public import Submission.Hurewicz.SimplicialTelescope
import all Submission.Hurewicz.SimplicialTelescope
public import Submission.Hurewicz.SimplicialDescent
import all Submission.Hurewicz.SimplicialDescent
public import Submission.Hurewicz.SimplicialRelationAt
import all Submission.Hurewicz.SimplicialRelationAt
public import Submission.Hurewicz.RelativeSimplicialDescent
import all Submission.Hurewicz.RelativeSimplicialDescent
public import Submission.Hurewicz.AbsoluteIsomorphism
import all Submission.Hurewicz.AbsoluteIsomorphism

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Submission.Hurewicz.SphereLoopBridge,`Submission.Hurewicz.StickSimplex,`Submission.Hurewicz.CubicalShell,`Submission.Hurewicz.NormalizedBoundary,`Submission.Hurewicz.StickBoundary,`Submission.Hurewicz.StickSphere,`Submission.Hurewicz.DeformationClass,`Submission.Hurewicz.SimplexHorn,`Submission.Hurewicz.SingularKan,`Submission.Hurewicz.SimplicialAddition,`Submission.Hurewicz.SimplicialRelation,`Submission.Hurewicz.SimplicialIndexShift,`Submission.Hurewicz.SimplicialTelescope,`Submission.Hurewicz.SimplicialDescent,`Submission.Hurewicz.SimplicialRelationAt,`Submission.Hurewicz.RelativeSimplicialDescent,`Submission.Hurewicz.AbsoluteIsomorphism]
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
  logInfo m!"ABSOLUTEISOMORPHISM AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

