module

public import Lean.Util.CollectAxioms
public import Submission.Approximation.Approx
import all Submission.Approximation.Approx
public import Submission.Approximation.Boundary
import all Submission.Approximation.Boundary
public import Submission.Approximation.Estimate
import all Submission.Approximation.Estimate
public import Submission.Approximation.Grid
import all Submission.Approximation.Grid
public import Submission.Approximation.RegularValue
import all Submission.Approximation.RegularValue
public import Submission.Approximation.Simplex
import all Submission.Approximation.Simplex
public import Submission.ForMathlib.HomotopyGroup.Basic
import all Submission.ForMathlib.HomotopyGroup.Basic
public import Submission.ForMathlib.HomotopyGroup.Contractible
import all Submission.ForMathlib.HomotopyGroup.Contractible
public import Submission.ForMathlib.HomotopyGroup.Homotopy
import all Submission.ForMathlib.HomotopyGroup.Homotopy
public import Submission.ForMathlib.HomotopyGroup.Map
import all Submission.ForMathlib.HomotopyGroup.Map
public import AkopyanResearch.Completion.ArrangementConnectivity
import all AkopyanResearch.Completion.ArrangementConnectivity
public import AkopyanResearch.Completion.QuadraticConnectivity
import all AkopyanResearch.Completion.QuadraticConnectivity

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Submission.Approximation.Approx,`Submission.Approximation.Boundary,`Submission.Approximation.Estimate,`Submission.Approximation.Grid,`Submission.Approximation.RegularValue,`Submission.Approximation.Simplex,`Submission.ForMathlib.HomotopyGroup.Basic,`Submission.ForMathlib.HomotopyGroup.Contractible,`Submission.ForMathlib.HomotopyGroup.Homotopy,`Submission.ForMathlib.HomotopyGroup.Map,`AkopyanResearch.Completion.ArrangementConnectivity,`AkopyanResearch.Completion.QuadraticConnectivity]
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
  logInfo m!"TOPOLOGY AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

#print axioms AkopyanResearch.ArrangementConnectivity.subsingleton_homotopyGroup_of_codim
#print axioms AkopyanResearch.subsingleton_homotopyGroup_quadComplement
