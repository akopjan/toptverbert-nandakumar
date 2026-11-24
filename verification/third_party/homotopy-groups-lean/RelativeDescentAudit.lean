module

public import Lean.Util.CollectAxioms
public import Submission.Homotopy.HomotopyLesTools
import all Submission.Homotopy.HomotopyLesTools
public import Submission.Cohomology.Cochain
import all Submission.Cohomology.Cochain
public import Submission.Cohomology.FrontBack
import all Submission.Cohomology.FrontBack
public import Submission.Cohomology.Cup
import all Submission.Cohomology.Cup
public import Submission.Cohomology.Basic
import all Submission.Cohomology.Basic
public import Submission.Cohomology.Singular
import all Submission.Cohomology.Singular
public import Submission.Homology.UCT.HomologyClass
import all Submission.Homology.UCT.HomologyClass
public import Submission.Homology.UCT.Dual
import all Submission.Homology.UCT.Dual
public import Submission.Cohomology.DualBridge
import all Submission.Cohomology.DualBridge
public import Submission.Hurewicz.DegreeOne.Affine
import all Submission.Hurewicz.DegreeOne.Affine
public import Submission.SphereGenerator
import all Submission.SphereGenerator
public import Submission.Hurewicz.NormalizedSimplex
import all Submission.Hurewicz.NormalizedSimplex
public import Submission.Homology.RelMap
import all Submission.Homology.RelMap
public import Submission.Hurewicz.RelativeMap
import all Submission.Hurewicz.RelativeMap
public import Submission.Hurewicz.RelativeSimplex
import all Submission.Hurewicz.RelativeSimplex
public import Submission.Hurewicz.SimplexCubeClass
import all Submission.Hurewicz.SimplexCubeClass
public import Submission.Hurewicz.RelativeNormalization
import all Submission.Hurewicz.RelativeNormalization
public import Submission.Hurewicz.RelativeRepresentatives
import all Submission.Hurewicz.RelativeRepresentatives
public import AkopyanResearch.Completion.RelativeHurewiczDescent
import all AkopyanResearch.Completion.RelativeHurewiczDescent

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Submission.Homotopy.HomotopyLesTools,`Submission.Cohomology.Cochain,`Submission.Cohomology.FrontBack,`Submission.Cohomology.Cup,`Submission.Cohomology.Basic,`Submission.Cohomology.Singular,`Submission.Homology.UCT.HomologyClass,`Submission.Homology.UCT.Dual,`Submission.Cohomology.DualBridge,`Submission.Hurewicz.DegreeOne.Affine,`Submission.SphereGenerator,`Submission.Hurewicz.NormalizedSimplex,`Submission.Homology.RelMap,`Submission.Hurewicz.RelativeMap,`Submission.Hurewicz.RelativeSimplex,`Submission.Hurewicz.SimplexCubeClass,`Submission.Hurewicz.RelativeNormalization,`Submission.Hurewicz.RelativeRepresentatives,`AkopyanResearch.Completion.RelativeHurewiczDescent]
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
  logInfo m!"RELATIVEDESCENT AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

