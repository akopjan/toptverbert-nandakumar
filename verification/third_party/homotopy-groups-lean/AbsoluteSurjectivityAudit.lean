module

public import Lean.Util.CollectAxioms
public import Submission.Homology.SmallSimplices
import all Submission.Homology.SmallSimplices
public import Submission.Homology.MayerVietoris
import all Submission.Homology.MayerVietoris
public import Submission.Homology.MayerVietorisLES
import all Submission.Homology.MayerVietorisLES
public import Submission.Homology.Excision
import all Submission.Homology.Excision
public import Submission.Hurewicz.SmallRelativeChains
import all Submission.Hurewicz.SmallRelativeChains
public import Submission.Homology.Contractible
import all Submission.Homology.Contractible
public import Submission.Homology.MayerVietorisIso
import all Submission.Homology.MayerVietorisIso
public import Submission.Homology.HomologyZero
import all Submission.Homology.HomologyZero
public import Submission.Homology.RightExact
import all Submission.Homology.RightExact
public import Submission.Homology.SphereZero
import all Submission.Homology.SphereZero
public import Submission.Homology.SphereZeroSplit
import all Submission.Homology.SphereZeroSplit
public import Submission.Homology.Sphere
import all Submission.Homology.Sphere
public import Submission.Homology.SphereOne
import all Submission.Homology.SphereOne
public import Submission.Hurewicz.CubeFundamentalClass
import all Submission.Hurewicz.CubeFundamentalClass
public import Submission.Hurewicz.RelativeAdditivity
import all Submission.Hurewicz.RelativeAdditivity
public import Submission.Model.SphereCompl
import all Submission.Model.SphereCompl
public import Submission.SphereHomotopy
import all Submission.SphereHomotopy
public import Submission.Model.SphereConnected
import all Submission.Model.SphereConnected
public import Submission.Hurewicz.SimplexCubeOrientation
import all Submission.Hurewicz.SimplexCubeOrientation
public import Submission.Hurewicz.RelativeSurjectivity
import all Submission.Hurewicz.RelativeSurjectivity
public import Submission.Hurewicz.AbsoluteSurjectivity
import all Submission.Hurewicz.AbsoluteSurjectivity
public import Submission.Hurewicz.AbsoluteComparison
import all Submission.Hurewicz.AbsoluteComparison

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Submission.Homology.SmallSimplices,`Submission.Homology.MayerVietoris,`Submission.Homology.MayerVietorisLES,`Submission.Homology.Excision,`Submission.Hurewicz.SmallRelativeChains,`Submission.Homology.Contractible,`Submission.Homology.MayerVietorisIso,`Submission.Homology.HomologyZero,`Submission.Homology.RightExact,`Submission.Homology.SphereZero,`Submission.Homology.SphereZeroSplit,`Submission.Homology.Sphere,`Submission.Homology.SphereOne,`Submission.Hurewicz.CubeFundamentalClass,`Submission.Hurewicz.RelativeAdditivity,`Submission.Model.SphereCompl,`Submission.SphereHomotopy,`Submission.Model.SphereConnected,`Submission.Hurewicz.SimplexCubeOrientation,`Submission.Hurewicz.RelativeSurjectivity,`Submission.Hurewicz.AbsoluteSurjectivity,`Submission.Hurewicz.AbsoluteComparison]
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
  logInfo m!"ABSOLUTESURJECTIVITY AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

