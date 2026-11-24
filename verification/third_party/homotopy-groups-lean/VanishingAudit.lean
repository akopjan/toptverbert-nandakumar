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
public import Submission.Hurewicz.SimplexBall
import all Submission.Hurewicz.SimplexBall
public import Submission.Hurewicz.SimplexGlue
import all Submission.Hurewicz.SimplexGlue
public import Submission.WhiteheadTheorem.Auxiliary
import all Submission.WhiteheadTheorem.Auxiliary
public import Submission.WhiteheadTheorem.Shapes.Disk
import all Submission.WhiteheadTheorem.Shapes.Disk
public import Submission.WhiteheadTheorem.Shapes.Jar
import all Submission.WhiteheadTheorem.Shapes.Jar
public import Submission.WhiteheadTheorem.Shapes.Maps
import all Submission.WhiteheadTheorem.Shapes.Maps
public import Submission.WhiteheadTheorem.CWComplex.Basic
import all Submission.WhiteheadTheorem.CWComplex.Basic
public import Submission.WhiteheadTheorem.Exponential
import all Submission.WhiteheadTheorem.Exponential
public import Submission.WhiteheadTheorem.HEP.Cofibration
import all Submission.WhiteheadTheorem.HEP.Cofibration
public import Submission.WhiteheadTheorem.Compressible.Defs
import all Submission.WhiteheadTheorem.Compressible.Defs
public import Submission.WhiteheadTheorem.Shapes.UnitInterval
import all Submission.WhiteheadTheorem.Shapes.UnitInterval
public import Submission.WhiteheadTheorem.Shapes.Cube
import all Submission.WhiteheadTheorem.Shapes.Cube
public import Submission.WhiteheadTheorem.RelHomotopyGroup.Algebra
import all Submission.WhiteheadTheorem.RelHomotopyGroup.Algebra
public import Submission.WhiteheadTheorem.RelHomotopyGroup.Defs
import all Submission.WhiteheadTheorem.RelHomotopyGroup.Defs
public import Submission.WhiteheadTheorem.HomotopyGroup.InducedMaps
import all Submission.WhiteheadTheorem.HomotopyGroup.InducedMaps
public import Submission.WhiteheadTheorem.Defs
import all Submission.WhiteheadTheorem.Defs
public import Submission.WhiteheadTheorem.Shapes.Pushout
import all Submission.WhiteheadTheorem.Shapes.Pushout
public import Submission.WhiteheadTheorem.Shapes.MappingCylinder
import all Submission.WhiteheadTheorem.Shapes.MappingCylinder
public import Submission.WhiteheadTheorem.Shapes.DiskHomeoCube
import all Submission.WhiteheadTheorem.Shapes.DiskHomeoCube
public import Submission.WhiteheadTheorem.HEP.Cube
import all Submission.WhiteheadTheorem.HEP.Cube
public import Submission.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
import all Submission.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
public import Submission.WhiteheadTheorem.HEP.Retract
import all Submission.WhiteheadTheorem.HEP.Retract
public import Submission.WhiteheadTheorem.RelHomotopyGroup.Compression
import all Submission.WhiteheadTheorem.RelHomotopyGroup.Compression
public import Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import all Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
public import Submission.WhiteheadTheorem.HEP.CubeJar
import all Submission.WhiteheadTheorem.HEP.CubeJar
public import Submission.WhiteheadTheorem.Compressible.Disk
import all Submission.WhiteheadTheorem.Compressible.Disk
public import Submission.Hurewicz.SimplexHEP
import all Submission.Hurewicz.SimplexHEP
public import Submission.Homology.Basic
import all Submission.Homology.Basic
public import Submission.Homology.Point
import all Submission.Homology.Point
public import Submission.Homology.Pair
import all Submission.Homology.Pair
public import Submission.Homology.Homotopy
import all Submission.Homology.Homotopy
public import Submission.Homology.PairHomotopy
import all Submission.Homology.PairHomotopy
public import Submission.Homology.SimplicialSplitting
import all Submission.Homology.SimplicialSplitting
public import Submission.Homology.LesTools
import all Submission.Homology.LesTools
public import Submission.Hurewicz.FaceHomotopy
import all Submission.Hurewicz.FaceHomotopy
public import Submission.Hurewicz.Vanishing
import all Submission.Hurewicz.Vanishing
public import Submission.Hurewicz.SimplexDict
import all Submission.Hurewicz.SimplexDict
public import Submission.Hurewicz.Prism
import all Submission.Hurewicz.Prism
public import Submission.Hurewicz.Tower
import all Submission.Hurewicz.Tower
public import Submission.Hurewicz.Deformation
import all Submission.Hurewicz.Deformation
public import Submission.Hurewicz.Compression
import all Submission.Hurewicz.Compression
public import Submission.Homotopy.Connected
import all Submission.Homotopy.Connected
public import Submission.Homotopy.SingletonPair
import all Submission.Homotopy.SingletonPair
public import Submission.ForMathlib.SimplexModel
import all Submission.ForMathlib.SimplexModel
public import Submission.Hurewicz.ConnectedVanishing
import all Submission.Hurewicz.ConnectedVanishing
public import AkopyanResearch.Completion.ArrangementHomology
import all AkopyanResearch.Completion.ArrangementHomology
public import AkopyanResearch.Completion.QuadraticHomology
import all AkopyanResearch.Completion.QuadraticHomology

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Submission.Approximation.Approx,`Submission.Approximation.Boundary,`Submission.Approximation.Estimate,`Submission.Approximation.Grid,`Submission.Approximation.RegularValue,`Submission.Approximation.Simplex,`Submission.ForMathlib.HomotopyGroup.Basic,`Submission.ForMathlib.HomotopyGroup.Contractible,`Submission.ForMathlib.HomotopyGroup.Homotopy,`Submission.ForMathlib.HomotopyGroup.Map,`AkopyanResearch.Completion.ArrangementConnectivity,`AkopyanResearch.Completion.QuadraticConnectivity,`Submission.Hurewicz.SimplexBall,`Submission.Hurewicz.SimplexGlue,`Submission.WhiteheadTheorem.Auxiliary,`Submission.WhiteheadTheorem.Shapes.Disk,`Submission.WhiteheadTheorem.Shapes.Jar,`Submission.WhiteheadTheorem.Shapes.Maps,`Submission.WhiteheadTheorem.CWComplex.Basic,`Submission.WhiteheadTheorem.Exponential,`Submission.WhiteheadTheorem.HEP.Cofibration,`Submission.WhiteheadTheorem.Compressible.Defs,`Submission.WhiteheadTheorem.Shapes.UnitInterval,`Submission.WhiteheadTheorem.Shapes.Cube,`Submission.WhiteheadTheorem.RelHomotopyGroup.Algebra,`Submission.WhiteheadTheorem.RelHomotopyGroup.Defs,`Submission.WhiteheadTheorem.HomotopyGroup.InducedMaps,`Submission.WhiteheadTheorem.Defs,`Submission.WhiteheadTheorem.Shapes.Pushout,`Submission.WhiteheadTheorem.Shapes.MappingCylinder,`Submission.WhiteheadTheorem.Shapes.DiskHomeoCube,`Submission.WhiteheadTheorem.HEP.Cube,`Submission.WhiteheadTheorem.HomotopyGroup.ChangeBasePt,`Submission.WhiteheadTheorem.HEP.Retract,`Submission.WhiteheadTheorem.RelHomotopyGroup.Compression,`Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq,`Submission.WhiteheadTheorem.HEP.CubeJar,`Submission.WhiteheadTheorem.Compressible.Disk,`Submission.Hurewicz.SimplexHEP,`Submission.Homology.Basic,`Submission.Homology.Point,`Submission.Homology.Pair,`Submission.Homology.Homotopy,`Submission.Homology.PairHomotopy,`Submission.Homology.SimplicialSplitting,`Submission.Homology.LesTools,`Submission.Hurewicz.FaceHomotopy,`Submission.Hurewicz.Vanishing,`Submission.Hurewicz.SimplexDict,`Submission.Hurewicz.Prism,`Submission.Hurewicz.Tower,`Submission.Hurewicz.Deformation,`Submission.Hurewicz.Compression,`Submission.Homotopy.Connected,`Submission.Homotopy.SingletonPair,`Submission.ForMathlib.SimplexModel,`Submission.Hurewicz.ConnectedVanishing,`AkopyanResearch.Completion.ArrangementHomology,`AkopyanResearch.Completion.QuadraticHomology]
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
  logInfo m!"VANISHING AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"


#print axioms Submission.IsNConnected.isZero_homology
#print axioms AkopyanResearch.ArrangementConnectivity.isZero_homology_complement
#print axioms AkopyanResearch.isZero_homology_quadComplement
