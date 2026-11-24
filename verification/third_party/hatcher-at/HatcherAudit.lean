module

public import Lean.Util.CollectAxioms
public import Hatcher.Singular.Relative
import all Hatcher.Singular.Relative
public import Hatcher.Excision.Devissage
import all Hatcher.Excision.Devissage
public import Hatcher.Excision.AffineSubdivision
import all Hatcher.Excision.AffineSubdivision
public import Hatcher.Excision.AffineChains
import all Hatcher.Excision.AffineChains
public import Hatcher.Excision.SingularSubdivision
import all Hatcher.Excision.SingularSubdivision
public import Hatcher.Excision.SubdivisionDiameter
import all Hatcher.Excision.SubdivisionDiameter
public import Hatcher.Excision.SmallSimplices
import all Hatcher.Excision.SmallSimplices
public import Hatcher.Excision.SmallChainEquivalence
import all Hatcher.Excision.SmallChainEquivalence
public import Hatcher.Excision.BinaryCover
import all Hatcher.Excision.BinaryCover
public import Hatcher.MayerVietoris.ChainComplex
import all Hatcher.MayerVietoris.ChainComplex
public import Hatcher.MayerVietoris.ShortExact
import all Hatcher.MayerVietoris.ShortExact
public import Hatcher.MayerVietoris.Sequence
import all Hatcher.MayerVietoris.Sequence

open Lean Elab Command

run_cmd do
  let permitted : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ownedModules : List Name := [`Hatcher.Singular.Relative, `Hatcher.Excision.Devissage, `Hatcher.Excision.AffineSubdivision, `Hatcher.Excision.AffineChains, `Hatcher.Excision.SingularSubdivision, `Hatcher.Excision.SubdivisionDiameter, `Hatcher.Excision.SmallSimplices, `Hatcher.Excision.SmallChainEquivalence, `Hatcher.Excision.BinaryCover, `Hatcher.MayerVietoris.ChainComplex, `Hatcher.MayerVietoris.ShortExact, `Hatcher.MayerVietoris.Sequence]
  let env := (← getEnv).setExporting false
  for m in ownedModules do
    unless (env.getModuleIdx? m).isSome do throwError "Missing module: {m}"
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
      unless bad.isEmpty do throwError "Forbidden dependencies in {name}: {bad}"
  if total == 0 then throwError "Empty audit"
  logInfo m!"HATCHER AUDIT OK: {total} declarations, {theorems} theorems, {ownedModules.length} modules; only propext, Classical.choice, Quot.sound"

#print axioms Hatcher.Relative.pairSequence_exact
#print axioms Hatcher.Excision.coverChainMap_homotopyEquivalence
#print axioms Hatcher.Excision.deletedSubsetHomologyMap_isIso_of_closure_subset_interior
#print axioms Hatcher.MayerVietoris.sequence_exact
