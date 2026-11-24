module

public import Lean

/-!
Read-only diagnostic for compiled module data. This file imports no project
module, elaborates no mathematical proof, and writes no compiled object.
It reads the exported/server/private parts through Lean's own file reader.
-/

open Lean

private def strictConstantEqual (a b : ConstantInfo) : Bool :=
  (a == b) && a.type.equal b.type &&
    (match a.value? true, b.value? true with
    | none, none => true
    | some x, some y => x.equal y
    | _, _ => false) &&
    (match a, b with
    | .recInfo x, .recInfo y =>
      x.rules.length == y.rules.length &&
        (x.rules.zip y.rules).all (fun p => p.1.rhs.equal p.2.rhs)
    | .recInfo _, _ => false
    | _, .recInfo _ => false
    | _, _ => true)

private def extensionShapes (d : ModuleData) : Json :=
  toJson (d.entries.toList.map fun p => (p.1.toString, p.2.size))

private def comparePart (label : String) (a b : ModuleData) : Json × Bool := Id.run do
  let mut differences : Array String := #[]
  if a.constants.size != b.constants.size then
    differences := differences.push "<different declaration counts>"
  else
    for h : i in [:a.constants.size] do
      let x := a.constants[i]
      let y := b.constants[i]!
      unless strictConstantEqual x y do
        differences := differences.push x.name.toString
  let same := differences.isEmpty && a.constNames == b.constNames &&
    a.extraConstNames == b.extraConstNames && a.isModule == b.isModule &&
    a.imports == b.imports
  return (Json.mkObj [
    ("part", toJson label),
    ("main_declarations", toJson a.constants.size),
    ("clean_declarations", toJson b.constants.size),
    ("strict_constant_differences", toJson differences),
    ("constant_names_equal", toJson (a.constNames == b.constNames)),
    ("extra_constant_names_equal", toJson (a.extraConstNames == b.extraConstNames)),
    ("module_flag_equal", toJson (a.isModule == b.isModule)),
    ("imports_equal", toJson (a.imports == b.imports)),
    ("main_extension_shapes", extensionShapes a),
    ("clean_extension_shapes", extensionShapes b),
    ("all_nonextension_fields_equal", toJson same)], same)

public def main (args : List String) : IO Unit := do
  unless args.length == 4 do
    throw (IO.userError "Expected MAIN CLEAN MODULES_TXT OUTPUT_JSON")
  let mainRoot : System.FilePath := args[0]!
  let cleanRoot : System.FilePath := args[1]!
  let modules := ((← IO.FS.readFile args[2]!).splitOn "\n").filter (· != "")
  let mut records : Array Json := #[]
  let mut allEqual := true
  for moduleName in modules do
    let rel := moduleName.replace "." "/"
    let mainStem := mainRoot / ".lake/build/lib/lean" / (rel ++ ".olean")
    let cleanStem := cleanRoot / ".lake/build/lib/lean" / (rel ++ ".olean")
    let a ← readModuleDataParts #[mainStem,
      mainStem.addExtension "server", mainStem.addExtension "private"]
    let b ← readModuleDataParts #[cleanStem,
      cleanStem.addExtension "server", cleanStem.addExtension "private"]
    let mut parts : Array Json := #[]
    for i in [:3] do
      let label := #["exported", "server", "private"][i]!
      let some (ma, _) := a[i]? | throw (IO.userError "Missing main module part")
      let some (mb, _) := b[i]? | throw (IO.userError "Missing clean module part")
      let (record, same) := comparePart label ma mb
      parts := parts.push record
      allEqual := allEqual && same
    records := records.push (Json.mkObj [
      ("module", toJson moduleName), ("parts", .arr parts)])
    IO.println s!"Compared stored declarations: {moduleName}"
  let result := Json.mkObj [
    ("all_nonextension_fields_equal", toJson allEqual),
    ("modules_compared", toJson modules.length),
    ("strict_expression_equality", toJson true),
    ("extension_payloads_compared", toJson false),
    ("records", .arr records)]
  IO.FS.writeFile args[3]! result.compress
  unless allEqual do
    throw (IO.userError "Stored declaration or import fields differ; inspect output JSON")
