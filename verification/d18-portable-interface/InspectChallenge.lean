module
public import Lean
import all Challenge

open Lean
set_option autoImplicit false
set_option maxRecDepth 4096

private def encodeName : Name → Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str parent value => .arr #[.str "str", encodeName parent, .str value]
  | .num parent value => .arr #[.str "num", encodeName parent, toJson value]

private def encodeLevel : Level → Json
  | .zero => .arr #[.str "zero"]
  | .succ u => .arr #[.str "succ", encodeLevel u]
  | .max u v => .arr #[.str "max", encodeLevel u, encodeLevel v]
  | .imax u v => .arr #[.str "imax", encodeLevel u, encodeLevel v]
  | .param n => .arr #[.str "param", encodeName n]
  | .mvar n => .arr #[.str "mvar", encodeName n.name]

/-- Only metadata and binder display names are omitted. Bound-variable indices,
universe levels, constant names, implicitness and every application remain. -/
private def encodeExpr : Expr → Json
  | .bvar i => .arr #[.str "bvar", toJson i]
  | .fvar i => .arr #[.str "fvar", encodeName i.name]
  | .mvar i => .arr #[.str "mvar", encodeName i.name]
  | .sort u => .arr #[.str "sort", encodeLevel u]
  | .const n us => .arr #[.str "const", encodeName n, .arr (us.toArray.map encodeLevel)]
  | .app f x => .arr #[.str "app", encodeExpr f, encodeExpr x]
  | .lam _ t b bi => .arr #[.str "lam", encodeExpr t, encodeExpr b, .str (reprStr bi)]
  | .forallE _ t b bi => .arr #[.str "forall", encodeExpr t, encodeExpr b, .str (reprStr bi)]
  | .letE _ t v b nondep => .arr #[.str "let", encodeExpr t, encodeExpr v,
      encodeExpr b, toJson nondep]
  | .lit (.natVal n) => .arr #[.str "nat", toJson n]
  | .lit (.strVal s) => .arr #[.str "string", .str s]
  | .mdata _ e => encodeExpr e
  | .proj n i e => .arr #[.str "proj", encodeName n, toJson i, encodeExpr e]

run_cmd do
  let env := (← getEnv).setExporting false
  let names : Array Name := #[`AkopyanSixfold.simplex, `AkopyanSixfold.DisjointSupports,
    `AkopyanSixfold.IsAlmostSixEmbedding, `AkopyanSixfold.Ambient,
    `AkopyanSixfold.Body, `AkopyanSixfold.unitBall, `AkopyanSixfold.IsSixPartition,
    `AkopyanSixfold.tverberg_counterexample, `AkopyanSixfold.convex_partition_counterexample_gt_17]
  let mut entries : Array Json := #[]
  for n in names do
    let some info := env.find? n | throwError "Missing compiled declaration: {n}"
    if info.type.hasFVar || info.type.hasMVar || info.type.hasLooseBVars then
      throwError "Compiled type is not closed: {n}"
    let fields := [("name", .str n.toString),
      ("level_params", .arr (info.levelParams.toArray.map encodeName)),
      ("type", encodeExpr info.type)]
    match info with
    | .defnInfo d =>
      if d.value.hasFVar || d.value.hasMVar || d.value.hasLooseBVars then
        throwError "Compiled definition is not closed: {n}"
      entries := entries.push (Json.mkObj (fields ++
        [("kind", .str "definition"), ("value", encodeExpr d.value)]))
    | .thmInfo _ =>
      entries := entries.push (Json.mkObj (fields ++ [("kind", .str "theorem")]))
    | _ => throwError "Unexpected genuine declaration kind: {n}"
  let record := Json.mkObj [("declarations", .arr entries),
    ("imports", toJson (env.allImportedModuleNames.toList.map Name.toString))]
  liftM <| IO.FS.writeFile "verification/d18-portable-interface/Challenge.json" record.compress
