# Independent compiled-interface comparison: A and B18

**PASS — `compiled-interfaces-identical`.** On 2026-11-24, 08:58:12–08:59:09
UTC, separate Lean processes read the compiled `Challenge` and
`PalomarSolution` environments. Their nine target types and seven definition
bodies are structurally identical. Both inspections and the comparison driver
returned exit code 0.

This check covers the current unconditional `d > 17` theorem. It supersedes
the scope of the historical `verification/compiled-interface` diagnostic,
which compared the earlier A+B36 interface.

## Compared declarations

Every name below belongs to the namespace `AkopyanSixfold`.

| Declaration | Compiled kind | Type | Definition body |
| --- | --- | --- | --- |
| `simplex` | definition | identical | identical |
| `DisjointSupports` | definition | identical | identical |
| `IsAlmostSixEmbedding` | definition | identical | identical |
| `Ambient` | definition | identical | identical |
| `Body` | definition | identical | identical |
| `unitBall` | definition | identical | identical |
| `IsSixPartition` | definition | identical | identical |
| `tverberg_counterexample` | theorem | identical | not compared |
| `convex_partition_counterexample_gt_17` | theorem | identical | not compared |

The serializer preserves bound-variable indices, binder types and
implicitness, universe parameters and levels, constant names, every
application including instance arguments, projections, literals, and let
types and values. It omits only expression metadata and binder display names.
Every inspected type and definition value is checked to contain no free
variables, metavariables, or loose bound variables. The declarations are
required to have their genuine definition/theorem kinds.

The canonical JSON digest of the nine declaration records is the same in
both environments:

```text
0da75f6ec67460498e6f5a13890e8d06a76dd9dad1739c7f433af31e0b51c3d2
```

## Isolation and input identity

The Challenge process imports `Lean` and `all Challenge`. Its only imported
project module is `Challenge`; it imports neither `Solution` nor
`PalomarSolution`. The proof process imports `Lean`, `all PalomarSolution`,
`all Solution`, and `all AkopyanResearch.Completion.DimensionEighteen`. It
imports no `Challenge`. The direct owner imports load the genuine theorem
declarations behind the publication entry point.

The statically determined project import closure was checked against both
actual imported environments. All **419 source files** and **1,257 compiled
objects** (`.olean`, `.olean.private`, `.olean.server`) in their combined
closure had identical SHA-256 hashes before and after inspection. The pinned
toolchain, package manifest, Lake configuration, serializer and driver were
also bound: **1,681 unchanged inputs** in total. Full pre/post hashes are in
`results.json`.

Selected source hashes:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `d7b36eaa7daf9c593b205f0fc3f748c0a6c8ab3ba726269947d71328c4ce4e66` |
| `Solution.lean` | `41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23` |
| `AkopyanResearch/Completion/DimensionEighteen.lean` | `24f45bfe59787b9308d242083be6163f7852abaec0bc2565cd90fafdaeac7ad8` |
| `PalomarSolution.lean` | `98bcca73c13415a014c1cb394eb8530f8e82993ca7b123fc42752ce0c560744e` |

## Reproduction and diagnostic history

With the pinned `lake` on `PATH` and the project already built, run from
the project root, choosing an output directory that does not yet exist:

```sh
python3 verification/d18-release/reproduce_compiled_interfaces.py \
  --output-dir verification/reproduction-compiled-interface
```

The portable reproducer resolves the selected Lean through `lake`, verifies
the project's toolchain version, reuses this exact serializer and comparison
rules, and records its own source, input and tool hashes. It refuses an
existing output path or a destination outside `verification/`, and never
overwrites this historical evidence. It runs no build or kernel replay.
The validation of this portability correction is recorded separately in
[`d18-portable-interface`](../d18-portable-interface/).

`compare_compiled_interfaces.py.txt` is the preserved historical runner.
It hardcodes the original workspace's sibling `tools-runtime` directory
and is not a portable reproduction command. Its bytes remain unchanged
because the original successful record binds its hash.

That historical driver recorded its exact working directory, environment
overrides, binary version and subprocess commands. It used Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with `lake env lean -j 1` for
each inspection. The generated inspection modules have explicit `module`
headers. Both JSON snapshots, sources, empty successful logs and exit-code
files are preserved here. No proof source, compiled project object, existing
script or configuration file was changed by this diagnostic.

The initial attempt imported only `all PalomarSolution` in the proof process.
Lean 4.35 then exposed the transitive theorem A through its exported
axiom-shaped interface; the strict genuine-kind guard rejected that view.
That attempt and its unchanged-input hashes are retained in
`initial-exported-view`. The successful inspection explicitly imports the
two declaration owners with `all`, without relaxing the guard. This behavior
matches the import-level rules and theorem/exported-axiom compatibility in
the pinned Lean `Lean/Environment.lean`.

## Scope

This is an independent compiled-interface diagnostic. It is **not** the
official Comparator, an official sandbox workflow run, or a comparison of
theorem proof bodies. The specification's theorem placeholders are not
imported into the proof process. Proof-body acceptance and the standard-axiom
inventory belong to the project's separate kernel and audit records.
The additional Mathlib-only semantic checks are recorded in
`../d18-extension-2026-11-24/SEMANTIC_SCOPE_REVIEW.md`.
