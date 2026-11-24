# Main and clean compiled-object comparison

Recorded 2026-11-24, 09:13:55–09:14:01 UTC.

**Result:** the two checkouts contain identical stored mathematical
declarations. Their compiled files are not all byte-identical: the observed
differences lie in extension metadata and serialized layout. No project
source or compiled object was changed, and no project rebuild, heavy export,
or additional kernel-check run was performed.

## Byte comparison

The comparison uses the complete inventory of **438 proof-module owners**
from the successful main build. For every owner it reads `.olean`,
`.olean.private`, and `.olean.server` from both `akopyan-completion` and
`clean-d18`. No object is missing.

| Object kind | Compared | Byte-identical | Different |
| --- | ---: | ---: | ---: |
| `.olean` | 438 | 437 | 1 |
| `.olean.private` | 438 | 374 | 64 |
| `.olean.server` | 438 | 374 | 64 |
| **Total** | **1,314** | **1,185** | **129** |

The 129 differences concern **64 modules**. All 472 source/configuration
inputs equal the successful main and clean build snapshots. Every source and
object hash was checked again after the comparison; both checkouts remained
unchanged. Full object sizes and hashes are in `object-hashes.json`, with
complete pre/post snapshots in `input-sha256-before.json` and
`input-sha256-after.json`.

## Stored declarations

For each differing module, the diagnostic uses Lean 4.35.0's
`readModuleDataParts`, in the required exported/server/private order. It
compares every `ConstantInfo` field, then strengthens expression comparison
to `Expr.equal` for every type, theorem/definition/opaque value, and recursor
right-hand side. This equality retains binder names and annotations. Names,
universe parameters, declaration kinds, safety and reducibility information,
and the remaining constructor fields are compared as well.

All comparisons pass. The 64 private parts contain **3,672 declaration
records**. Their exported and server declaration records also match. The
module flags, imports, constant-name arrays and extra-constant-name arrays
match in every part. Only opaque environment-extension payloads are outside
this field comparison; their names and entry counts are recorded for review.

The other 374 module triples are already byte-identical. Consequently every
stored project declaration in the complete 438-owner inventory agrees
between the two checkouts, including actual proof bodies.

## Characterization of the file differences

In 63 of the differing private parts, the aligned byte comparison finds only
one or two different bytes near the end of the file. The associated server
parts contain different absolute source paths, for example:

```text
/workspace/scratch/9db1b532943d/akopyan-completion/AkopyanResearch/Completion/RelativeHomologyConnectivity.lean
/workspace/scratch/9db1b532943d/clean-d18/AkopyanResearch/Completion/RelativeHomologyConnectivity.lean
```

Lean saves the three module parts as shared compacted regions; later parts
may reference objects stored in earlier parts. A changed server metadata
layout therefore also changes references in a private part without changing
its declarations. The direct field comparison above distinguishes these
layout differences from proof-term changes.

`AkopyanResearch.Completion.ArrangementConnectivity` is the sole differing
exported `.olean`. The clean file additionally contains the compiler package
marker `TopTverberg`. Its 17 exported declarations and 22 private declarations
are exactly equal, as are its imports and other nonextension fields. Its
private file has 32 differing aligned bytes; the recorded comparison again
finds no change to a type or proof.

The triples for `Audit`, `DimensionEighteen`, and
`ConcreteComparisonLifting` are byte-identical. `Solution` has the small
private/server metadata difference described above; its declarations,
including Theorem A and the convex-geometric reduction, are equal.

## Binding to the independent kernel export

All **1,314 main objects** match the object hashes recorded in
`verification/d18-kernels/results.json`. That export therefore uses the
same stored project declarations reproduced by the separate clean-source
build. This is a declaration/body equality claim, not a claim that all
compiled files are byte-identical.

At this comparison's timestamp the independent kernel driver was still
running. Its acceptance results are recorded separately. This comparison
neither reruns those checkers nor changes their stated scope.

## Reproduction

The exact invocation was:

```text
python -u /workspace/scratch/9db1b532943d/alternate-method/object-compare/run_comparison.py
```

`run_comparison.py.txt` preserves that driver, and
`CompareModuleData.lean.txt` preserves the diagnostic with its valid `module`
header. The Lean command, binary hash, reader hash, timing and exit code are
in `results.json`; its direct output and per-part results are in
`constant-comparison.log` and `constant-comparison.json`. The diagnostic
imports only `Lean` and reads the existing module files as data. It does not
import or elaborate the project proofs.
