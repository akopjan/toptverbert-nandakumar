# Verification evidence for the dimension-eighteen release

This directory contains current evidence and earlier development records.
The current publication interface is **A and B18**:
`AkopyanSixfold.tverberg_counterexample` and
`AkopyanSixfold.convex_partition_counterexample_gt_17`, read from
`PalomarSolution`. The additional closed construction theorem is
`AkopyanSixfold.almostSix_ninety`.

A historical successful check of A/B36 is not a certificate of B18.
A failed, interrupted, or running process is not counted as successful.
The table below identifies the evidence relevant to this release.

## Current evidence

| Directory | Scope and status source |
| --- | --- |
| `d18-final-retry/` | Successful full build, 37 infrastructure tests, literal independent Challenge statements, all-owner axiom audit; `results.json` |
| `d18-final/` | First integrated attempt; all proof modules built, but the larger audit command exceeded its former heartbeat budget; retained as failed evidence |
| `d18-clean-build/` | Source-only preparation of a fresh checkout, zero starting project objects, first build log, and source-only finalization without copying compiled objects |
| `d18-clean-final/` | Successful final verification in that independent checkout; all 472 input hashes match the main gate |
| `d18-archive-build/` | A separate immutable final proof snapshot extracted from ZIP, zero starting project objects, successful complete compilation, and the recorded initial statement-output path refusal |
| `d18-archive-final/` | PASS: all six stages in the extracted checkout after correcting the output directory; no proof-source changes and the same 472 hashes |
| `d18-archive-object-comparison/` | PASS: 1,314 objects of the immutable archive-source build compared with the kernel-bound main objects; all stored declarations, types, bodies and imports agree |
| `d18-kernels/` | PASS: selected actual proof bodies, transitive dependencies, axiom whitelist, Lean checker, NanoDa and bundled con-ron; `results.json` |
| `d18-approved-con-ron/` | PASS: same export accepted by the exact currently approved con-ron binary; supplemental component replay, not registry acceptance |
| `d18-clean-final/object-comparison/` | PASS: direct comparison of every stored declaration/type/proof body in modules whose binary metadata differs |
| `d18-comparator/` | Genuine local sandboxed Comparator attempt: exit 1 at `bwrap: Failed to mount tmpfs: No such file or directory`; no sandbox bypass |
| `d18-compiled-interface/` | Successful independent inspection of separately compiled Challenge and proof modules; nine types and seven definition bodies are identical |
| `d18-portable-interface/` | PASS: a new portable reproducer obtains the same interface digest using the pinned `lake` on `PATH`, without changing historical evidence or rebuilding the project |
| `d18-dependencies/` | Exact pinned revisions and clean tracked sources of all nine Git dependencies |
| `d18-extension-2026-11-24/` | Targeted theorem audits, mathematical reviews, independent semantic checks, and work-interval record |
| `d18-portable-semantic/` | PASS: portable replay of the exact Mathlib-only semantic reference and five proof checks; unchanged source/object/tool hashes, `results.json` |
| `d18-publication/` | Static submission checks, official source snapshots, metadata draft, attribution review, and optional official workflow validation |
| `original-specification/` | Original B36 Challenge preserved as text, including its recorded hash |

The final working-project audit checks **16,765 declarations** from
**438 proof-module owners**, comprising 14,244 public and 2,521 private
declarations. It includes 12,586 theorems and 3,975 definitions; constructors,
recursors and other declaration kinds are checked as well. No project
axiom or forbidden transitive axiom dependency is allowed. The only
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Ninety key theorems and twenty-eight key definitions have additional
kind and public-visibility guards. All 472 recorded inputs were unchanged
across the successful integrated gate.

The proof project has 439 Lean source modules including `Challenge`;
438 are proof/audit owners. Diagnostic Lean sources under `verification`
are not counted as proof owners. The independent Challenge deliberately
contains two statement placeholders. Its code is not imported by the
proof closure; the proof modules contain no admissions.

## Reproduction

Use the exact `lean-toolchain` and `lake-manifest.json` supplied in the
release. The recorded runs used Linux; the commands below assume a POSIX
environment with Bash, Python 3.11 or newer, and the pinned Lean/Lake on
`PATH`. From the repository root:

```sh
lake exe cache get
SKIP_MATHLIB_CACHE=1 bash scripts/verify.sh verification/reproduction
```

This runs structure checks, provenance checks, infrastructure tests,
`lake build`, a literal Challenge audit, and a fresh all-owner audit.
It does not run `lake update`. The cache command fetches pinned dependency
objects; the clean-build evidence concerns recompilation of all project
sources, not recompilation of the entire Lean/Mathlib toolchain.

To reproduce the separate compiled-interface comparison against those
already-built modules, choose a new output directory:

```sh
python3 verification/d18-release/reproduce_compiled_interfaces.py \
  --output-dir verification/reproduction-compiled-interface
```

This uses the exact preserved serializer, checks the pinned toolchain and
records source/object/tool hashes. It refuses an existing output directory
and leaves the historical interface results untouched. The saved older
`compare_compiled_interfaces.py.txt` is a workspace-specific historical
runner, not the portable reproduction entry point.

For the exported proof components, use a new output path:

```sh
python3 scripts/verify-selected-kernels.py Audit \
  AkopyanSixfold.tverberg_counterexample \
  AkopyanSixfold.almostSix_ninety \
  AkopyanSixfold.convex_partition_counterexample_gt_17 \
  AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting \
  --proof-module Solution \
  --proof-module AkopyanResearch.Completion.DimensionEighteen \
  --proof-module AkopyanResearch.Completion.ConcreteComparisonLifting \
  --definition AkopyanSixfold.IsAlmostSixEmbedding \
  --definition AkopyanSixfold.IsSixPartition \
  --output-dir verification/reproduction-kernels \
  --export-file /absolute/path/to/a/new/d18-proof.ndjson
```

The large generated NDJSON export is deliberately omitted from the source
archive. Its exact size, SHA-256, declaration-body checks, commands, tool
hashes, and exit codes are retained in the evidence. The script refuses
to overwrite an existing export. All three bundled checker tools are
required; NanoDa rejects unpermitted axioms as hard errors.

### Stored-object comparison after independent builds

For newly built checkouts, first run `scripts/verify.sh` above independently
in each project and run `scripts/verify-selected-kernels.py` above in the
main project. Keep each successful report in its own new directory. Then
pass those three reports explicitly to the configurable adapter:

```sh
python3 verification/d18-release/compare_rebuilt_objects.py \
  --main-project /path/to/main-project \
  --clean-project /path/to/independent-clean-project \
  --main-gate verification/reproduction/results.json \
  --clean-gate /path/to/independent-clean-project/verification/reproduction/results.json \
  --kernel-report verification/reproduction-kernels/results.json \
  --output-dir verification/reproduction-object-comparison
```

Both gate reports must certify all six stages, identical source-input
hashes and the same proof-owner inventory. Both actual trees must match
those source hashes. Every main object must match the supplied successful
kernel report; replacing that report with an unrelated result does not
bypass the hash checks. Relative report and output paths are resolved inside
the main project. The output must be a new directory below its
`verification/` directory; an existing path is refused.

The earlier adapter is retained for a different, release-specific replay:

```sh
python3 verification/d18-release/reproduce_object_comparison.py \
  --main-project /path/to/main-project \
  --clean-project /path/to/independent-clean-project \
  --output-dir verification/reproduction-object-comparison
```

It reads the archived release gate and kernel reports at their fixed
relative locations. It is relocatable, but its main objects must retain
the historical kernel-input hashes. An arbitrary fresh rebuild can change
object metadata and therefore requires the configurable adapter and its
own reports, rather than this historical mode.

Both adapters require the existing `.olean`, `.olean.private` and
`.olean.server` files. They resolve the pinned Lean through `lake` on PATH
and run the same unchanged, hash-pinned module-data inspector. Neither
adapter performs a build, copies objects between checkouts or exports
proofs. They retain the archived inspector and its provenance.

Byte-identical object triples need no further comparison. For every
differing triple, the inspector compares stored `ConstantInfo` fields,
types, proof/definition bodies, recursor right-hand sides, names, module
flags and imports using strict expression equality. Opaque environment
extension payloads remain outside that comparison. Source, object, tool,
adapter, diagnostic-input and historical-evidence hashes are checked before
and after. Successful release-specific and explicitly configured replays
are recorded separately in
[d18-portable-object-comparison/results.json](d18-portable-object-comparison/results.json)
and [d18-configurable-object-comparison/results.json](d18-configurable-object-comparison/results.json).
The original workspace-specific runner under
`d18-clean-final/object-comparison/` remains unchanged as historical evidence.

For a local sandboxed comparison on a host where `bwrap` works:

```sh
bash scripts/verify-comparator.sh
```

This is a local component check. It is not the complete Palomar registry
workflow: the registry additionally authenticates source and metadata,
controls its runtime, and applies its current external-checker policy.
The separately compiled structural diagnostic also does not replace
that workflow. The manual official preflight configuration and its exact
pinned contract are described in `d18-publication/OPTIONAL_PREFLIGHT.md`.

### Portable replay of the semantic-scope diagnostic

After building the pinned project, run the new adapter with an unused
directory under `verification/`:

```sh
python3 verification/d18-release/reproduce_semantic_scope.py \
  --output-dir verification/reproduction-semantic
```

The adapter locates `lake` on `PATH` and asks Lake for the selected Lean
toolchain and dependency search paths. It checks the release toolchain
version and requires the already-built project objects. It neither
updates dependencies nor rebuilds the project.

It copies the two preserved diagnostic sources byte for byte. First it
compiles `SemanticReference.lean`, importing only Mathlib with the
project-object directory excluded from its search path. Then it compiles
the original `SemanticScopeCheck.lean` against that fresh reference and
the actual `Solution` and `DimensionEighteen` modules. The five checks cover
the original theorem A, its direct height-extension bridge, the height
extension itself, the final B18 theorem, and theorem A with the actual
Euclidean target. The concrete disjoint-vertex and matching witnesses are
also preserved. Each printed axiom set must be contained in the standard
three axioms.

The output records commands, versions, logs, exact copied sources, generated
artifact hashes, and before/after hashes for the frozen release inputs,
the recorded proof import closure's objects, the adapter, and its tools.
It refuses to reuse an output directory or write outside `verification/`.
The validated run is in `d18-portable-semantic/`. This is the same semantic
diagnostic as the archived run, not an external proof-kernel replay or an
official Comparator check.

The historical file
`d18-extension-2026-11-24/SEMANTIC_SCOPE_RUNNER.py.txt` retains the exact
original invocation, including its original absolute workspace paths.
It is evidence of that invocation, not the portable entry point. It and
the original sources, logs, and results have not been edited.

## Source and object integrity

The integrated checker hashes source files, scripts, tests, configuration,
workflow files, provenance manifests, licences and original-specification
records before and after the run. No proof inputs may change unnoticed.

The clean checkout began with no project build objects. Its first phase
compiled the stable source closure. Final source changes were then copied
as source only; all already produced object bytes were preserved. Lake
rebuilt affected modules and checked the final source state. Dependency
caches were reused at the nine recorded pins. This is one cumulative
clean-source build, not a claim that two complete independent clean builds
were performed.

The imported topology files have 13 source manifests. The provenance
checker verifies all 164 registered modules, their upstream locations,
ported-file hashes, inventory coverage and retained licence texts. It
makes no authorship or licence decision for the user's original code.

## Historical records

The directories `final-delivery`, `clean-delivery`, `compiled-interface`,
`statement-audit-retry`, and earlier selected-kernel runs describe the
previous A/B36 interface and conditional stages of the extension.
Their logs are retained for traceability. They are not substituted for
the current B18 evidence.

`history-before-d18/` preserves the preceding README, changes and status
that correctly described the formerly open relative lifting step.
Their old statements of incompleteness are historical. The current
mathematical status is the one in `../FORMALIZATION_STATUS.md`.
