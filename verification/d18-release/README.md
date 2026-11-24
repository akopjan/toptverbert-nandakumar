# Release assembly and supplemental reproduction

The complete source ZIP is the authoritative project delivery. It contains
the proof sources, pinned build configuration, independent Challenge,
provenance records, documentation and verification evidence. It omits the
toolchain, dependency caches, project object files and the approximately
701 MB proof export. Their versions, commands and hashes are recorded.

The separate patch applies to the exact supplied reviewed archive. It covers
source code, configuration, scripts, tests, documentation and the original
Challenge snapshot needed by the structural check. It excludes other
generated verification evidence; that evidence is supplied in the ZIP.
The mathematical PDF is included in this directory and also delivered
separately, with its source and renderer under `docs/`. Its binary copy is
outside the text patch's scope.

## Release checks

`release_diff.py` generates the source patch. `validate_release_delivery.py`
applies it to a fresh copy of the input tree using `git apply --check` and
`git apply`, then compares every included file and executable flag against
the final source. Its report is `PATCH_VALIDATION.json` when assembly is
complete.

`release_package.py --verified-d18` permits the final release label only
when the recorded main gate, clean-source gate, independent interface
comparison and three-component proof check all succeeded. It checks their
input hashes against the actual source/object files and their exact module
inventory. It then writes every payload hash to `RELEASE_INVENTORY.json`
and `SHA256SUMS`. The archive validator independently checks ZIP integrity,
paths, regular-file modes, the complete checksum inventory, the exact final
source bytes and the bound verification reports. Its final report is
delivered alongside the archive rather than inserted into the archive it
hashes.

These are release-assembly tools, not substitutes for the actual checks.
The release guard intentionally rejects changed proof inputs or objects;
an independently rebuilt project must be validated with its own accurately
recorded evidence. Ordinary project verification is documented in
`verification/README.md` and does not require the original workspace.

## Portable supplemental diagnostics

The supplemental adapters use the pinned toolchain through `lake`
on `PATH`, require already-built objects and write to a new directory under
`verification/`. They preserve the archived diagnostic sources and do not
rebuild or export the project. Their successful release runs are separate:

| Adapter | Actual new evidence |
| --- | --- |
| `reproduce_compiled_interfaces.py` | `verification/d18-portable-interface/` |
| `reproduce_semantic_scope.py` | `verification/d18-portable-semantic/` |
| `reproduce_object_comparison.py` | `verification/d18-portable-object-comparison/` |
| `compare_rebuilt_objects.py` | `verification/d18-configurable-object-comparison/` |

The stored-object comparison has two modes. `reproduce_object_comparison.py`
is relocatable but deliberately binds the main objects to the archived
release kernel report. For independently rebuilt trees,
`compare_rebuilt_objects.py` instead requires explicit `--main-gate`,
`--clean-gate` and `--kernel-report` paths, produced by the existing
`scripts/verify.sh` and `scripts/verify-selected-kernels.py` commands.
It preserves all source, object, equality and unchanged-input guards and
uses the same hash-pinned inspector. Its recorded validation run selected
the existing release reports explicitly; it did not repeat the builds or
kernel checks.

Exact commands and scope limits are in `verification/README.md` and the
individual reports. The older workspace-specific runners remain historical
invocation evidence. `ADAPTER_REVIEW.md` records the code review and the
current hashes; it does not claim a new Lean execution.

## Companion and publication preparation

`PDF_BUILD.json`, `PDF_QA.json` and `PDF_REVIEW.md` bind the fifteen-page
companion to its source and renderer, record inspection of every rendered
page and confirm a byte-identical second rendering. They certify document
preparation, not a separate mathematical peer review.

The publication handoff is in
`verification/d18-publication/SUBMISSION_HANDOFF.md`. The genuine local
Comparator attempt failed during sandbox setup, before comparison. The
registry workflow and submission have not been performed. Confirmed human
authors, responsible maintainers, project licence, public repository and
immutable commit still have to be supplied before submission.
