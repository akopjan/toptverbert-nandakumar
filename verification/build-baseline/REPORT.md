# First actual build of the attached project

Lean 4.35.0 / Mathlib v4.35.0 were restored from verified local caches using a
committed manifest with exact git revisions. All nine dependency HEADs matched
the manifest. The attached project contained 84 Lean source modules.

The first `lake build` exited **1**. There were exactly two failed local targets:

- `AkopyanResearch`: two separately compiled modules exported the same public
  name `AkopyanResearch.homToCont`.
- `Audit`: the public-interface lookup treated a proved imported theorem as
  missing because Lean 4.35 weakens exported theorem interfaces to axiom records.

The mathematical source modules, including Construction.Assembly,
RequestProject.Solution, and the full original Solution, compiled. Both final
`#print axioms` commands reported only `propext`, `Classical.choice`, and
`Quot.sound`. This first run did not pass the complete project gate.

The original static check and 19 existing unit tests passed. The build emitted
343 warnings (including the two specification placeholders,
deprecations, and lint warnings); absence of warnings is not claimed.

The duplicate-name failure was recorded before repair. Subsequently the two
helper identifiers were renamed locally, without changing mathematical bodies;
these two sources therefore differ from the initial snapshot. Their exact
before/after hashes are in `namespace-collision-repair.json`. New Completion
modules were added separately after the initial inventory. This report is a
baseline diagnostic, not a certification of those later sources.

Exact diagnostics, the initial 84 source hashes, dependency revisions, successful
module names, and exit status are retained in `build.log`, `inputs.json`, and
`results.json`. A later full build and all-owner audit are required after the
infrastructure repairs and final Completion integration.
