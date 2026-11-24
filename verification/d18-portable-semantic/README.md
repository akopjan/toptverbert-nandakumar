# Portable semantic-scope replay

**PASS — 24 November 2026, 09:49:01 UTC.**

The adapter in
[reproduce_semantic_scope.py](../d18-release/reproduce_semantic_scope.py)
was validated once against the already-built pinned release. The run used:

    source ../tools-runtime/environment.sh
    python3 verification/d18-release/reproduce_semantic_scope.py \
      --output-dir verification/d18-portable-semantic

The first command selected the installed toolchain in this workspace.
A normal reproduction uses the pinned Lean installation through Lake on
PATH; the adapter itself contains no workspace-specific toolchain paths.
Use a NEW output directory for another run.

## Preserved diagnostic

[SemanticReference.lean](SemanticReference.lean) and
[SemanticScopeCheck.lean](SemanticScopeCheck.lean) are byte-for-byte copies
of the archived diagnostic sources. Their hashes are checked against
fixed values before compilation and again afterward.

The Mathlib-only reference compiled first, with the project-object path
excluded. The original proof checker then compiled against that fresh
reference and the built Solution and DimensionEighteen modules.
All five checked declarations passed, and their printed transitive axiom
sets contain only propext, Classical.choice, and Quot.sound:

- Original theorem A.
- Direct height-extension-to-A bridge.
- Original height-extension theorem.
- Final theorem B18.
- Theorem A with its target transported to the actual Euclidean space.

The original concrete disjoint-vertex and matching witnesses are included.

## Evidence and scope

[results.json](results.json) records all commands, exit codes, durations,
tool paths and versions, diagnostic hashes, axiom results, and generated
artifact hashes. The input snapshots bind the 472 unchanged release inputs,
the 1,254 objects in the recorded 418-module proof import closure, the
historical diagnostic evidence, and the adapter. Source, object, and tool
hashes agree before and after compilation.

The reference compilation took 4.864 seconds and the proof checker 4.162
seconds. This replay does not rebuild the project or repeat an exported-body
kernel check. Its source/object correspondence relies on the separately
recorded build and integrity evidence. It is not the official Palomar
Comparator.

The historical SEMANTIC_SCOPE_RUNNER.py.txt and all original diagnostic
sources, logs, and results remain unchanged. Their absolute workspace
paths record the original invocation.
