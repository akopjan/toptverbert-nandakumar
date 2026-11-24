# Full project verification

**Passed** at `2026-11-24T05:19:27.809095+00:00` with driver exit **0**. This run verifies
the complete configured source project, including all Completion additions.
It does not assert that the remaining relative lifting hypothesis has been
proved.

## Required gates

| Gate | Exit code |
| --- | ---: |
| structure | 0 |
| unit-tests | 0 |
| build | 0 |
| statement-audit | 0 |
| audit | 0 |

The structural checker found **120 Lean source modules**,
resolved all local imports without cycles, and checked that every proof module
has both public and private imports in Audit, exactly one owner-list entry,
and coverage by the Lake build globs. It checked the two independent comparator
signatures and all seven interface definitions against Solution.

All **23 unit and negative-control tests** passed. The controls include removal
of an audit owner, private import, public import, or build glob, and deliberate
interface-signature/definition mismatches.

The full `lake build` completed successfully. Its final summary was:
`Build completed successfully (9171 jobs).`.
No mathematical source was changed to suppress errors or warnings.

The literal independent statement check generated a separate namespace directly
from Challenge and filled its two proofs with the actual Solution theorems.
The reverse transformation recovered the original bytes exactly; Lean accepted
both statements. The bound in that independent specification is **36 ≤ d**.
See `statements/results.json` for the exact source and generator hashes.

## Complete declaration audit

The fresh `lake env lean -j 1 Audit.lean` run reported:

> PROJECT AUDIT OK: 5713 declarations from 119 proof-module owners; 4226 public, 1487 private; 4296 theorems, 1333 definitions, 0 opaque declarations; every kind checked against the axiom whitelist

All project-owned declarations were inspected in Lean's private environment,
including unused private and generated declarations. Actual axiom declarations
were rejected, and the transitive dependencies of every declaration kind were
restricted to `propext`, `Classical.choice`, and `Quot.sound`.

In addition, **36 selected mathematical milestones** had
to be genuine public theorem declarations with private proof information, and
**9 selected constructions** had to be genuine public
definitions. These include the original A/B36 theorems, the explicit conditional
B18 reductions, the concrete comparison and chosen section, the join/pair
constructions, the linking nine-sphere retract, and the arrangement-rank bounds.

The independent Challenge module is the single excluded proof owner: its two
`sorry` placeholders are the problem specification. They are not imported by
the solution proof closure or by Audit. No proof module contained `sorry`,
`admit`, a new `axiom`, `constant`, `opaque`, `unsafe`, `native_decide`, or
`run_tac` tokens under the source check.

## Snapshot and warnings

All **133 recorded source, script, test, workflow, and
configuration inputs** remained byte-identical throughout the run. Their
hashes and the exact source inventory are in `source-before.json`,
`source-after.json`, and `results.json`. `verifier-used.sh` is the exact script
used. Dependency revisions remain pinned in the committed manifest; the
verification did not run `lake update`.

The build log contains **349 warning lines**, mainly
inherited deprecations and linter suggestions, including the two expected
Challenge-placeholder warnings. The fresh Audit run produced **0 warnings**.
A successful build is reported without claiming a warning-free source tree.

## Scope and corrected audit integration

This project-wide gate is distinct from the independent proof-export checker
runs and from Palomar's sandboxed Comparator. It confirms kernel compilation,
exact original statements, complete owner coverage, and the axiom whitelist.
The theorem for d > 17 still has the explicit argument
`ConcreteComparison.RequiredRelativeLifting`; a proof of that proposition is
not supplied by this gate.

The preceding attempt in `../final-project` passed the complete private axiom
scan but failed a public-view key guard because the new modules were imported
only with `import all`. Lean 4.35 requires separate `public import M` and
`import all M` directives to inspect both views. The generator and static
coverage checks were corrected accordingly; all mathematical proof sources
remained unchanged. This report relies on the completed retry, not on the
failed integration attempt.
