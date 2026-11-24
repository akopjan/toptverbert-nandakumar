# Cold release rebuild: the 120-module snapshot

**Passed** at `2026-11-24T05:42:56.123891+00:00` with driver exit **0**. This is the complete
120-module source snapshot before the subsequent pair-rank/representation
additions. The final extended release is checked separately.

The staged source directory was
`clean-release/akopyan_formalization_updated`. All 133 source, configuration,
script, test and workflow hashes matched the preceding successful working-tree
gate. The stage initially contained **zero project build objects**. Only the
nine pinned external dependency caches were linked; each dependency git HEAD
was checked against the committed manifest. No project `.olean`, `.ir`,
`.ilean` or native object was copied from the working tree.

| Required stage | Exit code |
| --- | ---: |
| structure | 0 |
| unit-tests | 0 |
| build | 0 |
| statement-audit | 0 |
| audit | 0 |

Every one of the **120 source modules** has an explicit `Built` record in the
cold build log. Every expected project `.olean` was newly created as a regular
file in this stage. The build included the full original constructive chain
(`PyrDet`: 135 seconds; `Solution`: 134 seconds), every existing Completion
module, and Audit. The 23 unit and negative-control tests passed.

The fresh final audit reported:

> PROJECT AUDIT OK: 5713 declarations from 119 proof-module owners; 4226 public, 1487 private; 4296 theorems, 1333 definitions, 0 opaque declarations; every kind checked against the axiom whitelist

All 36 selected theorem-kind guards, 9 definition-kind guards, and the literal
independent Challenge statement gate passed. Only the three permitted
foundational axioms were allowed. The independent Challenge specification
retains its two intentional proof placeholders; no proof owner was allowed to
use `sorryAx` or an actual project axiom.

All 133 recorded test inputs remained unchanged throughout this cold run.
`source-before.json`, `source-after.json`, and `results.json` retain their
hashes. `cold-build-provenance.json` records the dependency revisions and the
120 newly built project-object hashes. Exact Audit and Completion entry-source
snapshots are retained as text files, because later unrelated additions may
extend their imports.

This confirms that the source release builds without preexisting project proof
objects. It is distinct from the selected independent-kernel certificates and
from the unsuccessful official Comparator sandbox attempt. In particular it
does not prove the remaining `RequiredRelativeLifting` premise of the d > 17
conditional theorem.
