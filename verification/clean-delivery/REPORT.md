# Final delivery: staged source rebuild

**Passed** at `2026-11-24T06:13:11.488371+00:00` with driver exit **0**.
The final staged project contains **132 source modules** and **131 proof-module
owners**. Its **145 source, configuration, script, test, and workflow hashes**
match the accepted working `final-delivery` snapshot exactly and remained
unchanged throughout this run.

| Required stage | Exit code |
| --- | ---: |
| structure | 0 |
| unit-tests | 0 |
| build | 0 |
| statement-audit | 0 |
| audit | 0 |

The 23 unit and negative-control tests passed. The final fresh audit reported:

> PROJECT AUDIT OK: 6144 declarations from 131 proof-module owners; 4611 public, 1533 private; 4625 theorems, 1432 definitions, 0 opaque declarations; every kind checked against the axiom whitelist

All 59 selected theorem-kind guards and 16 definition-kind guards passed,
including the new actual collapsed-locus strong deformation. The independent
literal Challenge statement gate also passed, preserving the original A/B36
interface. The audit was rerun in a fresh Lean process after the complete build.

## Source-only build provenance

The staged directory was `clean-release/akopyan_formalization_updated`.
The final project was verified in three successive source snapshots:

1. **120 modules** were built from a stage with zero project proof objects.
   Every module had an explicit fresh `Built` record; the whole gate passed.
2. **11 new mathematical modules** were copied as sources only and compiled
   from scratch; the updated 131-module project passed the whole gate.
3. **One new module**, `PairCollapsedLocus`, was copied as source only. It had
   no staged project object before this run, has an explicit fresh `Built`
   record now, and is included in the successful 132-module owner audit.

At each extension the Completion aggregate and Audit were rebuilt. The other
**129 objects** from the preceding 131-module snapshot retain their exact
hashes. All **132 final project `.olean` files** are regular local files. No
project `.olean`, `.ir`, `.ilean`, or native object was copied from the working
tree at any stage. Only the nine pinned external dependency caches were linked.

`cold-delivery-provenance.json` records the full final artifact hashes,
dependency revisions, and links to the preserved 120- and 131-module provenance.
`../final-extension/delivery-preparation.json` records the four changed/copied
source and inventory files and confirms the new module object was absent.
This is a cumulative **120 + 11 + 1** source rebuild; it is not misreported as
three independent from-zero rebuilds of every final module.

## Scope

This confirms source-package completeness, successful compilation, and the
full project-owner axiom/statement audits for the final 132-module revision.
Only the independent Challenge specification has its two intentional proof
placeholders. All project proof owners were checked against exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The original unconditional partition theorem retains d ≥ 36. The new d > 17
result is conditional on `ConcreteComparison.RequiredRelativeLifting`, still
unproved. The last collapsed-locus theorem is checked by this Lean build and
owner audit, and is not retroactively included in the historical seven-target
independent model certificate. The official Comparator startup failure and
all independent kernel results have separate reports; this build is not a
claim of Palomar registry acceptance.
