# Final source-release rebuild

**Passed** at `2026-11-24T06:00:29.350257+00:00` with driver exit **0**. The final
release contains **131 source modules** and **130 proof-module owners**.
All **144 input hashes** matched the successful final working-tree gate and
remained unchanged throughout this staged run.

| Required stage | Exit code |
| --- | ---: |
| structure | 0 |
| unit-tests | 0 |
| build | 0 |
| statement-audit | 0 |
| audit | 0 |

The 23 unit and negative-control tests passed. The fresh all-owner audit reported:

> PROJECT AUDIT OK: 6080 declarations from 130 proof-module owners; 4550 public, 1530 private; 4579 theorems, 1414 definitions, 0 opaque declarations; every kind checked against the axiom whitelist

All **58 theorem-kind guards** and **16 definition-kind guards** passed,
as did the literal independent Challenge statement comparison. The audit ran
again in a fresh Lean process after the complete Lake build.

## Build provenance

This release was validated in two successive source-only stages in
`clean-release/akopyan_formalization_updated`:

1. The original 120-module snapshot began with **zero project build objects**.
   Every one of its 120 modules was compiled from source and passed the full
   gate; that historical evidence remains in `../clean-release-120/`.
2. Eleven additional mathematical modules, the updated Completion aggregate,
   and the updated Audit inventory were copied as **source files only**.
   None of the eleven new modules had a project object before this final run.
   Every new module has an explicit `Built` record in this log and a newly
   created regular `.olean` file. The aggregate and Audit were rebuilt.
   The other **118** project objects still have their exact earlier cold-build
   hashes.

No project `.olean`, `.ir`, `.ilean`, or native object was copied from the
working tree at either stage. Only the nine external dependency caches were
linked, with revisions fixed by the committed manifest. The final stage has
**131 regular local project `.olean` files**. Full artifact hashes, fresh-build
records, and dependency revisions are recorded in
`cold-extension-provenance.json`; source-copy provenance is in
`../final-extension/stage-preparation.json`.

This sequence checks release completeness without throwing away already
validated cold build work. It is not described as a second from-zero rebuild
of all 131 modules. Both successive source snapshots passed every required
stage, and the final source/configuration/script snapshot is identical to the
working project that passed `../final-extended/`.

## Limits

The independent Challenge specification retains its two intentional proof
placeholders, while all project proof owners were checked against only
`propext`, `Classical.choice`, and `Quot.sound`. The unconditional original
partition result remains d ≥ 36. The new d > 17 result has the explicit
`ConcreteComparison.RequiredRelativeLifting` premise, still unproved.

This is a source build, statement, and all-owner audit result. Separate reports
record independent kernel checking and the unsuccessful official Comparator
startup; this report does not assert Palomar registry acceptance.
