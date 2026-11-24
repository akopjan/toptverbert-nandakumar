# Final delivery: complete project build and owner audit

**Passed** at `2026-11-24T06:11:59.919217+00:00` with driver exit **0**.
The final source package contains **132 Lean source modules** and **131
proof-module owners**. All **145 recorded source, configuration, script, test,
and workflow inputs** remained unchanged during this verification.

| Required stage | Exit code |
| --- | ---: |
| structure | 0 |
| unit-tests | 0 |
| build | 0 |
| statement-audit | 0 |
| audit | 0 |

All 23 unit and negative-control tests passed. The full Lake build compiled
the additional `PairCollapsedLocus` proof and the updated entry modules. A
fresh Lean process then reran the complete private/public owner audit:

> PROJECT AUDIT OK: 6144 declarations from 131 proof-module owners; 4611 public, 1533 private; 4625 theorems, 1432 definitions, 0 opaque declarations; every kind checked against the axiom whitelist

The audit checks every actual declaration owned by a project proof module,
including unused private and generated declarations. It rejects genuine
project axiom records and checks the transitive axiom closure of every
constant kind against exactly `propext`, `Classical.choice`, and `Quot.sound`.
The static coverage gate independently requires the complete literal owner
inventory, both public and private imports, and Lake build coverage.

All **59 selected theorem-kind guards** and **16 definition-kind guards**
passed. This includes the actual collapsed-locus theorem
`AkopyanResearch.PairCollapsedLocus.strong_deformation_retraction` and the
previously verified geometric models. The theorem guards require genuine
private theorem records and public availability; imported theorem weakening
is not mistaken for a proof or silently accepted as a new axiom.

The literal Challenge gate preserved all seven interface definitions and both
original theorem statements, changing only the namespace and replacing the
two placeholder proofs with actual Solution theorem applications. The original
partition statement still requires **36 ≤ d**. `Challenge.lean` alone retains
the two intentional specification placeholders and is excluded from proof
owners; no project proof owner is permitted to depend on `sorryAx`.

The build reported **349 warning lines**, from the
existing development and specification. The fresh owner audit reported
**0 warnings**. These messages are preserved in the
logs, not suppressed to obtain the verification result.

## Source lineage and independent certificates

The 131-module snapshot previously passed the same gates. This final extension
adds one separately compiled mathematical module, `PairCollapsedLocus`, and
updates only the Completion aggregate, Audit inventory, and audit generator
among the previous verification inputs. The previous mathematical proof sources
are unchanged. Exact old entry and generator snapshots are retained under
`../final-extension/131-inputs/`; final source-copy provenance is in
`../final-extension/delivery-preparation.json`.

The independently accepted **seven-model certificate** describes its own
131-source snapshot. Its selected proof bodies are unchanged, and its historical
Audit and Completion source snapshots remain preserved. The new collapsed-locus
theorem is covered by this full Lean source/owner gate; it was **not** added
retroactively to that earlier independent-kernel selection. The earlier original
A/B36 and four Completion certificates likewise retain their exact scopes.

The source-release reproduction and its outcome are recorded separately in
`../clean-delivery/REPORT.md`. Historical 120- and 131-module cold build records
remain under `../clean-release-120/` and `../clean-release-final/`.

## Reproduce

With the pinned Lean 4.35.0 toolchain on PATH, run:

```sh
bash scripts/verify.sh verification/project
```

The committed manifest fixes Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0) and pins all transitive
dependencies. Verification does not run `lake update`. The exact used script,
individual stage logs/exits, and source hashes are retained here.

This result establishes that the complete final source project builds and
passes the owner and statement audits. It does not establish Palomar registry
acceptance. The new d > 17 theorem still has the explicit, unproved
`ConcreteComparison.RequiredRelativeLifting` premise; no missing global
comparison theorem is replaced by a new axiom or silently omitted hypothesis.
