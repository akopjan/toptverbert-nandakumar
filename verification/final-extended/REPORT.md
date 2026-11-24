# Final extended project verification

**Passed** at `2026-11-24T05:58:46.308683+00:00` with driver exit **0**.
The final project has **131 Lean source modules**, of which
**130 are proof-module owners**. All **144**
recorded source, configuration, script, test and workflow inputs remained
byte-for-byte unchanged during the verification.

| Required stage | Exit code |
| --- | ---: |
| structure | 0 |
| unit-tests | 0 |
| build | 0 |
| statement-audit | 0 |
| audit | 0 |

The 23 unit and negative-control tests passed. The full `lake build` succeeded;
a subsequent fresh `lake env lean -j 1 Audit.lean` ran the complete audit again.
The latter reported:

> PROJECT AUDIT OK: 6080 declarations from 130 proof-module owners; 4550 public, 1530 private; 4579 theorems, 1414 definitions, 0 opaque declarations; every kind checked against the axiom whitelist

The audit obtains every constant's owning module in the imported private
proof environment. It rejects actual project axiom declarations, including
unused private or generated declarations, and checks the transitive axiom
closure of **every declaration kind** against exactly `propext`,
`Classical.choice`, and `Quot.sound`. It additionally verifies the genuine
kernel declaration kinds and public availability of **58
selected theorems** and **16 selected definitions**.
Both public and `import all` imports are required for every owner; the static
gate independently checks that the literal owner inventory and Lake's build
coverage match all project source files.

`Challenge.lean` is the independent specification, excluded from proof owners.
Its two intentional theorem placeholders remain in that specification only.
The literal statement gate reconstructs its seven definitions and two theorem
statements exactly, with only the namespace and proof bodies replaced, then
checks them against the actual Solution proofs. In particular the original
partition theorem still has the premise **36 ≤ d**.

The build log contains 349 warning lines, inherited
deprecation/lint messages and the two specification placeholders. The fresh
audit has **0 warnings**. Successful compilation and
owner checks do not depend on hiding or suppressing those messages.

## Final extension and reproducibility

The final source adds eleven mathematical modules to the previously verified
120-module snapshot. Among the 133 earlier test inputs, only the Completion
aggregate, Audit inventory, and its generator changed. Every earlier
mathematical proof source remained unchanged. The exact source lineage and
stage preparation are recorded in `../final-extension/stage-preparation.json`.
The historical cold 120-module run remains separately preserved under
`../clean-release-120/`.

Run from a pinned checkout with Lean 4.35.0 on PATH:

```sh
bash scripts/verify.sh verification/project
```

`verifier-used.sh`, `source-before.json`, `source-after.json`, individual exit
files and logs, and `results.json` retain the actual commands and input hashes.
The manifest fixes Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0); verification does not run
`lake update`.

## Scope

This is a complete source build and project-owner axiom audit, including the
literal independent statement gate. It is separate from the independently
executed kernel certificates and from the official Comparator attempt. It is
not registry acceptance. The new d > 17 theorem is conditional on the explicit
`ConcreteComparison.RequiredRelativeLifting` premise; this verification does
not supply a proof of that premise.
