# Palomar readiness: A and the full bound `17 < d`

Prepared on 2026-11-24 from the working tree. The unconditional
`DimensionEighteen` theorem module and all proof modules have compiled in
Lean. The complete build, statement checks and declaration-owner audit
passed at `2026-11-24T08:56:01Z`; the evidence is in
`verification/d18-final-retry/`. The independent compiled-interface
comparison passed at `08:59:09 UTC`; the separate cumulative source rebuild
passed at `09:01:10 UTC`. The selected final proofs and their dependencies
passed Lean checker, NanoDa and con-ron at `09:15:21 UTC`; the approved
newer con-ron also accepted the same export at `09:18:19 UTC`.
The new local Comparator attempt is **blocked at sandbox setup**; it has
not accepted or rejected the proof. No Palomar registration has been performed.

## Publication interface

The specification prepared for submission is `Challenge.lean`. The proof entry point is
`PalomarSolution.lean`; it imports the actual proof through
`AkopyanResearch.Completion.DimensionEighteen`.

| Comparator declaration | Actual declaration owner | Statement |
|---|---|---|
| `AkopyanSixfold.tverberg_counterexample` | `Solution` | Almost-six embedding of the 35-dimensional simplex into `R^6`. |
| `AkopyanSixfold.convex_partition_counterexample_gt_17` | `AkopyanResearch.Completion.DimensionEighteen` | Convex six-partition counterexample for every natural dimension `d` with `17 < d`. |

The second declaration has no extra lifting, homological or connectivity
premise. Its concrete relative lifting theorem is now proved, and its
unconditional declaration has passed targeted Lean compilation. The same
module proves `AkopyanSixfold.almostSix_ninety`, the supporting almost-six
embedding of the 89-dimensional simplex into `R^16`.
Its bodies, measure, topology and quantifiers were reviewed in
[`STATEMENT_AND_LIFTING_REVIEW.md`](../d18-extension-2026-11-24/STATEMENT_AND_LIFTING_REVIEW.md).
The separate
[`SEMANTIC_SCOPE_REVIEW.md`](../d18-extension-2026-11-24/SEMANTIC_SCOPE_REVIEW.md)
checks the theorem against a Mathlib-only reference compiled before importing
the proof project; it also checks dimensions, standard instances and
nonvacuity. These semantic checks passed and do not claim external peer review.
It asserts an absolutely continuous probability measure and `d - 1`
continuous body functionals. The equal-measure condition is one sixth of the
unit ball's measure; the statement does not impose support inside that ball.

`Solution.lean` remains byte-for-byte unchanged, with SHA-256
`41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23`.
The former B36 specification is retained as
`verification/original-specification/Challenge36.lean.txt`.
The old B36 declaration remains available but is no longer the second
Comparator target. Earlier B36 certificates do not certify the new B18 claim.

## Observed static checks

The machine-readable evidence is [`STATIC_PREFLIGHT.json`](STATIC_PREFLIGHT.json),
which records every scanned Lean source hash and the configuration hashes.
Its current snapshot is dated `2026-11-24T09:23:21Z`; rerun
`python3 verification/d18-publication/check_readiness.py` after final integration
to refresh it. The helper uses Python 3.11 or later and PyYAML, and performs no
Lean build or proof checking.

| Check | Observation |
|---|---|
| Entire submitted Lean source tree | 473 regular `.lean` files, excluding only `.git` and `.lake`; diagnostics are included. |
| Physical line cap | All scanned files are at most 10,000 lines. The maximum is `Solution.lean`, 9,336 lines. |
| Module headers | All 473 pass the lexical check. The initially missing header in `verification/d18-extension-2026-11-24/AnalyticGeometricAudit.lean` was corrected before the earlier rescan. |
| Lean symlinks / compiled artifacts / LFS | None detected in the submitted tree outside the excluded build directories. No `.gitmodules` is present. |
| Challenge size | 89 physical lines, 3,362 bytes: within both the hard limits and recommended limits. |
| Specification independence | Challenge imports only `Mathlib`; no local proof dependency occurs in its import closure. The local proof closure does not import Challenge. |
| Exact source signatures | Both Challenge signatures match their actual declaration owners; all seven interface definitions match the original Solution. |
| Publication imports | The `PalomarSolution` source closure contains 418 local modules; no missing local import was found. This is a source-graph result, not a compiled-closure certificate. |
| Lexical proof admissions | Across 438 proof source files, zero `sorry`, `admit` or `axiom` tokens outside comments and strings. Challenge has exactly its two intentional statement holes. |
| Comparator configuration | Correct A+B18 declarations, `Challenge` / `PalomarSolution`, and only the permitted standard axioms. No submitted `external_kernels` or other extra keys. |

The module-header and line-limit rules cover unused and verification files,
not only Lake targets. Challenge's hard limits are 1,000 lines and 100 KiB;
Palomar recommends at most 300 lines and 32 KiB. The official verifier also
checks headers with Lean's parser. Our lexical preflight does not replace
that parser check. See the official
[source and Challenge requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#21-lean-and-lake-files)
and [submission guide](https://palomar-registry.org/how-to-submit).

## Toolchain, dependencies and CI

The project uses `leanprover/lean4:v4.35.0`, exactly matching the toolchain in
the resolved Mathlib checkout. Mathlib is the canonical public repository at
commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All nine manifest packages
are credential-free public GitHub Git dependencies with full 40-character
commit revisions. The root contains one declarative `lakefile.toml`, and
`PalomarSolution` is a configured default target.

The current official
[`toolchains.json`](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json)
sets the minimum to `v4.35.0-rc2`. The selected stable 4.35.0 release satisfies
that minimum. Actual canonical ancestry, complete dependency content and
authenticated retrieval are still matters for the official verifier.

The configured GitHub workflow uses Ubuntu 22.04, Python 3.12 and read-only
repository permissions. Checkout, Python setup and lean-action each use a
full commit SHA. The lean-action input names were checked against the action
file at the exact configured revision. The workflow checks the committed
pins, runs the project verification script, checks for pin drift, installs
`bubblewrap`, then runs the bundled Comparator and independent kernels.
No execution of that GitHub workflow has been observed for the final release.

`scripts/verify-comparator.sh` preserves the submitted `comparator.json` and
registers bundled kernels only in a temporary configuration. Its commands
were left unchanged. Comments and the CI step name now describe this as a
local bundled-toolchain gate.

This local gate is not the complete registry pipeline. The current official
[pipeline README](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/README.md)
requires successful Lean and NanoDa checking, then runs con-ron separately
under a documented replay policy. The registry can authenticate an approved
newer con-ron using
[`checker-revisions.json`](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/checker-revisions.json);
its current documented update uses con-ron from Lean 4.36.0-rc1 for supported
Lean 4.35 releases. A recognized support or capacity decline is reported as
inconclusive, not as verification. An actual rejection still blocks acceptance.
The final report must identify which checkers actually accepted which export.

An additional manual-only workflow, `.github/workflows/palomar-preflight.yml`,
calls the official reusable verifier at authenticated commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, using the runtime repository and
source SHA. It requires an explicit truthful authorization relationship and
does not run automatically. See [`OPTIONAL_PREFLIGHT.md`](OPTIONAL_PREFLIGHT.md)
for its exact input contract and reference evidence. Its local configuration
checks passed; no remote run or registry submission has been initiated.

## Release verification

| Gate | Status for the new final A+B18 release |
|---|---|
| Targeted Lean compilation of `DimensionEighteen` and all proof modules | **Passed** |
| Final integrated build of all configured targets, including Audit | **Passed**, `2026-11-24T08:56:01Z` |
| Complete project declaration-owner audit, including private declarations and definitions | **Passed**, 16,765 declarations from 438 owners |
| Literal Challenge statement check and regression suite | **Passed**, all 37 tests |
| Separate cumulative clean source rebuild and full gate | **Passed**, `2026-11-24T09:01:10Z`, same 472 verification inputs and same owner audit |
| Main/clean compiled-object declaration comparison | **Passed**, all stored declarations agree across 438 owners; binary metadata differences are recorded separately |
| Separately compiled Challenge/proof interface comparison | **Passed**, `2026-11-24T08:59:09Z`, 9 types and 7 definition bodies identical |
| Export and replay the selected final theorem dependencies | **Passed**, Lean checker, NanoDa and bundled con-ron, all exit 0 |
| Supplemental replay with Palomar's approved newer con-ron | **Passed**, same export and authenticated checker; not the registry workflow |
| Sandboxed Comparator for the new A+B18 configuration | **Blocked locally**: `bwrap` failed to mount tmpfs before comparison; exit 1 |
| Public-commit GitHub CI / official Palomar preparation and verification | **Pending** |

All six release stages—structure, provenance, unit tests, build, literal
statement audit and owner audit—returned exit code zero. All recorded
verification inputs were unchanged. The owner inventory contains 14,244
public and 2,521 private declarations, including 12,586 theorems and 3,975
definitions, with no opaque declarations. Every declaration kind was checked
against the axiom whitelist. Additional guards cover 90 selected theorems
and 28 selected definitions. The build recorded 865 warnings; the fresh
owner audit recorded none.

The compiled-interface diagnostic used separate Challenge and proof
processes. All nine declaration types and seven definition bodies were
structurally identical, including instance arguments. Their common digest is
`0da75f6ec67460498e6f5a13890e8d06a76dd9dad1739c7f433af31e0b51c3d2`.
All 419 source files, 1,257 compiled objects and the five additional bound
inputs were unchanged: 1,681 inputs total. This diagnostic compares types
and definition bodies, not theorem proof bodies, and is not the official
Comparator.

The separate source-build directory began with zero project build objects.
It was built cumulatively from source; the final source-only synchronization
preserved 2,214 objects already produced there and copied no compiled objects
from the working project. The complete final gate then passed with all 472
input hashes exactly equal to the main successful gate. This is one
cumulative source rebuild, not repeated from-zero builds of the final snapshot.

The additional [compiled-object comparison](../d18-clean-final/object-comparison/REPORT.md)
checks all 1,314 main/clean module parts. Of these, 1,185 are byte-identical;
the remaining 129 concern 64 modules. Direct inspection of their stored
declarations, types, proof bodies and imports establishes equality despite
the recorded metadata and serialization differences. All main object hashes
match those bound to the independent-kernel export. The comparison does not
claim byte identity of every compiled file.

The exported proof targets are theorem A, `almostSix_ninety`, the unconditional
`convex_partition_counterexample_gt_17`, and the concrete
`requiredRelativeLifting` theorem. Their actual proof values and transitive
dependencies were replayed from the same 700,996,206-byte export, SHA-256
`978d77cdeecf295f3ae79fbc5c18f5d42fb66e911dc7ce0e758925c7d543a0be`.
All three bundled checking components returned zero, with unchanged proof
inputs and export. The export contains 58,974 theorem records, 17,008
definitions, 1,381 inductives, the three permitted axioms, four quotient
records and 38 opaque records. These are counts of the full exported
dependency closure, including core and library declarations; they differ
from the local-owner inventory above.

The supplemental con-ron replay used the approved 4.36.0-rc1 binary with
SHA-256 `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.
It returned zero in 109.273 seconds; the checker, export and earlier kernel
report remained unchanged. This is an additional version of con-ron, not
a fourth independent checker implementation. The local controls are recorded
separately from the official registry controls; no official workflow pass is
inferred from this replay.

The evidence layout is:

- `verification/d18-final-retry/`: the successful complete release gate,
  its input hashes, logs and final `results.json`;
- `verification/d18-clean-build/`: initial empty-build evidence, source-only
  finalization record and cumulative build log;
- `verification/d18-clean-final/`: the successful complete final gate in
  that separate source-build directory;
- `verification/d18-clean-final/object-comparison/`: direct comparison of
  the main and clean compiled declarations and proof bodies;
- `verification/d18-compiled-interface/`: the successful independent
  compiled-interface diagnostic and all unchanged-input hashes;
- `verification/d18-dependencies/results.json`: successful verification
  that all nine dependency checkouts match their manifest commits and have
  no tracked source modifications;
- `verification/d18-extension-2026-11-24/`: statement, exact-boundary
  lifting, and analytic/geometric review records;
- `verification/d18-publication/`: this preparation record and metadata.
- `verification/d18-kernels/`: export metadata and independent replay logs,
  recording acceptance by all three bundled checking components;
- `verification/d18-approved-con-ron/`: authenticated approved-checker
  provenance, the successful supplemental replay and local controls;
- `verification/d18-comparator/`: the new sandboxed Comparator attempt,
  its actual failure log and unchanged-input evidence.

The 700,996,206-byte NDJSON export is not included in the source package.
Its exact size, digest and reproduction commands are retained; see
[verification/README.md](../README.md). The exported-proof replay results
refer to that recorded file, not to a second export reconstructed from logs.

The Comparator attempt returned exit code 1 after 7.683 seconds with
`bwrap: Failed to mount tmpfs: No such file or directory`. All recorded
source hashes were unchanged, and sandboxing was not bypassed. This is an
observed local sandbox-initialization failure, not a mathematical rejection
or a successful comparison. A working-host official workflow run remains
necessary after the required metadata is completed.

The earlier `verification/d18-final/` attempt is historical; an
unfinished or failed attempt must not be cited as a successful release gate.

`comparator.json` permits only `propext`, `Classical.choice` and `Quot.sound`.
The completed owner audit checks this dependency property; the earlier
token scan alone did not establish it. It excludes `sorryAx`,
`Lean.ofReduceBool` and every project-specific axiom from the audited
declarations. An intentional Challenge hole is separate
from a hole in a Solution proof. These are the official
[Comparator requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#23-comparator-configuration).

## Administrative requirements and confirmed root metadata

The historical pre-confirmation draft [`formalization.yaml.draft`](formalization.yaml.draft)
left human authorship and license fields blank during the automated completion
session. Those fields have now been confirmed by the author and recorded in
the root [`formalization.yaml`](../../formalization.yaml):

1. **Human formalizer and responsible maintainer**: **Arseniy Akopyan** is
   confirmed as the sole human author of the mathematical manuscript
   ([`paper/manuscript.tex`](../../paper/manuscript.tex)), the initial Lean 4
   formalization (`RequestProject/`, `Solution.lean`, and initial
   `AkopyanResearch/` modules, developed with AI assistance from Aristotle and
   Gemini), and the $d > 17$ completion (`AkopyanResearch/Completion/`,
   developed with AI assistance from GPT-6 Astra Pro), as well as the
   responsible maintainer of the repository. AI models are disclosed under
   `automation.methods`.
2. **Repository license**: Confirmed as `Apache-2.0` in both root
   [`LICENSE`](../../LICENSE) and `project.license` in
   [`formalization.yaml`](../../formalization.yaml).
3. **Mathematical and formalization provenance**: Root
   [`formalization.yaml`](../../formalization.yaml) distinguishes Theorem A of
   [`paper/manuscript.tex`](../../paper/manuscript.tex) ($\Delta^{35} \to \mathbb{R}^6$,
   `relationship: formalizes`) from Theorem B of the manuscript ($d \ge 24$,
   `relationship: adapts`, strengthened in Lean to $d > 17$ via the
   unconditional $\Delta^{89} \to \mathbb{R}^{16}$ embedding
   `AkopyanSixfold.almostSix_ninety`), and records the earlier TopTverberg
   Lean baseline (`Solution.lean` for $d \ge 36$ and conditional $d \ge 18$,
   `relationship: adapts` in `sources` and `builds-on` in
   `related_formalizations`) alongside the ported `homotopy-groups-lean` and
   `hatcher-at` libraries.

These requirements come from the official
[metadata and provenance rules](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#31-fields-checked-mechanically),
[repository licence requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#25-repository-licence),
[submission authorization rule](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#4-confirm-that-you-are-authorised-to-submit)
and the current
[metadata template](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/formalization.yaml).

The draft records the pinned homotopy-groups-lean and hatcher-at sources,
their authors and secondary source credits, retained licences and local
provenance manifests. Its arXiv and MSC codes exist in the official taxonomy
snapshots; the mathematical classification remains an editorial choice.

## Reference snapshot

[`official-references/DOWNLOADS.json`](official-references/DOWNLOADS.json)
records official URLs, SHA-256 hashes and download outcomes. The current
policy, template, toolchain minimum, schema, taxonomies and the pinned
lean-action definition are retained alongside it. These are reference data;
they do not substitute for a future registry's authenticated verification
of the actual submitted commit.
