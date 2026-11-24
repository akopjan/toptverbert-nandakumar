# Final publication-documentation review

**Recorded:** 2026-11-24T09:36:40.662281+00:00. This is an agent review of release documentation and
its cited evidence. It is not external peer review or Palomar acceptance.
This timestamp does not close or measure the ongoing completion session.

## Result and exact scope

The current entry points consistently describe the unconditional theorem
`AkopyanSixfold.convex_partition_counterexample_gt_17` for every natural
`d` with `17 < d`, together with theorem A and
`AkopyanSixfold.almostSix_ninety`. They describe actual nonempty compact
convex bodies with the Hausdorff topology, continuous functionals defined
on the whole body space, and an absolutely continuous probability measure.
The publication interface has no extra lifting, connectivity or homology
premise. “Almost-six embedding” is not described as injectivity.

The documentation distinguishes the two intentional independent Challenge
placeholders from proof admissions. It identifies the standard permitted
axioms `propext`, `Classical.choice` and `Quot.sound`; no new project axiom
is asserted or excused. The source archive credit is retained without
assigning the uploader an identity or treating that credit as complete
human authorship or licence authority.

The checked documentation makes **no claim of registry acceptance, an
executed remote project workflow, external human peer review, confirmed
project authorship/licence, a published original paper for the exact
claims, or mathematical novelty/priority**. Local verification and official
submission are kept distinct.

## Evidence reconciled

| Item | Observed result |
|---|---|
| Main full gate | All six stages passed; 37 tests; 16,765 declarations from 438 owners; 472 unchanged bound inputs. |
| Separate cumulative source rebuild | Passed from a directory that began with zero project objects; final source-only synchronization copied no working-project objects; all 472 input hashes equal the main gate. |
| Compiled-object comparison | All stored declarations, types and proof bodies agree. Of 1,314 files, 1,185 are byte-identical; 129 metadata/layout differences affect 64 modules. Main objects match the kernel-bound hashes. |
| Separately compiled interface | Nine types and seven definition bodies agree; 419 sources, 1,257 compiled objects and five further inputs remain unchanged. This is not theorem-body replay. |
| Selected-proof export | Actual proof bodies of A, `almostSix_ninety`, B18 and `requiredRelativeLifting`, with dependencies, accepted by Lean checker, NanoDa and bundled con-ron. |
| Approved con-ron | Accepted the same 700,996,206-byte export. This is an additional version of one checker, not a fourth independent implementation or the registry workflow. |
| Local approved-checker controls | Four recorded local component controls have the expected outcomes; they are not claimed to be official registry controls. |
| Sandboxed Comparator | Exit 1 during `bwrap` tmpfs setup, before comparison; not a proof rejection or a passing Comparator run. |
| Dependency sources | All nine actual checkouts agree with their pinned revisions and have no tracked source changes. |
| Metadata | Draft remains invalid/incomplete: exactly two schema errors, plus four local profile errors. No metadata pass is claimed. |

The export digest is
`978d77cdeecf295f3ae79fbc5c18f5d42fb66e911dc7ce0e758925c7d543a0be`.
Its 38 opaque records belong to the full dependency export; the all-owner
project inventory has zero opaque declarations. The source archive omits
the large NDJSON, retaining its exact digest, size and reproduction commands.
Historical B36 and failed/unfinished attempts are not substituted for current
B18 evidence. All 472 frozen proof/configuration inputs were independently
rehash-checked during this documentation review and remain unchanged.

## Documentation corrections made

Only three existing Markdown documents were edited:

1. `verification/d18-publication/REPORT.md`: the remaining-metadata item now
   states that completed mathematical gates and the audited axiom list are
   already recorded. The evidence layout explicitly identifies export
   metadata/logs and the omitted large NDJSON. It also links the main/clean
   declaration comparison, preserving its limited non-byte-identical scope.
2. `docs/PALOMAR_PREPARATION.md`: the same export-location and already-completed
   mathematical-gate distinctions are explicit; the compiled-object comparison
   is linked.
3. `verification/d18-publication/ROOT_DOCUMENT_REVIEW.md`: an appended note
   identifies its earlier pending-replay wording as the historical 09:03 UTC
   state and links this review. The original finding and hashes remain intact.

The root `README.md`, `README.en.md`, `FORMALIZATION_STATUS.md`, `CHANGES.md`
and `verification/README.md` required no correction. No proof source,
script, CI workflow, configuration or metadata draft was changed.
The companion JSON records the local-link check and reviewed file hashes.

## Remaining human and external requirements

Before an actual submission, the responsible person must confirm:

- the complete human formalizer list and responsible human maintainers;
- the project's actual licence, matching SPDX identifier, and exactly one
  conventional root licence file; upstream Apache-2.0 licences do not decide
  the licence or ownership of this project's original code;
- the archive's correct attribution and publication history. The bounded
  search did not identify a published source of the exact claims and does
  not establish novelty;
- the public GitHub repository and immutable release commit;
- the truthful responsible-author/maintainer relationship or permission to
  submit, distinct from merely having repository write access.

The draft keeps `project.authors`, `project.responsible_maintainers` and
`project.license` empty. Its matching metadata report has exit 1, schema
errors for authors/licence, and additional profile errors for authors,
maintainers, licence and the missing root licence file. The draft's bytes
match the validator's recorded SHA-256. These are administrative omissions,
not extra premises or missing steps of the mathematical proof.

Once those fields are confirmed, complete root `formalization.yaml`,
validate it, and run the committed checks on the chosen public commit.
The prepared optional manual workflow calls the official verifier at
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; its default unconfirmed
relationship prevents an unauthorized assertion. No remote run was made.
A suitable sandbox host and actual official workflow results remain needed;
registration is a further external action.

Official references already cached for this preparation:
[submission guide](https://palomar-registry.org/how-to-submit),
[policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[metadata template](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/formalization.yaml),
and the [pinned reusable-workflow documentation](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md).
No new policy assertion was inferred from a successful local proof checker.

## Reviewed documentation snapshots

These hashes bind this review, not future permitted documentation updates.

| File | SHA-256 |
|---|---|
| `README.md` | `625c020f433b30c15377355369d388939dab143cc7f3710d7a233e0d2c23e868` |
| `README.en.md` | `89d0735777c487ce135cabbe9fb0c11c1ef8b9d06995682aa44c0f39afc653b2` |
| `FORMALIZATION_STATUS.md` | `b3f16786f4a25e1e5ed110b9b058ee29a0488c58473e78fe8cd8389a27af3804` |
| `CHANGES.md` | `f18e8e14c0d65d329b0df01a903eb34346e2ca11847921550e9687009d493b62` |
| `verification/README.md` | `2d99732424a85727d018eccfb2d5e6586bcde8e4fbc561524a5e025c4377bac5` |
| `docs/PALOMAR_PREPARATION.md` | `88b22e14dc20fbcf8395e4b897c13a95e8751ca8f6e1a8a55633249f4861c493` |
| `verification/d18-publication/LITERATURE_REVIEW.md` | `d728daf2db9d5636ba66717adf28a2aefb6c2f3c04da3345d896ac2f51884e37` |
| `verification/d18-publication/OPTIONAL_PREFLIGHT.md` | `5e3f30e23989588fb52c4b3dd4df72131beec920a9ceb4b54d88a1fda440d14e` |
| `verification/d18-publication/README.md` | `e52750babffb0400f37cfbad6a6e40dae88c2c5792d9153943e1687501393d04` |
| `verification/d18-publication/REPORT.md` | `44bf67d7b732f83c8d2580023b3aca74f6b146d2062ccbcb6d85cd1bc28092e8` |
| `verification/d18-publication/ROOT_DOCUMENT_REVIEW.md` | `8ac0f6678f2de17832e8d70f65f5cf77f82b63ba2cd660cb87d5fd759b8f1177` |
| `verification/d18-publication/formalization.yaml.draft` | `b973ceebd081c56386734920da987fa4e4b988af873920fbd2ab40761a15bc6b` |

## Read result-file snapshots

| Evidence file | SHA-256 |
|---|---|
| `verification/d18-final-retry/results.json` | `7de2a730fbfca4b547ddfb5aeba695e302f87e726b761a63821696e374aa6a74` |
| `verification/d18-clean-final/results.json` | `80e083c8538d77a4b1c64b43151dbf3d3c8c79af9a5f95e1603f12d292942937` |
| `verification/d18-clean-final/object-comparison/results.json` | `6ac269f3deefff999ebe879f598628fee45175f3547a7646d7ceac93a932efd0` |
| `verification/d18-compiled-interface/results.json` | `18fe4c5706c9a5f4f0349176bb2b91f5fea2885d0c6a9c4b4683bcd38fe511ae` |
| `verification/d18-kernels/results.json` | `7587d60175e14da6f6427624e2ff9d909b9b04f20f6b85eb33695fc347ae6c9b` |
| `verification/d18-approved-con-ron/results.json` | `ad214f3de796b105a8cdc27c29adb39147e68b9f4ab8fc03e0c32934101b67d1` |
| `verification/d18-approved-con-ron/local-controls/results.json` | `5d6751504ddc0b4ee3e49c2d25e7a670dae38bcad40bdda04ceea18cfc4ee67f` |
| `verification/d18-comparator/results.json` | `1e5c4c254890e6f97a947abfb29d9f280cd41763e7273cd4ebe6253f8f0319c7` |
| `verification/d18-dependencies/results.json` | `f29689d145bdcd30b3a6308b108e79dbafc176a2d8868c4cbd641309287183cf` |
| `verification/d18-publication/METADATA_VALIDATION.json` | `6686e1ce608c9dc845791b2040e504bc4bd802a7225682136c750504e47fc90f` |

## Final addendum: linked documents and portable reproductions

**Recorded:** 2026-11-24T09:53:17.318335+00:00. This addendum reviews the later documentation
snapshot without replacing the earlier observations or finalizing session
wall time. No Lean process, build, export, kernel check or external request
was launched for this review.

All **147 local Markdown links** resolve across the **13** documents listed
below, including the newly written `PDF_REVIEW.md`. No local Markdown
fragment required separate resolution. The mathematical notes, combined
companion, PDF reconstruction guide and submission handoff agree with the
current entry points. No prose or link correction was necessary.

The new reproduction sections accurately describe the three executed
portable diagnostics:

- **Compiled interface:** nine types and seven definition bodies agree;
  419 sources, 1,257 objects and all 1,683 bound inputs remain unchanged.
  The historical canonical digest is reproduced. This does not compare
  theorem proof bodies or execute the official Comparator.
- **Semantic scope:** the exact reference is first compiled with Mathlib
  alone, excluding the project object path; all five proof checks pass.
  Its 418-module proof closure, 1,254 existing objects and the 472 frozen
  release inputs remain bound, with unchanged input/tool hashes. This is
  the archived semantic diagnostic, not another external-kernel replay.
- **Object comparison:** all 438 owners are covered, comparing 1,314 object
  parts. Of those, 1,185 are byte-identical; the 129 differences concern
  64 modules whose stored declarations and imports compare equal. Opaque
  environment-extension payloads are explicitly outside the comparison.
  This does not claim byte identity of all files or a fresh project build.

Each diagnostic uses new output evidence, retains the historical runner and
bound record, and records a successful actual run. The displayed commands
refer to the existing portable adapters, not the workspace-specific old
runners. Their recorded scopes agree with `verification/README.md`.

The PDF review matches the actual build record and the delivery file:
fifteen pages, 252,932 bytes, PDF SHA-256
`22ce661902a89863283eacfd8d1abd64940e2aa0c22e89200442b1aec65585f2`. The recorded source and renderer hashes match
current files. The review explicitly identifies automated visual/document
inspection and does not assert external human peer review. No PDF source
change or rerender was needed for this addendum.

Across these current documents, official sandboxed Comparator success,
registry acceptance, remote project-workflow execution, confirmed human
peer review, and mathematical novelty remain **unclaimed**. The known local
Comparator initialization failure and unresolved human/repository/licence
fields remain explicit. All **472** frozen core inputs were rehash-checked
and remain unchanged.

### Current documentation hashes

| File | SHA-256 |
|---|---|
| `README.md` | `3b783049b037abc534caf61944e6e3cd96d94d6a11a28a4376dbd8e18848986e` |
| `README.en.md` | `82f641633f37fd9b1536c7038aaac1331d0123d373681d8f63601654f01fa736` |
| `FORMALIZATION_STATUS.md` | `b3f16786f4a25e1e5ed110b9b058ee29a0488c58473e78fe8cd8389a27af3804` |
| `CHANGES.md` | `9dd3005c9785ea0106f618a1a8e8fe3723f4992bda5232992ad7e4db296b8d73` |
| `verification/README.md` | `bba53115ef3ebee8b5ca51e1c4679aa735117a131f4215b1f2bf0b32147a1abe` |
| `docs/DIMENSION_EIGHTEEN_PROOF.md` | `f8c5a12f54433f84c840802b2fbad45b6d10b887077cb1e9faec842071461a74` |
| `docs/PROOF_MAP.md` | `bd80da23978ac64e107db05df04778355a86c4986fa3140089c986c816bbd928` |
| `docs/TARGET_SECTION.md` | `28a01945fd37059e06995f685a18d512aa9e297a2ab6acb7ca68fc1b9ca5db72` |
| `docs/SAFE_TABLE_TO_EMBEDDING.md` | `23369c7ea239dfaac57d2fe57cea439433079fa4b4f405cdc3d77b2f32988506` |
| `docs/PROOF_COMPANION.md` | `5e5d03e152eb843f3106649d7c86366dbdb944f395bedfbaa7c5f22a5a8ed158` |
| `docs/pdf/README.md` | `ddadbc8ff80dbc0d17dc8fb72d9a18b2abc6a74cb633e27440795746b4f5dc76` |
| `verification/d18-publication/SUBMISSION_HANDOFF.md` | `51e1bd728bd21e56d466a2abf27a9273bcee19af5956abc02e4800bac68988a5` |
| `verification/d18-release/PDF_REVIEW.md` | `155014e55f4b821a4e5acb95cded2a624f5e3cf34e7621034c421ebbbc87570d` |

### Portable result records read

| Result file | Actual outcome | SHA-256 |
|---|---|---|
| `verification/d18-portable-interface/results.json` | `compiled-interfaces-identical` | `a37c32c6a0787b00ff48f3bc06aa620570b68883e34d2f9f559596b6c05abd18` |
| `verification/d18-portable-semantic/results.json` | `PASS` | `7bc1246ed3025749701890d6d31dcb44269b48ec85664831c9b98c829d94ae2f` |
| `verification/d18-portable-object-comparison/results.json` | `same-declarations-different-metadata` | `49c292cbfabc2b56f35cc3dc12c6b6d9a40045330108e4af65f19feb4a4c8b01` |
