# Palomar submission handoff — A and B18

Prepared from the official instructions cached on 24 November 2026.
The mathematical proof is complete. No registry submission, remote workflow
run, editorial result or registration is claimed by this handoff.

## 1. Complete the human and repository fields

Start with [formalization.yaml.draft](formalization.yaml.draft). Preserve its
actual declarations, source credits, pinned dependencies, automation record
and verification distinctions. Supply these facts before placing completed
metadata at the repository root as `formalization.yaml`:

| Field or decision | Still required from the responsible person |
|---|---|
| `project.authors` | Complete confirmed human formalizer names. |
| `project.responsible_maintainers` | Confirmed responsible human maintainers. |
| `project.license` and root licence file | The actual SPDX identifier and exactly one corresponding conventional root licence file. Upstream licences do not decide this project's licence. |
| Source attribution | Confirm the supplied archive's attribution and publication history. Its Arseniy Akopyan header does not establish complete authorship, licence authority or novelty. |
| Public repository | Actual public GitHub repository URL. |
| Source revision | The final immutable commit: 40 lowercase hexadecimal characters. |
| Submission relationship | A truthful responsible-author/maintainer relationship, or approval from one. Repository write access is a separate requirement. |

No author, maintainer, licence, repository or approval has been invented.
The current draft intentionally fails validation: two schema errors and
four local profile errors. Their exact record is
[METADATA_VALIDATION.json](METADATA_VALIDATION.json).

## 2. Known values ready to use

| Item | Value |
|---|---|
| Project name | `TopTverberg` |
| Project directory | Repository root; omit the optional `project_path`. |
| Metadata path | `formalization.yaml`, after completing the draft. |
| Comparator configuration | `comparator.json` |
| Challenge / proof entry point | `Challenge` / `PalomarSolution` |
| Compared theorem A | `AkopyanSixfold.tverberg_counterexample` |
| Compared theorem B18 | `AkopyanSixfold.convex_partition_counterexample_gt_17` |
| Additional proved construction | `AkopyanSixfold.almostSix_ninety`; it is not a third Comparator target. |
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Existing classifications | arXiv `math.MG`, `math.AT`; MSC2020 `52C35`, `55S91`, `52A20`. |

### Proposed description

The official policy uses `project.description` as the registry abstract.
The following is a factual draft for that field or an accompanying note;
it is not an issue body or a replacement for the intake fields.

```text
This Lean 4.35.0 project proves an almost-six embedding of the
35-dimensional simplex into R^6 and an unconditional obstruction to
convex six-part equipartition in every natural dimension d > 17.

For the latter result, Body d is the Hausdorff space of nonempty compact
convex bodies in Euclidean d-space. There exist a continuous map from
Body d to R^(d-1) and a probability measure absolutely continuous with
respect to volume such that no convex partition of the closed unit ball
into six bodies with nonempty pairwise-disjoint interiors has both equal
measure and equal functional values. The completion constructs an
almost-six embedding of the 89-dimensional simplex into R^16 and applies
the supplied convex-geometric reduction. The final theorem has no extra
lifting, homology or connectivity premise.

The complete Lean build, all-owner audit, separate cumulative source
rebuild and independent compiled-interface comparison passed. The
selected actual proof bodies and their dependencies were accepted by
Lean checker, NanoDa and con-ron; an approved newer con-ron accepted the
same export. Only the three standard permitted axioms occur. The two
intentional Challenge placeholders are outside the proof closure.
The local sandboxed Comparator attempt stopped at bwrap tmpfs setup;
official workflow success and registration have not been established.

The package preserves the supplied archive's attribution and the pinned
upstream formalization credits. A bounded literature review did not
identify a published source of these exact claims. This does not
establish novelty or priority. The archive's credit is not treated as
the complete human author list or as licence authority.
```

Exact evidence, checker identities and limits are in [REPORT.md](REPORT.md)
and [the verification guide](../README.md). Preserve upstream credits in
the full draft even if the shorter description above is used.

## 3. Reproduce locally and run the optional official preflight

After completing root metadata, run from the repository root. Use a new
output location for reproduction evidence rather than overwriting the
recorded release gates:

```sh
python3 -m pip install -r verification/d18-publication/requirements.txt
python3 verification/d18-publication/validate_metadata.py formalization.yaml --output verification/submission-metadata-validation.json
lake exe cache get
SKIP_MATHLIB_CACHE=1 bash scripts/verify.sh verification/reproduction
python3 verification/d18-publication/check_readiness.py
bash scripts/verify-comparator.sh
```

The last command needs a host with working `bwrap`. The metadata validator
checks its documented local profile; it cannot establish human identity,
copyright ownership or official acceptance.

After committing the completed package to the chosen public repository,
open **Optional Palomar predictive preflight** in GitHub Actions. Select
`preflight` for preparation checks or `full` for mechanical verification,
and choose exactly one truthful relationship:

- `I am a responsible author or maintainer`
- `I have approval from a responsible author or maintainer`

The default `Unconfirmed` blocks the request. The existing workflow supplies
the runtime repository and commit, `comparator.json`, and the required
`palomar-standard-v1` profile. Its official reusable workflow is pinned to
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. No repository name or dispatch
identifier needs to be invented. Retain the actual run artifact and URL;
a predictive run is advisory and does not register the project. Details:
[OPTIONAL_PREFLIGHT.md](OPTIONAL_PREFLIGHT.md).

## 4. Actual registry intake

The inspected official instructions direct submissions to
[submit.palomar-registry.org](https://submit.palomar-registry.org/), not a
GitHub issue. The form asks for the public repository, immutable commit,
exactly one Comparator configuration path and the submission relationship.
Use the human-supplied repository/commit and `comparator.json`; metadata
comes from the committed root `formalization.yaml`. An approval note/link
is optional when applicable. Do not send the proposed prose as an invented
workflow `context` field: that field is not in the inspected closed contract.

An agent making a future submission must first read the server's
[llms.txt](https://submit.palomar-registry.org/llms.txt), as the official
policy requires; this handoff makes no server request and invents no API
procedure. The official process separately verifies repository access,
runs its checks and review, and leaves registration as a further decision.

Sources: cached [Palomar policy](official-references/PalomarPolicy-CONTRIBUTING.md),
the [pinned verifier README](palomar-workflow-reference/README.md), and the
inspected [submission contract](palomar-workflow-reference/submission_contract.py.txt).
Their recorded URLs and hashes are retained in
[DOWNLOADS.json](official-references/DOWNLOADS.json) and
[PROVENANCE.json](palomar-workflow-reference/PROVENANCE.json).
