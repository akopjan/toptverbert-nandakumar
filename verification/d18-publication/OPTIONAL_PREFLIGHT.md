# Optional official Palomar preflight workflow

The separate workflow
[`palomar-preflight.yml`](../../.github/workflows/palomar-preflight.yml) is
manual only (`workflow_dispatch`). It calls Palomar's supported reusable
workflow; it does not submit to, render for, review for, or register a result
with Palomar. The existing main `verify.yml` workflow is unchanged by this
addition. No remote job has been started.

## Pinned official interface

The caller uses
`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml` at commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. The `pipeline_commit` input is the
same full SHA. This is the exact interface described by the
[README at that commit](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md)
and declared in the
[pinned workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/.github/workflows/submission.yml).

| Input | Value supplied by this project |
|---|---|
| `repository` | Runtime `${{ github.repository }}`; no repository name is invented. |
| `commit` | Runtime `${{ github.sha }}`; the immutable revision selected by the manual run. |
| `pipeline_commit` | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. |
| `request_id` | A generated 12-character lowercase hexadecimal identifier, satisfying the official lowercase-alphanumeric contract. |
| `mode` | Manual choice `preflight` or `full`; default `preflight`. |
| `execution_profile` | `palomar-standard-v1`, required for ordinary external callers. |
| `options` | JSON containing only `comparator_config_path: comparator.json` and the explicitly selected `authorization_relationship`. |

The project lives at the repository root, so no `project_path` is supplied.
The workflow expects the completed metadata at root `formalization.yaml`.
It deliberately does not point to the unresolved `.draft` file. Preparation
will report missing or incomplete release metadata until the administrative
requirements in [`REPORT.md`](REPORT.md) are resolved.

## Manual use

After publishing the final project commit, open the **Optional Palomar
predictive preflight** workflow in GitHub Actions. Select:

- `preflight` for official preparation checks, or `full` to continue through
  the official toolchain and proof checks after preparation succeeds;
- the truthful relationship: responsible author/maintainer, or approval
  from one.

The relationship defaults to `Unconfirmed`. The local request job rejects
that value before calling the official workflow. Thus this configuration
does not assert human authorship, maintenance or approval on anyone's behalf.
The two accepted relationship strings were read directly from the pinned
official `submission_contract.py`; technical-maintainer and registry-correction
roles are not offered.

The request encoder passes inputs through environment variables and JSON
serialization. It uses no repository secrets and grants only `contents: read`.
The reusable verifier produces its own report artifacts. A passing predictive
run remains advisory: it is not registry acceptance, and full registry
submission remains a separate action.

## Reference and validation evidence

[`palomar-workflow-reference/PROVENANCE.json`](palomar-workflow-reference/PROVENANCE.json)
records all downloaded URLs, exact revision and file hashes. It accompanies
the pinned workflow, README, input-contract sources, GitHub commit response
and workflow-blob response.

The canonical Git remote and canonical GitHub API agreed on the commit.
GitHub reports its commit signature as verified; the raw pinned workflow
bytes match the API's content and Git blob SHA-1
`9e64a62a110e1beec226db86cb7fe70ee2cf5e47`. The workflow SHA-256 is
`10d97d59e223c3378d4b96601260f26fec1b27d4fd94739bc06a63ec3bab9c17`.
This records the authentication evidence actually obtained; it is not an
independent local GPG-signature verification.

[`OPTIONAL_WORKFLOW_VALIDATION.json`](OPTIONAL_WORKFLOW_VALIDATION.json)
records successful local checks of the YAML, exact supported input names,
required inputs, matching pin, runtime repository/commit, execution profile
and permissions. Four valid mode/relationship combinations produced the
required request format. The unconfirmed relationship and an invalid mode
were both rejected without emitting a request. These checks did not invoke
the remote verifier, build the main Lean project or change its proof sources.
