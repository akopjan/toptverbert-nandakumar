# Reproducing the publication checks

This directory prepares the actual A+B18 release for Palomar. It contains
static source checks, an offline metadata validator, cached official
references and a draft whose human authorship and licence fields remain
unresolved. These tools do not submit a project, execute a remote workflow
or replace the mathematical checks recorded elsewhere.

## Environment and commands

The checks were run with **PyYAML 6.0.3** and **jsonschema 4.26.0**, pinned
in [`requirements.txt`](requirements.txt). Use Python 3.11 or later. From
the project root, install the two direct dependencies if they are not
already available:

```sh
python3 -m pip install -r verification/d18-publication/requirements.txt
```

Package installation may require network access. The validation commands
themselves use only local files. Run:

```sh
python3 verification/d18-publication/check_readiness.py
python3 verification/d18-publication/validate_metadata.py
```

The source checker reads the existing pinned Mathlib checkout to compare
toolchains. Set up the project dependencies using the root build instructions
before running it. The metadata validator needs no Lean build or dependency
checkout; its schema and taxonomy inputs are already cached here.

## Static source and configuration check

`check_readiness.py` scans every regular `.lean` file outside `.git` and
`.lake`, including diagnostics. It records module-header and line-limit
checks, Challenge size and source independence, interface signatures,
lexical admissions, dependency pins and the main CI configuration.

It writes both `STATIC_PREFLIGHT.json` and `STATIC_PREFLIGHT_SUMMARY.json`.
These reports describe static observations. The script does not assign
execution statuses to builds, owner audits, independent kernels, Comparator
or GitHub CI. In particular, rerunning it cannot replace a completed gate
with a hardcoded “pending” label. Its lexical checks do not prove theorems.

## Offline metadata validation

`validate_metadata.py` reads `formalization.yaml.draft` by default and writes
`METADATA_VALIDATION.json`. To validate completed root metadata instead:

```sh
python3 verification/d18-publication/validate_metadata.py formalization.yaml
```

An optional `--output PATH` selects a separate report. The output cannot
overwrite the metadata input.

The validator:

- parses UTF-8 YAML and rejects duplicate mapping keys and merge keys;
- checks the cached official v0.4 schema, rejecting nonlocal schema
  references so that validation cannot fetch a remote schema;
- verifies the schema and arXiv/MSC cache hashes against `DOWNLOADS.json`;
- checks the documented name-list, classification, source-origin and
  other bounded profile requirements, plus the root licence file's shape;
- records metadata, schema, taxonomies, validator and requirements hashes;
- reads each available release report once, records its hash and copies
  its actual outcome fields. Missing or unreadable evidence is reported as
  such; it is not converted into an invented pending, passed or failed run.

The exit-code contract is:

| Exit | Meaning |
|---|---|
| `0` | The schema and implemented local profile checks passed. |
| `1` | The metadata is invalid or incomplete. |
| `2` | An input, parsing or cache-integrity error prevented validation. |

**The current draft correctly returns exit 1.** Its exact schema errors are
the empty `project.authors` list and empty `project.license` string. Additional
profile errors identify the empty responsible-maintainer list and missing
root licence. These are unresolved real requirements, not expected errors
silently converted into a passing result. When the responsible people supply
the actual fields and licence, rerun the same validator.

The tool cannot establish human identity, copyright ownership, permission to
submit, mathematical priority, external peer review or official SPDX-content
detection. A future exit 0 would not itself mean Palomar acceptance. Optional
`status.main_results` alignment is reported without inventing an official
requirement that this curated list exactly mirror Comparator.

## Actual release evidence

The metadata report reads the main build/owner audit, cumulative source
rebuild, compiled-interface comparison, selected-proof kernel replay,
approved con-ron replay, local Comparator attempt and dependency-integrity
records from their separate `verification/d18-*` directories. It does not
run those checks or reconstruct their proofs.

The full build, clean source gate and compiled-interface comparison passed.
The selected final proofs passed Lean checker, NanoDa and con-ron; the
approved newer con-ron also accepted the same export. The local sandboxed
Comparator stopped at `bwrap` tmpfs setup, and no registry acceptance is
claimed. See [`REPORT.md`](REPORT.md) for exact scope, hashes and remaining
administrative requirements.

The optional manually invoked official workflow is documented in
[`OPTIONAL_PREFLIGHT.md`](OPTIONAL_PREFLIGHT.md). It expects completed root
metadata and a truthful explicit submission relationship. It has not been
run remotely for this project.
