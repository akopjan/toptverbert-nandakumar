# Approved con-ron replay of the final export

This directory contains the acquisition evidence and a portable replay
runner for the official con-ron revision assigned by Palomar to
`leanprover/lean4:v4.35.0`. The approved binary is from Lean
`v4.36.0-rc1`, commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`.

**Preparation status:** the official archive and executable hashes were
verified on 24 November 2026. Preparing this directory did not execute
the replay. A completed attempt creates `results.json`; its outcome,
exit code, and unchanged-input checks determine the replay status.

The subsequently executed
[four local invocation controls](local-controls/README.md) all matched
their expected outcomes. Those checks use separate small existing
fixtures and do not constitute replay of the main export or the official
pipeline controls.

## Run after the ordinary kernel checks finish

Use Python 3.9 or later. The runner itself uses only the Python standard
library. It requires the existing binary and the completed export; neither
large file is included in this evidence directory.

```sh
python3 verification/d18-approved-con-ron/replay_approved_con_ron.py \
  --checker /path/to/approved/bin/con-ron \
  --export /path/to/final-selected.ndjson \
  --kernels-report verification/d18-kernels/results.json
```

The input paths can differ from their original locations: the bytes and
declaration records, rather than path spelling, are compared. By default
the attempt is recorded beside this README. Existing replay evidence is
never overwritten. For another attempt, pass `--output-dir` with a fresh
directory inside this bundle.

The checker command is exactly `con-ron --jobs=4 EXPORT`. Its default
process limit is 1,800 seconds; `--timeout-seconds` can change that limit,
which is recorded in the result.

## Enforced checks

Before execution, the runner verifies the copied acquisition records and
requires this exact executable SHA-256:

`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.

The ordinary-kernels report must be complete, identify Lean 4.35.0, and
record successful compilation, declaration audit, export, leanchecker,
and NanoDa checks with unchanged proof inputs and export. Its completed
bundled con-ron result is retained even if that older checker failed.
Such a failure is not reclassified as an authorized registry decline.

The runner independently parses and hashes the actual NDJSON. It checks
every selected declaration's kind and proof/definition body, the declared
axioms, and the declaration-record counts against the preceding report.
All four final theorem bodies must be selected and present:

- `AkopyanSixfold.tverberg_counterexample`;
- `AkopyanSixfold.almostSix_ninety`;
- `AkopyanSixfold.convex_partition_counterexample_gt_17`;
- `AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting`.

The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The export's SHA-256 and byte count must match the ordinary
checks. After execution, the export, binary, and preceding report are
hashed again. Success requires checker exit zero and unchanged inputs;
timeouts, nonzero exits, and validation failures are recorded as
unsuccessful or unverified.

## Recorded evidence

An attempt writes:

- `results.json`: checker command, executable hash, final-export hash,
  independently inspected declaration records, preceding checker exits,
  timestamps, elapsed time, and post-run hashes;
- `con-ron.log` and `con-ron.exit`: combined checker output and raw exit
  status;
- `prior-kernels-results.json`: an unchanged copy of the completed report
  against which the export was matched.

The acquisition evidence consists of `DOWNLOAD_VERIFICATION.json`, the
official checker manifest, official GitHub release/tag metadata,
`SOURCE_COPY_MANIFEST.json`, and the unchanged upstream `LICENSE` and
`LICENSES`. The canonical download was
<https://github.com/leanprover/lean4/releases/download/v4.36.0-rc1/lean-4.36.0-rc1-linux.tar.zst>.
The entire 605,563,669-byte archive matched
`26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2`
before the executable was extracted.

`fetch_official_checker.py` is preserved as the acquisition script used
in the original workspace; its original absolute source-manifest path
is part of that historical record. The replay runner has no such
workspace dependency. The archive and executable remain outside the
publication evidence bundle.

## Scope

This checks the approved runtime component against the same final proof
export. It does not run the Palomar Comparator, its protected export
generation, its separate sandbox setup, or its mandatory positive and
ill-typed negative controls. It does not assert registry acceptance.
It also does not repeat the independently recorded challenge-statement
comparison. An approved con-ron success supplements the preceding
component evidence; it does not replace the complete official workflow.
