# Local invocation controls for the approved con-ron binary

These four controls exercise the exact approved executable before replay
of the main project export. They are existing local fixtures, not the
official Palomar pipeline's positive and ill-typed negative controls.
`official_positive_negative_controls_run` remains false.

Only con-ron was invoked in this run. The original fixture was not
rebuilt, its exports were not regenerated, and no comparator, Lean
checker, or NanoDa process was started. The main project export was not
read or checked.

## Observed results

| Existing export | Expected runtime result | Actual exit | Interpretation |
| --- | --- | ---: | --- |
| `positive.ndjson` | Accept | 0 | The explicit successor witness was accepted. |
| `axiom.ndjson` | Decline | 2 | The executable identified the non-standard axiom `Fixture.assumedWitness`. |
| `sorry.ndjson` | Decline | 2 | The executable identified `sorryAx` and reported the affected theorem as skipped, without accepting the export. |
| `hypothesis.ndjson` | Accept | 0 | A proof with an additional hypothesis is well typed. Acceptance by a kernel does not establish equality with the independent challenge statement. |

All expected outcomes matched. The two accepted exports were reported
as containing 466 checked declarations. The raw logs also record the
new checker's in-process model of `Lean.Syntax`; those generated records
are distinguished from records in the input file. No declaration count
was used as a substitute for the actual outcome and diagnostic.

The challenge asks for a witness satisfying `m = n + 1` for every natural
number `n`. The hypothesis variant assumes the required existence
statement and returns that assumption. The preceding fixture's comparator
run rejected its interface, but this invocation-control run intentionally
performs no statement comparison.

## Integrity and reproducibility

The executable SHA-256 before and after every invocation was
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.
Every invocation used `--jobs=4` and the exact pre-existing export path.
The original export and its retained byte-for-byte copy had the same
SHA-256 before and after the attempt.

[results.json](results.json) records the commands, expected outcomes,
actual exit codes, elapsed times, source/export hashes, exported target
records and axioms, log hashes, and unchanged-input checks.
[logs](logs) contains the raw output and exit-code files.

The four small exports are retained in [inputs](inputs) with names
ending in `.ndjson.txt`. To reproduce an invocation elsewhere, copy the
chosen file without altering its bytes to a `.ndjson` path and pass that
path to the same hash-verified executable with `--jobs=4`. Compare its
hash with the corresponding `input_sha256_before` value first.

Fixture source copies end in `.lean.txt`. They document the intentional
negative cases and are not Lean modules in the mathematical project.
The original fixture script and earlier logs are retained under
[historical](historical), separately from this approved-runtime run.
Their presence does not imply that those historical commands were rerun.

These results verify local component behavior. They do not certify a
main-theorem export, a full sandboxed Palomar execution, or registry
acceptance.
