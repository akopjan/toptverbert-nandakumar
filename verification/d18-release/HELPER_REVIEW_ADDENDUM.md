# Packaging correction: generated Lean intermediate files

24 November 2026. The final comparison with the preserved official verifier
identified one concrete omission from the source-release filter: the new
semantic replay had generated two `.ir` files, which Palomar rejects when
committed outside `.lake`. Their `.ir.sig` companions are also runtime
outputs and need not be shipped.

The authoritative saved code is
[verify_submission.py.txt](../d18-publication/palomar-workflow-reference/verify_submission.py.txt),
specifically `COMPILED_ARTIFACT_SUFFIXES`,
`COMPILED_ARTIFACT_NAME_SUFFIXES` and
`reject_committed_build_artifacts`. Its forbidden suffixes are
`.a`, `.bc`, `.dll`, `.dylib`, `.ilean`, `.ir`, `.o`, `.obj`,
`.olean`, `.so` and `.trace`, plus the complete-name suffixes
`.olean.private` and `.olean.server`, matched case-insensitively.

## Authorized correction

`release_package.py` now excludes the complete official list, retaining its
existing local runtime exclusions and also excluding `.ir.sig`.
`validate_release_delivery.py` independently rejects any actual ZIP member
matching the official list or `.ir.sig`. Both release copies were updated.
The supplemental `check_readiness.py` now reports all these suffixes in its
working-tree scan, including the double-suffixed module parts.

`release_diff.py` was left unchanged: generated `verification/` paths are
already outside its patch scope. Its inventory was checked to confirm that
none of the four new IR/signature files enters the patch.

## Workspace evidence versus shipped payload

The actual workspace scan found two files of each of these kinds outside
`.lake`: `.olean`, `.olean.private`, `.olean.server`, `.ir` and `.ir.sig`.
It also found eight Python cache files, already excluded. The ten Lean
outputs belong to the isolated semantic replay.

All diagnostic outputs remain in the working evidence directory, and their
recorded hashes remain in the original successful report. No historical
output was deleted or rewritten. The source release retains their source
diagnostics, commands, logs, hashes and results, while excluding the compiled
runtime files themselves.

The corrected actual source selection contains **zero** files matching the
forbidden compiled-artifact predicate. Python syntax was parsed, and source
and release-copy hashes match. No project build, Lean process, kernel check
or export was run. Final ZIP creation and validation are separate release
steps; the previous dated review reports were not rewritten.

## Updated hashes

| File | SHA-256 |
| --- | --- |
| `release_package.py` and its release copy | `9477cecdaa6482bd823703075c3d03584f08b141cd5d73e37c760dd9cf3dfbe5` |
| `validate_release_delivery.py` and its release copy | `59ef69e469a2700390ecd029b1c58864b8ece61830266fefaee66f2656096f20` |
| `verification/d18-publication/check_readiness.py` | `3b877ad6b680998ce15c21a309b5ee71aa82084b9d69392e74e10453301be8c4` |
| Unchanged `release_diff.py` | `b32ee313b013f1203262854a37c960d3dc33dc146744a867f2860b47ae941d8c` |
