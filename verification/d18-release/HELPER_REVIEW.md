# Independent release-helper review

Reviewed on 24 November 2026, while the final exported-kernel checks were
still running. This is an integrity review of the packaging helpers,
not a substitute for the final patch application and ZIP validation.

## Defects found and corrected

1. The independent compiled-interface report was initially checked only
   through success flags. The final guard now binds its nonempty equal
   before/after snapshots to the actual files, requires the exact nine
   types and seven definition bodies, and checks independent imports.
2. Successful verification was initially checked before reading archive
   payload bytes, without binding those exact bytes. The final guard now
   checks the actual payload against the verified hash snapshots and
   rejects an added or missing proof module.
3. Patch generation initially excluded every verification path. Two files
   under `verification/original-specification` are required source inputs
   of the checker and are absent from the original archive. Both patch
   inventories now include that directory, while omitting generated logs.
4. Archive validation now requires the verified dimension-eighteen flag,
   all four current evidence records, exact payload inventory, report
   hashes, content hashes, and preserved permission bits.
5. The release guard now explicitly requires successful Lean checker,
   NanoDa and bundled con-ron steps and exported `thm` records with values
   for all four selected final declarations.

These were packaging defects and guard omissions. No mathematical theorem
mismatch or changed proof input was found.

## Independent checks of the actual working tree

The reviewer rehashed all 472 main/clean source inputs and all 1,681
compiled-interface inputs. They matched the successful records. Both
serialized interface snapshots matched their recorded digests and exact
A+B18 declarations. Build/audit logs, exit files, and the retained
verification scripts agreed with the reported outcomes.

At the review snapshot, the selected archive payload contained 1,013 files
and 18,193,517 bytes. Every selected Lean file had a module header and at
most 10,000 lines. The patch inventories contained 96 original and 496
updated files, including both required original-specification inputs.
These are dated review counts; later documentation and verification logs
may increase the final inventory. The final archive supplies its exact
`RELEASE_INVENTORY.json` and `SHA256SUMS`.

No remaining blocking packaging defect was found in that working tree.
No proof source or frozen verification input was edited during the review.

## Reviewed helper hashes

| Helper | SHA-256 |
| --- | --- |
| `release_package.py` | `f4d8d07af52d0ff4ef251549aa3fd6c658871a0da2310e117376a4490522ed0e` |
| `release_diff.py` | `b32ee313b013f1203262854a37c960d3dc33dc146744a867f2860b47ae941d8c` |
| `validate_release_delivery.py` | `e9a7967ad11323aff7a1aceba03e63e43608faf0fa7a89c774293b535236a688` |

The helpers used for the actual final release are copied into this directory.
The release record must state their final hashes and the real validation
outcomes; this review alone does not certify an archive that has not yet
been built.

## Read-only confirmation of the compiled-output correction

Recorded **24 November 2026, 09:57:15 UTC**. This addendum inspected the
corrected helper source and its release copies; it did not run either
helper, validate an archive, invoke Lean, or rebuild anything.

The two scratch-root helpers are byte-identical to their copies in this
directory. Their constant lists were compared with the preserved official
`verify_submission.py.txt`, SHA-256
`3ff03bf4d7774ec47e1e81fe397d03e54895ee59901036580c6da3b57010cc08`.
Both cover all eleven official compiled suffixes and the two official
full-name suffixes `.olean.private` and `.olean.server`. The additional
`.ir.sig` exclusion is explicitly a local runtime-output exclusion; it is
not falsely attributed to the official list.

The packager lowercases both `Path.suffix` and the complete filename before
matching. Thus `.ir` and `.ir.sig`, including mixed-case spellings, are
excluded. Ordinary `.lean` sources, JSON manifests/results, text, Markdown,
configuration and `.log` files do not match these filters. The selector
does not exclude the `verification` tree; diagnostic source and logs remain
eligible. Its existing exact proof-module inventory and verification-hash
guards are retained. No source or diagnostic output is deleted by selection.

The archive validator defines its own compiled-artifact lists and checks
every actual ZIP member with the same lowercase predicates. It raises an
error on a forbidden member before trusting the embedded inventory or
checksums; it does not rely on the packager having filtered correctly.
This source inspection confirms the intended independent rejection path.
The actual final ZIP run remains a separate release check.

| Corrected helper and identical release copy | SHA-256 |
|---|---|
| `release_package.py` | `9477cecdaa6482bd823703075c3d03584f08b141cd5d73e37c760dd9cf3dfbe5` |
| `validate_release_delivery.py` | `59ef69e469a2700390ecd029b1c58864b8ece61830266fefaee66f2656096f20` |

The earlier snapshot hashes above are preserved as history. This review
made no source/helper/configuration change; only this prose addendum was
written. The separate [correction record](HELPER_REVIEW_ADDENDUM.md)
documents the generated files that motivated the fix.
