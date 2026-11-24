# Source delivery and patch verification

The source patch was applied to a fresh copy of the supplied original tree.
Both `git apply --check` and `git apply` returned exit code 0. All **151**
resulting source, configuration, script, test and documentation files match
the final working tree byte-for-byte, including executable modes. The original
`Challenge.lean` and `Solution.lean` remain byte-for-byte unchanged.

Patch SHA-256: `433357066c8949fee8c373a1501bf844d6cc4f95e19298f85f62ad50b7763749`.
Patch size: 626847 bytes. Detailed evidence: `patch-validation.json`.
Verification logs and publication drafts are distributed in the ZIP and are
intentionally excluded from this source patch.

All **145** inputs of the successful final 132-module working and staged
checks still match their recorded hashes. The source bundle excludes runtime
caches, compiled objects and large kernel-export data. It includes the complete
Lean source project, pinned dependency manifest, verification scripts, reports,
publication preparation documents, and checksums for every bundled file.

## Reproduce the source patch

From a parent directory holding the original and updated source trees:

```sh
python3 akopyan-completion/verification/release/patch-used.py \
  original-reviewed akopyan-completion akopyan_formalization_updated.patch
python3 akopyan-completion/verification/release/validate-delivery-used.py patch \
  --source akopyan-completion --original original-reviewed \
  --patch akopyan_formalization_updated.patch --checkout patch-check \
  --output patch-validation.json
```

The patch-check destination must not already exist. Directory names in these
commands may be replaced by the actual extraction paths.

## Reproduce the ZIP and verify its contents

```sh
python3 akopyan-completion/verification/release/package-used.py \
  akopyan-completion akopyan_formalization_updated.zip
python3 akopyan-completion/verification/release/validate-delivery-used.py archive \
  --source akopyan-completion --archive akopyan_formalization_updated.zip \
  --output archive-validation.json
```

The generated inventory records its own creation time, so rebuilding reproduces
source contents and per-file hashes, not necessarily the identical ZIP hash.
The final ZIP hash and the actual archive validation outcome are reported in
the separately delivered status document; a ZIP cannot contain its own hash.

## Mathematical scope

The verified unconditional theorems are A and B for d ≥ 36. The new d > 17
reduction still explicitly assumes `ConcreteComparison.RequiredRelativeLifting`.
The final archive is a compiling, audited source project, **not a completed
unconditional formalization of the requested d > 17 theorem**. Full official
Comparator acceptance and registry publication are not claimed.
