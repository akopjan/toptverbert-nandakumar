# Delivery completeness review

Reviewed on 24 November 2026. Scope: independent read-only review of
`release_package.py`, `release_diff.py` and `validate_release_delivery.py`,
the current release selection, and the documented reproduction entry points.
No proof source, configuration, packaging helper or verification script was
changed. No Lean build or kernel check was repeated.

**Finding:** no remaining blocking packaging defect was found in the current
tree. Actual patch application and final ZIP validation remain separate
release steps. This review does not certify a not-yet-created archive or
claim Palomar registry acceptance.

## Content and exclusions

- The selection retains all project Lean sources, Lake configuration,
  dependency manifest, Comparator configuration, checking scripts, tests,
  workflows, mathematical documentation and publication records. A focused
  inventory check found none of the required entry points, thirteen vendor
  provenance manifests, vendor licence texts, four final evidence reports,
  or original-specification inputs missing from the selection.
- Excluding `.lake`, compiled objects, native libraries, temporary directories
  and Python caches is appropriate for a source release. External Git
  dependencies are restored from their manifest pins; the vendored
  `Submission` and `Hatcher` source trees remain in the archive.
- Large generated `.ndjson` exports are deliberately omitted. Their exact
  hashes, sizes, selected declaration bodies, tool hashes and checker outcomes
  are retained, together with the source-driven export command. The small
  local control exports end in `.ndjson.txt` and remain included.
- Existing release inventories and checksum files are excluded and regenerated
  for the exact new payload. Checkpoint markers are excluded; a verified
  archive is rejected by the delivery validator if such a marker appears.
- The snapshot inspected here selected 1,076 files and 25,979,121 bytes, before
  this review and the remaining publication additions. These are review
  counts, not promised final archive counts.

## Patch applicability and the PDF

The diff and patch-validator inventories agree: they retain source,
configuration, scripts, tests and documentation, plus
`verification/original-specification`. Generated verification records are
distributed in the ZIP rather than repeated in the patch. The original
specification is necessary for the checking scripts, so its explicit inclusion
is material.

The patch records additions, deletions, content changes and executable-mode
changes. Validation first runs `git apply --check`, then actually applies the
patch to a fresh copy of the original inventory and compares every resulting
file's bytes and executable flag with the final source inventory. The caller
must use the extraction of the supplied reviewed archive, whose SHA-256 is
`7537d4233d74c40aa3eddad5fd4912287810f6a78c6543dbf75cf2fe364e119b`;
the helper does not authenticate an arbitrary supplied original directory.

The diff generator accepts UTF-8 text with final newlines. A PDF under the
patched source tree would fail that check. The release owner confirmed that
the final PDF is a separate deliverable; only its Markdown source, renderer,
requirements and README will be placed under `docs/pdf`. No binary font or
image assets are planned there. This resolves the identified placement
constraint without changing the helpers. Those forthcoming documentation
files were not yet present at this review snapshot.

## Reproduction, pins and licences

The essential `scripts/` entry points derive the repository from their own
location and locate Lean tools through the selected toolchain. No fixed
private workspace path was found in those entry points. The approved con-ron
replay accepts checker, export and prior-report paths as arguments.
Its historical acquisition script retains its original absolute manifest
path, explicitly documented as historical evidence; it is not an essential
build or replay entry point.

`lean-toolchain` fixes Lean 4.35.0. `lake-manifest.json` fixes all nine Git
dependencies to full commits, including Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The build script does not run
`lake update`. Vendor provenance records retain upstream commits and exact
ported-source hashes, with their Apache-2.0 licence texts. The user's original
project licence and human submission metadata remain unconfirmed; the
publication documentation identifies these administrative prerequisites.
The source ZIP is not advertised as an offline bundle or an accepted
Palomar submission.

## Meaning of the verified release flag

The packaging guard requires successful main and clean six-stage gates,
unchanged inputs and identical input snapshots. It also requires all three
bundled kernel checks to succeed on actual exported theorem bodies for all
four selected final declarations, and the independent compiled-interface
comparison to report nine matching types and seven matching definition
bodies with separate imports.

It then rehashes the bound source/configuration/report inputs, compares the
actual ZIP payload against those hashes, and requires exact equality between
the packaged proof-module inventory and the verified inventory. The final
archive validator checks CRCs, regular safe member paths, unique members,
exact checksum coverage, evidence-report hashes, source bytes and permissions.
Supplemental approved con-ron evidence is retained without being confused
with the full registry workflow.

## Final release checklist

- [x] Required build, provenance, licence and publication files survive the
  source selection.
- [x] Patch and archive scopes are explicit; original-specification inputs
  survive both.
- [x] Required reproduction commands use relocatable entry points.
- [x] Final-release claims are bound to successful, unchanged proof evidence.
- [ ] Freeze the remaining publication text and include final helper copies
  and their hashes.
- [ ] Generate the patch against the authenticated original extraction;
  run its actual fresh-checkout application and equality validation.
- [ ] Create the archive with `--verified-d18` and run final archive validation
  after the last source/documentation edit.
- [ ] Record final ZIP, patch and separate PDF hashes; deliver those actual
  artifacts together with their validation results.

## Reviewed helper hashes

| Helper | SHA-256 |
| --- | --- |
| `release_package.py` | `f4d8d07af52d0ff4ef251549aa3fd6c658871a0da2310e117376a4490522ed0e` |
| `release_diff.py` | `b32ee313b013f1203262854a37c960d3dc33dc146744a867f2860b47ae941d8c` |
| `validate_release_delivery.py` | `e9a7967ad11323aff7a1aceba03e63e43608faf0fa7a89c774293b535236a688` |
