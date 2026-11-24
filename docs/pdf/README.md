# Rebuilding the mathematical companion

The source is [PROOF_COMPANION.md](../PROOF_COMPANION.md). The release PDF is
included at `verification/d18-release/akopyan_d18_proof_companion.pdf` and
also provided separately. It explains the complete
proof and records the verification boundary; it does not replace the Lean
sources or certify Palomar registration.

From the project root, with Python 3.12 and Pandoc installed:

```sh
python3 -m venv .venv-pdf
.venv-pdf/bin/python -m pip install -r docs/pdf/requirements.txt
.venv-pdf/bin/python docs/pdf/build_companion.py \
  --output ../akopyan_d18_proof_companion.pdf \
  --report ../akopyan_d18_pdf_build.json
```

The release used Pandoc 3.1.11.1. The Python dependencies are pinned in
`requirements.txt`. No TeX installation, external font download, or network
access is needed during rendering. The default source path is resolved from
the renderer's location; an alternative can be passed with `--source`.

ReportLab typesets the prose. Matplotlib parses the mathematics, and the
renderer places its glyphs and rules directly into the PDF as vector content.
TrueType font subsets are embedded. The font files are supplied by Matplotlib;
the DejaVu, STIX and BaKoMa licence notices are retained in this directory. Their
individual hashes appear in the build report. A fixed document date makes the
output reproducible for the same source and dependency versions.

For visual inspection, render every page:

```sh
mkdir -p ../companion-pages
pdftoppm -png -scale-to 1400 ../akopyan_d18_proof_companion.pdf \
  ../companion-pages/page
```

The final release records its actual source, renderer and PDF hashes in
`verification/d18-release/PDF_BUILD.json`, together with the visual review in
`verification/d18-release/PDF_REVIEW.md`. The binary PDF copy is outside the
text patch's scope; its source and renderer are included in the patch.
Build/render intermediates and fonts
are not added to the source archive. This renderer is documentation tooling;
it is not imported by Lean and has no role in the proof verification.
