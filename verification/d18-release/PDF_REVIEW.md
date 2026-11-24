# Final companion PDF review

The delivered companion is `akopyan_d18_proof_companion.pdf`, generated from
`docs/PROOF_COMPANION.md` by `docs/pdf/build_companion.py`. It is provided as a
separate file and as an identical copy in this directory. The source archive
contains that reviewed PDF, the complete Markdown source, renderer, pinned
Python dependencies and font licence notices. The binary PDF is outside
the text patch's scope.

## Actual final artifact

- Pages: **15**.
- Size: **252,932 bytes**.
- PDF SHA-256: `22ce661902a89863283eacfd8d1abd64940e2aa0c22e89200442b1aec65585f2`.
- Source SHA-256: `5e5d03e152eb843f3106649d7c86366dbdb944f395bedfbaa7c5f22a5a8ed158`.
- Renderer SHA-256: `636802069af5a25eb6be96dcea8be73ad3df2266ee311dac2527651533b850f6`.

The full rendering record, including the individual font hashes and 381
distinct formula renderings, is in `PDF_BUILD.json`. The final structural
inspection and byte comparison are in `PDF_QA.json`.

## Visual and structural checks

Every page of the final fifteen-page PDF was rendered with Poppler at a maximum
dimension of 1,400 pixels and visually inspected. The inspection covered
body text, inline and displayed formulae, subscripts and superscripts, page
breaks, long declaration names, footers and all bibliography entries. No
clipped text, overlapping lines or unreadable formulae were observed. The
last page contains the remaining three references and intentional white
space; there is no empty page.

Earlier layout defects were corrected before this final rendering: a tall
inline summation at the beginning of a line needed its actual ascent and
descent included in the line height; reference entries needed hanging
paragraphs instead of the renderer's generic list fallback; and a publication
year was parenthesized to avoid accidental Markdown list parsing.

The final PDF has no glyph bounding boxes outside the page bounds, no raster
images on any page, and embedded TrueType subsets for every font having a
font descriptor. Mathematics consists of native vector glyphs and rules.
The title and fixed publication date in the PDF metadata are correct. The
author field is deliberately empty because human authorship of the completed
release has not been confirmed.

## Reproduction and scope

The documented renderer was run again on the final source, with a distinct
output and build report. The resulting PDF is **byte-identical** to the
delivery artifact, with the same SHA-256 above. This checks reproduction with
the recorded versions, not arbitrary future dependency or font versions.

The exposition states the unconditional `d > 17` theorem and explains the
arrangement calculation, actual comparison map, target section, relative
Hurewicz step, exact boundary lifting, table realization, marker dimension
count and convex-body functional. It distinguishes the final quadratic
realization from the general averaging construction, handles zero masses and
degenerate convex bodies, and records the genuine local verification results.
It also explicitly records that the sandboxed Comparator stopped during
setup, the official registry workflow has not run, and publication metadata
still requires confirmed human identities, licence and repository details.

This is an automated documentation and rendering review, not external human
peer review or a replacement for the Lean proof checks.
