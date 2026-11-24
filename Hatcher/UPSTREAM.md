# Singular homology source provenance

These thirty-four Lean modules are ported from [hatcher-at](https://github.com/Deicyde/hatcher-at), commit `6d729567d1573a7e8785773a55de36d0e3ec5761`, under the Apache 2.0 license. Copyright notices by Joël Riou and Jack McCarthy have been preserved. The excision files also preserve their attribution to `joelriou/excision`, commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6`. The license is included at `LICENSES/Apache-2.0.txt`.

The port targets Lean 4.35.0 and the project's pinned Mathlib. It adds module visibility declarations and exposes private helpers used by exported definitions. Three formerly private helpers in `SmallChainEquivalence` receive the prefix `smallChain_` to avoid collisions with helpers from `Devissage`. Iteration of chain endomorphisms uses the new `CategoryTheory.End` structure through `End.of` and `End.asHom`. The mathematical hypotheses and proof constructions are unchanged.

The imported results concern the actual singular-set functor and Mathlib's relative chain quotient. They provide the long exact sequence of a pair, chain homotopy equivalence for binary-cover excision, deleted-subset excision, the ordinary Mayer–Vietoris exact sequence, explicit hemisphere neighborhoods, and the relative-to-reduced homology isomorphism for good pairs. They assert no Thom isomorphism or Hurewicz comparison.

The general definitions in `Singular/GoodPair.lean` are retained in full. Its independent application to classical CW subcomplexes and the corresponding regular-neighborhood import are omitted; the project supplies its own explicit neighborhood deformation. `Singular/ReducedRelative.lean` explicitly imports the Mathlib theorem transferring degreewise short exactness to chain complexes. These dependency changes do not alter any retained theorem's hypotheses or conclusion.

Exact source and port SHA-256 hashes and per-file changes are recorded in `docs/third_party/hatcher-at/`. The original audit there covers the first twelve modules; the expanded library is also included in the complete project owner audit.
