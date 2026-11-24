# Primary-source literature and provenance review

**Review date:** 24 November 2026 (UTC).
**Scope:** the mathematical context of the supplied almost-six embedding,
the convex equipartition obstruction for \(d>17\), and the table/arrangement
completion. This is a literature and attribution review, separate from
Lean compilation, statement checks, and transitive-axiom audits.

The publication-facing synthesis and complete bibliography are in
[MATHEMATICAL_CONTEXT.md](../../docs/MATHEMATICAL_CONTEXT.md).

## 1. Supplied-source evidence

The archive inspected before the external search was
`akopyan_toptverberg_formalization_reviewed(1).zip`, SHA-256
`7537d4233d74c40aa3eddad5fd4912287810f6a78c6543dbf75cf2fe364e119b`.
It contained 96 entries. The metadata documents were `README.md`,
`FORMALIZATION_STATUS.md`, and `CHANGES.md`. No PDF, TeX or BibTeX source,
or file named as a licence, notice, or citation record, was found.

The original archive entries had these SHA-256 digests:

| File | SHA-256 |
| --- | --- |
| `Solution.lean` | `41225428eeac553dc40649334f81dbdf25414cdebf141cb1618ddcd014544d23` |
| `RequestProject/Solution.lean` | `21a44423bd69b613010d1b935e054ddcc6883aaaaeef80f0ae0fa56699465930` |
| `Challenge.lean` | `cfd2f4648eee325094309614e72c032d7822cb1c23f09e941b86c36c667cff05` |
| `README.md` | `5ea27f1ec149de5b6ad9768f1cbb329cd8a4d6304dcf821a082efa1fa5cc30f3` |
| `FORMALIZATION_STATUS.md` | `66905f76f6e4efb5f222e7a047547d0d4533e8a9dd422c0f7c8dd389876f3ff8` |

The headers of `Challenge.lean` and `Solution.lean` name Arseniy Akopyan.
Targeted searches of the original Lean and Markdown files found no
identifiable external bibliography for the proof. Comments in the top-level
solution refer to “Lemma 4.2,” “Lemma 5.2,” and “Lemma 5.3,” concerning a
rank bound, an avoidance margin, and continuity of inward distance. They
also use the unexpanded label `[AKS]`. Files in `RequestProject` refer to
“Lemma 2,” “Corollary 3,” “Lemma 4,” “Lemma 5,” and “identity (18).”
Without a title or other identifier these cannot be assigned to a
particular paper. Matching a lemma number or author initials alone is
not evidence of a source.

The later `PLANAR_COMPARISON_RESEARCH.md` contains development references;
these are not evidence that they were the sources of the original
archive. Likewise, the historical assertion in `Solution.lean` that the
ninety-vertex input remained unresolved describes an earlier stage of
this project. The separate completion declaration is the current proof
entry point. No original Lean comment was changed in this review.

## 2. Primary-source checks

ArXiv version pages were used to distinguish first submission from later
revision. Full author manuscripts were inspected for the mathematical
claims; publisher records and author publication pages were used for
bibliographic metadata. Dates below are ISO calendar dates.

| Reference | Identifier and checked version | First arXiv submission / checked revision | Specific check |
| --- | --- | --- | --- |
| Frick | [1502.00947v2](https://arxiv.org/abs/1502.00947v2) | 2015-02-01 / 2015-11-13 | Abstract's sixfold \(\Delta^{100}\to\mathbb R^{19}\) example. |
| Avvakumov–Mabillard–Skopenkov–Wagner | [1511.03501v5](https://arxiv.org/abs/1511.03501v5) | 2015-11-11 / 2018-10-16 | Bound \(q\geq2r+1\); journal publication in 2021. |
| Avvakumov–Karasev–Skopenkov | [1908.08731v4](https://arxiv.org/html/1908.08731v4) | 2019-08-23 / 2023-02-26 | Theorem 1.1's exact ceiling formula; Remark 1.2's join construction. |
| Karasev–Hubard–Aronov | [1306.2741v2](https://arxiv.org/html/1306.2741v2) | 2013-06-12 / 2017-05-06 | Theorem 1.3's prime-power assertion for body functionals and a measure. |
| Blagojević–Ziegler | [1202.5504v3](https://arxiv.org/abs/1202.5504v3), [PDF](https://arxiv.org/pdf/1202.5504) | 2012-02-24 / 2013-07-04 | Theorems 1.2–1.4, especially the whole-partition domain in Theorem 1.4. |
| Akopyan–Avvakumov–Karasev | [1804.03057v14](https://arxiv.org/html/1804.03057v14) | 2018-04-09 / 2026-03-20 | Theorem 1.1 and its following functional/measure remarks; Sections 7–8. |
| Blagojević–Sadovek | [2305.10711v2](https://arxiv.org/abs/2305.10711v2), [publisher](https://link.springer.com/article/10.1007/s11856-025-2785-3) | 2023-05-18 / 2024-08-25 | Failure of the specified iterated test-map scheme; online 2025-06-29, journal issue 2026. |

Additional records checked were Tverberg's
[1966 publisher record](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/jlms/s1-41.1.123),
Hatcher's [book page](https://pi.math.cornell.edu/~hatcher/AT/ATpage.html)
and [Chapter 4](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf), and the
[publisher record for Ziegler–Živaljević](https://link.springer.com/article/10.1007/BF01444901).
The latter article is from 1993. A later digitization date is not its
publication date. The same distinction applies to the 1966 Tverberg paper.

## 3. Scope and outcome of the search

Searches combined the names Akopyan, Avvakumov, Karasev, Frick, and
Tverberg with the terms “almost 6 embedding,” “simplex 35,” “R6,”
“dimension 18,” “continuous functionals,” “convex equipartitions,”
“counterexample,” and “height table.” Recent-year searches included
2025 and 2026. Results were checked against primary papers and official
author or publisher pages. Search snippets and secondary summaries were
not used as proof of the mathematical statements in the context note.

[Akopyan's publication page](https://users.mccme.ru/akopyan/papers.html)
was also inspected. Neither that page nor the reviewed papers supplied
an identifiable publication for the exact almost-six map
\(\Delta^{35}\to\mathbb R^6\), the exact \(d>17\) obstruction for
individual-body functionals, or the present quadratic table/arrangement
argument. This negative finding is limited to the search performed.
It does not establish novelty, priority, or the absence of an unpublished
manuscript or a differently described published proof.

The distinctions most relevant to publication are:

- The numerical comparison is with the specific theorems checked. It is
  not a claim that their bounds are optimal or the latest available.
- A failure of a configuration-space/test-map scheme does not itself
  produce the project's functional \(\Phi:\mathcal K_d\to\mathbb R^{d-1}\).
- A function of the whole partition is not automatically an evaluation
  of a fixed functional on its individual bodies.
- The planar positive result for one arbitrary continuous functional
  does not settle simultaneous equalization of \(d-1\) functionals in
  the dimensions considered here.

## 4. Attribution decisions

The verified publication authors are named only for their cited papers.
The original archive's author header is reported as supplied metadata;
it is not used to identify the uploader, assign authorship of later
changes, establish permission to publish, or choose an original-project
licence. No author or maintainer was contacted during this review.

The imported Lean developments have their own pinned-source and licence
records under `docs/third_party` and `Submission/UPSTREAM.md`. This
review does not alter those records or extend their licences to the
original project. Conceptual mathematical background, copied code
provenance, and authorship of the present construction are separate
questions.

The resulting context note can accompany the formalization without
claiming an externally verified source or author for the supplied new
proof. Any publication metadata asserting such attribution or novelty
requires evidence beyond the archive and search documented here.
