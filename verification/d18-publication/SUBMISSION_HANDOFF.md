# Palomar Submission Handoff — Theorem A and Strengthened Theorem B (`d > 17`)

Prepared on 24 November 2026. The mathematical proof and root metadata
([`formalization.yaml`](../../formalization.yaml)) are complete.

## 1. Confirmed authorship, provenance, and license

All human authorship, provenance, and licensing fields are confirmed and
recorded in the root [`formalization.yaml`](../../formalization.yaml):

| Field | Confirmed value |
|---|---|
| `project.authors` | `["Arseniy Akopyan"]` (sole human author of both the initial Lean formalization and the $d > 17$ completion) |
| `project.responsible_maintainers` | `["Arseniy Akopyan"]` |
| `project.license` and root license file | `Apache-2.0` ([`LICENSE`](../../LICENSE)) |
| Manuscript provenance | [*Sixfold Tverberg counterexamples and convex equipartition obstructions*](../../paper/manuscript.tex) by Arseniy Akopyan: Theorem A ($\Delta^{35} \to \mathbb{R}^6$, relationship: `formalizes`) and Theorem B ($d \ge 24$, relationship: `adapts`, strengthened to $d > 17$ via $\Delta^{89} \to \mathbb{R}^{16}$) |
| Earlier Lean development provenance | Initial TopTverberg Lean 4 baseline (`Solution.lean`, `RequestProject/`, and 43 modules in `AkopyanResearch/`, relationship: `adapts` in `sources` and `builds-on` in `related_formalizations`), authored by Arseniy Akopyan with AI assistance from Aristotle and Gemini; extended by the $d > 17$ completion in `AkopyanResearch/Completion/` directed by Arseniy Akopyan with AI assistance from GPT-6 Astra Pro |
| Ported upstream formalizations | `homotopy-groups-lean` (`Submission/`, Apache-2.0) and `hatcher-at` (`Hatcher/`, Apache-2.0), recorded in `sources` (`adapts`) and `related_formalizations` (`builds-on`) |
| Public repository | `https://github.com/akopjan/toptverbert-nandakumar` |

Note: [`formalization.yaml.draft`](formalization.yaml.draft) is retained only
as a historical pre-confirmation template from the automated workspace run;
the authoritative metadata file for the repository is the root
[`formalization.yaml`](../../formalization.yaml).

## 2. Comparator and toolchain summary

| Item | Value |
|---|---|
| Project name | `Sixfold Tverberg Counterexamples and Convex Equipartition Obstructions` |
| Metadata path | `formalization.yaml` |
| Comparator configuration | `comparator.json` |
| Challenge / proof entry point | `Challenge` / `PalomarSolution` |
| Compared Theorem A | `AkopyanSixfold.tverberg_counterexample` |
| Compared Theorem B ($d > 17$) | `AkopyanSixfold.convex_partition_counterexample_gt_17` |
| Supporting 90-vertex theorem | `AkopyanSixfold.almostSix_ninety` ($\Delta^{89} \to \mathbb{R}^{16}$) |
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib commit | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Classifications | arXiv `math.CO`, `math.MG`, `math.AT`; MSC2020 `52C35`, `55M20`, `52A20`, `55S91` |

## 3. Verification commands

From the repository root:

```sh
python3 verification/d18-publication/validate_metadata.py formalization.yaml --output verification/submission-metadata-validation.json
lake exe cache get
SKIP_MATHLIB_CACHE=1 bash scripts/verify.sh verification/reproduction
```
