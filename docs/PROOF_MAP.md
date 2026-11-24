# Proof map for reviewers

Start with [PalomarSolution.lean](../PalomarSolution.lean), which exports
Theorem A from [Solution.lean](../Solution.lean) and the unconditional
dimension-eighteen conclusion from
[Completion/DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean).
The independent statements are in [Challenge.lean](../Challenge.lean).

## Scope of the module counts

| Scope | Project modules | Meaning |
| --- | ---: | --- |
| Publication entry point | **418** | Actual compiled import closure of `PalomarSolution`; excludes `Challenge`. |
| Independent compiled comparison | **419** | The preceding closure together with the separately inspected `Challenge`. |
| Complete owner audit | **438** | Every project proof-module owner, including auxiliary and historical modules; excludes `Challenge`. |
| Complete source inventory | **439** | All audited sources together with `Challenge`. |

These counts come from the
[compiled-interface record](../verification/d18-compiled-interface/results.json)
and the [complete audit record](../verification/d18-final-retry/results.json).
An import closure is not a minimal proof-term dependency count.

## Objects used below

Let `S : Finset (Fin 15)` be nonempty. Let \(Y_S\) be the space
`QuadComplement S`, the complement of the matching-equality subspaces in the
space of quadratic planar tables. Let \(P_S\) be
`ConcreteComparisonTarget.Space S`, the space of normalized matching tests
and compatible pair paths. The continuous map \(c_S:Y_S\to P_S\) is the literal
`ConcreteComparison.comparisonMap S hS`; its pair-path coordinates are
constant at infinity. Its naturality under face inclusion is proved in the
[same module](../AkopyanResearch/Completion/ConcreteComparison.lean).

Let \(I_S\) be the finite type `MatchingIndex S`, and let \(E_S\) be the finite
type `CriticalPairIndex S`. Let \(B\) be the local product space,
homeomorphic to \(S^9\times S^9\), and let \(q:B\to S^{13}\) be its
collapse map. Let \(D\subset B\) be the collapsed locus, and let
\(P_{\mathrm{loc}}\) be the homotopy fibre of \(q\) over infinity. All homology groups
below have integral coefficients. `Hgrp` is ordinary singular homology;
`HrelSet` is relative singular homology of the stated subset pair.

## Twenty interfaces carrying the argument

Names without an explicit top-level namespace below belong to
`AkopyanResearch`. Links identify the owning source files. The displayed
types are mathematical summaries of their actual declarations.

### A. Original theorem and homology of the comparison

| # | Exact interface | Owner | Input → output |
| ---: | --- | --- | --- |
| 1 | `AkopyanSixfold.tverberg_counterexample` | [Solution.lean](../Solution.lean) | No theorem hypothesis → an almost-six embedding \(\Delta^{35}\to\mathbb R^6\), obtained from the proved `Tverberg6R` height extension. |
| 2 | `QuadraticSourceCoordinates.singleCoordinatesIso` | [Completion/QuadraticSourceCoordinates.lean](../AkopyanResearch/Completion/QuadraticSourceCoordinates.lean) | `S.Nonempty` → \(H_9(Y_S)\cong\prod_{I_S}H_9(S^9)\), through the original normalized matching tests. |
| 3 | `QuadraticSourceCoordinates.collapsedCoordinatesIso` | [Completion/QuadraticSourceCoordinates.lean](../AkopyanResearch/Completion/QuadraticSourceCoordinates.lean) | `S.Nonempty` → \(H_{12}(Y_S)\cong\prod_{E_S}H_{12}(D)\), through the original normalized critical-pair tests. |
| 4 | `QuadraticComplementHomology.originalComplement_homology_zero` | [Completion/QuadraticComplementHomology.lean](../AkopyanResearch/Completion/QuadraticComplementHomology.lean) | \(1\le k\le13\), \(k\ne9,12\) → \(H_k(Y_S)=0\). In particular, \(H_{13}(Y_S)=0\). |
| 5 | `FirstHomologyComparison.targetProjection_isIso` | [Completion/FirstHomologyComparison.lean](../AkopyanResearch/Completion/FirstHomologyComparison.lean) | The actual projection \(P_S\to(S^9)^{I_S}\) → its induced map on \(H_9\) is an isomorphism. |
| 6 | `TargetPairCoordinates.homologyCoordinatesIso` | [Completion/TargetPairCoordinates.lean](../AkopyanResearch/Completion/TargetPairCoordinates.lean) | `S.Nonempty` → \(H_{12}(P_S)\cong\prod_{E_S}H_{12}(P_{\mathrm{loc}})\), induced by the literal pair/path projections. |
| 7 | `PairEndpointHomology.collapsedInclusion_isIso` | [Completion/PairEndpointHomology.lean](../AkopyanResearch/Completion/PairEndpointHomology.lean) | The original inclusion of \(D\) into the actual mapping-path fibre → an isomorphism on \(H_{12}\). The recorded fibre homeomorphism transports this map to \(P_{\mathrm{loc}}\). |
| 8 | `ConcreteComparisonHomology.homology_isIso` | [Completion/ConcreteComparisonHomology.lean](../AkopyanResearch/Completion/ConcreteComparisonHomology.lean) | \(0\le i\le13\) → the actual map \(H_i(c_S)\) is an isomorphism. |
| 9 | `ConcreteComparisonHomology.homology_epi` | [Completion/ConcreteComparisonHomology.lean](../AkopyanResearch/Completion/ConcreteComparisonHomology.lean) | \(0\le i\le14\) → the actual map \(H_i(c_S)\) is surjective. |
| 10 | `ConcreteComparisonHomology.cylinder_hrelSet_zero` | [Completion/ConcreteComparisonHomology.lean](../AkopyanResearch/Completion/ConcreteComparisonHomology.lean) | \(1\le i\le14\) → \(H_i(\operatorname{MapCyl}(c_S),\operatorname{top}(c_S))=0\). |

The `_apply` lemmas beside interfaces 2–3 identify every component with the
induced map of the stated continuous test. The strict coordinate squares in
[ConcreteComparisonCoordinates.lean](../AkopyanResearch/Completion/ConcreteComparisonCoordinates.lean)
then identify \(H_9(c_S)\) and \(H_{12}(c_S)\). Thus the comparison uses actual
maps, including the reversed pair-path coordinate, rather than a choice of
abstract bases.

For the source calculations, follow
[QuadraticDeletion.lean](../AkopyanResearch/Completion/QuadraticDeletion.lean),
[NormedLinearThom.lean](../AkopyanResearch/Completion/NormedLinearThom.lean),
and [QuadraticPairHomology.lean](../AkopyanResearch/Completion/QuadraticPairHomology.lean).
They assemble finite Mayer–Vietoris calculations using actual linear tubular
pairs. The local endpoint argument in interface 7 uses the genuine based-path
Serre fibration and the computed cyclic relative groups in degree thirteen.

At degree fourteen, only \(H_{14}(P_S)=0\) is needed for interface 9.
The proof makes no assertion that \(H_{14}(Y_S)=0\). The relative long exact
sequence gives interface 10, and the natural chain comparison transfers it
to the `HrelSet` used by relative Hurewicz.

### B. Relative connectivity, exact lifting, and the final construction

| # | Exact interface | Owner | Input → output |
| ---: | --- | --- | --- |
| 11 | `UniversalSimplexAddition.relativeHurewicz_injective` | [Completion/UniversalSimplexAddition.lean](../AkopyanResearch/Completion/UniversalSimplexAddition.lean) | A pair \((X,A)\) that is \((n+2)\)-connected, with path-connected and simply connected \(A\) → injectivity of its first relative Hurewicz map in degree \(n+3\). |
| 12 | `RelativeHomologyConnectivity.fourteen` | [Completion/RelativeHomologyConnectivity.lean](../AkopyanResearch/Completion/RelativeHomologyConnectivity.lean) | \(X\) and \(A\) eight-connected, and \(H_k(X,A)=0\) for \(9\le k\le14\) → the same pair is fourteen-connected. |
| 13 | `ConcreteComparisonConnectivity.cylinder_pair_fourteen` | [Completion/ConcreteComparisonConnectivity.lean](../AkopyanResearch/Completion/ConcreteComparisonConnectivity.lean) | `S.Nonempty` → the actual pair \((\operatorname{MapCyl}(c_S),\operatorname{top}(c_S))\) is fourteen-connected. |
| 14 | `MappingCylinderFaceLifting.extend` | [Completion/MappingCylinderFaceLifting.lean](../AkopyanResearch/Completion/MappingCylinderFaceLifting.lean) | A path-connected source \(X\), an \(N\)-connected mapping-cylinder pair, and a face of dimension at most \(N\) → extensions of a prescribed boundary map and its prescribed boundary homotopy, with literal boundary equalities and the required endpoints. |
| 15 | `ConcreteComparisonLifting.requiredRelativeLifting` | [Completion/ConcreteComparisonLifting.lean](../AkopyanResearch/Completion/ConcreteComparisonLifting.lean) | No hypothesis → `ConcreteComparison.RequiredRelativeLifting` for the original comparison and chosen section. |
| 16 | `ConcreteComparison.exists_safe_table_of_required_lifting` | [Completion/ConcreteComparison.lean](../AkopyanResearch/Completion/ConcreteComparison.lean) | The proved relative lifting property → a continuous planar quadratic table, compatible when a color mass vanishes and safe for every matching. |
| 17 | `exists_almostSix_of_safe_compatible_quadratic_table` | [SafeQuadraticRealization.lean](../AkopyanResearch/SafeQuadraticRealization.lean) | Such a table on fifteen colors → a continuous almost-six embedding \(\Delta^{89}\to\mathbb R^{16}\). |
| 18 | `AkopyanSixfold.almostSix_ninety` | [Completion/DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean) | No hypothesis → the ninety-vertex almost-six embedding in the original `IsAlmostSixEmbedding` interface. |
| 19 | `AkopyanSixfold.convex_partition_counterexample_ge_18` | [Solution.lean](../Solution.lean) | \(d\ge18\) and a ninety-vertex almost-six embedding → continuous functionals on convex bodies and an absolutely continuous probability measure obstructing convex six-equipartition. |
| 20 | `AkopyanSixfold.convex_partition_counterexample_gt_17` | [Completion/DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean) | Only `d : ℕ` and `17 < d` → the full unconditional conclusion specified in `Challenge`. |

Interface 11 proves the alternating face relation in a universal
simplex/skeleton pair and transports it by naturality. Interface 12 applies
the resulting relative Hurewicz step successively in degrees 9–14. The actual
mapping cylinder and its top are already eight-connected. Finally,
`S.card - 1 ≤ 14` supplies the precise face-dimension bound for interface 15;
both the boundary map and the entire prescribed boundary homotopy are
preserved by the extension.

Interface 16 supplies all hypotheses of interface 17. Interface 19 uses the
proved blocking-marker construction and padding to transfer interface 18
to every \(d\ge18\). The conditional lemmas are therefore internal composition
steps; neither the table nor the lifting property remains a hypothesis of
interface 20.

## Historical modules and further reading

Twenty audited modules lie outside the publication import closure. They
include the aggregate/audit entry points, earlier generic table-realization
bridges, and alternative geometric work such as
[EquivariantPinch64.lean](../AkopyanResearch/EquivariantPinch64.lean) and
[PairLocalConnectivity.lean](../AkopyanResearch/Completion/PairLocalConnectivity.lean).
They remain in the complete owner audit but are not imported by
`PalomarSolution`. The exact sets are recorded in the linked JSON inventories.

The unchanged `Solution.lean` also retains the earlier unconditional
\(d\ge36\) theorem and comments describing the former ninety-vertex gap.
The current resolution is interfaces 15–20 above. For the mathematical
argument, see [DIMENSION_EIGHTEEN_PROOF.md](DIMENSION_EIGHTEEN_PROOF.md).
For independent checks of the statements' meaning, see
[SEMANTIC_SCOPE_REVIEW.md](../verification/d18-extension-2026-11-24/SEMANTIC_SCOPE_REVIEW.md).
Build, axiom-audit, exported-body kernel checks and the independent interface
comparison have separate records under `verification/`; the scope of each
check is stated in its record.
