# Final companion review: sections 4–8

Reviewed the final `docs/PROOF_COMPANION.md` against the actual source
definitions and theorem arguments for the local comparison, chosen target
section, relative Hurewicz induction, exact boundary lifting, and table
realization. No mathematical correction was required. The companion and
its rendered PDF were not edited; no build or kernel check was rerun.

Companion SHA256: `5e5d03e152eb843f3106649d7c86366dbdb944f395bedfbaa7c5f22a5a8ed158`.

This addendum records the later, expanded companion snapshot. It does not
replace the earlier documentation review or the separate formal verification
evidence. It makes no claim about publication novelty or Palomar acceptance.

## Findings

**Local comparison.** The map of pairs goes from the original collapsed
pair to the mapping-path pair and then to the pointed thirteen-sphere.
Its composite is the original collapse. The fixed-source path-pair
inclusion induces an isomorphism on relative \(H_{13}\). For the endpoint
map, Serre lifting and Hurewicz supply surjectivity; both relative integral
groups are isomorphic to \(\mathbb Z\). Primitivity is consequently proved,
not assumed. Naturality of the boundary gives the actual
\(H_{12}(D_e)\to H_{12}(F_e)\) isomorphism. Reversal between the two path
models is implemented by a homeomorphism, and constant paths remain
constant. The global comparison is an isomorphism through degree thirteen
and an epimorphism in degree fourteen. Only target \(H_{14}\)-vanishing is
used.

**Chosen section.** The supplied nullhomotopy of \(q_0\) is ordinary, not
equivariant. The displayed join formula produces equivariance, and the
full block subgroup fixes the anchor used in the propagated contraction.
The right-row convention includes the inverse permutation. Both pure
phases give constant infinity paths. Every face uses the same fifteen-fold
join stage. Changing zero-mass labels has no effect, and naturality on
faces is equality of the complete paths, not merely their homotopy classes.
The section requires no comparison-lifting hypothesis.

**Relative connectivity and exact extension.** In the universal relation,
\(m=n+3\), the ambient simplex has dimension \(m+1\), and its
\((m-1)\)-skeleton is \((m-2)\)-connected. The retraction uses the positive
part after subtracting the second-smallest coordinate. The source is
simply connected; the pair starts eight-connected. The six Hurewicz steps
use degrees nine through fourteen. The generic lifting theorem also
requires a path-connected source, supplied by the concrete eight-connected
source. Its conclusion preserves the entire given boundary homotopy,
including both endpoints. The face dimension is \(|S|-1\le14\), with
singleton faces included.

**Realization.** The general compatible-table construction uses quotient
descent, not continuity of conditional distributions at zero masses.
Disjoint equal-mass rows force one label per active color; zero-mass
blocks vanish. The final theorem uses the quadratic bridge. Its 2701
features per coordinate have factors \(1,z_i,z_i z_k\); coefficients are
regularized by \(a/\max(\delta,p)\), with positive \(\delta\), and finite
matching tests remain nonzero by uniform stability. Removing the common
constant preserves safety. The direct polynomial-in-vertex-coordinates
formula and the simplex retraction give global continuity. The generic
map omits \(z_0\), while `quadraticMapNinety` omits \(z_{14}\); the text
correctly distinguishes them. The unconditional lifting theorem discharges
the only remaining input to the ninety-vertex construction.

## Principal checked interfaces

Paths below are relative to `AkopyanResearch/`; namespace prefixes are
shown when needed.

| Step | Source interfaces inspected |
| --- | --- |
| Local primitive maps | `Completion/PairCollapseHomology.lean`: `originalPairMap_homology_isIso`; `Completion/FibrationRelativeHomology.lean`: `fibrePairMap_homology_surjective`, `fibrePairMap_homology_isIso`; `Completion/LocalPairPathHomology.lean`: `basedPairInclusion_isIso`; `Completion/PairEndpointHomology.lean`: `collapsedInclusion_isIso`. |
| Actual global coordinates | `Completion/TargetPairCoordinates.lean`: `coordinate`, `homologyCoordinatesIso`; `Completion/ConcreteComparisonCoordinates.lean`: `collapsedInclusion_factor`, `pair_square`; `Completion/ConcreteComparisonHomology.lean`: `homology_isIso`, `homology_epi`, `cylinder_hrelSet_zero`. |
| Chosen section and faces | `Completion/OriginalJoinBridge.lean`: `exists_fifteen_join_map_with_block_nullhomotopy`; `Completion/OriginalPairPath.lean`: `pairPath_start`, `pairPath_finish`, `pairPath_pure`; `Completion/ChosenTargetSections.lean`: `pairSection_congr_of_support`; `Completion/ConcreteComparisonTarget.lean`: `chosen_relations`, `sectionMap_natural`. |
| Connectivity and exact lifting | `Completion/UniversalSimplexAddition.lean`: `universal_relation`, `relativeHurewicz_injective`; `Completion/RelativeHomologyConnectivity.lean`: `fourteen`; `Completion/MappingCylinderFaceLifting.lean`: `extend`; `Completion/ConcreteComparisonLifting.lean`: `requiredRelativeLifting`. |
| General and quadratic realization | `Completion/TableRealization.lean`: `project_isQuotientMap`, `exists_continuous_height`, `realized_height_separates`; `CanonicalExtraction.lean`: `quadratic_finrank_fifteen`; `SafeQuadraticBridge.lean`: `exists_safe_factored_quadratic_coefficients`; `SafeQuadraticRealization.lean`: `certificateFromFeatures_evaluation`; `QuadraticRealization.lean`: `quadraticHeight_pureColorPoint`, `quadraticMapNinety`, `exists_almostSix_of_simplex_quadratic_certificate`. |
| Final discharge | `Completion/ConcreteComparison.lean`: `exists_safe_table_of_required_lifting`; `Completion/ConcreteReduction.lean`: `AkopyanSixfold.almostSix_ninety_of_relative_lifting`; `Completion/DimensionEighteen.lean`: `AkopyanSixfold.almostSix_ninety`. |

Recorded at 2026-11-24 09:55:43 UTC by read-only source inspection, followed only by
creation of this addendum.
