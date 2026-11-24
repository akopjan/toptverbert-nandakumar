# Mathematical documentation review

## Scope and conclusion

Reviewed the current DIMENSION_EIGHTEEN_PROOF.md, PROOF_MAP.md,
GEOMETRIC_MARKERS.md, GEOMETRIC_FUNCTIONAL.md, and the combined
PROOF_COMPANION.md against the actual source declarations and the relevant
proof constructions. The review was read-only for Lean, scripts, and
configuration. No build or kernel check was rerun.

No remaining inconsistency was found in the stated dimension bounds,
homology ranges, local-to-global comparison, or final theorem scope.
The changes below correct omissions and notation in the exposition.
This review checks the explanations against their implementation; the
separate recorded build, axiom audit, interface comparison, and kernel
checks remain the evidence for formal acceptance.

## Corrections made

1. **Generic lifting hypothesis.** PROOF_MAP interface 14 now explicitly
   requires a path-connected source \(X\). This is the actual
   `[PathConnectedSpace X]` argument of
   `MappingCylinderFaceLifting.extend`, in addition to connectivity of
   the mapping-cylinder pair. The concrete source is eight-connected,
   so the final application already supplies this assumption.

2. **Skeleton retraction formula.** DIMENSION_EIGHTEEN_PROOF and
   PROOF_COMPANION now state that subtracting the second-smallest
   barycentric coordinate is followed by replacing negative coordinates
   by zero and then renormalizing. The source definition is
   `SimplexSkeletonRetraction.weight`:
   \(w_i=\max(p_i-\operatorname{second}(p),0)\).
   Omitting the positive-part operation gave an incomplete geometric
   description of the actual retraction.

3. **Domain of the compactness function.** In GEOMETRIC_FUNCTIONAL and
   PROOF_COMPANION, \(\rho\) is now defined on the entire six-body space
   \(\mathcal K_d^6\). Its positive minimum is taken over the compact bad
   family \(\mathcal F\). A partition meeting the inner ball then has
   \(\rho<\min_{\mathcal F}\rho\) and is excluded from that family.
   Previously the declared domain was only \(\mathcal F\), while a later
   sentence evaluated the function on an arbitrary partition.

4. **Literal deletion set.** The main proof note and companion now give
   the implementation's definition of \(Z\): all atom intersections
   of scalar rank at least eight, equivalently codimension at least
   sixteen. The existing pair/triple description is retained as the
   consequence of the checked rank bounds. The connectivity argument is
   described as finite-dimensional general position.

5. **Object and statement scope.** Central coverage in
   GEOMETRIC_FUNCTIONAL now explicitly means union equal to \(B\).
   The later geometric construction fixes a blocking family rather than
   leaving its choice implicit. The companion identifies \(B=B_d\),
   introduces its inner ball as a subset of \(V\), and uses the canonical
   point of the implemented local path construction. The inward-distance
   argument explicitly introduces both bodies and its separating vectors.

GEOMETRIC_MARKERS required no further change during this review.
None of these corrections changes a proof declaration or a theorem
hypothesis in the formal project.

## Checked declaration groups

| Mathematical step | Source declarations inspected |
| --- | --- |
| Exact final scope and geometric transfer | `AkopyanSixfold.almostSix_ninety` and `convex_partition_counterexample_gt_17` in Completion/DimensionEighteen.lean; `IsAlmostSixEmbedding`, `IsBlocking`, `IsSixPartition`, `convex_partition_of_embedding_and_blocking`, and `convex_partition_counterexample_ge_18` in Solution.lean. |
| Arrangement and deletion dimensions | `codim_L_M_eq_ten`, `codim_L_M_inf_two_ge_fourteen`, `codim_L_M_inf_three_ge_eighteen`; Completion/QuadraticPairRank; `DeletedIndex`, `deletedFlat_codim`, `deletedFlat_in_atom_codim`, `deletedFlat_in_critical_pair_codim`, and the connectivity and no-three-atoms lemmas in Completion/QuadraticDeletion.lean. |
| Actual source homology | `NormedLinearThom.relativeThomIso`; `QuadraticStratumHomology.atomRelativeThomIso` and `criticalRelativeThomIso`; `QuadraticSourceCoordinates.singleCoordinatesIso` and `collapsedCoordinatesIso`; `QuadraticComplementHomology.originalComplement_homology_zero`. |
| Target, local primitive map, and global comparison | `TargetHighHomology.homology_vanish` and `TargetPairCoordinates.homologyCoordinatesIso`; `PairCollapseHomology.originalPairMap_homology_isIso`; `LocalPairPathHomology.basedPairInclusion_isIso`; `FibrationRelativeHomology.fibrePairMap_homology_surjective`; `PairEndpointHomology.collapsedInclusion_isIso`; `ConcreteComparisonHomology.homology_isIso`, `homology_epi`, and `cylinder_hrelSet_zero`. |
| Relative homotopy and exact lifting | `SimplexSkeletonRetraction.weight`; `SimplexSkeletonConnectivity.isNConnected_skeleton`; `UniversalSimplexAddition.universal_relation` and `relativeHurewicz_injective`; `RelativeHomologyConnectivity.fourteen`; `MappingCylinderFaceLifting.extend` and `ConcreteComparisonLifting.requiredRelativeLifting`. |
| Blocking markers | Solution.lean: `central_partition_normal_rank`, `separating_normals_in_rref4_span`, `rank5_triangle_dependent`, `exists_treeParam`, `card_paramIdx_bound`, `ticket_counting`, `greedy_triples_bound`, `exists_dag_of_cones_r4`, `card_planeDagParamIdx`, `card_maxRankParamIdx`, `volume_image_eq_zero_of_card_lt`, and `exists_isBlocking_5d`. |
| Compactness and functional continuity | Solution.lean: `inwardDist_pos_iff`, `inwardDist_le`, `continuous_inwardDist`, `blaschke_isCompact_subsets_unitBall`, `exists_eta_of_isBlocking`, `fair_meets_eta_ball`, `normalized_ball_measure_props`, and the perspective construction inside `convex_partition_of_embedding_and_blocking`. |

The source needs isomorphisms through homology degree thirteen and an
epimorphism in degree fourteen. The notes correctly use
\(H_{14}(P_S)=0\), without claiming \(H_{14}(Y_S)=0\).
The relative induction starts from eight-connectivity and uses degrees
nine through fourteen. The final face dimension is \(|S|-1\le14\), and
the lifting conclusion preserves the entire prescribed boundary homotopy.

The geometric parameter counts remain exactly
\(4d+17+5d(d-1)\) and \(5d-1+5d(d-1)\). The first is strictly smaller than
\(5d^2\) precisely for \(d>17\). The compactness proof allows degenerate
limits and chooses \(\eta=\min(1/2,\delta/12)\). The final measure is
normalized Lebesgue measure on that inner ball, so \(\mu(B)=1\).

The companion preserves the distinction between formal proof acceptance,
bibliographic attribution, and the external Palomar registration workflow.
This review does not expand or revalidate the release's separate
primary-source literature search.

## Reviewed documentation snapshot

The hashes below identify the corrected text supplied to the PDF renderer.

- `docs/DIMENSION_EIGHTEEN_PROOF.md`: `afb18953fe80cc1b586c64b5e5c6a5fb7cdb5cc2fabbc5b3de6e52f48665c505`

- `docs/PROOF_MAP.md`: `bd80da23978ac64e107db05df04778355a86c4986fa3140089c986c816bbd928`

- `docs/GEOMETRIC_MARKERS.md`: `24c79fa85006ab17fc58a2bf60baf90cb1aacf5172b47f1a2e58aa2d1b57f42c`

- `docs/GEOMETRIC_FUNCTIONAL.md`: `46090bae36988f30b84fdc9b4e47e506cedb4c282b5c0150d54b4eb5dd9de14b`

- `docs/PROOF_COMPANION.md`: `deba93dfce6cc6edf40608bb6d7941b7e91656f551300ac122f1b68103a1703f`
