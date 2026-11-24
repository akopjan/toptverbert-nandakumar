# Historical Planar Comparison Outline and Completion Summary

24 November 2026, UTC. This document summarizes the planar comparison
program and its completion in Lean 4.35.0. All previously intermediate
topological obligations described in earlier research notes are now proved.
For the full mathematical exposition of the completed proof, see
[DIMENSION_EIGHTEEN_PROOF.md](DIMENSION_EIGHTEEN_PROOF.md) and
[PROOF_MAP.md](PROOF_MAP.md).

## Current status

`ConcreteComparisonLifting.requiredRelativeLifting` proves the relative
lifting property without any additional topological hypotheses. The module
`AkopyanResearch/Completion/DimensionEighteen.lean` compiles unconditionally
and exports `AkopyanSixfold.almostSix_ninety` ($\Delta^{89} \to \mathbb{R}^{16}$)
and `AkopyanSixfold.convex_partition_counterexample_gt_17` ($d > 17$).

The completed proof uses:
- excision of codimension $\ge 16$ intersections (`QuadraticDeletion`),
- explicit linear tubular neighborhoods and Mayer–Vietoris sequences
  (`NormedLinearThom`, `QuadraticPairHomology`, `QuadraticComplementHomology`),
- concrete single-matching ($H_9$) and critical-pair ($H_{12}$) coordinate
  isomorphisms (`QuadraticSourceCoordinates`, `TargetPairCoordinates`),
- the local $H_{12}$ isomorphism from the collapsed locus $D$ into the
  homotopy fiber of the pair collapse map (`PairEndpointHomology.collapsedInclusion_isIso`),
- vanishing relative homology of the mapping cylinder through degree $14$
  (`ConcreteComparisonHomology.cylinder_hrelSet_zero`),
- relative Hurewicz injectivity (`UniversalSimplexAddition.relativeHurewicz_injective`)
  and $14$-connectivity of the mapping-cylinder pair
  (`ConcreteComparisonConnectivity.cylinder_pair_fourteen`),
- relative compression and exact boundary homotopy extension
  (`MappingCylinderFaceLifting.extend`), and
- relative face induction across the $15$-color simplex (`RelativeComparison`).

## Key structural points

1. **Relative lifting contract vs. absolute target extension**:
   An absolute extension requirement (`ComparisonTarget.extend_high` for
   arbitrary boundary maps) would imply extension of arbitrary boundary maps
   into $S^9$ via the linking sphere retract `exists_matching_sphere_retract`,
   which is impossible on an $11$-color face ($\partial \Delta^{10} \cong S^9$).
   Instead, `RelativeLifting` extends a boundary map $g : \partial \Delta_S \to Y_S$
   together with a prescribed homotopy $\eta$ from $c_S \circ g$ to the chosen
   target section $p_S|_{\partial \Delta_S}$.

2. **Concrete target space and homotopy fiber**:
   For two six-matchings sharing four common words (a critical pair of
   codimension $14$), the normal model decomposes into a $6$-dimensional
   common component $W \cong \mathbb{R}^6$ and two $4$-dimensional private
   components $U, V \cong \mathbb{R}^4$. The pair collapse map sends
   $B \cong S^9 \times S^9$ to $\mathrm{OnePoint}(\mathrm{PairTarget}) \cong S^{13}$,
   and `TargetFiberModel.homotopyFiberHomeomorph` identifies
   `ConcreteComparisonTarget.Space S` with the path-space homotopy fiber of
   the product collapse map $\prod_{I_S} S^9 \to \prod_{E_S} S^{13}$.

3. **Chosen target sections from the $15$-fold equivariant join**:
   Using `PlanarTestGlobal.q0 : S^9 \to S^9` and its null-homotopy
   `PlanarTestJoin.nullHomotopy_q0`, `OriginalJoinBridge` and
   `ChosenTargetSections` construct the $15$-color single-matching sections
   and $S_4 \times D_8$-equivariant pair paths on the fixed $15$-color join,
   with exact independence of zero-mass color labels.

4. **Local deformation and degree-$12$ comparison**:
   `PairCollapsedLocus.strong_deformation_retraction` and
   `PairL2Deformation.strong_deformation_retraction` deform the local
   complement $Q$ and the collapsed locus $D = B \setminus \mathrm{chartDomain}$
   onto the balanced locus $K \cong S^5 * (S^3 \times S^3)$, which is
   $8$-connected. `PairCollapseHomology.integralDegree_eq_one_or_neg_one` and
   `PairEndpointHomology.collapsedInclusion_isIso` establish that the
   inclusion of $D$ into the local homotopy fiber induces an isomorphism on
   $H_{12}$.

See [DIMENSION_EIGHTEEN_PROOF.md](DIMENSION_EIGHTEEN_PROOF.md) for the
complete step-by-step mathematical proof and
[FORMALIZATION_STATUS.md](../FORMALIZATION_STATUS.md) for the verification
records.
