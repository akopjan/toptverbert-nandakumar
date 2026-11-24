# Final semantic review of the concrete models

Review of the frozen integrated sources, 24 November 2026. This is a
mathematical statement review, not an additional build or kernel run. The twelve
new model modules below establish their stated finite, linear, and topological
identifications. They do **not** prove `RequiredRelativeLifting` or the
unconditional conclusion for `d > 17`.

1. **Exact ranks concern the original quadratic space.**
   [QuadraticPairRank.lean](../AkopyanResearch/Completion/QuadraticPairRank.lean)
   computes `finrank ℝ (QuadSpace S ⧸ (L_M S m ⊓ L_M S n))`, using the actual
   surjective quadratic evaluation. The answer is `2*(11−card(m∩n))` for
   nonempty intersection and `20` for disjoint matchings. Hence scalar ranks
   seven and eight mean exactly four and three common words. No full-table
   surrogate or assumed rank equality enters the result.

2. **The pair index covers exactly the relevant combinatorics.**
   [PairRepresentation.lean](../AkopyanResearch/Completion/PairRepresentation.lean)
   represents every ordered pair of six-matchings with four common words by
   `ω : S → PairState`, with the actual `firstVertex` and `secondVertex` wordsets.
   [PairIntersection.lean](../AkopyanResearch/Completion/PairIntersection.lean)
   proves the converse for mixed phases and proves equality of the two
   matchings on pure phases. These are proofs, not enumeration assumptions.

3. **Redundant enumerations are removed with the correct action.**
   [PairOrbit.lean](../AkopyanResearch/Completion/PairOrbit.lean)
   proves unique global row reindexing and a unique `h : PairGroup` carrying
   one family to another over the same unordered critical pair. Its action is
   the original `h • ω c`; the label fibre has exactly 192 elements. The
   covariance uses right multiplication on row permutations, consistently with
   the inverse permutation in the target's row relation.

4. **The single factor has one sphere per matching.**
   [SingleCoordinateModel.lean](../AkopyanResearch/Completion/SingleCoordinateModel.lean)
   constructs `Coordinates S ≃ₜ (MatchingIndex S → Target)`, where `Target` is
   the original unit sphere in `Rep10`. Both inverse identities and continuity
   are proved. Thus a one-colour face contributes one `S⁹`, rather than 720
   independent factors indexed by row enumerations.

5. **The pair factor has the actual compact-open topology.**
   [PairPathCoordinates.lean](../AkopyanResearch/Completion/PairPathCoordinates.lean)
   defines `CriticalPairIndex S` as the image of critical labels under the
   unordered `pairWords` map. Coverage and orbit uniqueness justify this
   index. Its homeomorphism is
   `Family S ≃ₜ (CriticalPairIndex S → C(Time, OnePoint PairTarget))`.
   The inverse uses the proved unique transport and actual `actOnePoint`;
   all pure paths are forced to be constant infinity. No additional
   fixed-point path condition or unproved orbit hypothesis is imposed.

6. **The full target is a genuine path-space homotopy fibre.**
   [TargetCollapseModel.lean](../AkopyanResearch/Completion/TargetCollapseModel.lean)
   proves equivariance and pure-phase infinity for the original collapse
   applied to arbitrary row-equivariant single values.
   [TargetFiberModel.lean](../AkopyanResearch/Completion/TargetFiberModel.lean)
   then constructs `Space S ≃ₜ HomotopyFiber hS`, where this fibre consists
   literally of pairs `(f, γ : C(Time, PairProduct S))` satisfying
   `γ timeZero = collapseCoordinates hS f` and `γ timeOne = (fun _ => ∞)`.
   Both endpoints survive decoding, including pure labels. The product-of-paths
   identification is jointly continuous. `comparison_single` and
   `comparison_path` identify the original comparison with normalized
   matching evaluations and the constant infinity path.

7. **The normal model is induced by the actual evaluation.**
   [PairNormalModel.lean](../AkopyanResearch/Completion/PairNormalModel.lean)
   proves that `jointTest : QuadSpace S →ₗ[ℝ] Rep10 × Rep10` has kernel exactly
   the intersection of the two matching kernels. For a critical pair its
   range is the entire 14-dimensional subspace where the common projections
   agree. The resulting quotient equivalence is continuous linear; its
   `mk` formula is precisely `jointTest H`. Surjectivity is derived from the
   proved codimension, not assumed.

8. **The local deformation has a precise, limited conclusion.**
   [PairDeformation.lean](../AkopyanResearch/Completion/PairDeformation.lean)
   supplies continuous shortening, including zero vectors.
   [PairL2Deformation.lean](../AkopyanResearch/Completion/PairL2Deformation.lean)
   proves a strong deformation of
   `Q = {(z,a,b) : (z,a)≠0 ∧ (z,b)≠0}` onto
   `K = {(z,a,b) : ‖z‖²+‖a‖²=1 ∧ ‖z‖²+‖b‖²=1}`.
   The bundled theorem includes continuity, safety, both endpoints and
   pointwise fixing of `K`.
   [PairCollapsedLocus.lean](../AkopyanResearch/Completion/PairCollapsedLocus.lean)
   separately proves a strong deformation of the actual
   `D = {x : PairCollapse.PairSpace U V W // x ∉ chartDomain}` onto its
   `Balanced` subtype, where the two common components are equal. The
   maximum-common-vector choice agrees on the equal-norm boundary, including
   zero. Shortening and separate normalization give continuous paths that
   never vanish and remain in the actual closed locus. Both endpoints and
   pointwise fixing are proved. The canonical identification of this
   `Balanced` presentation with `Balanced2`, the join model, cofibration,
   and connectivity are not asserted by these deformation theorems.
   The new `PairCollapsedLocus` proof is outside the earlier seven-target
   independent kernel certificate for the 131-module snapshot.

9. **Face coverage and naturality have not been silently altered.**
   The hypotheses `hS : S.Nonempty` allow every required face, including
   all faces with 11–15 colours. The empty support carries no mass-one
   simplex point; the induction starts with singleton faces and their empty
   boundaries. The chosen-enumeration homeomorphisms are asserted separately
   for each `S`, not as natural coordinate projections.
   [ConcreteComparison.lean](../AkopyanResearch/Completion/ConcreteComparison.lean)
   retains the actual strictly natural comparison and chosen section on
   intrinsic families. Arbitrary coordinate choices do not replace those
   face maps.

10. **The final theorem remains explicitly conditional.**
    `RequiredRelativeLifting` is an abbreviation for
    `RelativeComparison.RelativeLifting diagram comparison chosenSection`,
    not an axiom or an instance. Its
    [definition](../AkopyanResearch/Completion/RelativeComparison.lean)
    requires extension of both a boundary map and its prescribed boundary
    homotopy to the chosen section. The finite induction preserves both.
    [ConcreteReduction.lean](../AkopyanResearch/Completion/ConcreteReduction.lean)
    proves, with this explicit argument, an almost-six map
    `(Fin 90 → ℝ) → (Fin 16 → ℝ)` and the full original body/measure conclusion
    for every natural `d` with `17 < d`. The conclusion retains continuous
    `Phi : Body d → ℝ^(d−1)`, an absolutely continuous probability measure,
    and quantification over every fair six-partition. A proof of the relative
    lifting proposition is still absent; the new model identifications and
    local deformation do not supply it.

No semantic weakening, missing endpoint, omitted required face, or hidden
existence hypothesis was found in these assembled model statements. The
remaining obstruction is the unproved topological lifting theorem, not the
finite indexing or the coordinate reconstruction reviewed here.
