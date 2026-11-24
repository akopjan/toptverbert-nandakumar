# The unconditional dimension-eighteen comparison argument

## Status of this note

The complete proof chain is implemented. The final module
[DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean)
has compiled successfully with the unconditional theorems
`AkopyanSixfold.almostSix_ninety` and
`AkopyanSixfold.convex_partition_counterexample_gt_17`. In particular,
the original `RequiredRelativeLifting` obligation is now a proved theorem,
not an additional hypothesis of either conclusion.

**Verification status at this update:** the integrated Lean build,
literal challenge-statement check, and complete project-owner axiom
audit passed on 24 November 2026 at 08:56:01 UTC. The audit covered
16,765 declarations from 438 proof-module owners and permitted only
`propext`, `Classical.choice`, and `Quot.sound`. The checked source
snapshot was unchanged during the run. See the
[recorded results](../verification/d18-final-retry/results.json).
The independent clean project build also passed at 09:01:10 UTC, with
all 472 source-input hashes identical to the main gate. The separately
compiled A/B18 interfaces matched in all nine types and seven definition
bodies. The selected export was accepted by Lean checker, NanoDa and con-ron at
09:15:21 UTC, and by the Palomar-approved con-ron version at 09:18:19 UTC.
All used the same unchanged export. This note does not replace their reports; current release status is recorded in
[FORMALIZATION_STATUS.md](../FORMALIZATION_STATUS.md).

All homology groups below are singular homology with integer coefficients.
The symbols `IsNConnected` and `IsNConnectedPair` in the Lean sources refer
to the usual homotopy groups of the actual topological spaces and pairs.
No connectivity property is built into a replacement definition of these
spaces.

## 1. The statement and the topological reduction

For a natural number \(d\), let \(\mathcal K_d\) be the space of nonempty
compact convex subsets of \(\mathbb R^d\), with its Hausdorff metric, and
let \(B_d\subset\mathbb R^d\) be the closed unit ball. The proved
conclusion, for every \(d>17\), is the existence of a continuous map
\(\Phi:\mathcal K_d\to\mathbb R^{d-1}\) and an absolutely continuous
probability measure \(\mu\) on \(\mathbb R^d\), such that no convex
six-partition of \(B_d\) into parts of measure \(\mu(B_d)/6\) has equal
values of \(\Phi\) on all six parts. A partition here has nonempty,
pairwise disjoint interiors and union equal to \(B_d\). The same functional
\(\Phi\) is evaluated on each individual body.

The geometric argument is detailed in [GEOMETRIC_MARKERS.md](GEOMETRIC_MARKERS.md)
and [GEOMETRIC_FUNCTIONAL.md](GEOMETRIC_FUNCTIONAL.md).
The geometric reduction takes an almost six-embedding
\(\Delta^{89}\to\mathbb R^{16}\) to this conclusion. The analytic table
construction takes a compatible safe planar table on fifteen colors to
such an almost embedding; its actual analytic realization is detailed in
[SAFE_TABLE_TO_EMBEDDING.md](SAFE_TABLE_TO_EMBEDDING.md). The topological construction supplies
a coherent lift over every face of a fourteen-dimensional
simplex. In particular, the parameter dimension is fourteen.

The reduction entry points are
`ConcreteComparison.exists_safe_table_of_required_lifting`,
`AkopyanResearch.exists_almostSix_of_safe_compatible_quadratic_table`, and
`AkopyanSixfold.convex_partition_counterexample_ge_18`.
The completed topological input is
`ConcreteComparisonLifting.requiredRelativeLifting`. All these maps and
predicates use the original simplex, table, and convex-body definitions.

## 2. The source arrangement

Fix a nonempty subset \(S\subset\{0,\ldots,14\}\) of colors. Let \(L\)
be the label set \(\{0,\ldots,5\}\), and let \(W_S=L^S\) be the word set.
Let \(Q_S\le\mathbb R^{W_S}\) be the span of constants, single-label
indicators and products of two label indicators. The finite-dimensional
real vector space \(V_S=Q_S^2\) is `QuadSpace S`.

Let \(I_S\) be the finite set of unordered six-element subsets of \(W_S\)
whose evaluation at each color is a bijection onto \(L\). These are the
six-matchings indexing the arrangement; permuting their six rows does
not create a new index. Choose an enumeration for each matching.
Its two height evaluations, after subtracting their row means, define
a linear map \(\ell_i:V_S\to\mathbb R^{10}\), using the ten-dimensional
space of two centered six-tuples. Let \(A_i\le V_S\) be its kernel. The arrangement complement, the subtype
`QuadComplement S`, is the open subset
\[
Y_S=V_S\setminus\bigcup_{i\in I_S}A_i.
\]

Every \(A_i\) has codimension ten. For distinct matchings \(i,j\), the
intersection \(A_i\cap A_j\) has codimension fourteen or at least sixteen.
Call the unordered pairs of the first kind critical, and denote their
finite set by \(E_S\). Equivalently, their two matchings have exactly four
words in common. Three distinct atoms have intersection of
codimension at least eighteen. These statements follow from the checked
rank and matching calculations.

Let \(Z\subset V_S\) be the union of all atom intersections of
codimension at least sixteen. The source indexes these by families of
scalar rank at least eight. By the rank bounds, the same union is obtained
from the noncritical pair intersections and the triple intersections.
Set \(W=V_S\setminus Z\). The surviving
atoms \(A'_i=A_i\cap W\) have only pairwise intersections. The critical
strata \(C'_e=A_i\cap A_j\cap W\), for \(e=\{i,j\}\in E_S\), are
pairwise disjoint and closed in \(W\). Moreover,
\(Y_S=W\setminus\bigcup_iA'_i\).

Finite-dimensional general position gives the following connectivity bounds:
\(W\) is fourteen-connected, each \(A'_i\) is four-connected, and each
\(C'_e\) is two-connected. Every partial atom complement in \(W\) is
eight-connected. These estimates use the codimensions sixteen, six,
four, and ten, respectively.

## 3. Source homology and its actual coordinates

Let \(U\) be an open subset of a finite-dimensional real vector space
\(V\), let \(A\le V\) have codimension \(c>0\), and set \(A'=A\cap U\).
The normal bundle of this stratum is trivial. Excision and the elementary
normal-disk calculation give \(H_k(U,U\setminus A')\cong H_{k-c}(A')\)
for \(k\geq c\), with zero relative groups for \(k<c\). The formal proof
constructs a continuous small-radius normal tube and computes the
product pair by repeated suspension and Mayer–Vietoris. It does not
assume a general Thom theorem.

Adding disjoint critical strata one at a time gives actual coordinate
isomorphisms in degree thirteen for their complements. Adding atoms one
at a time then uses the open cover by the previous partial complement
and the complement of the new atom. Their union is the complement of
the new critical strata. The Mayer–Vietoris sequence adds one generator
in degree nine and one generator in degree twelve for each new critical
pair. At the endpoint one also needs the vanishing of degree fourteen
for complements of disjoint critical strata. For a single such stratum,
the relative group in degree fifteen is its first homology and is zero.
Thus its complement maps onto \(H_{15}(W)\); the Mayer–Vietoris boundary
into degree fourteen vanishes. Induction gives the required vanishing
without assuming \(H_{15}(W)=0\). Thus
\[
\widetilde H_k(Y_S)\cong
\begin{cases}
\mathbb Z^{I_S},&k=9,\\
\mathbb Z^{E_S},&k=12,\\
0,&0\le k\le13,\ k\notin\{9,12\}.
\end{cases}
\]

The coordinate maps matter. The degree-nine isomorphism is induced by
the original normalized maps \(\ell_i/\|\ell_i\|:Y_S\to S^9\). On the
complement of its own atom in \(W\), each normalized test induces a
split epimorphism between infinite cyclic groups: an explicit small
normal meridian supplies the section. The canonical restriction maps
then give the asserted coordinates on \(Y_S\). The degree-twelve
isomorphism is induced by the original
joint centered tests, followed by the actual normalization into the
collapsed locus \(D_e\subset S^9\times S^9\).

For the latter assertion, naturality of the Mayer–Vietoris boundary
identifies the new coordinates on the kernel of the deletion sequence
with the degree-thirteen critical meridians. The old coordinates factor
through the previous partial complement. The elementary short exact
sequence argument then proves that the combined coordinate map is an
isomorphism. This proves its integral primitivity as well as its rank.

The checked interfaces are `QuadraticSourceCoordinates.singleCoordinatesIso`
and `QuadraticSourceCoordinates.collapsedCoordinatesIso`, together with
their literal coordinate formulas. No assertion about \(H_{14}(Y_S)\)
is needed.

## 4. The target and the local comparison

Let \(B_S=\prod_{i\in I_S}S^9\), let
\(T_S=\prod_{e\in E_S}S^{13}\), and let
\(\kappa_S:B_S\to T_S\) be the product of the original pair-collapse
maps. For each \(e\in E_S\), write
\(\kappa_e:S^9\times S^9\to S^{13}\) for the corresponding local collapse.
Let \(P_S=\operatorname{hofib}_{\infty}(\kappa_S)\). The project
constructs a homeomorphism from the originally defined target to this
homotopy fiber. Its comparison map \(c_S:Y_S\to P_S\) consists of the
normalized single tests and the specified constant pair paths.

The homotopy exact sequence shows that \(P_S\) is eight-connected.
It also identifies the degree-nine homotopy map of the projection
\(P_S\to B_S\); naturality of the absolute Hurewicz isomorphism then
identifies its degree-nine homology map. The higher homology of the path
and loop spaces is computed using hemisphere covers, explicit path
trivializations, and Mayer–Vietoris. The calculation for finite products
retains the actual coordinate projections. Together these give
\[
\widetilde H_k(P_S)\cong
\begin{cases}
\mathbb Z^{I_S},&k=9,\\
\mathbb Z^{E_S},&k=12,\\
0,&0\le k\le14,\ k\notin\{9,12\}.
\end{cases}
\]
The degree-nine projection statement is
`FirstHomologyComparison.targetProjection_isIso`.
The original pair-coordinate maps induce
\(H_{12}(P_S)\cong\prod_eH_{12}(F_e)\), where
\(F_e=\operatorname{hofib}_{\infty}(\kappa_e)\).

For a critical pair \(e\), the collapsed locus \(D_e\) has
\(H_{12}(D_e)\cong\mathbb Z\). The actual collapse induces an isomorphism
\(H_{13}(S^9\times S^9,D_e)\to H_{13}(S^{13},\{\infty\})\). The proof
uses its explicit open chart and a section obtained by fixing the
\(S^5\) coordinate of the chart. Consequently the relative map is
surjective between infinite cyclic groups.

To compare with \(F_e\), replace the collapse by its mapping-path
fibration \(p:E_e\to S^{13}\), where \(E_e\simeq S^9\times S^9\).
Fix the canonical point \(b_0\in S^9\times S^9\) used by
the local construction. Let \(L_0\) be the contractible
space of paths in \(S^{13}\) starting at \(\kappa_e(b_0)\), and let
\(F_0\subset L_0\) consist of those ending at infinity. The endpoint
map is a Serre fibration. Lifting relative homotopy classes, followed by
naturality of the relative Hurewicz homomorphism and surjectivity of the
absolute Hurewicz map of \(S^{13}\), makes
\(H_{13}(L_0,F_0)\to H_{13}(S^{13},\{\infty\})\) surjective.
Both groups are infinite cyclic, so this actual endpoint map is an
isomorphism.

The fixed-source inclusion \((L_0,F_0)\to(E_e,F_e)\) also induces an
isomorphism on relative \(H_{13}\). Indeed the finite-sphere hemisphere
calculation gives the actual fiber inclusion \(H_{12}(F_0)\to H_{12}(F_e)\)
as an isomorphism, and the ambient groups in degrees twelve and thirteen
vanish. Naturality of the pair exact sequence gives the claim. Hence
the endpoint map for \((E_e,F_e)\) is an isomorphism on relative
\(H_{13}\). The constant-path map of pairs
\((S^9\times S^9,D_e)\to(E_e,F_e)\) composes with it to the original
collapse. Naturality of the pair boundary now proves that its
restriction \(D_e\to F_e\) induces an isomorphism on \(H_{12}\).

This local proof is formalized by `PairEndpointHomology.collapsedInclusion_isIso`.
It uses neither Blakers–Massey nor an unproved local comparison theorem.
The exact coordinate squares identify the two nonzero positive-degree
homology maps of \(c_S\) in this range with products of the isomorphisms
just described. All other positive degrees through thirteen vanish on
both sides. Path connectedness gives the degree-zero isomorphism, and
\(H_{14}(P_S)=0\) gives the degree-fourteen epimorphism without computing
\(H_{14}(Y_S)\). Thus `ConcreteComparisonHomology.homology_isIso` proves
isomorphisms in degrees \(0\) through \(13\), and `homology_epi` proves
epimorphisms through degree \(14\).

## 5. Relative connectivity

Let \(M_S\) be the mapping cylinder of \(c_S\), with \(Y_S\) embedded
as its top. The cylinder retracts onto \(P_S\), and the top inclusion
followed by this retraction is exactly \(c_S\). The homology exact
sequence therefore gives \(H_k(M_S,Y_S)=0\) for \(1\le k\le14\).
The natural chain isomorphism in `RelativeHomologyBridge` identifies
this relative homology with the relative singular homology used by the
Hurewicz construction. Both spaces are eight-connected, so the pair is
initially eight-connected.

The relative Hurewicz step is proved for actual pairs. For an integer
\(m\ge3\), let \(\Delta^{m+1}\) be the standard simplex and let
\(K\subset\Delta^{m+1}\) be its \((m-1)\)-skeleton. The skeleton is
\((m-2)\)-connected. One explicit proof deletes the barycenter of each
facet, identifies the punctured boundary with a sphere minus finitely
many points, and retracts it to \(K\) by subtracting the second-smallest
barycentric coordinate, replacing negative values by zero, and renormalizing.

The ambient simplex is contractible. Its relative Hurewicz map in
degree \(m\) is therefore an isomorphism, by the absolute theorem and
the two boundary exact sequences. The cubical boundary comparison
keeps track of the orientation unit. The alternating sum of its
oriented facet classes is zero in relative homology and hence in
relative homotopy. Naturality of freely based relative classes
transports this relation to every map of this universal pair into a
pair with simply connected subspace.

Coherent normalization of singular simplices then makes this relation
the chain-boundary relation needed to construct a left inverse to the
first relative Hurewicz map. Its injectivity suffices: if a pair is
\((m-1)\)-connected,
its subspace is simply connected, and its relative \(H_m\) vanishes,
its relative \(\pi_m\) vanishes. Applying this successively for
\(m=9,10,\ldots,14\) makes \((M_S,Y_S)\) fourteen-connected.

The implementation separates the explicit geometric face relation
(`UniversalSimplexAddition`) from the singular-chain descent
(`RelativeHurewiczDescent`). `RelativeHomologyConnectivity.fourteen`
is the resulting finite induction. The concrete application is
`ConcreteComparisonConnectivity.cylinder_pair_fourteen`.
The hypotheses are genuine connectivity and vanishing statements.

## 6. Exact boundary data and the finite table induction

The chosen target section is constructed independently of the comparison
connectivity theorem. Its explicit join maps, subgroup contractions and
strict face identities are described in [TARGET_SECTION.md](TARGET_SECTION.md).

For each face of the mass simplex, the induction supplies a boundary
map to \(Y_S\) and a specified homotopy of its comparison to the chosen
target section. Pair connectivity compresses the corresponding disk
in \(M_S\) into \(Y_S\) relative to the boundary. The homotopy extension
property of the cube boundary then corrects the time parameter on the
entire cylinder boundary. This last correction keeps both end maps
fixed and recovers the prescribed boundary homotopy literally.

The distinction is necessary: an arbitrary reparametrization of a
boundary homotopy would not satisfy the next face-gluing contract.
The construction retains the complete given homotopy. Transfer by the
actual face-simplex and cube homeomorphisms supplies
`ConcreteComparison.RequiredRelativeLifting`: the actual face dimension
is \(|S|-1\leq14\), including the zero-dimensional case \(|S|=1\).
The theorem `ConcreteComparisonLifting.requiredRelativeLifting` has
no additional topological or homological input. The fifteen-color
induction then produces the compatible safe table. The two reductions
in Section 1 give the required almost six-embedding and the convex
partition obstruction for every \(d>17\).

## Verification boundary

The integrated build, literal challenge-statement check, and complete
project-owner axiom audit passed for the unchanged source snapshot.
The independent clean project build and separately compiled interface
comparison also passed. Selected-export checks in Lean checker, NanoDa and con-ron passed, as did
a supplemental replay with the Palomar-approved con-ron version. The
independent clean objects have the same stored declarations and proof
bodies as the exported working objects; serialized path metadata may differ.
The successful local statement check does not claim that the external
Palomar comparator or its complete publication workflow has run.
See [FORMALIZATION_STATUS.md](../FORMALIZATION_STATUS.md) for release status
and [MATHEMATICAL_CONTEXT.md](MATHEMATICAL_CONTEXT.md) for the primary-source
context and attribution limits.
