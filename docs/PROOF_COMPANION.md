# Convex six-partition obstructions in dimensions greater than seventeen

**A companion to the completed Lean formalization · 24 November 2026**

This note describes the unconditional proof implemented in the accompanying
project. It explains the fourteen-dimensional relative lifting argument,
the resulting almost-six embedding, and the geometric construction of a
continuous functional on convex bodies. The proof sources, their exact
interfaces, and the recorded verification results are part of the release.
The note is an exposition of that formalization; it does not assert a new
bibliographic attribution or a completed Palomar registration.

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

The geometric reduction takes an almost six-embedding
\(\Delta^{89}\to\mathbb R^{16}\) to this conclusion. The analytic table
construction takes a compatible safe planar table on fifteen colors to
such an almost embedding. The topological construction supplies
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
H_9(Y_S)\cong\mathbb Z^{I_S},\qquad H_{12}(Y_S)\cong\mathbb Z^{E_S}.
\]
All other reduced groups in degrees zero through thirteen vanish.

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
H_9(P_S)\cong\mathbb Z^{I_S},\qquad H_{12}(P_S)\cong\mathbb Z^{E_S}.
\]
All other reduced groups in degrees zero through fourteen vanish.
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

## 5. Constructing the target section

### 5.1. The supplied sphere map and its ordinary nullhomotopy

Let \(G=\operatorname{Perm}(\mathrm{Fin}(6))\) be the discrete symmetric
group, let \(E=\mathrm{Rep10}\) be the ten-dimensional Euclidean
representation of centered planar six-tuples, and let \(Q=S(E)\cong S^9\)
be its unit sphere. The action \(G\curvearrowright Q\) is the original
`permSphere` action. Let \(H\le G\) be the subgroup preserving the blocks
\(\{0,1,2,3\}\) and \(\{4,5\}\); thus \(H\cong S_4\times S_2\).

The supplied [PlanarTestGlobal.lean](../AkopyanResearch/PlanarTestGlobal.lean)
defines a continuous equivariant map \(q_0:Q\to Q\), named `q0`, and an
\(H\)-fixed point \(a_0\in Q\), named `anchorS`, with \(q_0(a_0)=a_0\).
The supplied [PlanarTestJoin.lean](../AkopyanResearch/PlanarTestJoin.lean)
constructs a continuous homotopy \(h:Q\times[0,1]\to Q\) from \(q_0\) to
the constant map \(a_0\). Its proof obtains a nowhere-zero filling using
the proved surgery theorem and then normalizes that filling along line
segments to the anchor. The declarations `exists_nowhere_zero_filling`,
`nullHomotopy_q0`, `nullHomotopy_q0_zero`, and `nullHomotopy_q0_one`
supply the construction and endpoints.

These are proved inputs; \(h\) is an ordinary nullhomotopy. Equivariance
of \(h\) is not a hypothesis. Both supplied modules, and the original
[PairCollapseEquivariant.lean](../AkopyanResearch/PairCollapseEquivariant.lean),
remain byte-identical to the reviewed input archive. The completion
modules below build the additional subgroup homotopies and compatible
coordinate families.

### 5.2. Explicit joins and subgroup contractions

Let \(X\) be a \(G\)-space and let \(F:X\to Q\) be a continuous equivariant
map. The actual topological join \(X*G\) is the quotient of
\([0,1]\times X\times G\), forgetting the \(G\)-coordinate at time zero
and the \(X\)-coordinate at time one. The join step is

\[
[t,x,g]\longmapsto g\cdot h(g^{-1}\cdot F(x),t).
\]

At the endpoints it equals \(q_0(F(x))\) and \(g\cdot a_0\), respectively,
so it descends through the quotient. The formula itself proves
\(G\)-equivariance, without requiring equivariance of \(h\).
[EquivariantJoinStep.lean](../AkopyanResearch/Completion/EquivariantJoinStep.lean)
checks descent, continuity, and these identities.

Starting with \(F_0:G\to Q\), \(F_0(g)=g\cdot a_0\), iteration gives
\(F_k:G^{*(k+1)}\to Q\). An \(H\)-equivariant contraction of the seed is
\(N_0(g,s)=g\cdot h(g^{-1}\cdot a_0,1-s)\). Its endpoint is \(a_0\)
because \(q_0(a_0)=a_0\).

The contraction also propagates explicitly. Given an \(H\)-equivariant
homotopy \(N:X\times[0,1]\to Q\) from \(F\) to \(a_0\), the first stage
on the new join is \(g\cdot h(g^{-1}\cdot N(x,s),t)\). The second is
\(g\cdot h(g^{-1}\cdot a_0,(1-s)t)\). They agree at their common endpoint,
descend through the join, and end at \(a_0\). The \(H\)-fixedness of
\(a_0\) gives the required subgroup equivariance.
[JoinNullhomotopy](../AkopyanResearch/Completion/JoinNullhomotopy.lean)
and [JoinNullIteration](../AkopyanResearch/Completion/JoinNullIteration.lean)
prove these assertions.
`OriginalJoinBridge.exists_fifteen_join_map_with_block_nullhomotopy`
instantiates them at \(k=14\), using exactly the supplied \(q_0,h,a_0\).

### 5.3. Row conventions and pair paths

Let \(C=\mathrm{Fin}(15)\) be the color set. The coordinate model
`PhaseExtension.Join C G` consists of nonnegative weights on \(C\times G\)
whose sum is one and which use at most one vertex at each color. The proved
`IteratedJoinCoordinates.finHomeomorph` identifies this with the iterated
quotient join.

The map `OriginalJoinCoordinates.rowMap 14` first inverts each row
permutation, then applies the transported join map. Thus, for a row-label
family \(\sigma:C\to G\), changing every label to \(\sigma_c\tau\) changes
the output by `permSphere` \(\tau^{-1}\). Its contraction
`rowNullhomotopy 14` has the same right-action convention for every
\(\tau\in H\). This is the convention required for different enumerations
of one matching.

Let \(J=G\times\{0,1\}\) be the pair-state set, named `PairState`, and let
\(K=S_4\times D_8\) be `PairGroup`, where \(D_8\) has eight elements.
Let \(r\in G\) be the transposition exchanging labels \(4,5\).
A state \((\sigma,b)\in J\) determines the two row permutations
\(\sigma\) and \(\sigma r^b\). These are `firstVertex` and
`secondVertex`; pushforward of join weights gives their continuous
projections.

The \(K\)-action combines a common permutation of the first four rows,
residual swaps, and exchange of the two matchings.
[PairSourceProjections](../AkopyanResearch/Completion/PairSourceProjections.lean)
checks its action on both projections. Each resulting row change lies
in \(H\), so the full block-subgroup contractions apply.

Let \(T=\mathrm{OnePoint}(\mathrm{PairTarget})\cong S^{13}\), with basepoint
\(\infty\), and let \(\kappa:Q\times Q\to T\) be the original pair collapse,
using `spherePairEquiv` to enter its coordinates. The map
`OriginalPairPath.pairPath 14` applies \(\kappa\) to the two simultaneous
row contractions. It starts at the collapse of the two row-map values
and ends at \(\kappa(a_0,a_0)=\infty\). The checked action identities make
this path \(K\)-equivariant.

If the phase \(b\) is constant on every active color, the two contracting
sphere points differ by the same fixed permutation \(r^b\).
`collapse_diagonal` and `collapse_swap45` show that the entire pair path
is then constantly \(\infty\), including the phase \(b=1\).
This is `OriginalPairPath.pairPath_pure`.

### 5.4. One fixed join stage on all faces

Let \(\Delta_C\) be the simplex of real-valued mass families
\(z:C\to\mathbb R\) with \(z_c\ge0\) and \(\sum_c z_c=1\). For labels \(\sigma:C\to G\), the point
`JoinMassCoordinates.fromMass z σ` places weight \(z_c\) at
\((c,\sigma_c)\). Labels at zero-mass colors have literally no effect.

`ChosenTargetSections.singleSection` evaluates `rowMap 14` at this point.
For pair labels \(\omega:C\to J\), `pairSection` evaluates `pairPath 14`
at the analogous point and the homotopy time. Both constructions are
continuous in the masses, and agree whenever labels agree on their
nonzero support.

A join step restricts on its old face to \(q_0\circ F\). The construction
therefore uses the same fifteen-color maps on every face, rather than
changing the iteration index with the number of active colors.

For a subset \(S\subset C\), let \(\Delta_S\subset\Delta_C\) be its mass
face. Extend a label family on \(S\) arbitrarily outside \(S\); the source
uses \(1\) for row labels and \((1,0)\) for pair labels. Independence of
zero-mass labels makes the resulting values independent of these choices.
The concrete model for \(P_S\), `ConcreteComparisonTarget.Space S`, records all
row values and pair paths satisfying five exact relations: row enumeration,
the prescribed path start, endpoint \(\infty\), pair equivariance, and
constant pure-phase paths. The theorem `chosen_relations` verifies them
for the constructed data.

Thus `sectionMap S` is a continuous map \(\Delta_S\to P_S\).
For subsets \(R\subset S\) and a point \(z\in\Delta_R\), it satisfies

\[
\operatorname{sectionMap}_S(\operatorname{faceIncl}(z))
 =\operatorname{lift}_{R,S}(\operatorname{sectionMap}_R(z)).
\]

Here `lift` evaluates labels after restriction from \(S\) to \(R\).
This equality is `sectionMap_natural`; it follows from equality of
`fromMass` points, including every pair-path value at every time.
Finally, `ConcreteComparison.chosenSection` packages these continuous
maps and equalities.

The final declarations are in
[ConcreteComparisonTarget.lean](../AkopyanResearch/Completion/ConcreteComparisonTarget.lean)
and [ConcreteComparison.lean](../AkopyanResearch/Completion/ConcreteComparison.lean).

The section uses no comparison-connectivity or lifting hypothesis.
Its subsequent lift into the arrangement complement is the separate
theorem `ConcreteComparisonLifting.requiredRelativeLifting`.

## 6. Relative connectivity

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

## 7. Exact boundary data and the finite table induction

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


## 8. From a safe table to the simplex map

### 8.1. The table and its precise hypotheses

Let \(C=\{0,\ldots,14\}\) be the color set, let \(L=\{0,\ldots,5\}\) be the
label set, and let \(T=\{0,1\}\) index two real coordinates. For a finite set
\(I\), write \(\Delta(I)\subset\mathbb R^I\) for the nonnegative vectors whose
coordinates sum to one. Let \(W=L^C\) be the finite set of words.

A planar table is a continuous map \(H:\Delta(C)\to(\mathbb R^2)^W\).
Thus \(H(z,w)\in\mathbb R^2\) is a height assigned to a mass vector
\(z\in\Delta(C)\) and a word \(w\in W\).
Compatibility means that \(H(z,w)=H(z,w')\) whenever \(w,w'\) agree on all
colors \(i\) with \(z_i>0\). Equivalently, changing the label of any zero-mass
color leaves the value unchanged. The equivalence follows by changing the
finitely many inactive labels one at a time:
`ProductExpectation.dependsOn_of_update_invariant`.

A matching is a family \(\sigma=(\sigma_i)_{i\in C}\) of permutations of \(L\).
Its six words are \(w_j(i)=\sigma_i(j)\), for \(j\in L\).
Safety is the assertion

\[
 \forall z\in\Delta(C),\ \forall \sigma\in(S_6)^C,\quad
 \exists j\in L:\ H(z,w_j)\ne H(z,w_0).
\]

This includes boundary mass vectors. Safety quantifies over independent label
permutations in every color; it imposes no permutation-invariance on \(H\).
The index \(0\) merely selects a reference word. These definitions are
`HeightTable`, `Compatible` and `Safe` in
[TableRealization.lean](../AkopyanResearch/Completion/TableRealization.lean).

### 8.2. Two averaged height coordinates

The ninety vertices are indexed by \(C\times L\). A point
\(x\in\Delta(C\times L)\) has coordinates \(x_{i,a}\). Define its color masses
by \(z_i(x)=\sum_{a\in L}x_{i,a}\), so \(z(x)\in\Delta(C)\).
If \(z_i(x)>0\), define a probability vector \(u_i\in\Delta(L)\) by
\(u_i(a)=x_{i,a}/z_i(x)\). If \(z_i(x)=0\), choose any vector in
\(\Delta(L)\); the source uses a fixed point mass.

The desired height \(h(x)\in\mathbb R^2\) is the product average

\[
 h_t(x)=
 \sum_{w\in W}\left(\prod_{i\in C}u_i(w_i)\right)H_t(z(x),w),
 \qquad t\in T.
\]

The product weights sum to one. Compatibility makes the expression
independent of the distributions chosen at inactive colors.
The finite-sum identities are proved in
[ProductExpectation.lean](../AkopyanResearch/Completion/ProductExpectation.lean),
particularly `sum_product_weights`, `expectation_congr_of_dependsOn` and
`expectation_eq_of_dirac_on`.

Continuity at zero masses is proved by a quotient construction. Let
\(P=\Delta(C)\times\Delta(L)^C\), a compact space, and define the continuous
surjection \(q:P\to\Delta(C\times L)\) by \(q(z,u)_{i,a}=z_i u_i(a)\).
Surjectivity follows from the conditional distributions above: a nonnegative
color block with zero sum vanishes identically. Since the target is
Hausdorff, \(q\) is a quotient map.

The averaging formula defines a continuous map on \(P\), being a finite sum
of products of continuous functions. Two parameters with the same image
under \(q\) have the same masses and the same distributions at every active
color. Compatibility therefore makes their averages equal. The average
descends to a continuous \(h\) on the entire simplex. This is proved by
`project_isQuotientMap`, `parameterHeight_constant_on_fibres` and
`exists_continuous_height` in `TableRealization`. No limit of the individual
quotients \(x_{i,a}/z_i(x)\) is asserted.

### 8.3. Fourteen masses suffice

Using the general construction, define

\[
 g(x)=\bigl(z_1(x),\ldots,z_{14}(x),h_0(x),h_1(x)\bigr)
       \in\mathbb R^{16}.
\]

If two images are equal, their fourteen displayed masses agree. The remaining
mass is \(z_0=1-\sum_{i=1}^{14}z_i\), so it agrees as well.
The bijection `finProdFinEquiv : Fin 15 × Fin 6 ≃ Fin 90` transports this
map to the ordinary simplex with ninety vertices, whose dimension is
eighty-nine. The corresponding declarations are `massAndHeight`,
`mass_eq_of_massAndHeight_eq` and `vertexEquiv` in
[SimplexEmbedding.lean](../AkopyanResearch/Completion/SimplexEmbedding.lean).

### 8.4. Disjoint supports force a matching

Suppose six points \(x^{(j)}\in\Delta(C\times L)\), indexed by \(j\in L\),
have pairwise disjoint supports and a common image under \(g\). They then
have a common mass vector \(z\).

Fix an active color \(i\). The matrix
\(Y_i=(x^{(j)}_{i,a})_{j,a\in L}\) has nonnegative entries, row sum \(z_i>0\),
and pairwise disjoint row supports. Each of its six rows occupies at least
one of the six columns. Consequently every row occupies exactly one column
and every column is occupied. There is a permutation \(\sigma_i\) with
\(x^{(j)}_{i,a}=z_i\) when \(a=\sigma_i(j)\), and zero otherwise.
For an inactive color all entries vanish, and any permutation may be chosen.
This is `MatchingExtraction.exists_colored_matching` in
[MatchingExtraction.lean](../AkopyanResearch/Completion/MatchingExtraction.lean).

For each row \(j\), the active conditional distributions are therefore point
masses at the word \(w_j(i)=\sigma_i(j)\). Averaging reduces to
\(h(x^{(j)})=H(z,w_j)\); inactive colors cause no ambiguity by compatibility.
Equal heights now contradict safety.
The precise transfer is `TableRealization.realized_height_separates`,
followed by `TableToEmbedding.exists_almostSix_of_continuous_table` in
[TableToEmbedding.lean](../AkopyanResearch/Completion/TableToEmbedding.lean).
That module also proves a globally continuous ambient extension using
Tietze's theorem; continuity on the simplex already suffices for the
almost-six condition.

### 8.5. The quadratic implementation used by the final theorem

The constructed table also belongs, at each mass vector and in each height
coordinate, to the span of constants, single-label indicators and products
of two label indicators. The canonical basis uses nonzero labels and pairs
of distinct colors \(i<k\). It has
\(1+15\cdot5+\binom{15}{2}25=2701\) features per height coordinate.
Here “quadratic” refers to the label indicators; the coefficients depend
continuously on the masses.

[CanonicalExtraction.lean](../AkopyanResearch/CanonicalExtraction.lean)
extracts coefficients by finite differences from words with at most two
nonzero labels. Compatibility makes every coefficient involving color \(i\)
vanish on \(z_i=0\). The required feature factors are respectively
\(1\), \(z_i\), and \(z_i z_k\).

Vanishing alone does not justify continuous division by these factors.
The source instead approximates a coefficient \(a_f(z)\) by
\(p_f(z)b_f(z)\), where
\(b_f(z)=a_f(z)/\max(\delta_f,p_f(z))\) and \(\delta_f>0\).
Compactness makes the approximation uniformly small. There are finitely
many matching tests, each a nonzero continuous vector-valued function on the
compact mass simplex; their norms have a uniform positive lower bound.
The approximation is chosen to preserve all these tests. This is
`exists_safe_factored_quadratic_coefficients` in
[SafeQuadraticBridge.lean](../AkopyanResearch/SafeQuadraticBridge.lean), using
`exists_continuous_factored_approximation` and
`exists_safe_finite_factored_coefficients`.

After subtracting a word-independent constant, the resulting safe certificate
has continuous coefficients \(A_{i,a,t}(z)\) and \(B_{ik,ab,t}(z)\).
Averaging its factored terms cancels the conditional denominators and yields
the concrete height formula

\[
 h_t(x)=
 \sum_{i,a}x_{i,a}A_{i,a,t}(z(x))
 +\sum_{i<k}\sum_{a,b}x_{i,a}x_{k,b}B_{ik,ab,t}(z(x)).
\]

The source implements this finite-sum formula directly as `quadraticHeight`.
Its equality with certificate evaluation on pure color points is
`quadraticHeight_pureColorPoint`. The constant subtraction preserves every
matching inequality, as proved in `certificateFromFeatures_evaluation` in
[SafeQuadraticRealization.lean](../AkopyanResearch/SafeQuadraticRealization.lean).

The coefficients extend to \(\mathbb R^{15}\) using the continuous simplex
retraction `simplexRetractionMap`. Its denominator is
\(\max(1,\sum_i\max(z_i,0))\geq1\), and it fixes the mass simplex.
Finite sums and products then prove global continuity.
The implemented `quadraticMapNinety` retains masses \(z_0,\ldots,z_{13}\),
omitting \(z_{14}\); the same sum-to-one argument recovers it.
All these assertions, including the zero-mass matching case, are proved in
[QuadraticRealization.lean](../AkopyanResearch/QuadraticRealization.lean).

Finally, `ConcreteComparison.exists_safe_table_of_required_lifting` supplies
the table, and the proved `ConcreteComparisonLifting.requiredRelativeLifting`
discharges its existence input. `AkopyanSixfold.almostSix_ninety_of_relative_lifting`
applies the quadratic realization bridge, and
[DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean)
packages the unconditional result as `AkopyanSixfold.almostSix_ninety`.

## 9. Blocking markers and the dimension bound

### 9.1. The blocking statement

Let \(d\ge18\) be an integer, let \(V=\mathbb R^d\) be Euclidean space, and let
\(B=B_d\subset V\) be the closed unit ball from Section 1. Put \(m=5d\). A central six-partition is
a family \(C:\mathrm{Fin}(6)\to\operatorname{ConvexBody}(V)\) whose union is
\(B\), whose members have pairwise disjoint interiors, and all contain the origin.
Here a convex body means a nonempty compact convex set; its interior may be
empty. A marker family \(p:\mathrm{Fin}(m)\to V\) is blocking if every such
partition has a marker in the interior of a part.

The theorem [`exists_isBlocking_5d`](../Solution.lean) asserts existence of
this family. Its proof chooses every marker in the open unit ball, although
the theorem's displayed type only records `IsBlocking p`. Allowing degenerate
parts is essential: a Hausdorff limit of partitions may acquire such parts.

### 9.2. Separating normals and the rank split

For a fixed central partition, choose vectors \(n_{ij}\in V\), indexed by
\(i,j\in\mathrm{Fin}(6)\). The lemma
[`exists_central_separating_normals`](../Solution.lean) makes these choices
antisymmetric, with \(n_{ii}=0\). For distinct parts with nonempty interior,
\(n_{ij}\ne0\), the scalar product with \(n_{ij}\) is nonnegative on \(C_i\)
and nonpositive on \(C_j\), and both inequalities are strict in the respective
interiors. Normals involving a part with empty interior are set to zero.
Separation initially gives an affine level; the common origin forces that
level to be zero.

The full-dimensional parts still cover \(B\). Consequently, a point in the
open ball outside all part interiors lies on a separating hyperplane between
two full-dimensional parts. This is
[`skeleton_in_separating_hyperplanes`](../Solution.lean).

Define vectors \(a_i\in V\) by \(a_i=\sum_j n_{ij}\), and let \(L\le V\) be
the span of all normals. Antisymmetry gives \(\sum_i a_i=0\). The key lemma
[`central_partition_normal_rank`](../Solution.lean) proves that any vector
orthogonal to every \(a_i\) is orthogonal to every \(n_{ij}\). Thus the row
sums and the normals span the same space, and \(\dim L\le5\).

The proof splits according to independence of the five vectors
\(a_1,\ldots,a_5\). Their dependence gives \(\dim L\le4\). Their independence
gives rank five and also forces all six parts to have nonempty interior.
In the latter case, [`rank5_triangle_dependent`](../Solution.lean) proves
that \(n_{ij},n_{jk},n_{ki}\) are linearly dependent for every three distinct
indices. This dependence is a consequence of the partition geometry.

### 9.3. Rank at most four: why the count is \(4d+17\)

In the dependent case,
[`separating_normals_in_rref4_span`](../Solution.lean) places all normals in
a four-dimensional subspace, even when their span has smaller dimension.
Choose injective pivot coordinates \(I:\mathrm{Fin}(4)\to\mathrm{Fin}(d)\)
and vectors \(u_r\in V\) satisfying \(u_r(I(s))=\delta_{rs}\). Their remaining
coordinates contribute \(4(d-4)\) real parameters. Every normal is recovered
from its four pivot coordinates by \(n_{ij}=\sum_r n_{ij}(I(r))u_r\).

Suppose first that every part has nonempty interior. Define vectors
\(c_{ij}\in\mathbb R^4\) by \(c_{ij}(r)=n_{ij}(I(r))\), and define a linear
map \(P:V\to\mathbb R^4\) by \(P(x)_r=\langle u_r,x\rangle\). The closed
polyhedral cones \(K_i\subset\mathbb R^4\), defined by
\(K_i=\{y:\langle c_{ij},y\rangle\ge0\text{ for }j\ne i\}\),
cover \(\mathbb R^4\), and each corresponding system of strict inequalities
has a solution. The pivot identities make \(P\) surjective; coverage follows
by lifting a vector and scaling its lift into \(B\).

Let \(\mathcal H\) be the finite set of actual wall hyperplanes of these
cones. There are at most fifteen, one for each unordered pair of parts.
Minimal facet descriptions and `baire_facet_wall` show that these walls cover
the cone boundaries relevant to the markers. The proof therefore needs to
parameterize this wall family.

The source builds its normals in an acyclic sequence with two operations.
A free normal has one chosen coordinate normalized to one, leaving three
parameters. A ridge operation combines two earlier normals \(v_a,v_b\in
\mathbb R^4\) as \(v_a+s v_b\), with one real parameter \(s\). It applies
when three distinct hyperplanes contain the same two-dimensional plane.
Nonzero rescaling preserves their kernels.

Let \(M=|\mathcal H|\le15\) and \(b\) be the numbers of walls and free steps.
The parameter cost is \(3b+(M-b)=M+2b\). The geometric counting argument
[`ticket_counting`](../Solution.lean), together with
[`greedy_triples_bound`](../Solution.lean), makes this cost at most \(33\).
More precisely, if \(M\ge12\), the number \(h\) of walls belonging to no
coplanar triple satisfies \(h\le(15-M)+\lfloor(15-M)/2\rfloor\).
The remaining \(M-h\) walls admit a sequence with at most
\(\lfloor2(M-h)/3\rfloor\) free steps. When \(M=15\), the additional
geometric lemma `hnot_part_15` improves this last bound to nine. For
\(M\le11\), taking every step free already costs at most \(33\).
These are the bounds assembled in
[`exists_dag_of_cones_r4`](../Solution.lean).

If a part has empty interior, at most five parts remain full-dimensional.
Only ten pair hyperplanes are then needed, and ten free normals cost at most
thirty parameters. This case is included in the same family of charts.

For each marker, choose a wall containing it and a nonzero coordinate of
that wall's normal. Choose the other \(d-1\) marker coordinates freely and
solve its orthogonality equation for the remaining coordinate. All discrete
choices form the finite type `PlaneDagConfig`. The resulting parameter count
is the bound in [`card_planeDagParamIdx`](../Solution.lean):

\[
4(d-4)+33+m(d-1)=4d+17+m(d-1).
\]

The map `planeDagMap` is differentiable on `planeDagOpen`, where the chosen
denominators are nonzero. The coverage lemma
`mem_range_planeDagMap_of_dag` puts every avoided marker tuple from this
rank case into one of these images.

### 9.4. Rank five: the tree parameter count

The rank-five branch uses the triangle dependences above. Let \(q\)
be an integer with \(1\le q\le5\) and \(q\le d\). The classification lemma
[`exists_treeParam`](../Solution.lean) applies to a vector family
\(v:\mathrm{Fin}(q+1)\times\mathrm{Fin}(q+1)\to V\) that is antisymmetric,
nonzero off the diagonal, has dependent triangles, and spans a space of
dimension at least \(q\).
It represents every edge vector up to a nonzero scalar using one of finitely
many objects `TreeShape d q`.

At a star node of dimension \(q\), the parameters consist of a subspace
chart with \(q(d-q)\) coordinates, \(q\) normalized directions with
\(q(q-1)\) coordinates, and at most \(q-1\) relative scale coordinates.
Their total is at most \(qd-1\). When no independent star exists, the construction
splits recursively into smaller configurations. Their dimensions add to
\(q\), and their parameter counts retain the same upper bound. This is
[`card_paramIdx_bound`](../Solution.lean), applied with \(q=5\).

Choose, for each marker, its containing pair hyperplane and a nonzero normal
coordinate. Adding its \(d-1\) free coordinates gives

\[
(5d-1)+m(d-1).
\]

The finite type `MaxRankConfig` records these choices. The lemmas
`card_maxRankParamIdx`, `differentiableOn_maxRankMap`, and
`mem_range_maxRankMap_of_tree` provide respectively the count, regularity,
and coverage of the corresponding images.

### 9.5. Avoiding the bad images

The marker configuration space is \(V^m\cong\mathbb R^{md}\). A tuple whose
points lie in the open unit ball and are avoided by a central partition
belongs to one of the two finite
families of differentiable images just constructed. Since \(m=5d\), their
dimension bounds satisfy

\[
4d+17+5d(d-1)<5d^2\quad\Longleftrightarrow\quad d>17,
\qquad
5d-1+5d(d-1)=5d^2-1.
\]

This is the precise source of the threshold. The rank-five count always
has a one-dimensional margin; the lower-rank count requires \(d>17\).

The lemma [`volume_image_eq_zero_of_card_lt`](../Solution.lean) proves that
each such image has Lebesgue measure zero. Its implementation embeds the
smaller parameter space into a coordinate hyperplane of the target and
uses preservation of null sets under differentiable maps on that set.
Finite unions remain null. The set of tuples with all markers in the open
unit ball is nonempty and open, hence has positive measure. Choosing a tuple
outside the bad union proves `exists_isBlocking_5d`. This is an existence
argument; it does not supply numerical marker coordinates.
Fix a blocking family \(p:\mathrm{Fin}(m)\to V\) furnished by this theorem.


## 10. From the simplex map to a body functional

### 10.1. Padding to every dimension

For an integer \(m>0\), let \(\Delta^{m-1}\subset\mathbb R^m\) be the standard
simplex. An almost-six embedding is a continuous map on this simplex under
which six points with pairwise disjoint barycentric supports cannot all have
the same image. No injectivity on individual faces is required by this
definition.

The proved theorem `almostSix_ninety` supplies such a map
\(g_0:\Delta^{89}\to\mathbb R^{16}\). Joining with the constant map
\(\Delta^4\to\mathbb R^0\) adds five vertices and one target coordinate.
The constant map has the required property because six nonempty disjoint
supports cannot fit into five vertices. After \(d-18\) joins, the vertex and
target counts are \(90+5(d-18)=5d\) and \(16+(d-18)=d-2\).
Thus, with \(m=5d\), we obtain \(g:\Delta^{m-1}\to\mathbb R^{d-2}\).
The join is a weighted join, with continuous extension at zero block mass;
the relevant proved lemmas are `join_almostSixEmbedding`,
`emptyFive_almostSixEmbedding` and `iterated_padding_from` in
[Solution.lean](../Solution.lean).


### 10.2. Continuous weights on all convex bodies

Write \(d_H\) for the Hausdorff metric on \(\mathcal K_d\).

For a point \(p\in V\) and a body \(C\in\mathcal K_d\), define the inward
distance \(w_p(C)=\inf\{\lVert p-y\rVert:y\in V\setminus C\}\).
The complement is nonempty because \(C\) is compact and \(d>0\).
The weight is nonnegative, and \(w_p(C)>0\) precisely when
\(p\in\operatorname{int}C\).

For bodies \(C,D\in\mathcal K_d\), the source proves
\(w_p(D)\leq w_p(C)+d_H(C,D)\). Choose a point \(y\in V\setminus C\)
and a unit vector \(u\in V\) strictly separating \(y\) from \(C\).
For a real number \(\varepsilon>0\), define a point \(z\in V\) by
\(z=y+(d_H(C,D)+\varepsilon)u\).
Hausdorff approximation and the separating inequality imply \(z\notin D\).
Consequently \(w_p(D)\leq\lVert p-y\rVert+d_H(C,D)+\varepsilon\).
Taking the infimum over \(y\), then letting \(\varepsilon\) decrease to zero,
gives the estimate. Interchanging \(C,D\) shows
\(\lvert w_p(C)-w_p(D)\rvert\leq d_H(C,D)\).

Thus each weight is continuous on the whole body space, including bodies with
empty interior. These are the assertions `inwardDist_pos_iff`,
`inwardDist_le` and `continuous_inwardDist` following the definition
[inwardDist](../Solution.lean).

### 10.3. A positive radius from compactness

Blocking at the origin yields a uniform version: there is a real number
\(0<\eta<1\) such that any six-partition whose every part meets
\(\overline B_V(0,\eta)\) contains a marker in some interior.
This is [exists_eta_of_isBlocking](../Solution.lean).

Here is its compactness argument. Blaschke compactness makes the family of
bodies contained in \(B\) compact. Inside its sixth power, let \(\mathcal F\)
consist of tuples covering \(B\), having disjoint interiors, and having no
marker in any interior. These are closed conditions. Coverage can be written
as \(\prod_i\operatorname{dist}(x,C_i)=0\) for every \(x\in B\); interior
disjointness as \(w_x(C_i)w_x(C_j)=0\) for every \(x\in V\) and \(i\ne j\);
and absence of markers as \(w_{p_a}(C_i)=0\).
Hence \(\mathcal F\) is compact.

Define a continuous function \(\rho:\mathcal K_d^6\to\mathbb R\) by
\(\rho(\mathbf C)=\sum_i\operatorname{dist}(0,C_i)\). Its restriction to
\(\mathcal F\) has a strictly positive minimum \(\delta\), if \(\mathcal F\)
is nonempty. A zero minimum would put
the origin in every closed part, contradicting blocking. Choose
\(\eta=\min(1/2,\delta/12)\). If all parts meet the closed \(\eta\)-ball,
then \(\rho(\mathbf C)\leq6\eta\leq\delta/2\), so the tuple cannot belong
to \(\mathcal F\).
If \(\mathcal F\) is empty, choose \(\eta=1/2\).
Allowing degenerate parts in the blocking condition is essential here:
nonempty interiors need not persist under Hausdorff limits.

### 10.4. An absolutely continuous probability measure

Let \(B_\eta=\overline B_V(0,\eta)\subset V\), and let \(\lambda_d\) be Lebesgue measure on
\(V\). For every measurable set \(A\subset V\), define
\(\mu(A)=\lambda_d(A\cap B_\eta)/\lambda_d(B_\eta)\).
The radius is positive, so \(0<\lambda_d(B_\eta)\); compactness gives
\(\lambda_d(B_\eta)<\infty\). Thus \(\mu\) is a probability measure,
\(\mu\ll\lambda_d\), and \(\mu(B_\eta)=\mu(B)=1\), since \(B_\eta\subset B\).
These identities are proved inside
[normalized_ball_measure_props](../Solution.lean).

Every fair part has measure \(1/6>0\), so it meets \(B_\eta\). The source uses
`fair_meets_eta_ball`, which proves the stronger assertion under the
concentration inequality \(5\mu(B)<6\mu(B_\eta)\). Our measure satisfies that
inequality immediately. The uniform blocking conclusion therefore applies
to every fair six-partition.

### 10.5. The functional and the contradiction

For each body \(C\in\mathcal K_d\), let \(w(C)\in\mathbb R^m\) have coordinates
\(w_a(C)=w_{p_a}(C)\), and let \(s(C)=\sum_a w_a(C)\).
When \(s(C)>0\), the vector \(w(C)/s(C)\) belongs to \(\Delta^{m-1}\).
Define

\[
\Phi(C)=\bigl(s(C),\,s(C)g(w(C)/s(C))\bigr)\quad\text{if }s(C)>0.
\]
When \(s(C)=0\), set \(\Phi(C)=(0,0)\).

Its target is \(\mathbb R\times\mathbb R^{d-2}\cong\mathbb R^{d-1}\).
Continuity where \(s>0\) follows by composition. At zero, compactness of the
simplex bounds \(\lVert g(x)\rVert\) by a finite constant \(M\), so the last
coordinates have norm at most \(Ms(C)\). They therefore tend to zero even
if the normalized weights have no limit. This is the perspective argument
formalized in `continuousOn_perspective`; continuity of \(g\) outside the
simplex is unnecessary.

Suppose a fair six-partition had equal \(\Phi\)-values. The first coordinates
give a common total weight \(s\geq0\). If \(s=0\), every nonnegative marker
weight vanishes. No part then contains a marker in its interior, contradicting
uniform blocking.

If \(s>0\), define six points \(x_i=w(C_i)/s\in\Delta^{m-1}\). Their supports
are pairwise disjoint: a coordinate positive for both \(x_i\) and \(x_j\)
would put the same marker in both interiors. Equality of the remaining
coordinates, followed by cancellation of \(s\), gives
\(g(x_i)=g(x_0)\) for every \(i\). This contradicts the almost-six property.

This completes [convex_partition_of_embedding_and_blocking](../Solution.lean).
The final theorem supplies its two inputs through `almostSix_ninety`,
join-padding and `exists_isBlocking_5d`. The older conditional helper
`convex_partition_counterexample_ge_18` remains useful internally; its
historical comment about an open embedding problem does not describe the
completed theorem in `DimensionEighteen.lean`.

## 11. Verification and reproducibility

The final unconditional declarations are
`AkopyanSixfold.almostSix_ninety` and
`AkopyanSixfold.convex_partition_counterexample_gt_17` in
`AkopyanResearch/Completion/DimensionEighteen.lean`.
The latter has only the natural-number argument and the hypothesis
\(17<d\). The relative lifting theorem is proved inside the project.
The source `PalomarSolution.lean` is the publication entry point.

The project uses Lean 4.35.0 and a pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The final integrated check passed on 24 November 2026 at 08:56:01 UTC;
a build starting without project object files passed at 09:01:10 UTC.
Both checks had the same 472 source-input hashes. All six stages passed:
source structure, vendored provenance, 37 infrastructure tests, the project
build, the literal statement check, and the owner-based axiom audit.

The audit checked 16,765 declarations from 438 proof-module owners,
including private and unused declarations. Its permitted axiom set is
exactly `propext`, `Classical.choice`, and `Quot.sound`.
Proof modules contain no admission or new axiom. The independent
`Challenge.lean` contains two intentional specification holes; no proof
module imports it. The original `Solution.lean` is preserved byte for byte.
The release records the exact change from the previous B36 specification
to the now-proved B18 statement.

Separately compiled challenge and proof interfaces agree in all nine types
and seven definition bodies, retaining implicit arguments, typeclass
arguments, and universe levels. An additional comparison of the clean and
working object files checked the stored declarations, types, and proof
bodies wherever their serializations differed. Those mathematical objects
agree exactly; source-path metadata can differ between build directories.

The selected export contains the actual proof bodies of the original
Tverberg counterexample, the ninety-vertex almost embedding, the final
convex-partition theorem, and the relative lifting theorem. Lean checker,
NanoDa, and con-ron accepted this export at 09:15:21 UTC. A supplemental
replay using the Palomar-approved con-ron release also passed at
09:18:19 UTC. The unchanged export has 700,996,206 bytes and SHA-256

`978d77cdeecf295f3ae79fbc5c18f5d42fb66e911dc7ce0e758925c7d543a0be`.

The source archive includes hashes, checker versions, commands, complete
logs, and machine-readable reports. It omits the large export and compiled
build caches; the scripts reproduce them. The main entry points are
`scripts/verify.sh`, `scripts/verify-comparator.sh`,
`verification/d18-compiled-interface/`, and
`verification/d18-approved-con-ron/`. Exact invocation instructions are
in the release README and verification README.

These completed checks are distinct from the registry workflow. The local
sandboxed Comparator attempt stopped during `bwrap` setup before comparison.
The official Palomar workflow has not been executed. Submission metadata
still requires confirmed human authors and maintainers, a project licence,
and a public repository and immutable commit. The supplied archive's
attribution is preserved without assigning unverified authorship to the
completion. No claim of priority or completed publication is made here.

## 12. Mathematical context and references

The positive convex equipartition theorem for prime-power multiplicities
is proved by Karasev, Hubard, and Aronov [KHA14]. It concerns an absolutely
continuous finite measure and continuous functionals on individual convex
bodies. The obstruction above has precisely that individual-body meaning.
A negative equivariant test-map statement allowing dependence on an entire
partition is a different assertion. The planar theorem for any number of
parts in Akopyan, Avvakumov, and Karasev [AAK26] is also consistent with the
present higher-dimensional obstruction.

The published topological Tverberg counterexamples [F15, AMSW21, AKS23]
provide context. They are not cited as proofs of the exact ninety-vertex
construction in this project. The primary sources examined during this
work did not identify its exact construction or the original supplied
almost-six embedding of the thirty-five-dimensional simplex into
six-dimensional space. That is a bounded literature-search result, not a
claim of novelty. Standard homotopy background is available in [H02], and
subspace-arrangement background in [ZZ93]. The present formalization
proves its concrete coordinate comparisons and relative lifting statements.

This companion was prepared with automated assistance from ChatGPT
(GPT-6 Astra Pro) and checked against the project sources. Human authorship
and responsible maintenance require confirmation in the publication metadata;
no external human peer review is claimed.

The following references are the primary sources checked for the release.
The separate note `docs/MATHEMATICAL_CONTEXT.md` gives the numerical
comparisons and the limits of the attribution evidence.



- **[T66]** H. Tverberg, *A Generalization of Radon's Theorem*, Journal of
  the London Mathematical Society s1-41 (1966), 123–128.
  [DOI: 10.1112/jlms/s1-41.1.123](https://doi.org/10.1112/jlms/s1-41.1.123).
- **[F15]** F. Frick, *Counterexamples to the topological Tverberg
  conjecture*, Oberwolfach Reports 12(1) (2015), 318–321.
  [arXiv:1502.00947v2](https://arxiv.org/abs/1502.00947v2).
- **[AMSW21]** S. Avvakumov, I. Mabillard, A. Skopenkov, U. Wagner,
  *Eliminating Higher-Multiplicity Intersections, III. Codimension 2*,
  Israel Journal of Mathematics 245 (2021), 501–534.
  [arXiv:1511.03501v5](https://arxiv.org/abs/1511.03501v5);
  [DOI: 10.1007/s11856-021-2216-z](https://doi.org/10.1007/s11856-021-2216-z).
- **[AKS23]** S. Avvakumov, R. Karasev, A. Skopenkov,
  *Stronger counterexamples to the topological Tverberg conjecture*,
  Combinatorica 43 (2023), 717–727.
  [arXiv:1908.08731v4](https://arxiv.org/abs/1908.08731v4);
  [DOI: 10.1007/s00493-023-00031-w](https://doi.org/10.1007/s00493-023-00031-w).
- **[KHA14]** R. Karasev, A. Hubard, B. Aronov,
  *Convex Equipartitions: The Spicy Chicken Theorem*,
  Geometriae Dedicata 170 (2014), 263–279.
  [arXiv:1306.2741v2](https://arxiv.org/abs/1306.2741v2);
  [DOI: 10.1007/s10711-013-9879-5](https://doi.org/10.1007/s10711-013-9879-5).
- **[BZ14]** P. V. M. Blagojević, G. M. Ziegler,
  *Convex Equipartitions via Equivariant Obstruction Theory*,
  Israel Journal of Mathematics 200 (2014), 49–77.
  [arXiv:1202.5504v3](https://arxiv.org/abs/1202.5504v3);
  [DOI: 10.1007/s11856-014-1006-6](https://doi.org/10.1007/s11856-014-1006-6).
- **[AAK26]** A. Akopyan, S. Avvakumov, R. Karasev,
  *Convex fair partitions into an arbitrary number of pieces*,
  Advances in Mathematics 493 (2026), article 110927.
  [arXiv:1804.03057v14](https://arxiv.org/abs/1804.03057v14);
  [DOI: 10.1016/j.aim.2026.110927](https://doi.org/10.1016/j.aim.2026.110927).
- **[BS26]** P. V. M. Blagojević, N. Sadovek,
  *Convex equipartitions inspired by the little cubes operad*,
  Israel Journal of Mathematics 271 (2026), 399–459;
  first published online 29 June 2025.
  [arXiv:2305.10711v2](https://arxiv.org/abs/2305.10711v2);
  [DOI: 10.1007/s11856-025-2785-3](https://doi.org/10.1007/s11856-025-2785-3).
- **[H02]** A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002). [Author's book page](https://pi.math.cornell.edu/~hatcher/AT/ATpage.html);
  [Chapter 4, including Theorem 4.32](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf).
- **[ZZ93]** G. M. Ziegler, R. T. Živaljević,
  *Homotopy types of subspace arrangements via diagrams of spaces*,
  Mathematische Annalen 295 (1993), 527–548.
  [DOI: 10.1007/BF01444901](https://doi.org/10.1007/BF01444901);
  [author's publication record](https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Publikationen_old/homotopy_types_of_subspace_arrangements_via_diagrams_of_spaces/index.html).
