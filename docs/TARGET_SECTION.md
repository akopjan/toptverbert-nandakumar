# The chosen section of the comparison target

The maps `ConcreteComparisonTarget.sectionMap` and
`ConcreteComparison.chosenSection` are constructed before the comparison
connectivity theorem. They provide compatible target values and paths on
every mass face. The later relative lifting theorem lifts these data into
the quadratic-arrangement complement. This note describes the former
construction and its precise earlier inputs.

## 1. The supplied sphere map and its ordinary nullhomotopy

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

## 2. Explicit joins and subgroup contractions

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

## 3. Row conventions and pair paths

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

## 4. One fixed join stage on all faces

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
The target \(P_S=\mathrm{ConcreteComparisonTarget.Space}\ S\) records all
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
