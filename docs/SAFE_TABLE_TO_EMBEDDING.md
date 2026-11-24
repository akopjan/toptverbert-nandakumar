# From a safe planar table to an almost-six map

This note explains the analytic passage from a table on fifteen colors with
six labels to a continuous almost-six map \(\Delta^{89}\to\mathbb R^{16}\).
The project proves both a general averaging construction and a construction
using quadratic coefficients. The final theorem uses the latter; the former
makes the averaging and the treatment of zero masses particularly explicit.
Neither construction assumes continuity of conditional probabilities at zero
mass.

## 1. The table and its precise hypotheses

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

## 2. Two averaged height coordinates

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

## 3. Fourteen masses suffice

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

## 4. Disjoint supports force a matching

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

## 5. The quadratic implementation used by the final theorem

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
