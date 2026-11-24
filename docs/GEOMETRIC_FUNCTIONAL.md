# From an almost-six embedding to the convex-partition obstruction

This note explains the final geometric and analytic part of
`AkopyanSixfold.convex_partition_counterexample_gt_17`. The topological construction
of the required simplex map is described in
[DIMENSION_EIGHTEEN_PROOF.md](DIMENSION_EIGHTEEN_PROOF.md).
All lemmas below are proved in the project; the hypotheses of the general
transfer lemma are discharged by the final theorem.

## 1. The statement and the simplex map

Fix a natural number \(d\geq18\). Let \(V=\mathbb R^d\) be Euclidean space,
let \(B=\overline B_V(0,1)\), and let \(\mathcal K_d\) be the metric space of
nonempty compact convex subsets of \(V\), with Hausdorff distance \(d_H\).
Bodies in \(\mathcal K_d\) may have empty interior. A six-partition is a tuple
\((C_0,\ldots,C_5)\in\mathcal K_d^6\) whose union is \(B\), with all interiors
nonempty and pairwise disjoint.

The theorem constructs a continuous map \(\Phi:\mathcal K_d\to\mathbb R^{d-1}\)
and a probability measure \(\mu\) on \(V\), absolutely continuous with respect
to Lebesgue measure, such that

\[
 \bigl[\mu(C_i)=\mu(B)/6\ \text{for every }i\bigr]
 \quad\Longrightarrow\quad
 \Phi(C_i)\ne\Phi(C_0)\ \text{for some }i
\]

for every six-partition. The construction below has \(\mu(B)=1\).
See the literal statement in
[DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean).

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

## 2. A finite set of blocking markers

Let \(p:\{0,\ldots,m-1\}\to V\) be a marker configuration. It is *blocking*
if every tuple of six bodies whose union is \(B\), with pairwise disjoint interiors
and with \(0\) in every body, contains some \(p_a\) in some body's interior.
This condition includes tuples with degenerate parts.

The theorem [exists_isBlocking_5d](../Solution.lean) proves that a blocking
configuration exists for \(m=5d\). Fix such a blocking configuration for
the rest of this note. Its proof chooses markers in the open unit
ball outside finitely many exceptional images. Convex separation associates
separating normals to a missed central partition. The proof divides these
configurations according to the rank of five sums of normals. It parametrizes
both branches by differentiable maps from open subsets of spaces with the
following dimension bounds:

| Branch | Parameter dimension, at most | Configuration dimension |
| --- | ---: | ---: |
| Rank at most four | \(4d+17+m(d-1)\) | \(md\) |
| Rank five | \(5d-1+m(d-1)\) | \(md\) |

For \(m=5d\), the differences are \(d-17>0\) and \(1\). The exceptional images
therefore have Lebesgue measure zero, whereas the open set of configurations
inside the ball has positive measure. This proves existence, rather than
assuming a generic configuration works. The source lemmas
`card_planeDagParamIdx`, `card_maxRankParamIdx` and
`volume_image_eq_zero_of_card_lt` establish the dimension and measure steps.

## 3. Continuous weights on all convex bodies

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

## 4. A positive radius from compactness

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

## 5. An absolutely continuous probability measure

Let \(E=\overline B_V(0,\eta)\), and let \(\lambda_d\) be Lebesgue measure on
\(V\). For every measurable set \(A\subset V\), define
\(\mu(A)=\lambda_d(A\cap E)/\lambda_d(E)\).
The radius is positive, so \(0<\lambda_d(E)\); compactness gives
\(\lambda_d(E)<\infty\). Thus \(\mu\) is a probability measure,
\(\mu\ll\lambda_d\), and \(\mu(E)=\mu(B)=1\), since \(E\subset B\).
These identities are proved inside
[normalized_ball_measure_props](../Solution.lean).

Every fair part has measure \(1/6>0\), so it meets \(E\). The source uses
`fair_meets_eta_ball`, which proves the stronger assertion under the
concentration inequality \(5\mu(B)<6\mu(E)\). Our measure satisfies that
inequality immediately. The uniform blocking conclusion therefore applies
to every fair six-partition.

## 6. The functional and the contradiction

For each body \(C\in\mathcal K_d\), let \(w(C)\in\mathbb R^m\) have coordinates
\(w_a(C)=w_{p_a}(C)\), and let \(s(C)=\sum_a w_a(C)\).
When \(s(C)>0\), the vector \(w(C)/s(C)\) belongs to \(\Delta^{m-1}\).
Define

\[
 \Phi(C)=
 \begin{cases}
 \bigl(s(C),\,s(C)g(w(C)/s(C))\bigr),&s(C)>0,\\
 (0,0),&s(C)=0.
 \end{cases}
\]

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
