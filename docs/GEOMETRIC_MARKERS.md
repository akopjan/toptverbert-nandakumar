# Blocking markers and the threshold \(d>17\)

This note follows the geometric argument in [Solution.lean](../Solution.lean).
All named lemmas below belong to `AkopyanSixfold`; private lemma names identify
their source declarations. The final topological input and its assembly with
this argument are described in [PROOF_MAP.md](PROOF_MAP.md).

## 1. The blocking statement

Let \(d\ge18\) be an integer, let \(E=\mathbb R^d\) be Euclidean space, and let
\(B\subset E\) be the closed unit ball. Put \(m=5d\). A central six-partition is
a family \(C:\mathrm{Fin}(6)\to\operatorname{ConvexBody}(E)\) whose union is
\(B\), whose members have pairwise disjoint interiors, and all contain the origin.
Here a convex body means a nonempty compact convex set; its interior may be
empty. A marker family \(p:\mathrm{Fin}(m)\to E\) is blocking if every such
partition has a marker in the interior of a part.

The theorem [`exists_isBlocking_5d`](../Solution.lean) asserts existence of
this family. Its proof chooses every marker in the open unit ball, although
the theorem's displayed type only records `IsBlocking p`. Allowing degenerate
parts is essential: a Hausdorff limit of partitions may acquire such parts.

## 2. Separating normals and the rank split

For a fixed central partition, choose vectors \(n_{ij}\in E\), indexed by
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

Define vectors \(a_i\in E\) by \(a_i=\sum_j n_{ij}\), and let \(L\le E\) be
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

## 3. Rank at most four: why the count is \(4d+17\)

In the dependent case,
[`separating_normals_in_rref4_span`](../Solution.lean) places all normals in
a four-dimensional subspace, even when their span has smaller dimension.
Choose injective pivot coordinates \(I:\mathrm{Fin}(4)\to\mathrm{Fin}(d)\)
and vectors \(u_r\in E\) satisfying \(u_r(I(s))=\delta_{rs}\). Their remaining
coordinates contribute \(4(d-4)\) real parameters. Every normal is recovered
from its four pivot coordinates by \(n_{ij}=\sum_r n_{ij}(I(r))u_r\).

Suppose first that every part has nonempty interior. Define vectors
\(c_{ij}\in\mathbb R^4\) by \(c_{ij}(r)=n_{ij}(I(r))\), and define a linear
map \(P:E\to\mathbb R^4\) by \(P(x)_r=\langle u_r,x\rangle\). The closed
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

## 4. Rank five: the tree parameter count

The rank-five branch uses the triangle dependences above. Let \(q\)
be an integer with \(1\le q\le5\) and \(q\le d\). The classification lemma
[`exists_treeParam`](../Solution.lean) applies to a vector family
\(v:\mathrm{Fin}(q+1)\times\mathrm{Fin}(q+1)\to E\) that is antisymmetric,
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

## 5. Avoiding the bad images

The marker configuration space is \(E^m\cong\mathbb R^{md}\). A tuple whose
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

## 6. From central partitions to a uniform inner ball

Fix a blocking family \(p\). Blaschke compactness, proved as
[`blaschke_isCompact_subsets_unitBall`](../Solution.lean), makes the space
of nonempty compact convex subsets of \(B\) compact in the Hausdorff metric.
Let \(\mathcal S\) be the set of six-tuples in this space that cover \(B\),
have disjoint interiors, and avoid every marker in their interiors.

For a point \(x\in E\) and a convex body \(C\subset E\), define its inward
distance by \(w_x(C)=\operatorname{dist}(x,E\setminus C)\). This is positive
exactly when \(x\in\operatorname{int}C\), and is continuous in \(C\).
Coverage is expressed by \(\prod_i\operatorname{dist}(x,C_i)=0\) for every
\(x\in B\); disjointness by \(w_x(C_i)w_x(C_j)=0\) for \(i\ne j\); marker
avoidance by \(w_{p_a}(C_i)=0\). These closed conditions make
\(\mathcal S\) compact, including its degenerate limits.

Define a continuous function \(F:\operatorname{ConvexBody}(E)^6\to\mathbb R\)
by \(F(C)=\sum_i\operatorname{dist}(0,C_i)\). It is strictly positive on
\(\mathcal S\): if it
vanished, all six closed parts would contain the origin, contradicting
blocking. If \(\mathcal S\ne\varnothing\), let \(f>0\) be its minimum and
choose \(\eta=\min(1/2,f/12)\). A partition whose six parts meet the closed
\(\eta\)-ball satisfies \(F(C)\le6\eta\le f/2\), so cannot belong to
\(\mathcal S\). If \(\mathcal S\) is empty, take \(\eta=1/2\).
This proves [`exists_eta_of_isBlocking`](../Solution.lean).

Finally, normalized Lebesgue measure on that inner ball forces every part
of an equal-measure partition to meet it. In
[`convex_partition_of_embedding_and_blocking`](../Solution.lean), the
inward distances at the markers then supply simplex coordinates. Disjoint
interiors give disjoint coordinate supports, and blocking ensures a positive
total weight in some part. The almost-six-embedding input converts these
facts into the required failure of simultaneous equality of the continuous
convex-body functionals.
