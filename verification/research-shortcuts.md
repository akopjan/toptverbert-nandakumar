# Checks of shorter routes from the proved scalar example

This is a source-level mathematical addendum, not a new Lean theorem. The
unconditional input is the verified almost-six map with 36 source vertices and
target dimension 6. No argument below proves nonexistence of the desired map
with 90 vertices and target dimension 16. The conclusions concern the specific
constructions examined.

## 1. Joins, auxiliary blocks, and ordinary constraints

For a signature `(n,q)`, where `n` is the number of source vertices and `q` the
target dimension, put `δ(n,q)=n−5(q+1)`. The actual
`join_almostSixEmbedding` in `Solution.lean` sends two signatures to
`(n₁+n₂,q₁+q₂+1)`, so δ is additive. The proved scalar seed has δ=1 and costs
seven units of `q+1`. Padding adds `(5,1)` and preserves δ.

This also controls joins with any further helper blocks whose signatures satisfy
`n≤5(q+1)`: such blocks have nonpositive excess. If a construction uses `k`
scalar seeds, then `δ≤k` and `q+1≥7k`. Source restriction and target dimension
enlargement do not improve these inequalities. Consequently, in this class,

`n≤5(q+1)+⌊(q+1)/7⌋`.

At `q=16` the bound is 87, attained by two scalar seeds and three padding steps.
This extends the numerical observation to nonpositive-excess auxiliary blocks;
it is not a classification of all possible topological operations.

The usual one-coordinate constraint method gives exactly the same allowance
when the known map is defined on a face. Let `K` be a nonempty face of a simplex
with `N` vertices, and let `m` be the number of vertices of `K`. Every six
support-disjoint simplex points include a point in `K` if and only if `N−m≤5`.
Indeed, six points outside `K` need six distinct outside vertices; conversely,
six outside vertices themselves give a counterexample. Extend the face map by
the affine retraction sending all outside mass to one fixed vertex of `K`, and
append the outside mass as one real coordinate. Equality of six outputs forces
that mass to vanish, hence returns all six points to `K`. This adds at most five
vertices per extra coordinate.

A different unavoidable complex could be useful, but needs a new map. For
example, the 14-skeleton of the simplex on 90 vertices is six-unavoidable: a
point outside it uses at least 16 vertices, so six disjoint such supports would
need 96 vertices. The 13-skeleton is not six-unavoidable, since six disjoint
15-element supports partition the 90 vertices. The corresponding constraint
route therefore needs a new almost-six map on the entire 14-skeleton into
`ℝ¹⁵`; the proved map on one 36-vertex face does not supply it.

Two other direct operations fail for explicit reasons. A map from a larger
simplex to the 36-vertex simplex that preserves disjointness of every six
supports cannot exist when the source has more than 36 vertices. Any two source
vertices extend to six distinct vertices, so all vertex images would have
pairwise disjoint nonempty supports. There are only 36 target coordinates.
Likewise, a product formed only from row and column marginals fails on a `6×6`
grid. For `j∈ℤ/6`, give weight `1/6` to the six vertices `(i,i+j)`. These six
points have disjoint supports but identical uniform row and column marginals.
Every map depending only on those two marginals identifies all six points.

## 2. Why the existing surgery does not handle the four extra dimensions

The precise input is `Surgery.GoodMap` in
`RequestProject/Surgery/Good.lean`. For a map `F:ℝ^(k+1)→V` and each linear
test `Q:V→ℝ^(k+1)`, it requires a finite zero set, a locally affine expression
at each zero, an invertible square frame matrix, and vanishing signed count of
the zeros. `Surgery.surgery` in `RequestProject/Surgery/Main.lean` then performs
strong induction on the finite total number of zeros. Its operations separate
two opposite-sign zeros, clear an arc, and cancel the pair. The scalar
application in `Construction/Assembly.lean` uses `k=4`.

For the planar 15-colour construction the mass simplex has dimension 14, whereas
a matching test has rank 10. A transverse zero set therefore has expected
dimension four. This agrees with the deleted-configuration count for a map
with 90 source vertices into `ℝ¹⁶`: the relevant configuration strata have
dimension `90−6`, and equal images impose `5·16` equations.

Replacing the ten-coordinate test `Q` by a fourteen-coordinate test does not
repair the mismatch. To infer `Q(v)≠0` from `Q̃(v)≠0`, one needs
`ker Q⊆ker Q̃`. It follows that `rank Q̃≤rank Q≤10`, so every fourteen-square
frame matrix is singular. Padding with zero coordinates is a special case.
Adding four independent equations instead avoids a smaller bad set and does
not establish avoidance of the original matching kernel.

A literal cylinder `F(x,u)=F₀(x)` turns every zero of `QF₀` into an infinite
parameter family, violating both finiteness and invertibility of the required
frame. Applying the theorem separately at each parameter gives no continuous
choice of the modifications and no control of the lateral boundary. Even a
constant family on an unbounded parameter space changes the compact support
`K` to the noncompact set `K×ℝ⁴`. Thus the existing theorem is an isolated-zero
cancellation theorem, not a parametrized cancellation theorem. A relative
family theorem would require additional proof, precisely where the present
comparison/lifting route remains unfinished.

## 3. Fair central partitions do not follow from the concentration argument

The marker transfer in `Solution.lean` uses measures concentrated near the
origin. Fair partitions for these measures have central limiting partitions,
but the limits need not have equal angular volumes. Offsets of the same order
as the concentration radius survive after rescaling.

There is an explicit reason for this even among full-rank simplex fans. Let
`a₀,…,a₅∈ℝᵈ` be affinely independent, and let `ν` be an absolutely continuous
probability measure with compact support. For `b∈ℝ⁶` with `Σbᵢ=0`, define

`Ψ(b)=∫ maxᵢ(⟨aᵢ,x⟩+bᵢ) dν(x)−(Σbᵢ)/6`.

This function is coercive on that hyperplane: it is bounded below by
`maxᵢ bᵢ` minus a fixed constant, and the maximum controls the norm when the sum
is zero. It therefore has a minimum. Tie hyperplanes have measure zero, so its
derivatives are the six cell masses minus `1/6`. The constrained minimum has
all six masses equal to `1/6`.

For the pushforward measure `μ_η` under `x↦ηx`, the cells defined by
`⟨aᵢ,x⟩+ηbᵢ≥⟨aⱼ,x⟩+ηbⱼ` are therefore fair. After intersection with the unit
ball and passage to `η→0`, they converge to the central normal fan determined
by the `aᵢ`, whose angular masses were unrestricted. Thus five fairness
equations cannot simply be subtracted from the dimension of the limiting
central family in the existing compactness argument.

Nor does full normal rank five force a simplex fan. Take three sectors of angle
`2π/3` in a fixed two-dimensional subspace, and bisect each sector with its own
independent coordinate in the orthogonal complement. The six cones have equal
solid angle, and their separating normals span a five-dimensional space. They
include repeated separating hyperplanes. These split constructions are among
the families covered by the actual `TreeShape` parametrization; a fairness
argument confined to simplex fans would miss them.

One could try to force centrality directly by adding `dist(0,C)` as a coordinate
of the body functional. Since some cell contains the origin, equality of that
coordinate forces all cells to contain it. With the existing marker-mass
coordinate retained, this leaves target dimension 15 for the simplex map when
`d=18`. The two-seed construction then supplies 82 vertices. Even if five
independent fairness equations cut the 89-dimensional central family down to
dimension 84, the corresponding generic marker count would be 85. This
particular modification retains the same three-vertex deficit. It does not
exclude a different geometric construction or a more economical functional.

No shorter implication from the already proved inputs to the required
90-vertex, 16-dimensional almost-six map was obtained. The concrete remaining
topological input in the release is still `RequiredRelativeLifting`.
