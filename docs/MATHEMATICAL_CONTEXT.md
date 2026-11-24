# Mathematical context and source attribution

Reviewed against primary sources on **24 November 2026**. This note describes
the mathematical statements, their relation to published work, and the limits
of the available attribution evidence. Build and axiom-audit results are
recorded separately in the verification reports.

## The statements in this project

For natural numbers \(N,q,r\), with \(r\geq2\), let \(\Delta^N\) be the
standard \(N\)-simplex. A continuous map \(f:\Delta^N\to\mathbb R^q\) is an
*almost \(r\)-embedding* if the images of any \(r\) pairwise disjoint faces
have empty common intersection. This is the meaning of
`AkopyanSixfold.IsAlmostSixEmbedding` when \(r=6\): its formulation uses
points with pairwise disjoint barycentric supports. It does not assert
that \(f\) is injective.

| Lean declaration | Mathematical conclusion |
| --- | --- |
| `AkopyanSixfold.tverberg_counterexample` | An almost six-embedding \(\Delta^{35}\to\mathbb R^6\). |
| `AkopyanSixfold.almostSix_ninety` | An almost six-embedding \(\Delta^{89}\to\mathbb R^{16}\). |
| `AkopyanSixfold.convex_partition_counterexample_gt_17` | A convex equipartition obstruction in every integer dimension \(d>17\). |

Here is the precise meaning of the third statement. For an integer \(d>17\),
let \(\mathcal K_d\) be the space of nonempty compact convex subsets of
\(\mathbb R^d\), with the Hausdorff metric, and let \(B_d\subset\mathbb R^d\)
be the closed unit ball. There exist a continuous map
\(\Phi:\mathcal K_d\to\mathbb R^{d-1}\) and a probability measure \(\mu\)
on \(\mathbb R^d\), absolutely continuous with respect to Lebesgue measure,
for which no six convex bodies \(C_0,\ldots,C_5\in\mathcal K_d\) satisfy
all three requirements: their union is \(B_d\), their interiors are
nonempty and pairwise disjoint, and

\[
\mu(C_i)=\mu(B_d)/6\quad\text{and}\quad\Phi(C_i)=\Phi(C_0)
\qquad(0\leq i<6).
\]

Each value \(\Phi(C_i)\) depends only on the individual body \(C_i\).
The functionals are not specified to be surface area, perimeter, or
additive measures. The declarations are in [Solution.lean](../Solution.lean)
and [DimensionEighteen.lean](../AkopyanResearch/Completion/DimensionEighteen.lean).

## Topological Tverberg context

The affine Tverberg theorem [T66] holds for every multiplicity \(r\).
The corresponding topological question replaces affine maps by continuous
maps and has critical simplex dimension \(N=(r-1)(q+1)\). Published
counterexamples for multiplicities that are not prime powers provide
the following comparison points:

| Source | Explicit consequence for multiplicity six |
| --- | --- |
| Frick [F15] | An almost six-embedding \(\Delta^{100}\to\mathbb R^{19}\). |
| Avvakumov–Mabillard–Skopenkov–Wagner [AMSW21] | Their theorem for \(q\geq2r+1\) gives \(\Delta^{70}\to\mathbb R^{13}\), and also \(\Delta^{85}\to\mathbb R^{16}\). |
| Avvakumov–Karasev–Skopenkov [AKS23], Theorem 1.1 | An almost \(r\)-embedding with simplex dimension \(N=(q+1)r-r\lceil(q+2)/(r+1)\rceil-2\). Substitution of \(r=6,q=16\) gives \(N=82\). |

The numerical substitutions are calculations from the cited statements.
They do not compare every construction obtainable by combining published
results. In particular, the formula in [AKS23] does not give the project's
\(\Delta^{89}\to\mathbb R^{16}\). The first project statement is at the
critical dimension \(35=5(6+1)\); its ninety-vertex statement has simplex
dimension four above the critical dimension \(85=5(16+1)\).

The primary sources reviewed here did not identify a published proof of
the exact \(\Delta^{35}\to\mathbb R^6\) statement or the project's exact
ninety-vertex construction. This is a bounded literature-search result,
not a claim of priority or an exhaustive determination of the current
best dimension. The supplied Lean proof is not attributed to [F15],
[AMSW21], or [AKS23].

## Convex equipartitions: three distinct questions

Karasev–Hubard–Aronov [KHA14], Theorem 1.3, prove that a convex body admits
an equipartition for an absolutely continuous finite measure and
\(d-1\) continuous body functionals when the number of parts is a prime
power. This is the direct positive counterpart to the type of obstruction
asserted here for six parts.

Akopyan–Avvakumov–Karasev [AAK26], Theorem 1.1 and its following remarks,
prove the planar assertion for every number of parts: equal area and
perimeter, with area replaceable by an absolutely continuous measure and
perimeter by one continuous body functional. Their discussion of the
difficulty of equalizing two functions does not supply the present
\(d>17\) counterexample. The project's theorem does not contradict that
planar result.

Two related obstruction statements must also be distinguished. In
Blagojević–Ziegler [BZ14], Theorem 1.4, the negative example outside prime
powers allows equivariant functions whose components depend on the
*whole partition*. Such functions need not be evaluations of a fixed
functional on its individual pieces. In Blagojević–Sadovek [BS26], the
negative conclusion concerns an iterated configuration-space/test-map
scheme outside the prime-power case. Neither statement alone constructs
the individual-body functional required by this project's theorem.

## The table and arrangement argument

The completion uses the actual finite-dimensional spaces defined in the
project. A table has fifteen colors and six labels per color. Its two
height coordinates, together with fourteen independent mass coordinates,
produce the target \(\mathbb R^{16}\). Quadratic word evaluations give a
finite arrangement of linear kernels. A single kernel has codimension
ten; critical pair intersections have codimension fourteen; the other
pair intersections have codimension at least sixteen; and triple
intersections have codimension at least eighteen.

The proof removes the higher intersections and calculates integral
homology using explicit normal tubes, excision, and Mayer–Vietoris.
It identifies the actual degree-nine and degree-twelve coordinate maps,
compares the arrangement complement with a specified homotopy fiber,
and uses relative Hurewicz to obtain the fourteen-dimensional lifting
property needed for compatible face data. The resulting safe table
provides the ninety-vertex almost embedding. The convex-geometric
reduction then supplies the functionals and measure.

These are descriptions of the local proof sources, detailed in
[the dimension-eighteen argument](DIMENSION_EIGHTEEN_PROOF.md) and
[the analytic and geometric review](../verification/d18-extension-2026-11-24/ANALYTIC_GEOMETRIC_REVIEW.md).
Hatcher [H02] supplies standard background for the homotopy and homology
tools. Ziegler–Živaljević [ZZ93] is relevant background for the topology
of subspace arrangements. The present proof does not use an assumed
general arrangement homology formula or an assumed Blakers–Massey theorem.
No external primary source for this exact table/arrangement construction
was identified in this review.

## Attribution and historical comments

The supplied archive names “Arseniy Akopyan” in the headers of
`Challenge.lean` and `Solution.lean`. It contains no identified paper,
bibliography, or original-project licence. Numbered lemma references and
the unexpanded label `[AKS]` do not identify an external document.
This evidence does not establish the authorship or publication history
of every proof in the archive or of the subsequent completion.

The original `Solution.lean` contains a historical comment describing the
ninety-vertex input as unresolved at that stage. That source is preserved;
the unconditional conclusion is added in the completion module named
above. Neither that old comment nor this literature search is a statement
that the corresponding mathematical problem remains open.

Code attribution and licences for the imported Lean developments are
recorded separately in [Submission/UPSTREAM.md](../Submission/UPSTREAM.md)
and [docs/third_party](third_party). Those dependency licences do not
establish a licence for the supplied original project. The precise search
scope and source checks are in the
[literature review](../verification/d18-publication/LITERATURE_REVIEW.md).

## Primary references

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
