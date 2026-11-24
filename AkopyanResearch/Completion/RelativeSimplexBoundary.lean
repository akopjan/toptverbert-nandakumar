module

public import AkopyanResearch.Completion.FreeRelativeOperations
public import AkopyanResearch.Completion.SimplexSkeletonRetraction
public import AkopyanResearch.Completion.RelativeHurewiczDescent

/-!
# The relative classes of the faces of a simplex

The alternating sum of normalized face classes is a boundary in the
actual relative singular complex. The maps and face relations retain
the geometric simplex and its full boundary in the distinguished subspace.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.deprecated false
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor
attribute [local implicit_reducible] Submission.relComplex Submission.Hrel RelHomotopyGroup

namespace AkopyanResearch.RelativeSimplexBoundary

open Submission RelativeHurewiczDescent

structure Boundary (n : ℕ) (X : TopCat.{0}) (A : Set X) where
  simplex : Sng X _⦋n + 3⦌
  face (i : Fin (n + 4)) : PairNormalizedSimplex n X A
  face_simplex (i : Fin (n + 4)) : (face i).simplex = (Sng X).δ i simplex

variable {n : ℕ} {X : TopCat.{0}} {A : Set X}

/-- The geometric higher simplex carries its codimension-two skeleton
into the distinguished subspace. -/
theorem maps_skeleton (s : Boundary n X A) :
    Set.MapsTo (sngEquiv X (n + 3) s.simplex)
      (SimplexSkeletonRetraction.skeleton (n + 2)) A := by
  intro z hz
  obtain ⟨i, k, hik, hi, hk⟩ := hz
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hik.symm
  let w : stdSimplex ℝ (Fin (n + 3)) := dropMap i hi
  have hw : w.val j = 0 := by
    change z.val (i.succAbove j) = 0
    rw [hj]
    exact hk
  have hzw : faceMap i w = z := faceMap_dropMap i hi
  rw [← hzw, ← apply_δ, ← s.face_simplex i]
  exact (s.face i).simplex_boundary w ⟨j, hw⟩

/-- The oriented face classes sum to zero in relative homology. -/
theorem alternating_relativeClass_eq_zero (s : Boundary n X A) :
    ∑ i : Fin (n + 4), ((-1 : ℤ) ^ (i : ℕ)) • (s.face i).relativeClass = 0 := by
  let K := relComplex (subIncl A)
  let z (i : Fin (n + 4)) : cyclesSub K (n + 2) :=
    ⟨relativeSimplexChain A (s.face i).simplex, by
      change K.d (n + 2) ((ComplexShape.down ℕ).next (n + 2))
        (relativeSimplexChain A (s.face i).simplex) = 0
      rw [ChainComplex.next_nat_succ]
      exact relativeSimplexChain_cycle (s.face i).simplex (s.face i).face_lift⟩
  have hz : ∀ i, homologyMkHom K (n + 2) (z i) = (s.face i).relativeClass :=
    fun _ => rfl
  have hs : ∑ i : Fin (n + 4), ((-1 : ℤ) ^ (i : ℕ)) • (s.face i).relativeClass =
      homologyMkHom K (n + 2) (∑ i : Fin (n + 4), ((-1 : ℤ) ^ (i : ℕ)) • z i) := by
    rw [map_sum]
    simp only [map_zsmul, hz]
  rw [hs]
  change homologyMk _ _ = 0
  apply (homologyMk_eq_zero_iff _ _).2
  rw [ChainComplex.prev]
  refine ⟨relativeSimplexChain A s.simplex, ?_⟩
  change K.d (n + 3) (n + 2) (relativeSimplexChain A s.simplex) = _
  change (relComplex (subIncl A)).d (n + 3) (n + 2)
    ((relProj (subIncl A)).f (n + 3) (gen s.simplex)) = _
  have hd : (Csing X).d (n + 3) (n + 2) (gen s.simplex) =
      ∑ i : Fin (n + 4), ((-1 : ℤ) ^ (i : ℕ)) • gen ((Sng X).δ i s.simplex) :=
    d_gen s.simplex
  rw [← ConcreteCategory.comp_apply, (relProj (subIncl A)).comm,
    ConcreteCategory.comp_apply, hd, map_sum]
  simp only [map_zsmul, ← s.face_simplex]
  change _ = (cyclesSub K (n + 2)).subtype
    (∑ i : Fin (n + 4), ((-1 : ℤ) ^ (i : ℕ)) • z i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  rfl

end AkopyanResearch.RelativeSimplexBoundary
