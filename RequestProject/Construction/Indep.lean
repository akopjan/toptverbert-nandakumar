module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import RequestProject.Balance

@[expose] public section

/-!
# Affine systems with points in general position

`Indep5 z`: any five of the six points `z s ∈ ℝ⁵` are linearly independent.  Then a solution of
`affMat z *ᵥ y = e₀` with `y ≥ 0` is strictly positive, `affMat z` is invertible, and the
solution is unique.
-/

open Matrix

namespace Tverberg6R

/-- Any five of the six points are linearly independent. -/
def Indep5 (z : Fin 6 → Fin 5 → ℝ) : Prop :=
  ∀ y : Fin 6 → ℝ, ∑ s, y s • z s = 0 → ∀ a, y a = 0 → y = 0

lemma affMat_mulVec_zero (z : Fin 6 → Fin 5 → ℝ) (y : Fin 6 → ℝ) :
    (affMat z *ᵥ y) 0 = ∑ s, y s := by
  simp [affMat, mulVec, dotProduct]

lemma affMat_mulVec_succ (z : Fin 6 → Fin 5 → ℝ) (y : Fin 6 → ℝ) (r : Fin 5) :
    (affMat z *ᵥ y) r.succ = (∑ s, y s • z s) r := by
  simp [affMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma affMat_mulVec_iff (z : Fin 6 → Fin 5 → ℝ) (y : Fin 6 → ℝ) :
    affMat z *ᵥ y = Pi.single 0 1 ↔ ∑ s, y s = 1 ∧ ∑ s, y s • z s = 0 := by
  constructor
  · intro h
    refine ⟨by rw [← affMat_mulVec_zero, h]; simp, ?_⟩
    funext r
    rw [← affMat_mulVec_succ, h]
    simp [Fin.succ_ne_zero]
  · rintro ⟨h1, h2⟩
    funext r
    refine Fin.cases ?_ (fun r => ?_) r
    · rw [affMat_mulVec_zero, h1]; simp
    · rw [affMat_mulVec_succ, h2]; simp [Fin.succ_ne_zero]

lemma pos_of_sol {z : Fin 6 → Fin 5 → ℝ} (hz : Indep5 z) {y : Fin 6 → ℝ}
    (hy : affMat z *ᵥ y = Pi.single 0 1) (hnn : ∀ s, 0 ≤ y s) : ∀ s, 0 < y s := by
  rw [affMat_mulVec_iff] at hy
  intro s
  rcases (hnn s).lt_or_eq with h | h
  · exact h
  · have := hz y hy.2 s h.symm
    rw [this] at hy
    simp at hy

lemma det_ne_zero_of_sol {z : Fin 6 → Fin 5 → ℝ} (hz : Indep5 z) {y : Fin 6 → ℝ}
    (hy : affMat z *ᵥ y = Pi.single 0 1) (hnn : ∀ s, 0 ≤ y s) : (affMat z).det ≠ 0 := by
  have hpos := pos_of_sol hz hy hnn
  rw [affMat_mulVec_iff] at hy
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hw' : ∑ s, w s = 0 ∧ ∑ s, w s • z s = 0 := by
    constructor
    · rw [← affMat_mulVec_zero, hw]; rfl
    · funext r; rw [← affMat_mulVec_succ, hw]; rfl
  -- `y 0 • w - w 0 • y` is a relation with vanishing `0`-coordinate
  set u := y 0 • w - w 0 • y with hu
  have hrel : ∑ s, u s • z s = 0 := by
    simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib]
    simp only [SemigroupAction.mul_smul, ← Finset.smul_sum, hw'.2, hy.2, smul_zero, sub_zero]
  have hu0 : u 0 = 0 := by simp [hu]; ring
  have huz := hz u hrel 0 hu0
  -- hence `w` is proportional to `y`, so `∑ w = (w 0 / y 0) ≠ 0` unless `w = 0`
  have hwy : ∀ s, y 0 * w s = w 0 * y s := by
    intro s; have := congrFun huz s; simp [hu] at this; linarith
  have hsum : y 0 * ∑ s, w s = w 0 * ∑ s, y s := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => hwy s
  rw [hw'.1, hy.1, mul_zero, mul_one] at hsum
  apply hw0
  funext s
  have := hwy s
  rw [← hsum, zero_mul] at this
  exact (mul_eq_zero.1 this).resolve_left (hpos 0).ne'

lemma sol_unique {z : Fin 6 → Fin 5 → ℝ} (hdet : (affMat z).det ≠ 0) {y y' : Fin 6 → ℝ}
    (hy : affMat z *ᵥ y = Pi.single 0 1) (hy' : affMat z *ᵥ y' = Pi.single 0 1) : y = y' := by
  have : affMat z *ᵥ (y - y') = 0 := by rw [mulVec_sub, hy, hy', sub_self]
  exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hdet this)

lemma simplexIndex_of_sol {z : Fin 6 → Fin 5 → ℝ} {y : Fin 6 → ℝ} (hpos : ∀ s, 0 < y s)
    (hy : affMat z *ᵥ y = Pi.single 0 1) : simplexIndex z = rsign (affMat z).det := by
  unfold simplexIndex
  rw [if_pos ⟨y, hpos, hy⟩]

lemma simplexIndex_of_no_sol {z : Fin 6 → Fin 5 → ℝ}
    (h : ¬ ∃ y : Fin 6 → ℝ, (∀ s, 0 < y s) ∧ affMat z *ᵥ y = Pi.single 0 1) :
    simplexIndex z = 0 := by
  unfold simplexIndex
  rw [if_neg h]

/-! ### The point sets of the construction -/

/-- The six colour vectors are in general position. -/
lemma indep5_vvec {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) : Indep5 (vvec q m) := by
  intro y hy a ha
  rw [Fin.sum_univ_succAbove _ a, ha, zero_smul, zero_add] at hy
  have hz := coeff_eq_zero_of_det_ne_zero (fun s => vvec q m (a.succAbove s))
    (hq.five m hm _ Fin.succAbove_right_injective) (fun s => y (a.succAbove s)) hy
  funext s
  rcases Fin.eq_self_or_eq_succAbove a s with rfl | ⟨t, rfl⟩
  · exact ha
  · exact congrFun hz t

/-- The anchor vector and the five colour vectors of a facet. -/
def facetPts (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (P : Finset (Fin 6)) (k : Fin 6) :
    Fin 6 → Fin 5 → ℝ :=
  Fin.cons (uvec P) (fun t => vvec q m (k.succAbove t))

lemma facetIndex_eq (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (P : Finset (Fin 6)) (k : Fin 6) :
    facetIndex q m P k = simplexIndex (facetPts q m P k) := rfl

lemma indep5_facetPts {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {P : Finset (Fin 6)} (hP1 : P.Nonempty) (hP2 : P ≠ Finset.univ)
    (k : Fin 6) : Indep5 (facetPts q m P k) := by
  intro y hy a ha
  rw [Fin.sum_univ_succ] at hy
  simp only [facetPts, Fin.cons_zero, Fin.cons_succ] at hy
  refine Fin.cases ?_ (fun t0 => ?_) a ha
  · intro h0
    rw [h0, zero_smul, zero_add] at hy
    have hz := coeff_eq_zero_of_det_ne_zero (fun s => vvec q m (k.succAbove s))
      (hq.five m hm _ Fin.succAbove_right_injective) (fun s => y s.succ) hy
    funext s
    refine Fin.cases h0 (fun t => ?_) s
    exact congrFun hz t
  · intro ht0
    rw [Fin.sum_univ_succAbove _ t0, ht0, zero_smul, zero_add] at hy
    have hinj : Function.Injective (fun t => k.succAbove (t0.succAbove t)) :=
      Fin.succAbove_right_injective.comp Fin.succAbove_right_injective
    have hz := coeff_eq_zero_of_det_ne_zero
      (Fin.cons (uvec P) (fun t => vvec q m (k.succAbove (t0.succAbove t))) : Fin 5 → Fin 5 → ℝ)
      (hq.anchor m hm P hP1 hP2 _ hinj) (Fin.cons (y 0) (fun t => y (t0.succAbove t).succ))
      (by rw [Fin.sum_univ_succ]; simpa using hy)
    funext s
    refine Fin.cases (by simpa using congrFun hz 0) (fun t => ?_) s
    rcases Fin.eq_self_or_eq_succAbove t0 t with rfl | ⟨t', rfl⟩
    · exact ht0
    · simpa using congrFun hz t'.succ

end Tverberg6R
