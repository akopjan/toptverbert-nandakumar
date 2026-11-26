module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
Coordinate-gap algebra for one Coxeter chamber of the sum-zero subspace of R⁶.

The five rays are centered indicators of the terminal subsets {j+1,...,5}.
Their nonnegative cone is exactly the chamber of increasing coordinates.
This file proves the expansion and independence algebra. It does not assert
that a sphere triangulation or an equivariant degree theorem is already built.
-/

open scoped BigOperators

namespace CoxeterChamber

noncomputable section

def ray (j : Fin 5) (i : Fin 6) : ℝ :=
  (if j.val < i.val then 1 else 0) - ((5 - j.val : ℕ) : ℝ) / 6

def combine (a : Fin 5 → ℝ) (i : Fin 6) : ℝ :=
  ∑ j, a j * ray j i

def gap (x : Fin 6 → ℝ) (j : Fin 5) : ℝ :=
  x j.succ - x j.castSucc

lemma sum_ray_zero (j : Fin 5) : ∑ i, ray j i = 0 := by
  fin_cases j <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> norm_num [ray]

lemma sum_combine_zero (a : Fin 5 → ℝ) : ∑ i, combine a i = 0 := by
  simp only [combine]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_ray_zero, mul_zero]
  simp

lemma gap_combine (a : Fin 5 → ℝ) : gap (combine a) = a := by
  ext j
  fin_cases j <;> norm_num [gap, combine, ray, Fin.sum_univ_succ] <;> ring

lemma combine_gap {x : Fin 6 → ℝ} (hx : ∑ i, x i = 0) :
    combine (gap x) = x := by
  have hx' := hx
  norm_num [Fin.sum_univ_succ] at hx'
  ext i
  fin_cases i <;> norm_num [combine, gap, ray, Fin.sum_univ_succ] <;> linarith

lemma combine_injective : Function.Injective combine := by
  intro a b h
  have := congrArg gap h
  simpa only [gap_combine] using this

lemma combine_eq_zero_iff (a : Fin 5 → ℝ) : combine a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hh := congrArg gap h
    have hg0 : gap (0 : Fin 6 → ℝ) = 0 := by
      ext j
      simp [gap]
    simpa only [gap_combine, hg0] using hh
  · rintro rfl
    ext i
    simp [combine]

lemma gap_nonneg {x : Fin 6 → ℝ} (hx : Monotone x) (j : Fin 5) :
    0 ≤ gap x j :=
  sub_nonneg.mpr (hx j.castSucc_le_succ)

lemma gap_pos {x : Fin 6 → ℝ} (hx : StrictMono x) (j : Fin 5) :
    0 < gap x j :=
  sub_pos.mpr (hx j.castSucc_lt_succ)

lemma monotone_combine {a : Fin 5 → ℝ} (ha : ∀ j, 0 ≤ a j) :
    Monotone (combine a) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  have := ha j
  have hg := congrFun (gap_combine a) j
  simp only [gap] at hg
  linarith

/-- No sorting algorithm is hidden here: the sorted order is a hypothesis.
Permuting the coordinates transports this formula to every other chamber. -/
lemma exists_nonnegative_chamber_coordinates {x : Fin 6 → ℝ}
    (hsum : ∑ i, x i = 0) (hmono : Monotone x) :
    ∃! a : Fin 5 → ℝ, (∀ j, 0 ≤ a j) ∧ combine a = x := by
  refine ⟨gap x, ⟨gap_nonneg hmono, combine_gap hsum⟩, ?_⟩
  intro a ha
  apply combine_injective
  exact ha.2.trans (combine_gap hsum).symm


/-- The strict terminal set belonging to a positive gap is intrinsic to the
coordinate values, even when other neighboring values are equal. -/
lemma tail_iff_value_lt {x : Fin 6 → ℝ} (hmono : Monotone x)
    {j : Fin 5} (hgap : 0 < gap x j) (i : Fin 6) :
    j.val < i.val ↔ x j.castSucc < x i := by
  constructor
  · intro h
    have hji : j.succ ≤ i := by
      change j.val + 1 ≤ i.val
      omega
    exact lt_of_lt_of_le (sub_pos.mp hgap) (hmono hji)
  · intro h
    by_contra hn
    have hij : i ≤ j.castSucc := by
      change i.val ≤ j.val
      omega
    exact (not_lt_of_ge (hmono hij)) h

lemma ray_invariant_of_fixed_values {x : Fin 6 → ℝ} (hmono : Monotone x)
    {j : Fin 5} (hgap : 0 < gap x j) (e : Equiv.Perm (Fin 6))
    (he : ∀ i, x (e i) = x i) :
    ∀ i, ray j (e i) = ray j i := by
  intro i
  simp only [ray, tail_iff_value_lt hmono hgap, he]

/-- Sorting is provided by Mathlib's finite tuple API, not by case enumeration. -/
lemma exists_chamber_coordinates {x : Fin 6 → ℝ} (hsum : ∑ i, x i = 0) :
    ∃ (e : Equiv.Perm (Fin 6)) (a : Fin 5 → ℝ),
      (∀ j, 0 ≤ a j) ∧ x = fun i => combine a (e.symm i) := by
  let e := Tuple.sort x
  have he : Monotone (x ∘ e) := Tuple.monotone_sort x
  have hs : ∑ i, (x ∘ e) i = 0 := by
    simpa only [Function.comp_apply, Equiv.sum_comp] using hsum
  refine ⟨e, gap (x ∘ e), gap_nonneg he, ?_⟩
  ext i
  have hi := congrFun (combine_gap hs) (e.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi.symm

end

end CoxeterChamber
