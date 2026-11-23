module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith


@[expose] public section

/-!
# Finite algebraic genericity without enumerating parameter values

A finite family of nonzero real multivariate polynomials can simultaneously
be kept nonzero in any prescribed open box. The number of polynomials is not
evaluated. In a geometric application one must separately prove that each
rank minor used as a polynomial is nonzero. This file makes no transversality
claim and does not supply that rank proof.
-/

namespace AkopyanResearch

open scoped BigOperators

theorem exists_polynomial_generic_in_box
    {σ J : Type*} [Fintype J]
    (P : J → MvPolynomial σ ℝ) (hP : ∀ j, P j ≠ 0)
    (l u : σ → ℝ) (hlu : ∀ i, l i < u i) :
    ∃ x : σ → ℝ, (∀ i, l i < x i ∧ x i < u i) ∧
      ∀ j, MvPolynomial.eval x (P j) ≠ 0 := by
  classical
  let Q : MvPolynomial σ ℝ := ∏ j, P j
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hP j)
  by_contra h
  apply hQ
  apply MvPolynomial.funext_set (fun i => Set.Ioo (l i) (u i))
    (fun i => Set.Ioo_infinite (hlu i))
  intro x hx
  have hx' : ∀ i, l i < x i ∧ x i < u i := fun i => hx i (Set.mem_univ i)
  have hzero : MvPolynomial.eval x Q = 0 := by
    by_contra hne
    apply h
    refine ⟨x, hx', ?_⟩
    intro j
    have hprod : (∏ k, MvPolynomial.eval x (P k)) ≠ 0 := by
      simpa only [Q, MvPolynomial.eval_prod] using hne
    exact (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
  simpa only [map_zero] using hzero

theorem exists_polynomial_generic_near
    {σ J : Type*} [Fintype J]
    (P : J → MvPolynomial σ ℝ) (hP : ∀ j, P j ≠ 0)
    (z : σ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : σ → ℝ, (∀ i, |x i - z i| < ε) ∧
      ∀ j, MvPolynomial.eval x (P j) ≠ 0 := by
  obtain ⟨x, hx, hPx⟩ := exists_polynomial_generic_in_box P hP
    (fun i => z i - ε) (fun i => z i + ε) (fun i => by linarith)
  refine ⟨x, ?_, hPx⟩
  intro i
  rw [abs_lt]
  have hi := hx i
  constructor <;> linarith

end AkopyanResearch
