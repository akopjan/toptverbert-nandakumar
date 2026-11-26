module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic


@[expose] public section

/-!
# The elementary averaged chain-homotopy calculation

This module verifies the factor `2 * card J`, and in particular `16` for
`J = Fin 8`. The averaged chain-homotopy identity is an explicit hypothesis.
The module does not construct a chain homotopy or claim exactness of a complex.
-/

namespace AkopyanCochain

open scoped BigOperators

variable {C₁₂ C₁₃ C₁₄ A J : Type*}
variable [AddCommGroup C₁₂] [AddCommGroup C₁₃] [AddCommGroup C₁₄]
variable [AddCommGroup A] [Fintype J]
variable [Module ℤ C₁₂] [Module ℤ C₁₃] [Module ℤ C₁₄] [Module ℤ A]

/-- An averaged homotopy between sign-reversing maps and the identity gives
an explicit primitive for `2 * card J` times a cocycle. -/
theorem averaged_homotopy_annihilates
    (d₁₃ : C₁₃ →ₗ[ℤ] C₁₂) (d₁₄ : C₁₄ →ₗ[ℤ] C₁₃)
    (K₁₂ : C₁₂ →ₗ[ℤ] C₁₃) (K₁₃ : C₁₃ →ₗ[ℤ] C₁₄)
    (g : J → C₁₃ →ₗ[ℤ] C₁₃) (c : C₁₃ →ₗ[ℤ] A)
    (hK : d₁₄.comp K₁₃ + K₁₂.comp d₁₃ =
      ∑ j, g j - Fintype.card J • LinearMap.id)
    (hc : c.comp d₁₄ = 0) (hg : ∀ j, c.comp (g j) = -c) :
    (-c.comp K₁₂).comp d₁₃ = (2 * Fintype.card J) • c := by
  ext x
  have h := congrArg (fun f : C₁₃ →ₗ[ℤ] C₁₃ => c (f x)) hK
  have hc' : c (d₁₄ (K₁₃ x)) = 0 := congrArg (fun f => f (K₁₃ x)) hc
  have hg' (j : J) : c (g j x) = -c x := congrArg (fun f => f x) (hg j)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_add, map_sub, map_sum, map_nsmul, hc', zero_add, hg',
    Finset.sum_const, Finset.card_univ] at h
  change -c (K₁₂ (d₁₃ x)) = (2 * Fintype.card J) • c x
  rw [h]
  simp only [smul_neg, neg_sub, sub_neg_eq_add, two_mul, add_nsmul]

/-- Eight averaged conjugates yield the integer annihilator `16`. -/
theorem eight_conjugates_annihilate
    (d₁₃ : C₁₃ →ₗ[ℤ] C₁₂) (d₁₄ : C₁₄ →ₗ[ℤ] C₁₃)
    (K₁₂ : C₁₂ →ₗ[ℤ] C₁₃) (K₁₃ : C₁₃ →ₗ[ℤ] C₁₄)
    (g : Fin 8 → C₁₃ →ₗ[ℤ] C₁₃) (c : C₁₃ →ₗ[ℤ] A)
    (hK : d₁₄.comp K₁₃ + K₁₂.comp d₁₃ = ∑ j, g j - 8 • LinearMap.id)
    (hc : c.comp d₁₄ = 0) (hg : ∀ j, c.comp (g j) = -c) :
    (-c.comp K₁₂).comp d₁₃ = 16 • c := by
  simpa using averaged_homotopy_annihilates d₁₃ d₁₄ K₁₂ K₁₃ g c hK hc hg

end AkopyanCochain
