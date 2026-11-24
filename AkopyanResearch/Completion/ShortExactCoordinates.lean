module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Coordinates detected on a short-exact kernel

A map from the middle term which is an isomorphism on the kernel, together
with the original quotient map, gives an isomorphism onto a biproduct.
This is the algebraic step used in the actual pair-meridian induction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ShortExactCoordinates

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem isIso_lift_of_kernel_iso (S : ShortComplex C) (hS : S.ShortExact)
    {K : C} (u : S.X₂ ⟶ K) [IsIso (S.f ≫ u)] : IsIso (biprod.lift u S.g) := by
  let T : ShortComplex C :=
    ShortComplex.mk (biprod.inl : K ⟶ K ⊞ S.X₃) biprod.snd (by simp)
  let φ : S ⟶ T :=
    { τ₁ := S.f ≫ u
      τ₂ := biprod.lift u S.g
      τ₃ := 𝟙 _
      comm₁₂ := by
        apply biprod.hom_ext
        · simp [T]
        · simp [T, S.zero]
      comm₂₃ := by simp [T] }
  have hT : T.ShortExact := (ShortComplex.Splitting.ofHasBinaryBiproduct K S.X₃).shortExact
  have : IsIso φ.τ₁ := by change IsIso (S.f ≫ u); infer_instance
  have : IsIso φ.τ₃ := by change IsIso (𝟙 S.X₃); infer_instance
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hT

end AkopyanResearch.ShortExactCoordinates
