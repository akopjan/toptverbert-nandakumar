module

public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Identifying a common section by an actual exact sequence

If an epimorphism in an exact sequence factors through an epimorphism
which already kills the preceding map, the remaining factor is an
isomorphism. This is the cokernel comparison used in the sphere-factor
Mayer--Vietoris argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ExactCommonSection

open CategoryTheory CategoryTheory.Limits

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem isIso_factor (S : ShortComplex C) (hS : S.Exact) {A : C}
    (p : S.X₂ ⟶ A) (s : A ⟶ S.X₃) (hfp : S.f ≫ p = 0)
    (hps : p ≫ s = S.g) [Epi p] [Epi S.g] : IsIso s := by
  let r : S.X₃ ⟶ A := hS.desc p hfp
  have hgr : S.g ≫ r = p := hS.g_desc p hfp
  have hsr : s ≫ r = 𝟙 A := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hps, hgr, Category.comp_id]
  have : Mono s := mono_of_mono_fac hsr
  have : Epi s := epi_of_epi_fac hps
  exact isIso_of_mono_of_epi s

end AkopyanResearch.ExactCommonSection
