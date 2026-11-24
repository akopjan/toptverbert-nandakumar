module

public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Cancelling a split summand in an exact sequence

This lemma is used for the reduced part of the homology of a product with
a sphere. It is stated in an arbitrary abelian category and concerns actual
categorical kernels and the actual morphism induced by the connecting map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.SplitExactKernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {B X Y D : C}
variable (p : X ⟶ B) (s : B ⟶ X) (δ : X ⟶ Y) (q : Y ⟶ D)
variable (hsp : s ≫ p = 𝟙 B) (hsδ : s ≫ δ = 0) (hδq : δ ≫ q = 0)

def kernelRetraction : X ⟶ kernel p :=
  kernel.lift p (𝟙 X - p ≫ s) (by
    rw [sub_comp, Category.id_comp, Category.assoc, hsp, Category.comp_id, sub_self])

theorem kernelRetraction_ι :
    kernelRetraction p s hsp ≫ kernel.ι p = 𝟙 X - p ≫ s := by
  simp only [kernelRetraction, kernel.lift_ι]

def kernelMap : kernel p ⟶ kernel q :=
  kernel.lift q (kernel.ι p ≫ δ) (by rw [Category.assoc, hδq, comp_zero])

theorem kernelMap_ι :
    kernelMap p δ q hδq ≫ kernel.ι q = kernel.ι p ≫ δ := by
  simp only [kernelMap, kernel.lift_ι]

include hsδ in
theorem retraction_comp_kernelMap :
    kernelRetraction p s hsp ≫ kernelMap p δ q hδq = kernel.lift q δ hδq := by
  apply (cancel_mono (kernel.ι q)).mp
  rw [Category.assoc, kernelMap_ι, ← Category.assoc, kernelRetraction_ι,
    sub_comp, Category.id_comp, Category.assoc, hsδ, comp_zero, sub_zero, kernel.lift_ι]

include hsp in
/-- If the image of `s` is the kernel of `δ`, the image of `δ` is the
kernel of `q`, and `s` is a section of `p`, then `δ` restricts to an
isomorphism between the two complementary kernels. -/
theorem isIso_kernelMap
    (hex₁ : (ShortComplex.mk s δ hsδ).Exact)
    (hex₂ : (ShortComplex.mk δ q hδq).Exact) :
    IsIso (kernelMap p δ q hδq) := by
  have : Mono s := mono_of_mono_fac hsp
  have : Epi (kernel.lift q δ hδq) :=
    (ShortComplex.exact_iff_epi_kernel_lift _).mp hex₂
  have : Epi (kernelMap p δ q hδq) :=
    epi_of_epi_fac (retraction_comp_kernelMap p s δ q hsp hsδ hδq)
  have : Mono (kernelMap p δ q hδq) := by
    apply Abelian.mono_of_kernel_ι_eq_zero
    let k := kernelMap p δ q hδq
    have hz : (kernel.ι k ≫ kernel.ι p) ≫ δ = 0 := by
      rw [Category.assoc, ← kernelMap_ι p δ q hδq, ← Category.assoc]
      change (kernel.ι k ≫ k) ≫ kernel.ι q = 0
      rw [kernel.condition, zero_comp]
    obtain ⟨l, hl⟩ := hex₁.lift' (kernel.ι k ≫ kernel.ι p) hz
    have hlzero : l = 0 := by
      calc
        l = l ≫ (s ≫ p) := by rw [hsp, Category.comp_id]
        _ = (kernel.ι k ≫ kernel.ι p) ≫ p := by rw [← Category.assoc, hl]
        _ = 0 := by rw [Category.assoc, kernel.condition, comp_zero]
    apply (cancel_mono (kernel.ι p)).mp
    change kernel.ι k ≫ kernel.ι p = 0 ≫ kernel.ι p
    rw [← hl, hlzero, zero_comp, zero_comp]
  exact isIso_of_mono_of_epi _

def kernelIso
    (hex₁ : (ShortComplex.mk s δ hsδ).Exact)
    (hex₂ : (ShortComplex.mk δ q hδq).Exact) : kernel p ≅ kernel q := by
  letI := isIso_kernelMap p s δ q hsp hsδ hδq hex₁ hex₂
  exact asIso (kernelMap p δ q hδq)

theorem kernelIso_hom_ι
    (hex₁ : (ShortComplex.mk s δ hsδ).Exact)
    (hex₂ : (ShortComplex.mk δ q hδq).Exact) :
    (kernelIso p s δ q hsp hsδ hδq hex₁ hex₂).hom ≫ kernel.ι q = kernel.ι p ≫ δ :=
  kernelMap_ι p δ q hδq

/-- Naturality of the restricted connecting map. In particular the
kernel isomorphism above preserves maps of the actual exact sequences. -/
theorem kernelMap_natural {B' X' Y' D' : C}
    (p' : X' ⟶ B') (δ' : X' ⟶ Y') (q' : Y' ⟶ D') (hδq' : δ' ≫ q' = 0)
    (b : B ⟶ B') (x : X ⟶ X') (y : Y ⟶ Y') (d : D ⟶ D')
    (hp : p ≫ b = x ≫ p') (hδ : δ ≫ y = x ≫ δ') (hq : q ≫ d = y ≫ q') :
    kernel.map p p' x b hp ≫ kernelMap p' δ' q' hδq' =
      kernelMap p δ q hδq ≫ kernel.map q q' y d hq := by
  apply (cancel_mono (kernel.ι q')).mp
  simp only [Category.assoc, kernelMap, kernel.map, kernel.lift_ι,
    kernel.lift_ι_assoc]
  rw [hδ]

end AkopyanResearch.SplitExactKernel
