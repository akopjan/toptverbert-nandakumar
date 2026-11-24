module

public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The complementary kernel in a signed exact sequence

For a short exact sequence whose first map has components `(p,-q)` and
whose second map has the same component `r` on both summands, restriction
of `q` identifies `ker p` with `ker r`. This keeps the actual morphism in
the ordinary Mayer--Vietoris calculation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.SignedExactKernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I F T : C} (p q : I ⟶ F) (r : F ⟶ T)
variable (hz : biprod.lift p (-q) ≫ biprod.desc r r = 0)

include hz in
theorem components_equal : p ≫ r = q ≫ r := by
  apply sub_eq_zero.mp
  simpa only [biprod.lift_desc, neg_comp, sub_eq_add_neg] using hz

def kernelMap : kernel p ⟶ kernel r :=
  kernel.lift r (kernel.ι p ≫ q) (by
    rw [Category.assoc, ← components_equal p q r hz, ← Category.assoc,
      kernel.condition, zero_comp])

theorem kernelMap_ι : kernelMap p q r hz ≫ kernel.ι r = kernel.ι p ≫ q :=
  kernel.lift_ι _ _ _

variable (hex : (ShortComplex.mk (biprod.lift p (-q)) (biprod.desc r r) hz).Exact)
variable [Mono (biprod.lift p (-q))]

def inverseLift : kernel r ⟶ I :=
  hex.lift (biprod.lift 0 (-kernel.ι r)) (by
    simp only [biprod.lift_desc, zero_comp, neg_comp, kernel.condition,
      neg_zero, add_zero])

theorem inverseLift_signed :
    inverseLift p q r hz hex ≫ biprod.lift p (-q) = biprod.lift 0 (-kernel.ι r) :=
  hex.lift_f _ _

theorem inverseLift_p : inverseLift p q r hz hex ≫ p = 0 := by
  have h := congrArg (fun k => k ≫ biprod.fst) (inverseLift_signed p q r hz hex)
  simpa only [Category.assoc, biprod.lift_fst] using h

theorem inverseLift_q : inverseLift p q r hz hex ≫ q = kernel.ι r := by
  have h := congrArg (fun k => k ≫ biprod.snd) (inverseLift_signed p q r hz hex)
  simpa only [Category.assoc, biprod.lift_snd, comp_neg, neg_inj] using h

def inverse : kernel r ⟶ kernel p :=
  kernel.lift p (inverseLift p q r hz hex) (inverseLift_p p q r hz hex)

theorem inverse_kernelMap : inverse p q r hz hex ≫ kernelMap p q r hz = 𝟙 _ := by
  apply (cancel_mono (kernel.ι r)).mp
  rw [Category.assoc, kernelMap_ι, ← Category.assoc]
  simp only [inverse, kernel.lift_ι, Category.id_comp]
  exact inverseLift_q p q r hz hex

theorem mono_kernelMap : Mono (kernelMap p q r hz) := by
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply (cancel_mono (kernel.ι p)).mp
  apply (cancel_mono (biprod.lift p (-q))).mp
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, kernel.condition, comp_zero, zero_comp]
  · simp only [Category.assoc, biprod.lift_snd, comp_neg, zero_comp]
    rw [← kernelMap_ι p q r hz, ← Category.assoc, kernel.condition,
      zero_comp, neg_zero]

include hex in
theorem isIso_kernelMap : IsIso (kernelMap p q r hz) := by
  have := mono_kernelMap p q r hz
  have : Epi (kernelMap p q r hz) :=
    epi_of_epi_fac (inverse_kernelMap p q r hz hex)
  exact isIso_of_mono_of_epi _

def kernelIso : kernel p ≅ kernel r := by
  letI := isIso_kernelMap p q r hz hex
  exact asIso (kernelMap p q r hz)

theorem kernelIso_hom_ι :
    (kernelIso p q r hz hex).hom ≫ kernel.ι r = kernel.ι p ≫ q :=
  kernelMap_ι p q r hz

section Coordinates

variable {A B : C} (p₀ : I ⟶ A) (q₀ : I ⟶ B) (a : A ≅ F) (b : B ≅ F)
variable (u : A ⊞ B ⟶ T) (hu : biprod.desc a.hom b.hom ≫ r = u)
variable (hzero : biprod.lift p₀ (-q₀) ≫ u = 0)

theorem signed_conjugation :
    biprod.lift p₀ (-q₀) ≫ (biprod.mapIso a b).hom =
      biprod.lift (p₀ ≫ a.hom) (-(q₀ ≫ b.hom)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.mapIso_hom, biprod.map_fst,
      biprod.lift_fst_assoc, biprod.lift_fst]
  · simp only [Category.assoc, biprod.mapIso_hom, biprod.map_snd,
      biprod.lift_snd_assoc, biprod.lift_snd, neg_comp]

include hu in
theorem desc_conjugation :
    (biprod.mapIso a b).hom ≫ biprod.desc r r = u := by
  rw [← hu]
  apply biprod.hom_ext'
  · simp only [biprod.mapIso_hom, biprod.inl_map_assoc,
      biprod.inl_desc_assoc, biprod.inl_desc]
  · simp only [biprod.mapIso_hom, biprod.inr_map_assoc,
      biprod.inr_desc_assoc, biprod.inr_desc]

include hu hzero in
theorem normalized_zero :
    biprod.lift (p₀ ≫ a.hom) (-(q₀ ≫ b.hom)) ≫ biprod.desc r r = 0 := by
  rw [← signed_conjugation p₀ q₀ a b, Category.assoc,
    desc_conjugation r a b u hu, hzero]

variable (he : (ShortComplex.mk (biprod.lift p₀ (-q₀)) u hzero).Exact)
variable [Mono (biprod.lift p₀ (-q₀))]

def kernelIsoOfIsos : kernel (p₀ ≫ a.hom) ≅ kernel r := by
  let z := normalized_zero r p₀ q₀ a b u hu hzero
  let S : ShortComplex C := ShortComplex.mk (biprod.lift p₀ (-q₀)) u hzero
  let S' : ShortComplex C :=
    ShortComplex.mk (biprod.lift (p₀ ≫ a.hom) (-(q₀ ≫ b.hom))) (biprod.desc r r) z
  let e : S ≅ S' := ShortComplex.isoMk (Iso.refl _) (biprod.mapIso a b) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.id_comp] using
      (signed_conjugation p₀ q₀ a b).symm)
    (by simpa only [Iso.refl_hom, Category.comp_id] using desc_conjugation r a b u hu)
  have hex' : S'.Exact := ShortComplex.exact_of_iso e he
  have hm : Mono (biprod.lift (p₀ ≫ a.hom) (-(q₀ ≫ b.hom))) := by
    rw [← signed_conjugation p₀ q₀ a b]
    infer_instance
  exact kernelIso (p₀ ≫ a.hom) (q₀ ≫ b.hom) r z hex'

end Coordinates

end AkopyanResearch.SignedExactKernel
