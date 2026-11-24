module

public import AkopyanResearch.Completion.RankOneSplit
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Detecting an actual two-coordinate homology isomorphism

Independent sections make the two-coordinate map split epic. If the
kernel of its first coordinate and its second target are infinite cyclic,
the second coordinate is an isomorphism on that kernel.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.RankOneProduct

open CategoryTheory CategoryTheory.Limits

variable {F A B : AddCommGrpCat.{0}}
variable (r : F ⟶ A) (q : F ⟶ B) (s : A ⟶ F) (t : B ⟶ F)
variable (hsr : s ≫ r = 𝟙 _) (hsq : s ≫ q = 0)
variable (htr : t ≫ r = 0) (htq : t ≫ q = 𝟙 _)
variable (eK : kernel r ≅ AddCommGrpCat.of ℤ) (eB : B ≅ AddCommGrpCat.of ℤ)

include htr htq eK eB in
theorem isIso_kernelCoordinate : IsIso (kernel.ι r ≫ q) := by
  have h : kernel.lift r t htr ≫ (kernel.ι r ≫ q) = 𝟙 _ := by
    rw [← Category.assoc, kernel.lift_ι, htq]
  have : IsSplitEpi (kernel.ι r ≫ q) := IsSplitEpi.mk' ⟨_, h⟩
  exact RankOneSplit.isIso_of_splitEpi eK eB _

include hsr hsq htr htq eK eB in
theorem isIso_coordinates : IsIso (biprod.lift r q) := by
  have hsec : biprod.desc s t ≫ biprod.lift r q = 𝟙 _ := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simpa only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst,
          Category.comp_id, biprod.inl_fst] using hsr
      · simpa only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd,
          Category.comp_id, biprod.inl_snd] using hsq
    · apply biprod.hom_ext
      · simpa only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst,
          Category.comp_id, biprod.inr_fst] using htr
      · simpa only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd,
          Category.comp_id, biprod.inr_snd] using htq
  have : IsSplitEpi (biprod.lift r q) := IsSplitEpi.mk' ⟨_, hsec⟩
  have hk := isIso_kernelCoordinate r q t htr htq eK eB
  have hm : Mono (biprod.lift r q) := by
    apply Abelian.mono_of_kernel_ι_eq_zero
    have hr : kernel.ι (biprod.lift r q) ≫ r = 0 := by
      simpa only [Category.assoc, biprod.lift_fst, zero_comp] using
        congrArg (fun k => k ≫ biprod.fst) (kernel.condition (biprod.lift r q))
    have hq : kernel.ι (biprod.lift r q) ≫ q = 0 := by
      simpa only [Category.assoc, biprod.lift_snd, zero_comp] using
        congrArg (fun k => k ≫ biprod.snd) (kernel.condition (biprod.lift r q))
    let l := kernel.lift r (kernel.ι (biprod.lift r q)) hr
    have hl : l = 0 := by
      apply (cancel_mono (kernel.ι r ≫ q)).mp
      simp only [l, kernel.lift_ι_assoc, hq, zero_comp]
    calc
      kernel.ι (biprod.lift r q) = l ≫ kernel.ι r := (kernel.lift_ι _ _ _).symm
      _ = 0 := by rw [hl, zero_comp]
  exact isIso_of_mono_of_epi _

end AkopyanResearch.RankOneProduct
