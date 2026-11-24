module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Split maps between infinite cyclic homology groups

Every split monomorphism or split epimorphism between groups isomorphic to
the additive integers is an isomorphism. The proof uses the commutativity
of endomorphisms of the additive integers and retains the actual map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.RankOneSplit

open CategoryTheory

abbrev IntegerGroup := AddCommGrpCat.of ℤ

theorem integerHom_apply (f : IntegerGroup ⟶ IntegerGroup) (n : ℤ) :
    f n = n * f 1 := by
  calc
    f n = f (n • (1 : ℤ)) := by simp
    _ = n • f 1 := map_zsmul f.hom _ _
    _ = n * f 1 := zsmul_eq_mul _ _

theorem integerEnd_comm (f g : IntegerGroup ⟶ IntegerGroup) : f ≫ g = g ≫ f := by
  apply AddCommGrpCat.int_hom_ext
  change g (f 1) = f (g 1)
  rw [integerHom_apply g (f 1), integerHom_apply f (g 1), mul_comm]

theorem integerEnd_isIso_of_splitMono (f : IntegerGroup ⟶ IntegerGroup)
    [IsSplitMono f] : IsIso f := by
  refine ⟨⟨retraction f, IsSplitMono.id f, ?_⟩⟩
  rw [integerEnd_comm]
  exact IsSplitMono.id f

theorem integerEnd_isIso_of_splitEpi (f : IntegerGroup ⟶ IntegerGroup)
    [IsSplitEpi f] : IsIso f := by
  refine ⟨⟨section_ f, ?_, IsSplitEpi.id f⟩⟩
  rw [integerEnd_comm]
  exact IsSplitEpi.id f

/-- A surjective endomorphism of the additive integers has unit coefficient. -/
theorem integerEnd_isIso_of_surjective (f : IntegerGroup ⟶ IntegerGroup)
    (hf : Function.Surjective f) : IsIso f := by
  obtain ⟨k, hk⟩ := hf 1
  have hne : f 1 ≠ 0 := by
    intro h
    rw [integerHom_apply, h, mul_zero] at hk
    exact zero_ne_one hk
  apply (ConcreteCategory.isIso_iff_bijective f).2
  refine ⟨?_, hf⟩
  intro x y h
  rw [integerHom_apply f x, integerHom_apply f y] at h
  exact mul_right_cancel₀ hne h

variable {X Y : AddCommGrpCat.{0}}

theorem isIso_of_splitMono (eX : X ≅ IntegerGroup) (eY : Y ≅ IntegerGroup)
    (f : X ⟶ Y) [IsSplitMono f] : IsIso f := by
  let g : IntegerGroup ⟶ IntegerGroup := eX.inv ≫ f ≫ eY.hom
  have : IsSplitMono g := by dsimp [g]; infer_instance
  have : IsIso g := integerEnd_isIso_of_splitMono g
  have hf : f = eX.hom ≫ g ≫ eY.inv := by simp [g]
  rw [hf]
  infer_instance

theorem isIso_of_splitEpi (eX : X ≅ IntegerGroup) (eY : Y ≅ IntegerGroup)
    (f : X ⟶ Y) [IsSplitEpi f] : IsIso f := by
  let g : IntegerGroup ⟶ IntegerGroup := eX.inv ≫ f ≫ eY.hom
  have : IsSplitEpi g := by dsimp [g]; infer_instance
  have : IsIso g := integerEnd_isIso_of_splitEpi g
  have hf : f = eX.hom ≫ g ≫ eY.inv := by simp [g]
  rw [hf]
  infer_instance

/-- Surjectivity suffices when both groups are infinite cyclic. -/
theorem isIso_of_surjective (eX : X ≅ IntegerGroup) (eY : Y ≅ IntegerGroup)
    (f : X ⟶ Y) (hf : Function.Surjective f) : IsIso f := by
  let g : IntegerGroup ⟶ IntegerGroup := eX.inv ≫ f ≫ eY.hom
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨w, hw⟩ := hf (eY.inv z)
    refine ⟨eX.hom w, ?_⟩
    change eY.hom (f (eX.inv (eX.hom w))) = z
    rw [Iso.hom_inv_id_apply, hw, Iso.inv_hom_id_apply]
  have : IsIso g := integerEnd_isIso_of_surjective g hg
  have he : f = eX.hom ≫ g ≫ eY.inv := by simp [g]
  rw [he]
  infer_instance

/-- In chosen integral generators, an invertible map has coefficient `1`
or `-1`; a merely nonzero coefficient would not suffice. -/
theorem integerEnd_unit_coefficient (f : IntegerGroup ⟶ IntegerGroup) [IsIso f] :
    f 1 = 1 ∨ f 1 = -1 := by
  have h := ConcreteCategory.congr_hom (IsIso.hom_inv_id f) (1 : ℤ)
  change inv f (f 1) = 1 at h
  rw [integerHom_apply] at h
  exact Int.isUnit_eq_one_or (IsUnit.of_mul_eq_one (inv f 1) h)

end AkopyanResearch.RankOneSplit
