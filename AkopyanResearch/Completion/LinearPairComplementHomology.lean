module

public import AkopyanResearch.Completion.PuncturedSpace
public import AkopyanResearch.Completion.LinearPreimageHomotopy
public import AkopyanResearch.Completion.SphereHomology
public import Hatcher.MayerVietoris.Sequence

/-!
# Homology of the actual two-kernel normal complement

For two surjective linear tests in a fourteen-dimensional normal space,
each ten-dimensional, assume their common kernel is zero. Their nonzero
loci cover the punctured normal space. The genuine Mayer--Vietoris boundary
then identifies degree twelve of their intersection with the coefficient
group, because the two cover members have the homotopy type of a nine-sphere.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearPairComplementHomology

open CategoryTheory CategoryTheory.Limits ContinuousMap
open ProductSphereKernel

variable {E F G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

abbrev Ambient := PuncturedSpace.Space E

def nonzeroSet (f : E →L[ℝ] F) : Set (Ambient (E := E)) :=
  {x | f x.val ≠ 0}

theorem isOpen_nonzeroSet (f : E →L[ℝ] F) : IsOpen (nonzeroSet f) :=
  isOpen_ne_fun (f.continuous.comp continuous_subtype_val) continuous_const

def nonzeroHomeomorph (f : E →L[ℝ] F) :
    ↥(nonzeroSet f) ≃ₜ (f ⁻¹' {y : F | y ≠ 0}) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, fun hx => by
      have hf := x.property
      change f x.val ≠ 0 at hf
      rw [hx, map_zero] at hf
      exact hf rfl⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def memberSphereEquiv (f : E →L[ℝ] F) (hf : Function.Surjective f)
    (n : ℕ) (hdim : Module.finrank ℝ F = n + 1) :
    ↥(nonzeroSet f) ≃ₕ TopCat.sphere.{0} n :=
  (nonzeroHomeomorph f).toHomotopyEquiv.trans
    ((LinearPreimageHomotopy.surjectivePreimageEquiv f hf {y : F | y ≠ 0}).trans
      (PuncturedSpace.sphereEquiv F n hdim))

variable (f : E →L[ℝ] F) (g : E →L[ℝ] G)

abbrev Complement := {x : E // f x ≠ 0 ∧ g x ≠ 0}

def intersectionHomeomorph :
    Complement f g ≃ₜ ↥(nonzeroSet f ∩ nonzeroSet g) where
  toFun x := ⟨⟨x.val, fun hx => by
      have hf := x.property.1
      rw [hx, map_zero] at hf
      exact hf rfl⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem cover (hjoint : ∀ x, f x = 0 → g x = 0 → x = 0) :
    Hatcher.Excision.CoverCondition
      (X := TopCat.of (Ambient (E := E))) (nonzeroSet f) (nonzeroSet g) where
  union_interior := by
    rw [(isOpen_nonzeroSet f).interior_eq, (isOpen_nonzeroSet g).interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    change f x.val ≠ 0 ∨ g x.val ≠ 0
    by_contra h
    push Not at h
    exact x.property (hjoint x.val h.1 h.2)

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

def boundaryHomologyIso
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hjoint : ∀ x, f x = 0 → g x = 0 → x = 0)
    (hE : Module.finrank ℝ E = 14)
    (hF : Module.finrank ℝ F = 10) (hG : Module.finrank ℝ G = 10)
    (R : C) : homology R 12 (TopCat.of (Complement f g)) ≅ R := by
  let h := cover f g hjoint
  let eF := memberSphereEquiv f hf 9 hF
  let eG := memberSphereEquiv g hg 9 hG
  have hFzero (i : ℕ) (hi : i = 12 ∨ i = 13) :
      IsZero (homology R i (TopCat.of ↥(nonzeroSet f))) :=
    (SphereHomology.isZero_offDiagonal R 9 i (by omega) (by omega)).of_iso
      (Hatcher.Singular.homologyIsoOfHomotopyEquiv eF R i)
  have hGzero (i : ℕ) (hi : i = 12 ∨ i = 13) :
      IsZero (homology R i (TopCat.of ↥(nonzeroSet g))) :=
    (SphereHomology.isZero_offDiagonal R 9 i (by omega) (by omega)).of_iso
      (Hatcher.Singular.homologyIsoOfHomotopyEquiv eG R i)
  have hABzero (i : ℕ) (hi : i = 12 ∨ i = 13) :
      IsZero (homology R i (TopCat.of ↥(nonzeroSet f)) ⊞
        homology R i (TopCat.of ↥(nonzeroSet g))) :=
    (biprod_isZero_iff _ _).mpr ⟨hFzero i hi, hGzero i hi⟩
  have hIso : IsIso (Hatcher.MayerVietoris.connecting h R 13 12 rfl) :=
    (Hatcher.MayerVietoris.sequence_exact h R 13 12 rfl).isIso_map' 1 (by decide)
      ((hABzero 13 (Or.inr rfl)).eq_zero_of_src _)
      ((hABzero 12 (Or.inl rfl)).eq_zero_of_tgt _)
  exact (homologyFunctor R 12).mapIso (TopCat.isoOfHomeo (intersectionHomeomorph f g)) ≪≫
    (asIso (Hatcher.MayerVietoris.connecting h R 13 12 rfl)).symm ≪≫
    Hatcher.Singular.homologyIsoOfHomotopyEquiv (PuncturedSpace.sphereEquiv E 13 hE) R 13 ≪≫
    SphereHomology.diagonalIso R 13 (by decide)

end AkopyanResearch.LinearPairComplementHomology
