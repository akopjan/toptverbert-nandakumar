module

public import AkopyanResearch.Completion.LinearTubeThom

/-!
# Linear-stratum Thom isomorphism with an arbitrary closed exceptional set

For the empty exceptional set the global orthogonal decomposition gives an
actual isomorphism of pairs. For a nonempty exceptional set the proved tube
excision theorem applies. The resulting statement has no nonemptiness
assumption on the exceptional set.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearTubeClosed

open CategoryTheory CategoryTheory.Limits
open LinearTube LinearTubePair ProductSphereKernel

universe w v u
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℝ E)

def emptyAmbientHomeomorph : Ambient (∅ : Set E) ≃ₜ E where
  toFun x := x.val
  invFun x := (⟨x, by simp⟩ : Ambient (∅ : Set E))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def emptyBaseHomeomorph : Base L (∅ : Set E) ≃ₜ L where
  toFun x := x.val
  invFun x := (⟨x, by simp⟩ : Base L (∅ : Set E))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The global coordinates used when no exceptional set is removed. -/
def emptyNormalCoordinates :
    (Base L (∅ : Set E) × NormalBall L) ≃ₜ Ambient (∅ : Set E) :=
  ((emptyBaseHomeomorph L).prodCongr
      (Homeomorph.unitBall : Lᗮ ≃ₜ NormalBall L).symm).trans
    ((coordinates L).toHomeomorph.symm.trans emptyAmbientHomeomorph.symm)

theorem emptyNormalCoordinates_punctured_iff
    (p : Base L (∅ : Set E) × NormalBall L) :
    emptyNormalCoordinates L p ∈ Punctured L (∅ : Set E) ↔ p.2.val ≠ 0 := by
  change (coordinates L).symm
      (p.1.val, (Homeomorph.unitBall : Lᗮ ≃ₜ NormalBall L).symm p.2) ∉ L ↔ _
  rw [← normal_zero_iff L, (coordinates L).apply_symm_apply]
  apply not_congr
  have h := ProductNormalPairKernel.unitBall_eq_zero_iff Lᗮ
    ((Homeomorph.unitBall : Lᗮ ≃ₜ NormalBall L).symm p.2)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The empty-exceptional case is an actual pair isomorphism. -/
def emptyNormalPairIso : NormalPair L (∅ : Set E) ≅ AmbientPair L (∅ : Set E) :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo ((emptyNormalCoordinates L).subtype
      (fun p => (emptyNormalCoordinates_punctured_iff L p).symm)))
    (TopCat.isoOfHomeo (emptyNormalCoordinates L)) (by ext p; rfl)

variable (Z : Set E) (hZ : IsClosed Z)
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

def normalHomologyIso (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R i).obj (NormalPair L Z) ≅
      (Hatcher.Relative.homologyFunctor R i).obj (AmbientPair L Z) := by
  classical
  by_cases hne : Z.Nonempty
  · exact LinearTubeExcision.normalHomologyIso L Z hZ hne R i
  · have hz : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst Z
    exact (Hatcher.Relative.homologyFunctor R i).mapIso (emptyNormalPairIso L)

/-- The actual relative Thom isomorphism, allowing the empty exceptional
set and an arbitrary base complement. -/
def relativeThomIso (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (c + i)).obj (AmbientPair L Z) ≅
      homology R i (TopCat.of (Base L Z)) :=
  (normalHomologyIso L Z hZ R (c + i)).symm.trans
    (ProductNormalThom.normalThomIso (Base L Z) Lᗮ c hc
      ((LinearTubeThom.normal_finrank_eq_codim L).trans hcodim) R i)

include hZ in
theorem isZero_relative_below_codim (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) (hi : i < c) :
    IsZero ((Hatcher.Relative.homologyFunctor R i).obj (AmbientPair L Z)) :=
  (ProductNormalThom.isZero_normal_relative_below (Base L Z) Lᗮ c hc
    ((LinearTubeThom.normal_finrank_eq_codim L).trans hcodim) R i hi).of_iso
      (normalHomologyIso L Z hZ R i).symm

end AkopyanResearch.LinearTubeClosed
