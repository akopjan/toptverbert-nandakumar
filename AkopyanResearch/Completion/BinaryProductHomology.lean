module

public import AkopyanResearch.Completion.ProductSphereProjection
public import AkopyanResearch.Completion.RankOneProduct
public import Hatcher.Singular.Homology

/-! # Actual homology projections and sections of a binary product -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.BinaryProductHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y] (R : C) (i : ℕ)

def leftProjection : homology R i (TopCat.of (X × Y)) ⟶ homology R i (TopCat.of X) :=
  (homologyFunctor R i).map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)

def rightProjection : homology R i (TopCat.of (X × Y)) ⟶ homology R i (TopCat.of Y) :=
  (homologyFunctor R i).map (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)

def leftSection (y₀ : Y) : homology R i (TopCat.of X) ⟶ homology R i (TopCat.of (X × Y)) :=
  (homologyFunctor R i).map (TopCat.ofHom ⟨fun x => (x, y₀), continuous_id.prodMk continuous_const⟩)

def rightSection (x₀ : X) : homology R i (TopCat.of Y) ⟶ homology R i (TopCat.of (X × Y)) :=
  (homologyFunctor R i).map (TopCat.ofHom ⟨fun y => (x₀, y), continuous_const.prodMk continuous_id⟩)

theorem leftSection_leftProjection (y₀ : Y) :
    leftSection X Y R i y₀ ≫ leftProjection X Y R i = 𝟙 _ := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  exact (homologyFunctor R i).map_id _

theorem rightSection_rightProjection (x₀ : X) :
    rightSection X Y R i x₀ ≫ rightProjection X Y R i = 𝟙 _ := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  exact (homologyFunctor R i).map_id _

theorem constantMap_zero (y₀ : Y) (hi : i ≠ 0) :
    (homologyFunctor R i).map (TopCat.ofHom (ContinuousMap.const X y₀)) = 0 := by
  let a : TopCat.of X ⟶ TopCat.of PUnit.{w + 1} := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let b : TopCat.of PUnit.{w + 1} ⟶ TopCat.of Y := TopCat.ofHom (ContinuousMap.const _ y₀)
  have hz : IsZero (homology R i (TopCat.of PUnit.{w + 1})) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C i R _ hi
  change (homologyFunctor R i).map (a ≫ b) = 0
  rw [Functor.map_comp, hz.eq_zero_of_tgt ((homologyFunctor R i).map a), zero_comp]

theorem leftSection_rightProjection (y₀ : Y) (hi : i ≠ 0) :
    leftSection X Y R i y₀ ≫ rightProjection X Y R i = 0 := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  exact constantMap_zero X Y R i y₀ hi

theorem rightSection_leftProjection (x₀ : X) (hi : i ≠ 0) :
    rightSection X Y R i x₀ ≫ leftProjection X Y R i = 0 := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  exact constantMap_zero Y X R i x₀ hi

def coordinates : homology R i (TopCat.of (X × Y)) ⟶
    homology R i (TopCat.of X) ⊞ homology R i (TopCat.of Y) :=
  biprod.lift (leftProjection X Y R i) (rightProjection X Y R i)

theorem integral_coordinates_isIso (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (i : ℕ) (hi : i ≠ 0) (x₀ : X) (y₀ : Y)
    (eK : kernel (leftProjection X Y (AddCommGrpCat.of ℤ) i) ≅ AddCommGrpCat.of ℤ)
    (eY : homology (AddCommGrpCat.of ℤ) i (TopCat.of Y) ≅ AddCommGrpCat.of ℤ) :
    IsIso (coordinates X Y (AddCommGrpCat.of ℤ) i) :=
  RankOneProduct.isIso_coordinates _ _ (leftSection X Y (AddCommGrpCat.of ℤ) i y₀)
    (rightSection X Y (AddCommGrpCat.of ℤ) i x₀)
    (leftSection_leftProjection X Y (AddCommGrpCat.of ℤ) i y₀)
    (leftSection_rightProjection X Y (AddCommGrpCat.of ℤ) i y₀ hi)
    (rightSection_leftProjection X Y (AddCommGrpCat.of ℤ) i x₀ hi)
    (rightSection_rightProjection X Y (AddCommGrpCat.of ℤ) i x₀) eK eY

end AkopyanResearch.BinaryProductHomology
