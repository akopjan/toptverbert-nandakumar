module

public import AkopyanResearch.Completion.FiniteLoop13Coordinates

/-!
# Homology coordinates for finite families of actual loop-space models

Coordinatewise homotopy equivalences transport the checked product-loop
calculation. The resulting isomorphism remains the map induced by the
actual coordinate projections.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.FiniteLoopModelHomology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel ContinuousMap
open FiniteLoop13Homology

variable {ι : Type} [Fintype ι] {Y : ι → Type} [∀ j, TopologicalSpace (Y j)]
variable (e : ∀ j, Y j ≃ₕ Loop)

def productEquiv : (∀ j, Y j) ≃ₕ (ι → Loop) := HomotopyEquiv.piCongrRight e

def homologyIso (i : ℕ) : homology Coefficients i (TopCat.of (∀ j, Y j)) ≅
    homology Coefficients i (TopCat.of (ι → Loop)) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (productEquiv e) Coefficients i

include e in
theorem homology_vanish (i : ℕ) (hi : 0 < i) (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    IsZero (homology Coefficients i (TopCat.of (∀ j, Y j))) :=
  (FiniteLoop13Homology.homology_vanish ι i hi hi₁₄ hne).of_iso (homologyIso e i)

def evaluation (j : ι) : C((∀ j, Y j), Y j) := ⟨fun x => x j, continuous_apply j⟩

def coordinates : homology Coefficients 12 (TopCat.of (∀ j, Y j)) ⟶
    AddCommGrpCat.of (∀ j, ↥(homology Coefficients 12 (TopCat.of (Y j)))) := AddCommGrpCat.ofHom {
  toFun x j := (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation (Y := Y) j)) x
  map_zero' := by funext j; exact map_zero _
  map_add' := by intro x y; funext j; exact map_add _ x y }

def componentIso (j : ι) : homology Coefficients 12 (TopCat.of (Y j)) ≅ LoopHomology :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (e j) Coefficients 12

theorem coordinates_naturality (x : ↥(homology Coefficients 12 (TopCat.of (∀ j, Y j)))) (j : ι) :
    (componentIso e j).hom (coordinates (Y := Y) x j) =
      FiniteLoop13Coordinates.coordinates ι ((homologyIso e 12).hom x) j := by
  have h : (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation (Y := Y) j)) ≫
      (componentIso e j).hom = (homologyIso e 12).hom ≫
        (homologyFunctor Coefficients 12).map (TopCat.ofHom (FiniteLoop13Coordinates.evaluation ι j)) := by
    change (homologyFunctor Coefficients 12).map _ ≫ (homologyFunctor Coefficients 12).map _ =
      (homologyFunctor Coefficients 12).map _ ≫ (homologyFunctor Coefficients 12).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h x

include e in
theorem coordinates_bijective : Function.Bijective (coordinates (Y := Y)) := by
  have he : Function.Bijective (homologyIso e 12).hom := ConcreteCategory.bijective_of_isIso _
  have hc := FiniteLoop13Coordinates.coordinates_bijective ι
  have hj (j : ι) : Function.Bijective (componentIso e j).hom := ConcreteCategory.bijective_of_isIso _
  constructor
  · intro x y hxy
    apply he.1
    apply hc.1
    funext j
    rw [← coordinates_naturality, ← coordinates_naturality, congrFun hxy j]
  · intro z
    obtain ⟨a, ha⟩ := hc.2 (fun j => (componentIso e j).hom (z j))
    obtain ⟨x, hx⟩ := he.2 a
    refine ⟨x, funext fun j => ?_⟩
    apply (hj j).1
    rw [coordinates_naturality, hx, ha]

def coordinatesIso : homology Coefficients 12 (TopCat.of (∀ j, Y j)) ≅
    AddCommGrpCat.of (∀ j, ↥(homology Coefficients 12 (TopCat.of (Y j)))) := by
  letI := (ConcreteCategory.isIso_iff_bijective (coordinates (Y := Y))).mpr (coordinates_bijective e)
  exact asIso (coordinates (Y := Y))

end AkopyanResearch.FiniteLoopModelHomology
