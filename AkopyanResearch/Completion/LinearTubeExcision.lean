module

public import AkopyanResearch.Completion.LinearTubePair
public import Hatcher.Excision.BinaryCover

/-!
# Excision onto the actual trivial normal tube

The geometric inclusion of the product normal pair induces an isomorphism
on relative singular homology in every degree. This applies the proved
binary-cover excision theorem to the actual open tube, with the normal
coordinates and the deleted zero section identified exactly.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearTubeExcision

open CategoryTheory CategoryTheory.Limits
open LinearTubePair

universe u v w
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℝ E) (Z : Set E) (hZ : IsClosed Z) (hne : Z.Nonempty)

include hZ hne in
theorem cover : Hatcher.Excision.CoverCondition
    (X := TopCat.of (Ambient Z)) (Punctured L Z) (Neighborhood L Z) where
  union_interior := by
    rw [(isOpen_punctured L Z).interior_eq,
      (isOpen_neighborhood L Z hZ).interior_eq,
      punctured_union_neighborhood L Z hZ hne]

variable {C : Type v} [Category.{w} C] [Preadditive C]
  [HasCoproducts.{u} C] [CategoryWithHomology C]

include hZ hne in
theorem tubeInclusion_isIso (R : C) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map (tubeInclusion L Z)) := by
  change IsIso ((Hatcher.Relative.homologyFunctor R n).map
    (Hatcher.Excision.coverPairHom (cover L Z hZ hne)))
  infer_instance

theorem normalInclusion_isIso (R : C) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map (normalInclusion L Z hZ hne)) := by
  have := tubeInclusion_isIso L Z hZ hne R n
  rw [normalInclusion, Functor.map_comp]
  infer_instance

/-- Relative singular homology is identified by the actual geometric
normal inclusion, without a separately assumed Thom isomorphism. -/
def normalHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Relative.homologyFunctor R n).obj (NormalPair L Z) ≅
      (Hatcher.Relative.homologyFunctor R n).obj (AmbientPair L Z) := by
  letI := normalInclusion_isIso L Z hZ hne R n
  exact asIso ((Hatcher.Relative.homologyFunctor R n).map (normalInclusion L Z hZ hne))

theorem normalHomologyIso_hom (R : C) (n : ℕ) :
    (normalHomologyIso L Z hZ hne R n).hom =
      (Hatcher.Relative.homologyFunctor R n).map (normalInclusion L Z hZ hne) := rfl

end AkopyanResearch.LinearTubeExcision
