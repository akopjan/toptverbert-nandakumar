module

public import AkopyanResearch.Completion.ProductNormalThom
public import AkopyanResearch.Completion.LinearTubeExcision
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The relative homology of an actual linear stratum complement

The actual geometric normal inclusion induces the excision isomorphism.
Composing its inverse with the product normal-pair calculation identifies
the relative homology of the exceptional-set complement with the shifted
homology of the stratum outside the exceptional set.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearTubeThom

open CategoryTheory CategoryTheory.Limits
open LinearTube LinearTubePair ProductSphereKernel

universe w v u
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℝ E) (Z : Set E) (hZ : IsClosed Z) (hne : Z.Nonempty)
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

theorem normal_finrank_eq_codim :
    Module.finrank ℝ Lᗮ = Module.finrank ℝ (E ⧸ L) := by
  have h₁ := L.finrank_add_finrank_orthogonal
  have h₂ := L.finrank_quotient_add_finrank
  omega

/-- The relative Thom isomorphism for a linear stratum with a closed
exceptional set removed. Both the pair and its normal inclusion are the
actual geometric objects. -/
def relativeThomIso (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (c + i)).obj (AmbientPair L Z) ≅
      homology R i (TopCat.of (Base L Z)) :=
  (LinearTubeExcision.normalHomologyIso L Z hZ hne R (c + i)).symm.trans
    (ProductNormalThom.normalThomIso (Base L Z) Lᗮ c hc
      ((normal_finrank_eq_codim L).trans hcodim) R i)

/-- The normal inclusion followed by the ambient Thom isomorphism is
exactly the product normal-pair Thom isomorphism. -/
@[reassoc]
theorem normalInclusion_comp_relativeThomIso (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (c + i)).map
        (normalInclusion L Z hZ hne) ≫
      (relativeThomIso L Z hZ hne c hc hcodim R i).hom =
      (ProductNormalThom.normalThomIso (Base L Z) Lᗮ c hc
        ((normal_finrank_eq_codim L).trans hcodim) R i).hom := by
  change (LinearTubeExcision.normalHomologyIso L Z hZ hne R (c + i)).hom ≫
    ((LinearTubeExcision.normalHomologyIso L Z hZ hne R (c + i)).symm.trans _).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

def relativeThomDegreeIso (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) (hci : c ≤ i) :
    (Hatcher.Relative.homologyFunctor R i).obj (AmbientPair L Z) ≅
      homology R (i - c) (TopCat.of (Base L Z)) := by
  simpa only [Nat.add_sub_of_le hci] using
    relativeThomIso L Z hZ hne c hc hcodim R (i - c)

include hZ hne in
theorem isZero_relative_below_codim (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) (hi : i < c) :
    IsZero ((Hatcher.Relative.homologyFunctor R i).obj (AmbientPair L Z)) :=
  (ProductNormalThom.isZero_normal_relative_below (Base L Z) Lᗮ c hc
    ((normal_finrank_eq_codim L).trans hcodim) R i hi).of_iso
      (LinearTubeExcision.normalHomologyIso L Z hZ hne R i).symm

include hZ hne in
theorem isZero_relative_of_base (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ)
    (hi : IsZero (homology R i (TopCat.of (Base L Z)))) :
    IsZero ((Hatcher.Relative.homologyFunctor R (c + i)).obj (AmbientPair L Z)) :=
  hi.of_iso (relativeThomIso L Z hZ hne c hc hcodim R i)

end AkopyanResearch.LinearTubeThom
