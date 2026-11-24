module

public import AkopyanResearch.Completion.PairNormalHomology
public import AkopyanResearch.Completion.PairGoodPair
public import AkopyanResearch.Completion.RepresentationSphereInvariants

/-!
# The degree-thirteen relative group of the actual pair collapse

The ambient pair space is the product of the two original nine-spheres.
Its homology vanishes in degrees twelve and thirteen. The genuine pair
connecting map therefore identifies degree-thirteen relative homology with
degree-twelve homology of the actual collapsed locus, already computed by
the two-linear-kernel Mayer--Vietoris calculation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairRelativeHomology

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel PairCofiberModel

def ambientHomeomorph :
    PairSpace ≃ₜ OriginalJoinBridge.Target × (TopCat.sphere.{0} 9 : Type) :=
  spherePairEquiv.symm.trans
    (Homeomorph.prodCongr (Homeomorph.refl OriginalJoinBridge.Target)
      RepresentationSphereInvariants.singleHomeomorph)

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
variable (R : C)

theorem ambient_homology_vanish (i : ℕ) (hi : 9 < i) (hne : i ≠ 18) :
    IsZero (homology R i (TopCat.of PairSpace)) := by
  have hbase := RepresentationSphereInvariants.single_homology_vanish R i
    (by omega) (by omega)
  have hshift := RepresentationSphereInvariants.single_homology_vanish R (i - 9)
    (by omega) (by omega)
  have hker : IsZero (Kernel OriginalJoinBridge.Target R 9 i) :=
    hshift.of_iso (degreeShiftIso OriginalJoinBridge.Target R 9 i (by omega))
  have : IsIso (kernel.ι (projectionMap OriginalJoinBridge.Target R 9 i)) :=
    kernel.ι_of_zero (hbase.eq_zero_of_tgt _)
  exact (hker.of_iso (asIso
    (kernel.ι (projectionMap OriginalJoinBridge.Target R 9 i))).symm).of_iso
      ((homologyFunctor R i).mapIso (TopCat.isoOfHomeo ambientHomeomorph))

theorem connecting_isIso :
    IsIso (Hatcher.Relative.pairConnecting PairGoodPair.pair R 13 12 rfl) := by
  have h13 := ambient_homology_vanish R 13 (by decide) (by decide)
  have h12 := ambient_homology_vanish R 12 (by decide) (by decide)
  exact (Hatcher.Relative.pairSequence_exact PairGoodPair.pair R 13 12 rfl).isIso_map'
    1 (by decide) (h13.eq_zero_of_src _) (h12.eq_zero_of_tgt _)

/-- The relative group for the original pair is the coefficient object.
The first factor is the actual long-exact-sequence connecting map. -/
def relativeHomologyIso :
    (Hatcher.Relative.homologyFunctor R 13).obj PairGoodPair.pair ≅ R := by
  have := connecting_isIso R
  exact asIso (Hatcher.Relative.pairConnecting PairGoodPair.pair R 13 12 rfl) ≪≫
    PairNormalHomology.collapsedHomologyIso R

theorem relativeHomologyIso_hom :
    (relativeHomologyIso R).hom =
      Hatcher.Relative.pairConnecting PairGoodPair.pair R 13 12 rfl ≫
        (PairNormalHomology.collapsedHomologyIso R).hom := rfl

end AkopyanResearch.PairRelativeHomology
