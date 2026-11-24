module

public import AkopyanResearch.Completion.ProductSphereThom
public import Hatcher.Singular.PointedRelative

/-!
# Sphere homology from the proved product-sphere recurrence

For a point base, positive-dimensional homology of the base is zero.
Thus the actual product-projection kernel is the whole sphere homology.
The Mayer--Vietoris recurrence computes its diagonal group and all other
positive degrees without another excision or sphere-homology backend.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.SphereHomology

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
variable (R : C)

def positiveKernelIso (n i : ℕ) (hi : 0 < i) :
    homology R i (TopCat.sphere.{0} n) ≅ Kernel PUnit R n i := by
  let e : sphereProduct PUnit n ≅ TopCat.sphere.{0} n :=
    TopCat.isoOfHomeo (Homeomorph.punitProd (TopCat.sphere.{0} n))
  have hz := Hatcher.Singular.isZero_pointHomology R i (Nat.ne_of_gt hi)
  have : IsIso (kernel.ι (projectionMap PUnit R n i)) :=
    kernel.ι_of_zero (hz.eq_zero_of_tgt _)
  exact (homologyFunctor R i).mapIso e.symm ≪≫
    (asIso (kernel.ι (projectionMap PUnit R n i))).symm

/-- Positive-dimensional sphere homology in its top degree is the
coefficient object. The isomorphism chooses the orientation supplied by
the actual iterated Mayer--Vietoris maps. -/
def diagonalIso (n : ℕ) (hn : 0 < n) : homology R n (TopCat.sphere.{0} n) ≅ R :=
  positiveKernelIso R n n hn ≪≫
    (by simpa only [Nat.add_zero] using suspensionIso PUnit R n 0) ≪≫
    Hatcher.Singular.pointHomologyZeroIso R

theorem isZero_offDiagonal (n i : ℕ) (hi : 0 < i) (hne : i ≠ n) :
    IsZero (homology R i (TopCat.sphere.{0} n)) := by
  by_cases hin : i < n
  · exact (isZero_kernel_below PUnit R n i hin).of_iso (positiveKernelIso R n i hi)
  · have hni : n ≤ i := Nat.le_of_not_gt hin
    have hsub : i - n ≠ 0 := by omega
    have hz := Hatcher.Singular.isZero_pointHomology R (i - n) hsub
    exact (hz.of_iso (degreeShiftIso PUnit R n i hni)).of_iso
      (positiveKernelIso R n i hi)

def reducedDiagonalIso (n : ℕ) (hn : 0 < n) :
    (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.sphere.{0} n) ≅ R :=
  (Hatcher.Reduced.homologyIsoOfPositiveDegree R n hn).app (TopCat.sphere.{0} n) ≪≫
    diagonalIso R n hn

theorem isZero_reduced_offDiagonal (n i : ℕ) (hi : 0 < i) (hne : i ≠ n) :
    IsZero ((Hatcher.Reduced.homologyFunctor R i).obj (TopCat.sphere.{0} n)) :=
  (isZero_offDiagonal R n i hi hne).of_iso
    ((Hatcher.Reduced.homologyIsoOfPositiveDegree R i hi).app (TopCat.sphere.{0} n))

end AkopyanResearch.SphereHomology
