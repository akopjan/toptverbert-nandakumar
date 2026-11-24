module

public import AkopyanResearch.Completion.ProductSphereThom
public import AkopyanResearch.Completion.ProductNormalPairKernel

/-!
# Relative homology of a trivial normal ball bundle

The pair sequence, the radial deformation of a punctured ball, and the
actual product-sphere Mayer--Vietoris recurrence give the degree shift for
the product normal pair. No Thom-isomorphism hypothesis is introduced.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ProductNormalThom

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel ProductNormalPairKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (Z : Type w) [TopologicalSpace Z]
variable (E : Type w) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual relative normal-pair homology shifts by the dimension of
the normal vector space. -/
def normalThomIso (c : ℕ) (hc : 0 < c) (hE : Module.finrank ℝ E = c)
    (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (c + i)).obj (normalBallPair Z E) ≅
      homology R i (TopCat.of Z) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hdim : Module.finrank ℝ E = (c - 1) + 1 := by omega
  have hdegree : c + i = ((c - 1) + i) + 1 := by omega
  rw [hdegree]
  exact (normalBallKernelIso Z E (c - 1) hdim R ((c - 1) + i)).trans
    (suspensionIso Z R (c - 1) i)

/-- Every relative group below the normal rank vanishes, for an arbitrary
base space, including an empty or disconnected base. -/
theorem isZero_normal_relative_below (c : ℕ) (hc : 0 < c)
    (hE : Module.finrank ℝ E = c) (R : C) (i : ℕ) (hi : i < c) :
    IsZero ((Hatcher.Relative.homologyFunctor R i).obj (normalBallPair Z E)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  cases i with
  | zero => exact isZero_normalBall_relative_zero Z E R
  | succ i =>
      have hdim : Module.finrank ℝ E = (c - 1) + 1 := by omega
      exact (isZero_kernel_below Z R (c - 1) i (by omega)).of_iso
        (normalBallKernelIso Z E (c - 1) hdim R i)

theorem isZero_normal_relative_of_homology (c : ℕ) (hc : 0 < c)
    (hE : Module.finrank ℝ E = c) (R : C) (i : ℕ)
    (hi : IsZero (homology R i (TopCat.of Z))) :
    IsZero ((Hatcher.Relative.homologyFunctor R (c + i)).obj (normalBallPair Z E)) :=
  hi.of_iso (normalThomIso Z E c hc hE R i)

/-- A degree-indexed version of the same geometric isomorphism. -/
def normalThomDegreeIso (c : ℕ) (hc : 0 < c) (hE : Module.finrank ℝ E = c)
    (R : C) (i : ℕ) (hci : c ≤ i) :
    (Hatcher.Relative.homologyFunctor R i).obj (normalBallPair Z E) ≅
      homology R (i - c) (TopCat.of Z) := by
  simpa only [Nat.add_sub_of_le hci] using normalThomIso Z E c hc hE R (i - c)

def rankTenIso (hE : Module.finrank ℝ E = 10) (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (10 + i)).obj (normalBallPair Z E) ≅
      homology R i (TopCat.of Z) := normalThomIso Z E 10 (by decide) hE R i

def rankFourteenIso (hE : Module.finrank ℝ E = 14) (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (14 + i)).obj (normalBallPair Z E) ≅
      homology R i (TopCat.of Z) := normalThomIso Z E 14 (by decide) hE R i

end AkopyanResearch.ProductNormalThom
