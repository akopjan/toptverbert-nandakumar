module

public import AkopyanResearch.Completion.LoopSphereCover
public import AkopyanResearch.Completion.LoopSpaceConnectivity
public import AkopyanResearch.Completion.ProductSphereThom

/-!
# Homology recurrence for the actual loop fibre of a sphere

Ordinary Mayer--Vietoris for the contractible based path space makes its
signed overlap map an isomorphism in positive degrees. Taking the kernel
of the northern projection identifies fibre homology with the already
computed kernel of product-sphere projection. This is a direct proof from
ordinary singular homology and explicit path-space trivialisations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.LoopSphereHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap
open LoopSphereCover ProductSphereKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

local instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
local instance : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts

variable (R : C)

theorem isZero_totalHomology (n i : ℕ) (hi : i ≠ 0) :
    IsZero (homology R i (TopCat.of (Total.{w} n))) := by
  let e : Total.{w} n ≃ₕ PUnit.{w + 1} := (ContractibleSpace.hequiv _ _).some
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C i R
    (TopCat.of PUnit.{w + 1}) hi).of_iso
      (Hatcher.Singular.homologyIsoOfHomotopyEquiv e R i)

def northHomologyIso (n i : ℕ) :
    homology R i (TopCat.of (LoopSphereCover.North.{w} n)) ≅
      homology R i (TopCat.of (Fibre.{w} n)) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (northEquiv n) R i

def southHomologyIso (n i : ℕ) :
    homology R i (TopCat.of (LoopSphereCover.South.{w} n)) ≅
      homology R i (TopCat.of (Fibre.{w} n)) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (southEquiv n) R i

def overlapHomologyIso (n i : ℕ) :
    homology R i (TopCat.of ↑(LoopSphereCover.North.{w} n ∩ LoopSphereCover.South n)) ≅
      homology R i (sphereProduct (Fibre.{w} n) n) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (intersectionEquiv n) R i

def northInclusionMap (n i : ℕ) :
    homology R i (TopCat.of ↑(LoopSphereCover.North.{w} n ∩ LoopSphereCover.South n)) ⟶
      homology R i (TopCat.of (LoopSphereCover.North.{w} n)) :=
  (homologyFunctor R i).map
    (Hatcher.MayerVietoris.intersectionToLeft
      (X := TopCat.of (Total.{w} n))
      (LoopSphereCover.North n) (LoopSphereCover.South n))

theorem northInclusionMap_projection (n i : ℕ) :
    northInclusionMap R n i ≫ (northHomologyIso R n i).hom =
      (overlapHomologyIso R n i).hom ≫ projectionMap (Fibre.{w} n) R n i := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ =
    (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

theorem isIso_intersectionMap (n i : ℕ) (hi : i ≠ 0) :
    IsIso (Hatcher.MayerVietoris.intersectionMap
      (X := TopCat.of (Total.{w} n))
      (LoopSphereCover.North.{w} n) (LoopSphereCover.South n) R i) := by
  have hs := Hatcher.MayerVietoris.sequence_exact (cover n) R (i + 1) i rfl
  have hm : Mono (Hatcher.MayerVietoris.intersectionMap
      (X := TopCat.of (Total.{w} n))
      (LoopSphereCover.North.{w} n) (LoopSphereCover.South n) R i) :=
    (hs.exact 2).mono_g ((isZero_totalHomology R n (i + 1) (by omega)).eq_zero_of_src _)
  have he : Epi (Hatcher.MayerVietoris.intersectionMap
      (X := TopCat.of (Total.{w} n))
      (LoopSphereCover.North.{w} n) (LoopSphereCover.South n) R i) :=
    (hs.exact 3).epi_f ((isZero_totalHomology R n i hi).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

def mayerVietorisIso (n i : ℕ) (hi : i ≠ 0) :
    homology R i (TopCat.of ↑(LoopSphereCover.North.{w} n ∩ LoopSphereCover.South n)) ≅
      homology R i (TopCat.of (LoopSphereCover.North.{w} n)) ⊞
        homology R i (TopCat.of (LoopSphereCover.South.{w} n)) := by
  letI := isIso_intersectionMap R n i hi
  exact asIso (Hatcher.MayerVietoris.intersectionMap
    (X := TopCat.of (Total.{w} n))
    (LoopSphereCover.North n) (LoopSphereCover.South n) R i)

theorem mayerVietorisIso_hom_fst (n i : ℕ) (hi : i ≠ 0) :
    (mayerVietorisIso R n i hi).hom ≫ biprod.fst = northInclusionMap R n i :=
  biprod.lift_fst _ _

/-- The kernel of a map which becomes the first projection under an
actual isomorphism is the second summand. -/
def kernelFstFactorIso {X A B : C} (e : X ≅ A ⊞ B) (p : X ⟶ A)
    (hp : e.hom ≫ biprod.fst = p) : kernel p ≅ B :=
  (kernel.mapIso p biprod.fst e (Iso.refl A) (by simpa using hp.symm)).trans
    (kernelBiprodFstIso (X := A) (Y := B))

/-- The actual product-projection kernel is the actual fibre homology. -/
def projectionKernelIso (n i : ℕ) (hi : i ≠ 0) :
    Kernel (Fibre.{w} n) R n i ≅ homology R i (TopCat.of (Fibre.{w} n)) :=
  (kernel.mapIso (northInclusionMap R n i) (projectionMap (Fibre.{w} n) R n i)
      (overlapHomologyIso R n i) (northHomologyIso R n i)
      (northInclusionMap_projection R n i)).symm.trans
    ((kernelFstFactorIso (mayerVietorisIso R n i hi) (northInclusionMap R n i)
      (mayerVietorisIso_hom_fst R n i hi)).trans (southHomologyIso R n i))

theorem isZero_fibre_below (n i : ℕ) (hi : 0 < i) (hin : i < n) :
    IsZero (homology R i (TopCat.of (Fibre.{w} n))) :=
  (isZero_kernel_below (Fibre.{w} n) R n i hin).of_iso
    (projectionKernelIso R n i (by omega)).symm

/-- Positive-degree loop-sphere homology recurs with period equal to the
dimension of the equator. -/
def recurrenceIso (n i : ℕ) (hi : 0 < i) (hni : n ≤ i) :
    homology R i (TopCat.of (Fibre.{w} n)) ≅
      homology R (i - n) (TopCat.of (Fibre.{w} n)) :=
  (projectionKernelIso R n i (by omega)).symm.trans
    (ProductSphereKernel.degreeShiftIso (Fibre.{w} n) R n i hni)

def firstDegreeIso (n : ℕ) (hn : 0 < n) :
    homology R n (TopCat.of (Fibre.{w} n)) ≅
      homology R 0 (TopCat.of (Fibre.{w} n)) := by
  simpa only [Nat.sub_self] using recurrenceIso R n n hn le_rfl

/-- In the first two periods, the only possible positive homology degree
is the equator dimension. -/
theorem isZero_fibre_low_offDiagonal (n i : ℕ)
    (hi : 0 < i) (hi₂ : i < 2 * n) (hine : i ≠ n) :
    IsZero (homology R i (TopCat.of (Fibre.{w} n))) := by
  by_cases hin : i < n
  · exact isZero_fibre_below R n i hi hin
  · exact (isZero_fibre_below R n (i - n) (by omega) (by omega)).of_iso
      (recurrenceIso R n i hi (by omega))

def loopHomologyIso (n i : ℕ) :
    homology R i (TopCat.of (Path (basepoint.{w} n) (basepoint n))) ≅
      homology R i (TopCat.of (Fibre.{w} n)) :=
  (homologyFunctor R i).mapIso (TopCat.isoOfHomeo (loopHomeomorph n).symm)

theorem isZero_loop_low_offDiagonal (n i : ℕ)
    (hi : 0 < i) (hi₂ : i < 2 * n) (hine : i ≠ n) :
    IsZero (homology R i (TopCat.of (Path (basepoint.{w} n) (basepoint n)))) :=
  (isZero_fibre_low_offDiagonal R n i hi hi₂ hine).of_iso (loopHomologyIso R n i)

/-- The first nonzero positive-degree fibre group is the coefficient
object. Path connectedness is proved from the vanishing sphere π₁. -/
def fibreDiagonalIso (n : ℕ) (hn : 0 < n) :
    homology R n (TopCat.of (Fibre.{w} n)) ≅ R := by
  have := LoopSpaceConnectivity.pathConnectedSpace_fibre n hn
  exact (firstDegreeIso R n hn).trans
    (asIso ((TopCat.of (Fibre.{w} n)).singularHomology₀ε R))

def loopDiagonalIso (n : ℕ) (hn : 0 < n) :
    homology R n (TopCat.of (Path (basepoint.{w} n) (basepoint n))) ≅ R :=
  (loopHomologyIso R n n).trans (fibreDiagonalIso R n hn)

def omegaSphere13Homology12Iso :
    homology R 12 (TopCat.of (Path (basepoint.{w} 12) (basepoint 12))) ≅ R :=
  loopDiagonalIso R 12 (by decide)

theorem omegaSphere13_homology_vanish (i : ℕ) (hi : 0 < i)
    (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    IsZero (homology R i (TopCat.of (Path (basepoint.{w} 12) (basepoint 12)))) :=
  isZero_loop_low_offDiagonal R 12 i hi (by omega) hne

end AkopyanResearch.LoopSphereHomology
