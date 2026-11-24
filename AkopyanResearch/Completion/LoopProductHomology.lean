module

public import AkopyanResearch.Completion.LoopProductGeometry
public import AkopyanResearch.Completion.SphereSourceKernel

/-!
# Ordinary homology of a product with a sphere loop space

The split Mayer--Vietoris sequence of `X × PathSpace(S^(n+1))` computes
the kernel of the actual projection `X × ΩS^(n+1) → X`. The kernel is the
degree-shifted homology of the common-base fiber, through the previously
proved product-sphere recurrence.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.LoopProductHomology

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel LoopProductGeometry

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : Type w) [TopologicalSpace X] (R : C)

def baseIso (n i : ℕ) :
    homology R i (TopCat.of (Base X n)) ≅ homology R i (TopCat.of (X × LoopSphereCover.Fibre n)) :=
  (homologyFunctor R i).mapIso (TopCat.isoOfHomeo (baseHomeomorph X n))

def totalIso (n i : ℕ) : homology R i (TopCat.of (Total X n)) ≅ homology R i (TopCat.of X) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (totalEquiv X n) R i

def projectionMap (n i : ℕ) :
    homology R i (TopCat.of (X × LoopSphereCover.Fibre n)) ⟶ homology R i (TopCat.of X) :=
  (homologyFunctor R i).map (TopCat.ofHom (LoopProductGeometry.projection X n))

theorem epi_projectionMap (n i : ℕ) : Epi (projectionMap X R n i) := by
  have h : (homologyFunctor R i).map (TopCat.ofHom (sectionMap X n)) ≫
      projectionMap X R n i = 𝟙 _ := by
    change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
    rw [← Functor.map_comp]
    exact (homologyFunctor R i).map_id _
  exact epi_of_epi_fac h

theorem inclusion_projection (n i : ℕ) :
    SphereSourceHomology.baseInclusionMap (sourceMap X n) (LoopSphereCover.basepoint n) R i ≫
      (totalIso X R n i).hom = (baseIso X R n i).hom ≫ projectionMap X R n i := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ =
    (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem epi_baseInclusionMap (n i : ℕ) :
    Epi (SphereSourceHomology.baseInclusionMap
      (sourceMap X n) (LoopSphereCover.basepoint n) R i) := by
  have := epi_projectionMap X R n i
  apply (epi_comp_iff_of_isIso _ (totalIso X R n i).hom).mp
  rw [inclusion_projection]
  infer_instance

def projectionKernelIso (n i : ℕ) :
    Kernel (Base X n) R n i ≅ kernel (projectionMap X R n i) := by
  letI := epi_baseInclusionMap X R n (i + 1)
  exact SphereSourceKernel.kernelIso (sourceMap X n) (LoopSphereCover.basepoint n) R i ≪≫
    kernel.mapIso _ _ (baseIso X R n i) (totalIso X R n i) (inclusion_projection X R n i)

def projectionKernelShiftIso (n i : ℕ) (hni : n ≤ i) :
    kernel (projectionMap X R n i) ≅ homology R (i - n) (TopCat.of (Base X n)) :=
  (projectionKernelIso X R n i).symm ≪≫ degreeShiftIso (Base X n) R n i hni

theorem isIso_projection_of_isZero_kernel (n i : ℕ)
    (h : IsZero (kernel (projectionMap X R n i))) : IsIso (projectionMap X R n i) := by
  have := epi_projectionMap X R n i
  have : Mono (projectionMap X R n i) :=
    Abelian.mono_of_kernel_ι_eq_zero _ (h.eq_zero_of_src _)
  exact isIso_of_mono_of_epi _

theorem isIso_projection_below (n i : ℕ) (hi : i < n) :
    IsIso (projectionMap X R n i) :=
  isIso_projection_of_isZero_kernel X R n i
    ((isZero_kernel_below (Base X n) R n i hi).of_iso (projectionKernelIso X R n i).symm)

theorem isIso_projection_of_base_vanish (n i : ℕ) (hni : n ≤ i)
    (h : IsZero (homology R (i - n) (TopCat.of (Base X n)))) :
    IsIso (projectionMap X R n i) :=
  isIso_projection_of_isZero_kernel X R n i
    (h.of_iso (projectionKernelShiftIso X R n i hni))

end AkopyanResearch.LoopProductHomology
