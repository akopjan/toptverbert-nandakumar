module

public import AkopyanResearch.Completion.SphereSourceHomology
public import AkopyanResearch.Completion.SignedExactKernel

/-!
# The complementary homology of a sphere-source homotopy fiber

When the common-base inclusion is epic in the next degree, the actual
Mayer--Vietoris sequence identifies its kernel with the product-sphere
kernel on the overlap. No spectral sequence or Künneth formula is used.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.SphereSourceKernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open ProductSphereKernel SphereSourceCover SphereSourceHomology

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

local instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
local instance : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {n : ℕ} (f : C(X × LoopSphereCover.Sphere.{w} n, Y)) (y₀ : Y) (R : C)

def overlapKernelIso (i : ℕ) :
    kernel (northOverlapMap f y₀ R i ≫ (northIso f y₀ R i).hom) ≅
      Kernel (BaseSpace f y₀) R n i :=
  kernel.mapIso _ _ (overlapIso f y₀ R i) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using north_projection f y₀ R i)

def kernelIso (i : ℕ) [Epi (baseInclusionMap f y₀ R (i + 1))] :
    Kernel (BaseSpace f y₀) R n i ≅ kernel (baseInclusionMap f y₀ R i) := by
  let hs := Hatcher.MayerVietoris.sequence_exact (cover f y₀) R (i + 1) i rfl
  have := epi_plusMap f y₀ R (i + 1)
  have he : Epi (Hatcher.MayerVietoris.unionMap (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R (i + 1)) := by
    rw [SphereSourceHomology.union_factor]
    infer_instance
  have hz : Hatcher.MayerVietoris.unionMap (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R (i + 1) ≫
        Hatcher.MayerVietoris.connecting (cover f y₀) R (i + 1) i rfl = 0 :=
    hs.toIsComplex.zero 1
  have hδ : Hatcher.MayerVietoris.connecting (cover f y₀) R (i + 1) i rfl = 0 :=
    zero_of_epi_comp _ hz
  have hm : Mono (Hatcher.MayerVietoris.intersectionMap
      (X := TopCat.of (Total f y₀))
      (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R i) :=
    (hs.exact 2).mono_g hδ
  have hm' : Mono (biprod.lift (northOverlapMap f y₀ R i)
      (-southOverlapMap f y₀ R i)) := hm
  exact (overlapKernelIso f y₀ R i).symm ≪≫
    SignedExactKernel.kernelIsoOfIsos (baseInclusionMap f y₀ R i)
      (northOverlapMap f y₀ R i) (southOverlapMap f y₀ R i)
      (northIso f y₀ R i) (southIso f y₀ R i)
      (Hatcher.MayerVietoris.unionMap (X := TopCat.of (Total f y₀))
        (SphereSourceCover.North f y₀) (SphereSourceCover.South f y₀) R i)
      (SphereSourceHomology.union_factor f y₀ R i).symm (hs.toIsComplex.zero 3) (hs.exact 3)

end AkopyanResearch.SphereSourceKernel
