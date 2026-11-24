module

public import AkopyanResearch.Completion.ProductSphereThom

/-!
# When product-sphere projection induces a homology isomorphism

Projection has an actual constant-sphere section. Its categorical kernel
was computed from Mayer--Vietoris; vanishing of that kernel therefore
makes the actual projection morphism an isomorphism.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ProductProjectionIsomorphism

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (Z : Type w) [TopologicalSpace Z] (R : C)

def spherePoint : (n : ℕ) → (TopCat.sphere.{w} n : Type w)
  | 0 => Hatcher.Sphere.zeroSpherePoint true
  | n + 1 => ProductHemisphereCover.commonPoint n

def projectionSection (n : ℕ) : TopCat.of Z ⟶ sphereProduct Z n :=
  TopCat.ofHom ⟨fun z => (z, spherePoint n), continuous_id.prodMk continuous_const⟩

theorem section_projection (n i : ℕ) :
    (homologyFunctor R i).map (projectionSection Z n) ≫ projectionMap Z R n i = 𝟙 _ := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
  rw [← Functor.map_comp]
  exact (homologyFunctor R i).map_id _

theorem epi_projection (n i : ℕ) : Epi (projectionMap Z R n i) :=
  epi_of_epi_fac (section_projection Z R n i)

theorem isIso_of_isZero_kernel (n i : ℕ) (h : IsZero (Kernel Z R n i)) :
    IsIso (projectionMap Z R n i) := by
  have := epi_projection Z R n i
  have : Mono (projectionMap Z R n i) :=
    Abelian.mono_of_kernel_ι_eq_zero _ (h.eq_zero_of_src _)
  exact isIso_of_mono_of_epi _

theorem isIso_below (n i : ℕ) (hi : i < n) : IsIso (projectionMap Z R n i) :=
  isIso_of_isZero_kernel Z R n i (isZero_kernel_below Z R n i hi)

theorem isIso_of_base_vanish (n i : ℕ) (hni : n ≤ i)
    (h : IsZero (homology R (i - n) (TopCat.of Z))) : IsIso (projectionMap Z R n i) :=
  isIso_of_isZero_kernel Z R n i (h.of_iso (degreeShiftIso Z R n i hni))

end AkopyanResearch.ProductProjectionIsomorphism
