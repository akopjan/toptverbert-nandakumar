module

public import AkopyanResearch.Completion.ProductSphereProjection
public import Hatcher.Sphere.ZeroSphere
public import Hatcher.MayerVietoris.Sequence

/-!
# The zero-sphere base of the product-sphere kernel calculation

The projection from a product with the zero-sphere is the codiagonal on
singular homology. Its actual categorical kernel is one copy of the homology
of the base. The decomposition is derived from Mayer--Vietoris for the two
open, disjoint components; no product or Thom formula is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.ProductSphereKernel

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Every degree of singular homology of an empty space vanishes. -/
theorem isZero_homology_of_isEmpty (R : C) (i : ℕ) (X : TopCat.{w}) [IsEmpty X] :
    IsZero (homology R i X) := by
  cases i with
  | zero =>
      have h : IsZero (∐ fun _ : X => R) := by
        rw [IsZero.iff_id_eq_zero]
        apply Sigma.hom_ext
        intro x
        exact isEmptyElim x
      exact h.of_iso (singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R X)
  | succ i =>
      exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C (i + 1) R X
        (Nat.succ_ne_zero i)

/-- For a disjoint interior cover, the actual Mayer--Vietoris union map is
an isomorphism in every degree. -/
theorem isIso_unionMap_of_disjoint {X : TopCat.{w}} {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B) (hd : Disjoint A B)
    (R : C) (i : ℕ) :
    IsIso (Hatcher.MayerVietoris.unionMap A B R i) := by
  have : IsEmpty ↥(A ∩ B) :=
    ⟨fun x => Set.disjoint_left.mp hd x.2.1 x.2.2⟩
  have hz (j : ℕ) : IsZero (homology R j (TopCat.of ↥(A ∩ B))) :=
    isZero_homology_of_isEmpty R j _
  have hm : Mono (Hatcher.MayerVietoris.unionMap A B R i) := by
    have he := (Hatcher.MayerVietoris.sequence_exact h R (i + 1) i rfl).exact 3
    exact he.mono_g ((hz i).eq_zero_of_src _)
  have he : Epi (Hatcher.MayerVietoris.unionMap A B R i) := by
    cases i with
    | zero => exact Hatcher.MayerVietoris.unionMap_zero_epi h R
    | succ i =>
        have he := (Hatcher.MayerVietoris.sequence_exact h R (i + 1) i rfl).exact 1
        exact he.epi_f ((hz i).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- One of the two open components of the actual product with the zero-sphere. -/
def zeroComponent (Z : Type w) [TopologicalSpace Z] (b : Bool) :
    Set (sphereProduct Z 0) :=
  {x | Hatcher.Sphere.zeroSphereHomeomorphTwoPoint x.2 = ULift.up b}

theorem zeroComponent_isOpen (Z : Type w) [TopologicalSpace Z] (b : Bool) :
    IsOpen (zeroComponent Z b) := by
  change IsOpen ((fun x : sphereProduct Z 0 =>
    Hatcher.Sphere.zeroSphereHomeomorphTwoPoint x.2) ⁻¹' {ULift.up b})
  exact (isOpen_discrete _).preimage
    (Hatcher.Sphere.zeroSphereHomeomorphTwoPoint.continuous.comp continuous_snd)

theorem zeroComponents_disjoint (Z : Type w) [TopologicalSpace Z] :
    Disjoint (zeroComponent Z false) (zeroComponent Z true) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h : (ULift.up false : ULift.{w} Bool) = ULift.up true := hx.symm.trans hy
  cases h

theorem zeroComponents_cover (Z : Type w) [TopologicalSpace Z] :
    Hatcher.Excision.CoverCondition (zeroComponent Z false) (zeroComponent Z true) where
  union_interior := by
    rw [(zeroComponent_isOpen Z false).interior_eq,
      (zeroComponent_isOpen Z true).interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    change Hatcher.Sphere.zeroSphereHomeomorphTwoPoint x.2 = ULift.up false ∨
      Hatcher.Sphere.zeroSphereHomeomorphTwoPoint x.2 = ULift.up true
    rcases Hatcher.Sphere.zeroSphereHomeomorphTwoPoint x.2 with ⟨b⟩
    cases b <;> simp

/-- The projection identifies each component with the base space. -/
def zeroComponentHomeomorph (Z : Type w) [TopologicalSpace Z] (b : Bool) :
    ↥(zeroComponent Z b) ≃ₜ Z where
  toEquiv := {
    toFun := fun x => x.1.1
    invFun := fun z => ⟨(z, Hatcher.Sphere.zeroSpherePoint b),
      Hatcher.Sphere.zeroSphereIsoTwoPoint_hom_point b⟩
    left_inv := by
      intro x
      apply Subtype.ext
      have hx : Hatcher.Sphere.zeroSpherePoint b = x.1.2 := by
        apply Hatcher.Sphere.zeroSphereHomeomorphTwoPoint.injective
        exact (Hatcher.Sphere.zeroSphereIsoTwoPoint_hom_point b).trans x.2.symm
      exact Prod.ext rfl hx
    right_inv := fun _ => rfl }
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk continuous_const).subtype_mk _

/-- The section selecting one of the two points of the zero-sphere. -/
def zeroSection (Z : Type w) [TopologicalSpace Z] (b : Bool) :
    TopCat.of Z ⟶ sphereProduct Z 0 :=
  TopCat.ofHom ⟨fun z => (z, Hatcher.Sphere.zeroSpherePoint b),
    continuous_id.prodMk continuous_const⟩

@[simp]
theorem zeroSection_comp_projection (Z : Type w) [TopologicalSpace Z] (b : Bool) :
    zeroSection Z b ≫ projection Z 0 = 𝟙 (TopCat.of Z) := rfl

@[simp]
theorem zeroComponent_inverse_comp_inclusion (Z : Type w) [TopologicalSpace Z] (b : Bool) :
    (TopCat.isoOfHomeo (zeroComponentHomeomorph Z b)).inv ≫
      Hatcher.MayerVietoris.subspaceInclusion (zeroComponent Z b) = zeroSection Z b := rfl

/-- The two sections give the biproduct decomposition in every homology degree. -/
def zeroProductHomologyIso (Z : Type w) [TopologicalSpace Z] (R : C) (i : ℕ) :
    homology R i (TopCat.of Z) ⊞ homology R i (TopCat.of Z) ≅
      homology R i (sphereProduct Z 0) := by
  have := isIso_unionMap_of_disjoint (zeroComponents_cover Z)
    (zeroComponents_disjoint Z) R i
  exact biprod.mapIso
      ((homologyFunctor R i).mapIso
        (TopCat.isoOfHomeo (zeroComponentHomeomorph Z false)).symm)
      ((homologyFunctor R i).mapIso
        (TopCat.isoOfHomeo (zeroComponentHomeomorph Z true)).symm) ≪≫
    asIso (Hatcher.MayerVietoris.unionMap
      (zeroComponent Z false) (zeroComponent Z true) R i)

theorem zeroProductHomologyIso_hom (Z : Type w) [TopologicalSpace Z] (R : C) (i : ℕ) :
    (zeroProductHomologyIso Z R i).hom =
      biprod.desc ((homologyFunctor R i).map (zeroSection Z false))
        ((homologyFunctor R i).map (zeroSection Z true)) := by
  apply biprod.hom_ext'
  · simp only [zeroProductHomologyIso, Iso.trans_hom, biprod.mapIso_hom,
      Functor.mapIso_hom, Iso.symm_hom, asIso_hom, biprod.inl_map_assoc,
      Hatcher.MayerVietoris.unionMap, biprod.inl_desc]
    change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
    rw [← Functor.map_comp, zeroComponent_inverse_comp_inclusion]
  · simp only [zeroProductHomologyIso, Iso.trans_hom, biprod.mapIso_hom,
      Functor.mapIso_hom, Iso.symm_hom, asIso_hom, biprod.inr_map_assoc,
      Hatcher.MayerVietoris.unionMap, biprod.inr_desc]
    change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ = _
    rw [← Functor.map_comp, zeroComponent_inverse_comp_inclusion]

/-- The decomposition is compatible with the actual projection. -/
theorem zeroProductHomologyIso_hom_comp_projectionMap
    (Z : Type w) [TopologicalSpace Z] (R : C) (i : ℕ) :
    (zeroProductHomologyIso Z R i).hom ≫ projectionMap Z R 0 i =
      biprod.desc (𝟙 _) (𝟙 _) := by
  rw [zeroProductHomologyIso_hom]
  apply biprod.hom_ext' <;>
    simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_desc, biprod.inr_desc, projectionMap, ← Functor.map_comp,
      zeroSection_comp_projection]
  all_goals exact (homologyFunctor R i).map_id (TopCat.of Z)

/-- The anti-diagonal identifies the kernel of a codiagonal with one summand. -/
def codiagonalKernelIso (A : C) : kernel (biprod.desc (𝟙 A) (𝟙 A)) ≅ A where
  hom := kernel.ι (biprod.desc (𝟙 A) (𝟙 A)) ≫ biprod.fst
  inv := kernel.lift (biprod.desc (𝟙 A) (𝟙 A))
    (biprod.lift (𝟙 A) (-𝟙 A)) (by simp [biprod.lift_desc])
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
    apply biprod.hom_ext
    · simp
    · have h := kernel.condition (biprod.desc (𝟙 A) (𝟙 A))
      simp only [biprod.desc_eq, Category.comp_id, Preadditive.comp_add] at h
      simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_neg,
        Category.comp_id]
      exact (eq_neg_of_add_eq_zero_right h).symm
  inv_hom_id := by simp

/-- The actual projection from the zero-sphere product has kernel `Hᵢ(Z)`. -/
def zeroSphereKernelIso (Z : Type w) [TopologicalSpace Z] (R : C) (i : ℕ) :
    Kernel Z R 0 i ≅ homology R i (TopCat.of Z) :=
  (kernel.mapIso (biprod.desc (𝟙 _) (𝟙 _)) (projectionMap Z R 0 i)
    (zeroProductHomologyIso Z R i) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      (zeroProductHomologyIso_hom_comp_projectionMap Z R i).symm)).symm ≪≫
    codiagonalKernelIso _

end AkopyanResearch.ProductSphereKernel
