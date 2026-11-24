module

public import AkopyanResearch.Completion.LinearPreimageHomotopy
public import AkopyanResearch.Completion.PuncturedSpace
public import AkopyanResearch.Completion.ProductSphereProjection

/-!
# Primitive linear meridians after a closed deletion

Let `f : E →L[ℝ] F` be onto and let `Z` be a closed subset of `E`.
A point of `ker f` outside `Z` supplies a small meridian. A continuous
positive rescaling of a linear right inverse places the entire punctured
target inside that small neighbourhood. Its composite with `f` is radially
homotopic to the identity, so the actual induced homology map is split onto.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearMeridian

open ContinuousMap CategoryTheory CategoryTheory.Limits

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev Complement (f : E →L[ℝ] F) (Z : Set E) := {x : E // f x ≠ 0 ∧ x ∉ Z}

def map (f : E →L[ℝ] F) (Z : Set E) : C(Complement f Z, PuncturedSpace.Space F) :=
  ⟨fun x => ⟨f x.val, x.property.1⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

variable (f : E →L[ℝ] F) (g : F →L[ℝ] E)
  (hfg : f.comp g = ContinuousLinearMap.id ℝ F)
  (Z : Set E) (a : E) (ha : f a = 0) (ε : ℝ) (hε : 0 < ε)
  (hball : Metric.ball a ε ⊆ Zᶜ)

def factor (y : PuncturedSpace.Space F) : ℝ := ε / (1 + ‖g y.val‖)

include hε in
theorem factor_pos (y : PuncturedSpace.Space F) : 0 < factor g ε y :=
  div_pos hε (by positivity)

theorem continuous_factor : Continuous (factor g ε) :=
  continuous_const.div (continuous_const.add (g.continuous.comp continuous_subtype_val).norm)
    (fun _ => ne_of_gt (by positivity))

def rawSection (y : PuncturedSpace.Space F) : E := a + factor g ε y • g y.val

include hε in
theorem rawSection_dist_lt (y : PuncturedSpace.Space F) : dist (rawSection g a ε y) a < ε := by
  rw [dist_eq_norm]
  change ‖a + factor g ε y • g y.val - a‖ < ε
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (factor_pos g ε hε y).le]
  unfold factor
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : 0 < 1 + ‖g y.val‖)).mpr
  nlinarith

include hfg ha in
theorem map_rawSection (y : PuncturedSpace.Space F) :
    f (rawSection g a ε y) = factor g ε y • y.val := by
  have hfg' : f (g y.val) = y.val := congrArg (fun k : F →L[ℝ] F => k y.val) hfg
  simp only [rawSection, map_add, map_smul, ha, zero_add, hfg']

def sectionMap : C(PuncturedSpace.Space F, Complement f Z) where
  toFun y := ⟨rawSection g a ε y, by
    constructor
    · rw [map_rawSection f g hfg a ha ε]
      exact smul_ne_zero (factor_pos g ε hε y).ne' y.property
    · exact hball (rawSection_dist_lt g a ε hε y)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add
      ((continuous_factor g ε).smul (g.continuous.comp continuous_subtype_val))

def homotopyFactor (t : unitInterval) (y : PuncturedSpace.Space F) : ℝ :=
  (1 - t.val) * factor g ε y + t.val

include hε in
theorem homotopyFactor_pos (t : unitInterval) (y : PuncturedSpace.Space F) :
    0 < homotopyFactor g ε t y := by
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · have h := mul_pos (sub_pos.mpr ht) (factor_pos g ε hε y)
    exact add_pos_of_pos_of_nonneg h t.property.1
  · simp only [homotopyFactor, ht, sub_self, zero_mul, zero_add, zero_lt_one]

def sectionHomotopy :
    ((map f Z).comp (sectionMap f g hfg Z a ha ε hε hball)).Homotopy
      (ContinuousMap.id (PuncturedSpace.Space F)) where
  toFun p := ⟨homotopyFactor g ε p.1 p.2 • p.2.val,
    smul_ne_zero (homotopyFactor_pos g ε hε p.1 p.2).ne' p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have ht : Continuous (fun p : unitInterval × PuncturedSpace.Space F => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    exact (((continuous_const.sub ht).mul
      ((continuous_factor g ε).comp continuous_snd)).add ht).smul
      (continuous_subtype_val.comp continuous_snd)
  map_zero_left y := by
    apply Subtype.ext
    change ((1 - (0 : ℝ)) * factor g ε y + 0) • y.val = f (rawSection g a ε y)
    rw [map_rawSection f g hfg a ha ε]
    simp
  map_one_left y := by
    apply Subtype.ext
    change ((1 - (1 : ℝ)) * factor g ε y + 1) • y.val = y.val
    simp

include ha in
/-- The actual linear meridian admits a continuous section up to homotopy
whenever its kernel has a point outside the closed deletion. -/
theorem exists_homotopy_section [FiniteDimensional ℝ F]
    (hf : Function.Surjective f) (hZ : IsClosed Z) (haZ : a ∉ Z) :
    ∃ s : C(PuncturedSpace.Space F, Complement f Z),
      ((map f Z).comp s).Homotopic (ContinuousMap.id (PuncturedSpace.Space F)) := by
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hZ.isOpen_compl a haZ
  exact ⟨sectionMap f g hg Z a ha ε hε hball,
    ⟨sectionHomotopy f g hg Z a ha ε hε hball⟩⟩

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

include ha in
/-- This is a statement about the induced map of the original linear map,
not merely an abstract isomorphism between two homology groups. -/
theorem homologyMap_splitEpi [FiniteDimensional ℝ F]
    (hf : Function.Surjective f) (hZ : IsClosed Z) (haZ : a ∉ Z) (R : C) (i : ℕ) :
    IsSplitEpi ((ProductSphereKernel.homologyFunctor R i).map (TopCat.ofHom (map f Z))) := by
  obtain ⟨s, ⟨H⟩⟩ := exists_homotopy_section f Z a ha hf hZ haZ
  refine IsSplitEpi.mk' ⟨(ProductSphereKernel.homologyFunctor R i).map (TopCat.ofHom s), ?_⟩
  rw [← Functor.map_comp]
  change HomologicalComplex.homologyMap
    (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
      (TopCat.ofHom s ≫ TopCat.ofHom (map f Z))) i = 𝟙 _
  calc
    _ = HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
          (𝟙 (TopCat.of (PuncturedSpace.Space F)))) i :=
      TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R i
    _ = 𝟙 _ := by simp

include ha in
theorem homologyMap_splitEpi_of_homeomorph [FiniteDimensional ℝ F]
    (hf : Function.Surjective f) (hZ : IsClosed Z) (haZ : a ∉ Z)
    {T : Type} [TopologicalSpace T] (e : T ≃ₜ Complement f Z) (R : C) (i : ℕ) :
    IsSplitEpi ((ProductSphereKernel.homologyFunctor R i).map
      (TopCat.ofHom ((map f Z).comp ⟨e, e.continuous⟩))) := by
  have := homologyMap_splitEpi f Z a ha hf hZ haZ R i
  have he : TopCat.ofHom ((map f Z).comp ⟨e, e.continuous⟩) =
      (TopCat.isoOfHomeo e).hom ≫ TopCat.ofHom (map f Z) := rfl
  rw [he, Functor.map_comp]
  infer_instance

end AkopyanResearch.LinearMeridian
