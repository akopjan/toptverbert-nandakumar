module

public import Hatcher.Singular.Relative
public import Hatcher.Singular.Homology
public import Submission.WhiteheadTheorem.Shapes.MappingCylinder
public import Submission.Hurewicz.ConnectedVanishing

/-!
# Relative homology of the actual mapping-cylinder pair

The domain is embedded by the original mapping-cylinder inclusion. The
canonical deformation retraction composes with this inclusion to the
original map. The long exact sequence then turns surjectivity in degree
`i+1` and injectivity in degree `i` into vanishing of the actual relative
group in degree `i+1`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingCylinderHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Submission

abbrev Coefficients := AddCommGrpCat.of ℤ
abbrev relative (P : TopPair) (i : ℕ) := (Hatcher.Relative.homologyFunctor Coefficients i).obj P

/-- The homology of a pair vanishes between an epimorphism and a
monomorphism in its genuine long exact sequence. -/
theorem relative_isZero_of_epi_mono (P : TopPair) (i : ℕ)
    [Epi (HgrpMap (i + 1) P.map)] [Mono (HgrpMap i P.map)] :
    IsZero (relative P (i + 1)) := by
  let T := Hatcher.Relative.pairSequence P Coefficients (i + 1) i rfl
  have hT := Hatcher.Relative.pairSequence_exact P Coefficients (i + 1) i rfl
  let a01 := T.map' 0 1
  let a34 := T.map' 3 4
  have hE : Epi a01 := by change Epi (HgrpMap (i + 1) P.map); infer_instance
  have hM : Mono a34 := by change Mono (HgrpMap i P.map); infer_instance
  apply (hT.exact 1).isZero_X₂
  · apply (cancel_epi a01).mp
    rw [comp_zero]
    exact hT.zero 0
  · apply (cancel_mono a34).mp
    rw [zero_comp]
    exact hT.zero 2

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

abbrev embeddedPair : TopPair :=
  TopPair.of (TopCat.MapCyl.domIncl f) (TopCat.MapCyl.isEmbedding_domIncl f)

abbrev topPair : TopPair := TopPair.ofSubset (X := TopCat.MapCyl f) (TopCat.MapCyl.top f)

def embeddedPairIsoTop : embeddedPair f ≅ topPair f :=
  MorphismProperty.Arrow.isoMk (TopCat.isoOfHomeo (TopCat.MapCyl.domHomeoTop f))
    (Iso.refl _) rfl

def retractionHomologyIso (i : ℕ) : Hgrp i (TopCat.MapCyl f) ≅ Hgrp i Y :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (TopCat.MapCyl.homotopyEquivBase f) Coefficients i

theorem retractionHomologyIso_hom (i : ℕ) :
    (retractionHomologyIso f i).hom = HgrpMap i (TopCat.MapCyl.retr f) := rfl

theorem inclusion_retraction_homology (i : ℕ) :
    HgrpMap i (TopCat.MapCyl.domIncl f) ≫ HgrpMap i (TopCat.MapCyl.retr f) = HgrpMap i f := by
  rw [← Functor.map_comp, TopCat.MapCyl.domIncl_retr_eq]

theorem inclusion_epi (i : ℕ) [Epi (HgrpMap i f)] :
    Epi (HgrpMap i (TopCat.MapCyl.domIncl f)) := by
  have hR : IsIso (HgrpMap i (TopCat.MapCyl.retr f)) :=
    (retractionHomologyIso f i).isIso_hom
  apply (epi_comp_iff_of_isIso _ (HgrpMap i (TopCat.MapCyl.retr f))).mp
  rw [inclusion_retraction_homology]
  infer_instance

theorem inclusion_mono (i : ℕ) [Mono (HgrpMap i f)] :
    Mono (HgrpMap i (TopCat.MapCyl.domIncl f)) := by
  have hR : IsIso (HgrpMap i (TopCat.MapCyl.retr f)) :=
    (retractionHomologyIso f i).isIso_hom
  apply (mono_comp_iff_of_mono _ (HgrpMap i (TopCat.MapCyl.retr f))).mp
  rw [inclusion_retraction_homology]
  infer_instance

theorem embeddedPair_homology_zero (i : ℕ)
    [Epi (HgrpMap (i + 1) f)] [Mono (HgrpMap i f)] :
    IsZero (relative (embeddedPair f) (i + 1)) := by
  have hE : Epi (HgrpMap (i + 1) (embeddedPair f).map) := inclusion_epi f (i + 1)
  have hM : Mono (HgrpMap i (embeddedPair f).map) := inclusion_mono f i
  exact relative_isZero_of_epi_mono (embeddedPair f) i

theorem topPair_homology_zero (i : ℕ)
    [Epi (HgrpMap (i + 1) f)] [Mono (HgrpMap i f)] :
    IsZero (relative (topPair f) (i + 1)) :=
  (embeddedPair_homology_zero f i).of_iso
    ((Hatcher.Relative.homologyFunctor Coefficients (i + 1)).mapIso (embeddedPairIsoTop f)).symm

section DegreeZero

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

theorem singletonInclusion_zero_isIso (hA : IsNConnected 1 A) (a : A) :
    IsIso (HgrpMap 0 (subIncl (Y := TopCat.of A) ({a} : Set A))) := by
  let hp := hA.connectedSingletonPair a
  obtain ⟨d⟩ := exists_simplicialDeformation_of_connectedPair 1 (TopCat.of A)
    ({a} : Set A) (Set.singleton_nonempty a) hp.surjective_iStar_zero
    (fun n hn => hp.unique_piRel n (by omega))
  exact d.isIso_relIota 0 (by decide)

def singletonHomeomorph (a : A) (b : B) : ({a} : Set A) ≃ₜ ({b} : Set B) where
  toFun _ := ⟨b, Set.mem_singleton b⟩
  invFun _ := ⟨a, Set.mem_singleton a⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

theorem singleton_square (g : C(A, B)) (a : A) :
    subIncl (Y := TopCat.of A) ({a} : Set A) ≫ TopCat.ofHom g =
      (TopCat.isoOfHomeo (singletonHomeomorph a (g a))).hom ≫
        subIncl (Y := TopCat.of B) ({g a} : Set B) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrArg g (Set.mem_singleton_iff.mp x.property)

/-- The actual induced map on degree-zero homology is an isomorphism.
The available one-connected hypotheses suffice to construct the natural
singleton comparison directly from the checked simplex compression. -/
theorem homologyMap_zero_isIso (g : C(A, B))
    (hA : IsNConnected 1 A) (hB : IsNConnected 1 B) :
    IsIso (HgrpMap 0 (TopCat.ofHom g)) := by
  let a : A := Classical.choice hA.nonempty
  have := singletonInclusion_zero_isIso hA a
  have := singletonInclusion_zero_isIso hB (g a)
  apply (isIso_comp_left_iff (HgrpMap 0 (subIncl (Y := TopCat.of A) ({a} : Set A))) _).mp
  rw [← Functor.map_comp, singleton_square, Functor.map_comp]
  infer_instance

end DegreeZero
end AkopyanResearch.MappingCylinderHomology
