module

public import AkopyanResearch.Completion.QuadraticComplementCoordinates
public import AkopyanResearch.Completion.OpenUnionBoundary

/-!
# The genuine degree-twelve atom-addition extension

Adding one atom gives a short exact sequence whose kernel is indexed by
the new critical pairs. The middle object is the actual homology of the
new partial complement, and the quotient map is induced by inclusion into
the old partial complement. The kernel map is the actual Mayer--Vietoris
boundary applied to the inclusion-induced degree-thirteen coordinates.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticBoundaryExtension

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets
open QuadraticStratumHomology QuadraticComplementHomology QuadraticComplementCoordinates
open ProductSphereKernel Submission DisjointComplementCoordinates OpenUnionBoundary

variable {S : Finset (Fin 15)}

def rawSequence (hS : S.Nonempty) (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    ShortComplex AddCommGrpCat :=
  OpenUnionBoundary.sequence (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ
    (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl coefficients 12
    (atomComplement_homology_zero hS m 12 (by norm_num) (by norm_num) (by norm_num))

def unionCoordinatesIso (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    (rawSequence hS F m).X₁ ≅ AddCommGrpCat.of (newPairs S F m → ℤ) :=
  (HgrpFunctor 13).mapIso (TopCat.isoOfHomeo
    (Homeomorph.setCongr (actual_atom_cover_union hS F m hm))) ≪≫
    pairIntegralCoordinatesIso hS (newPairs S F m)

def intersectionIso (hS : S.Nonempty) (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    (rawSequence hS F m).X₂ ≅ Hgrp 12 (TopCat.of ↥(partialComplementSet S (insert m F))) :=
  (HgrpFunctor 12).mapIso (TopCat.isoOfHomeo
    (Homeomorph.setCongr (partialComplementSet_insert F m).symm))

theorem intersectionIso_hom (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) :
    (intersectionIso hS F m).hom =
      (HgrpFunctor 12).map (TopCat.isoOfHomeo
        (Homeomorph.setCongr (partialComplementSet_insert F m).symm)).hom := rfl

theorem rawSequence_f (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) :
    (rawSequence hS F m).f =
      Hatcher.MayerVietoris.connecting
        (OpenUnionMayerVietoris.cover (X := TopCat.of (OpenAmbient S))
          (partialComplementSet S F) (atomSet S m)ᶜ
          (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl)
        coefficients 13 12 rfl ≫
      (HgrpFunctor 12).map (TopCat.isoOfHomeo
        (OpenUnionMayerVietoris.intersectionHomeomorph (X := TopCat.of (OpenAmbient S))
          (partialComplementSet S F) (atomSet S m)ᶜ)).hom :=
  OpenUnionBoundary.sequence_f (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ
    (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl coefficients 12
    (atomComplement_homology_zero hS m 12 (by norm_num) (by norm_num) (by norm_num))

def additionSequence (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) : ShortComplex AddCommGrpCat :=
  transport (rawSequence hS F m) (unionCoordinatesIso hS F m hm)
    (intersectionIso hS F m) (Iso.refl _)

theorem additionSequence_shortExact (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) : (additionSequence hS F m hm).ShortExact := by
  apply transport_shortExact
  exact OpenUnionBoundary.sequence_shortExact (X := TopCat.of (OpenAmbient S))
    (partialComplementSet S F) (atomSet S m)ᶜ
    (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl coefficients 12
    (atomComplement_homology_zero hS m 12 (by norm_num) (by norm_num) (by norm_num))
    (partialComplement_homology_zero hS F 13 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (atomComplement_homology_zero hS m 13 (by norm_num) (by norm_num) (by norm_num))
    (atomCoverUnion_homology_zero hS F m hm 12 (by norm_num) (by norm_num) (by norm_num))

def oldInclusion (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    TopCat.of ↥(partialComplementSet S (insert m F)) ⟶
      TopCat.of ↥(partialComplementSet S F) :=
  TopCat.ofHom (ContinuousMap.inclusion (by
    intro x hx n hn
    exact hx n (Finset.mem_insert_of_mem hn)))

theorem additionSequence_g (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    (additionSequence hS F m hm).g = (HgrpFunctor 12).map (oldInclusion F m) := by
  change (intersectionIso hS F m).inv ≫ (rawSequence hS F m).g ≫ 𝟙 _ = _
  rw [Category.comp_id]
  unfold rawSequence
  rw [OpenUnionBoundary.sequence_g]
  simp only [intersectionIso, Functor.mapIso_inv, ← Functor.map_comp]
  rfl

theorem additionSequence_f (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    (additionSequence hS F m hm).f =
      (unionCoordinatesIso hS F m hm).inv ≫ (rawSequence hS F m).f ≫
        (intersectionIso hS F m).hom := rfl

end AkopyanResearch.QuadraticBoundaryExtension
