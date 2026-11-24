module

public import AkopyanResearch.Completion.QuadraticNewPairKernel

/-!
# The actual degree-twelve pair-coordinate isomorphism

Finite induction uses the actual Mayer--Vietoris short exact sequence.
The new pair maps are isomorphisms on its kernel; the old pair maps are
the coordinate maps on its quotient. Thus the complete coordinate map,
with the original critical-pair indexing, is an isomorphism.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticPairHomology

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets
open QuadraticPairEnumeration QuadraticPairCoordinates QuadraticNewPairKernel
open QuadraticBoundaryExtension QuadraticComplementHomology QuadraticStratumHomology
open QuadraticComplementCoordinates ProductSphereKernel Submission
open PairNormalModel PairPathCoordinates PairConcreteLocalModel

variable {S : Finset (Fin 15)}

def oldPairInAll (F : Finset (MatchingIndex S)) (m : MatchingIndex S)
    (e : containedPairs S F) : containedPairs S (insert m F) :=
  ⟨e.val, containedPairs_mono (Finset.subset_insert m F) e.property⟩

def insertionProductEquiv (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    (containedPairs S (insert m F) → ↥LocalHomology) ≃+
      ((newPairs S F m → ↥LocalHomology) × (containedPairs S F → ↥LocalHomology)) :=
  (AddEquiv.arrowCongr (insertionEquiv hS F m hm) (AddEquiv.refl ↥LocalHomology)).trans
    { toEquiv := (Equiv.sumArrowEquivProdArrow (containedPairs S F)
        (newPairs S F m) ↥LocalHomology).trans (Equiv.prodComm _ _)
      map_add' := by intro f g; rfl }

def insertionProductIso (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    PairHomologyProduct S (insert m F) ≅
      NewHomologyProduct S F m ⊞ PairHomologyProduct S F :=
  (insertionProductEquiv hS F m hm).toAddCommGrpIso ≪≫
    (AddCommGrpCat.biprodIsoProd (NewHomologyProduct S F m) (PairHomologyProduct S F)).symm

theorem insertionProductIso_fst_apply (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (z : PairHomologyProduct S (insert m F))
    (e : newPairs S F m) :
    ((insertionProductIso hS F m hm).hom ≫ biprod.fst) z e =
      z (newPairInAll hS F m e) := by
  simp only [insertionProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AddCommGrpCat.biprodIsoProd_inv_comp_fst]
  rfl

theorem insertionProductIso_snd_apply (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (z : PairHomologyProduct S (insert m F))
    (e : containedPairs S F) :
    ((insertionProductIso hS F m hm).hom ≫ biprod.snd) z e = z (oldPairInAll F m e) := by
  simp only [insertionProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AddCommGrpCat.biprodIsoProd_inv_comp_snd]
  rfl

theorem coordinates_insertion (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    homologyCoordinates hS (insert m F) ≫ (insertionProductIso hS F m hm).hom =
      biprod.lift (newCoordinates hS F m)
        ((additionSequence hS F m hm).g ≫ homologyCoordinates hS F) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst]
    ext z e
    exact insertionProductIso_fst_apply hS F m hm (homologyCoordinates hS (insert m F) z) e
  · rw [Category.assoc, biprod.lift_snd, additionSequence_g hS F m hm]
    ext z e
    change ((insertionProductIso hS F m hm).hom ≫ biprod.snd)
        (homologyCoordinates hS (insert m F) z) e =
      homologyCoordinates hS F ((HgrpFunctor 12).map (oldInclusion F m) z) e
    rw [insertionProductIso_snd_apply hS F m hm]
    exact (homologyCoordinates_naturality hS (Finset.subset_insert m F) z e).symm

/-- The degree-twelve coordinate homomorphism is induced by the original
joint linear maps on every partial complement. -/
theorem homologyCoordinates_isIso (hS : S.Nonempty) (F : Finset (MatchingIndex S)) :
    IsIso (homologyCoordinates hS F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hsource : IsZero (Hgrp 12 (TopCat.of ↥(partialComplementSet S ∅))) :=
        (openAmbient_homology_zero 12 (by norm_num) (by norm_num)).of_iso
          ((HgrpFunctor 12).mapIso (TopCat.isoOfHomeo emptyPartialHomeomorph))
      have htarget : IsZero (PairHomologyProduct S ∅) := by
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        rw [PairHomologyProduct, containedPairs_empty hS]
        infer_instance
      exact hsource.isIso htarget _
  | @insert m F hm ih =>
      have := isIso_new_and_old hS F m hm
      have hi : IsIso ((biprod.lift (newCoordinates hS F m) (additionSequence hS F m hm).g) ≫
          (biprod.mapIso (Iso.refl _) (asIso (homologyCoordinates hS F))).hom) := inferInstance
      have heq : (biprod.lift (newCoordinates hS F m) (additionSequence hS F m hm).g) ≫
          (biprod.mapIso (Iso.refl _) (asIso (homologyCoordinates hS F))).hom =
        homologyCoordinates hS (insert m F) ≫ (insertionProductIso hS F m hm).hom := by
        rw [coordinates_insertion hS F m hm]
        apply biprod.hom_ext
        · simp
          exact biprod.lift_fst _ _
        · simp
          rw [← Category.assoc, biprod.lift_snd]
      rw [heq] at hi
      exact IsIso.of_isIso_comp_right _ (insertionProductIso hS F m hm).hom

def coordinateIso (hS : S.Nonempty) (F : Finset (MatchingIndex S)) :
    Hgrp 12 (TopCat.of ↥(partialComplementSet S F)) ≅ PairHomologyProduct S F := by
  have := homologyCoordinates_isIso hS F
  exact asIso (homologyCoordinates hS F)

def fullIndexEquiv (hS : S.Nonempty) :
    containedPairs S (Finset.univ : Finset (MatchingIndex S)) ≃ CriticalPairIndex S where
  toFun := Subtype.val
  invFun e := ⟨e, by rw [containedPairs_univ hS]; exact Finset.mem_univ e⟩
  left_inv _ := rfl
  right_inv _ := rfl

def originalPairCoordinatesIso (hS : S.Nonempty) :
    Hgrp 12 (TopCat.of (QuadComplement S)) ≅
      AddCommGrpCat.of (CriticalPairIndex S → ↥LocalHomology) :=
  (HgrpFunctor 12).mapIso (TopCat.isoOfHomeo fullComplementHomeomorph) ≪≫
    coordinateIso hS Finset.univ ≪≫
      (AddEquiv.arrowCongr (fullIndexEquiv hS) (AddEquiv.refl ↥LocalHomology)).toAddCommGrpIso

def originalPairMap (hS : S.Nonempty) (e : CriticalPairIndex S) :
    C(QuadComplement S, CommonComplement) :=
  (pairMap hS Finset.univ ((fullIndexEquiv hS).symm e)).comp
    ⟨fullComplementHomeomorph, fullComplementHomeomorph.continuous⟩

theorem originalPairMap_apply (hS : S.Nonempty) (e : CriticalPairIndex S)
    (x : QuadComplement S) :
    (originalPairMap hS e x).val = QuadraticMeridians.criticalTest e x.val := rfl

theorem originalPairCoordinatesIso_apply (hS : S.Nonempty)
    (z : Hgrp 12 (TopCat.of (QuadComplement S))) (e : CriticalPairIndex S) :
    (originalPairCoordinatesIso hS).hom z e =
      (HgrpFunctor 12).map (TopCat.ofHom (originalPairMap hS e)) z := by
  change ((HgrpFunctor 12).map (TopCat.isoOfHomeo fullComplementHomeomorph).hom ≫
    (HgrpFunctor 12).map (TopCat.ofHom
      (pairMap hS Finset.univ ((fullIndexEquiv hS).symm e)))) z = _
  rw [← Functor.map_comp]
  rfl

def originalTwelveIso (hS : S.Nonempty) :
    Hgrp 12 (TopCat.of (QuadComplement S)) ≅ AddCommGrpCat.of (CriticalPairIndex S → ℤ) :=
  originalPairCoordinatesIso hS ≪≫
    piIso (fun _ : CriticalPairIndex S => CommonPairHomology.commonHomologyIso coefficients)

end AkopyanResearch.QuadraticPairHomology
