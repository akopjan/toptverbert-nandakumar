module

public import AkopyanResearch.Completion.QuadraticPairEnumeration
public import AkopyanResearch.Completion.QuadraticMeridians
public import AkopyanResearch.Completion.CommonPairHomology

/-!
# Actual pair-coordinate maps on partial quadratic complements

Each contained critical pair is evaluated by its original joint centered
test. The maps take values in the original common-equality complement and
commute with the inclusions between partial complements.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticPairCoordinates

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets QuadraticPairEnumeration
open QuadraticMeridians QuadraticStratumHomology
open PairPathCoordinates PairSourceProjections PairNormalModel PairConcreteLocalModel
open MatchingSphereMap
open ProductSphereKernel Submission

variable {S : Finset (Fin 15)}

def firstAtom (hS : S.Nonempty) (e : CriticalPairIndex S) : MatchingIndex S :=
  ⟨matchingWords (firstVertex ∘ representative e), matchingWords_sixMatching hS _⟩

def secondAtom (hS : S.Nonempty) (e : CriticalPairIndex S) : MatchingIndex S :=
  ⟨matchingWords (secondVertex ∘ representative e), matchingWords_sixMatching hS _⟩

def testAtom (hS : S.Nonempty) (e : CriticalPairIndex S) : Bool → MatchingIndex S
  | false => firstAtom hS e
  | true => secondAtom hS e

theorem words_pair (hS : S.Nonempty) (e : CriticalPairIndex S) :
    e.val = {(firstAtom hS e).val, (secondAtom hS e).val} :=
  (representative_pairWords e).symm

theorem firstAtom_ne_secondAtom (hS : S.Nonempty) (e : CriticalPairIndex S) :
    firstAtom hS e ≠ secondAtom hS e := by
  intro he
  have hc : ((firstAtom hS e).val ∩ (secondAtom hS e).val).card = 4 :=
    representative_critical e
  rw [congrArg Subtype.val he, Finset.inter_self, (secondAtom hS e).property.1] at hc
  omega

theorem test_zero_iff (hS : S.Nonempty) (e : CriticalPairIndex S) (b : Bool)
    (x : QuadSpace S) :
    CommonPairHomology.test b (criticalTest e x) = 0 ↔ x ∈ L_M S (testAtom hS e b).val := by
  cases b
  · exact matchingVectorLinear_eq_zero_iff (firstVertex ∘ representative e) x
  · exact matchingVectorLinear_eq_zero_iff (secondVertex ∘ representative e) x

theorem pairMap_safe (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (e : containedPairs S F) (x : ↥(partialComplementSet S F)) :
    (criticalTest e.val x.val.val).val.1 ≠ 0 ∧
      (criticalTest e.val x.val.val).val.2 ≠ 0 := by
  obtain ⟨ha, hb⟩ := (mem_containedPairs_iff F e.val (firstAtom hS e.val)
    (secondAtom hS e.val) (words_pair hS e.val)).mp e.property
  exact (PairEvaluationEquivalence.jointCommon_mem_safe_iff (representative e.val)
    x.val.val).mpr ⟨x.property (firstAtom hS e.val) ha,
      x.property (secondAtom hS e.val) hb⟩

def pairMap (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (e : containedPairs S F) : C(↥(partialComplementSet S F), CommonComplement) :=
  ⟨fun x => ⟨criticalTest e.val x.val.val, pairMap_safe hS F e x⟩,
    ((criticalTest e.val).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

theorem pairMap_apply (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (e : containedPairs S F) (x : ↥(partialComplementSet S F)) :
    (pairMap hS F e x).val = criticalTest e.val x.val.val := rfl

def partialInclusion {F G : Finset (MatchingIndex S)} (h : F ⊆ G) :
    TopCat.of ↥(partialComplementSet S G) ⟶ TopCat.of ↥(partialComplementSet S F) :=
  TopCat.ofHom (ContinuousMap.inclusion (fun _ hx m hm => hx m (h hm)))

theorem pairMap_naturality (hS : S.Nonempty) {F G : Finset (MatchingIndex S)}
    (h : F ⊆ G) (e : containedPairs S F) :
    partialInclusion h ≫ TopCat.ofHom (pairMap hS F e) =
      TopCat.ofHom (pairMap hS G ⟨e.val, containedPairs_mono h e.property⟩) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

abbrev LocalHomology : AddCommGrpCat := Hgrp 12 (TopCat.of CommonComplement)
abbrev PairHomologyProduct (S : Finset (Fin 15)) (F : Finset (MatchingIndex S)) : AddCommGrpCat :=
  AddCommGrpCat.of (containedPairs S F → ↥LocalHomology)

def homologyCoordinates (hS : S.Nonempty) (F : Finset (MatchingIndex S)) :
    Hgrp 12 (TopCat.of ↥(partialComplementSet S F)) ⟶ PairHomologyProduct S F :=
  AddCommGrpCat.ofHom
    { toFun := fun z e => (HgrpFunctor 12).map (TopCat.ofHom (pairMap hS F e)) z
      map_zero' := by funext e; exact map_zero _
      map_add' := by intro x y; funext e; exact map_add _ _ _ }

theorem homologyCoordinates_naturality (hS : S.Nonempty)
    {F G : Finset (MatchingIndex S)} (h : F ⊆ G)
    (z : Hgrp 12 (TopCat.of ↥(partialComplementSet S G))) (e : containedPairs S F) :
    homologyCoordinates hS F ((HgrpFunctor 12).map (partialInclusion h) z) e =
      homologyCoordinates hS G z ⟨e.val, containedPairs_mono h e.property⟩ := by
  change ((HgrpFunctor 12).map (partialInclusion h) ≫
    (HgrpFunctor 12).map (TopCat.ofHom (pairMap hS F e))) z = _
  rw [← Functor.map_comp, pairMap_naturality]
  rfl

theorem newPair_sides (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    (firstAtom hS e.val = m ∧ secondAtom hS e.val ∈ F) ∨
      (firstAtom hS e.val ∈ F ∧ secondAtom hS e.val = m) := by
  classical
  have he : e.val ∈ containedPairs S (insert m F) := by
    rw [containedPairs_insert hS F m]
    exact Finset.mem_union.mpr (Or.inr e.property)
  obtain ⟨ha, hb⟩ := (mem_containedPairs_iff (insert m F) e.val (firstAtom hS e.val)
    (secondAtom hS e.val) (words_pair hS e.val)).mp he
  rcases Finset.mem_insert.mp ha with ha | ha <;>
    rcases Finset.mem_insert.mp hb with hb | hb
  · exact (firstAtom_ne_secondAtom hS e.val (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (Finset.disjoint_left.mp (containedPairs_disjoint_new F m hm)
      ((mem_containedPairs_iff F e.val (firstAtom hS e.val) (secondAtom hS e.val)
        (words_pair hS e.val)).mpr ⟨ha, hb⟩) e.property).elim

def newPairInAll (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (e : newPairs S F m) : containedPairs S (insert m F) :=
  ⟨e.val, by rw [containedPairs_insert hS F m]; exact Finset.mem_union.mpr (Or.inr e.property)⟩

def oldSide (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (e : newPairs S F m) : Bool := by
  classical
  exact if firstAtom hS e.val = m then true else false

theorem oldSide_mem (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    testAtom hS e.val (oldSide hS F m e) ∈ F := by
  classical
  rcases newPair_sides hS F m hm e with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa [oldSide, ha, testAtom] using hb
  · have hne : firstAtom hS e.val ≠ m := fun h => hm (h ▸ ha)
    simpa [oldSide, hne, testAtom] using ha

theorem newSide_eq (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) (e : newPairs S F m) :
    testAtom hS e.val (!(oldSide hS F m e)) = m := by
  classical
  rcases newPair_sides hS F m hm e with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [oldSide, ha, testAtom]
  · have hne : firstAtom hS e.val ≠ m := fun h => hm (h ▸ ha)
    simpa [oldSide, hne, testAtom] using hb

end AkopyanResearch.QuadraticPairCoordinates
