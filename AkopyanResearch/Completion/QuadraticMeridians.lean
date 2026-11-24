module

public import AkopyanResearch.Completion.LinearMeridian
public import AkopyanResearch.Completion.QuadraticStratumHomology
public import AkopyanResearch.Completion.PairEvaluationEquivalence
public import AkopyanResearch.Completion.RankOneSplit
public import AkopyanResearch.Completion.RepresentationSphereInvariants
public import AkopyanResearch.Completion.SingleCoordinateModel

/-!
# Actual primitive matching and critical-pair meridians

The linear tests are the original centered matching evaluations and the
original joint evaluation on the common-equality representation. The small
meridian construction applies after the actual closed deletion of higher
strata. Thus these precise maps, rather than unspecified generators, induce
split epimorphisms on integral homology.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticMeridians

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticDeletedPairs
open QuadraticMayerVietorisSets QuadraticStratumHomology
open MatchingSphereMap PairNormalModel PairPathCoordinates PairSourceProjections
open ProductSphereKernel

variable {S : Finset (Fin 15)}

def matchingTest (m : MatchingIndex S) : QuadSpace S →L[ℝ] Rep10 :=
  (matchingVectorLinear (SingleCoordinateModel.enumeration m)).toContinuousLinearMap

theorem matchingTest_zero_iff (m : MatchingIndex S) (x : QuadSpace S) :
    matchingTest m x = 0 ↔ x ∈ L_M S m.val := by
  change matchingVectorLinear (SingleCoordinateModel.enumeration m) x = 0 ↔ _
  rw [matchingVectorLinear_eq_zero_iff, SingleCoordinateModel.matchingWords_enumeration']

theorem matchingTest_surjective (hS : S.Nonempty) (m : MatchingIndex S) :
    Function.Surjective (matchingTest m) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hk : (matchingTest m).ker = L_M S m.val := by
    ext x
    exact matchingTest_zero_iff m x
  have he := (matchingTest m).toLinearMap.quotKerEquivRange.finrank_eq
  rw [hk, codim_L_M_eq_ten S hS m.val m.property, finrank_euclideanSpace_fin] at *
  exact he.symm

def criticalTest (e : CriticalPairIndex S) : QuadSpace S →L[ℝ] commonEquality :=
  PairEvaluationEquivalence.jointCommon (representative e)

theorem criticalTest_zero_iff (hS : S.Nonempty) (e : CriticalPairIndex S) (x : QuadSpace S) :
    criticalTest e x = 0 ↔ x ∈ criticalFlat e := by
  let ω := representative e
  let m : MatchingIndex S := ⟨matchingWords (firstVertex ∘ ω), matchingWords_sixMatching hS _⟩
  let n : MatchingIndex S := ⟨matchingWords (secondVertex ∘ ω), matchingWords_sixMatching hS _⟩
  have he : e.val = {m.val, n.val} := (representative_pairWords e).symm
  have hj : criticalTest e x = 0 ↔ jointTest ω x = 0 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [criticalFlat_eq_inf e m n he, ← ker_jointTest ω]
  exact hj

theorem criticalTest_surjective (hS : S.Nonempty) (e : CriticalPairIndex S) :
    Function.Surjective (criticalTest e) :=
  PairEvaluationEquivalence.jointCommon_surjective hS (representative e)
    (representative_critical e)

section Generic

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (U : Submodule ℝ (QuadSpace S)) (f : QuadSpace S →L[ℝ] F)
  (hker : ∀ x, f x = 0 ↔ x ∈ U)

def deletedComplementHomeomorph :
    (deletionPair U).snd ≃ₜ LinearMeridian.Complement f (deletedLocus S) where
  toFun x := ⟨x.val.val, (not_congr (hker x.val.val)).mpr x.property,
    (ambientHomeomorph x.val).property⟩
  invFun x := ⟨ambientHomeomorph.symm ⟨x.val, x.property.2⟩,
    (not_congr (hker x.val)).mp x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def deletedTestMap : C((deletionPair U).snd, PuncturedSpace.Space F) :=
  (LinearMeridian.map f (deletedLocus S)).comp
    ⟨deletedComplementHomeomorph U f hker, (deletedComplementHomeomorph U f hker).continuous⟩

theorem deletedTestMap_apply (x : (deletionPair U).snd) :
    (deletedTestMap U f hker x).val = f x.val.val := rfl

theorem deletedTestMap_splitEpi [FiniteDimensional ℝ F]
    (hf : Function.Surjective f) (hne : Nonempty (ExceptionalBase U)) (i : ℕ) :
    IsSplitEpi ((homologyFunctor coefficients i).map (TopCat.ofHom (deletedTestMap U f hker))) := by
  let a := Classical.choice hne
  exact LinearMeridian.homologyMap_splitEpi_of_homeomorph f (deletedLocus S) a.val.val
    ((hker _).mpr a.val.property) hf isClosed_deletedLocus a.property
    (deletedComplementHomeomorph U f hker) coefficients i

end Generic

def matchingMeridian (m : MatchingIndex S) :
    C((deletionPair (L_M S m.val)).snd, PuncturedSpace.Space Rep10) :=
  deletedTestMap (L_M S m.val) (matchingTest m) (matchingTest_zero_iff m)

theorem matchingMeridian_splitEpi (hS : S.Nonempty) (m : MatchingIndex S) (i : ℕ) :
    IsSplitEpi ((homologyFunctor coefficients i).map (TopCat.ofHom (matchingMeridian m))) :=
  deletedTestMap_splitEpi (L_M S m.val) (matchingTest m) (matchingTest_zero_iff m)
    (matchingTest_surjective hS m) (atomBase_pathConnected hS m).nonempty i

def criticalMeridian (hS : S.Nonempty) (e : CriticalPairIndex S) :
    C((deletionPair (criticalFlat e)).snd, PuncturedSpace.Space commonEquality) :=
  deletedTestMap (criticalFlat e) (criticalTest e) (criticalTest_zero_iff hS e)

theorem criticalMeridian_splitEpi (hS : S.Nonempty) (e : CriticalPairIndex S) (i : ℕ) :
    IsSplitEpi ((homologyFunctor coefficients i).map (TopCat.ofHom (criticalMeridian hS e))) :=
  deletedTestMap_splitEpi (criticalFlat e) (criticalTest e) (criticalTest_zero_iff hS e)
    (criticalTest_surjective hS e) (criticalBase_pathConnected hS e).nonempty i

def criticalSourceHomologyIso (hS : S.Nonempty) (e : CriticalPairIndex S) :
    homology coefficients 13 (deletionPair (criticalFlat e)).snd ≅ coefficients := by
  have := ComplementMayerVietoris.isIso_pairConnecting_of_ambient_zero
    (deletionPair (criticalFlat e)) coefficients 13
    (openAmbient_homology_zero 14 (by norm_num) (by norm_num))
    (openAmbient_homology_zero 13 (by norm_num) (by norm_num))
  exact (asIso (Hatcher.Relative.pairConnecting
    (deletionPair (criticalFlat e)) coefficients 14 13 rfl)).symm ≪≫
    criticalRelativeThomIso hS e 0 ≪≫ criticalBaseZeroIso hS e

def criticalTargetHomologyIso :
    homology coefficients 13 (TopCat.of (PuncturedSpace.Space commonEquality)) ≅ coefficients :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    (PuncturedSpace.sphereEquiv commonEquality 13 finrank_commonEquality) coefficients 13 ≪≫
    SphereHomology.diagonalIso coefficients 13 (by norm_num)

theorem criticalMeridian_isIso (hS : S.Nonempty) (e : CriticalPairIndex S) :
    IsIso ((homologyFunctor coefficients 13).map (TopCat.ofHom (criticalMeridian hS e))) := by
  have := criticalMeridian_splitEpi hS e 13
  exact RankOneSplit.isIso_of_splitEpi (criticalSourceHomologyIso hS e)
    criticalTargetHomologyIso _

def matchingSphereMap (m : MatchingIndex S) :
    C((deletionPair (L_M S m.val)).snd, OriginalJoinBridge.Target) :=
  (PuncturedSpace.normalization Rep10).comp (matchingMeridian m)

theorem matchingSphereMap_isIso (hS : S.Nonempty) (m : MatchingIndex S) :
    IsIso ((homologyFunctor coefficients 9).map (TopCat.ofHom (matchingSphereMap m))) := by
  have := matchingMeridian_splitEpi hS m 9
  have hn : IsIso ((homologyFunctor coefficients 9).map
      (TopCat.ofHom (PuncturedSpace.normalization Rep10))) :=
    (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      (PuncturedSpace.radialEquiv Rep10) coefficients 9).isIso_hom
  have hs : IsSplitEpi ((homologyFunctor coefficients 9).map
      (TopCat.ofHom (matchingSphereMap m))) := by
    change IsSplitEpi ((homologyFunctor coefficients 9).map
      (TopCat.ofHom (matchingMeridian m) ≫ TopCat.ofHom (PuncturedSpace.normalization Rep10)))
    rw [Functor.map_comp]
    infer_instance
  exact RankOneSplit.isIso_of_splitEpi (atomComplementNineIso hS m)
    (RepresentationSphereInvariants.singleHomologyIso coefficients) _

end AkopyanResearch.QuadraticMeridians
