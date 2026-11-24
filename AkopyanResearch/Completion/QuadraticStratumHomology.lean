module

public import AkopyanResearch.Completion.QuadraticDeletedPairs
public import AkopyanResearch.Completion.ArrangementHomology
public import AkopyanResearch.Completion.NormedLinearThom
public import AkopyanResearch.Completion.ComplementMayerVietoris
public import Submission.Homology.Point

/-!
# Integral homology of the actual deleted ambient and individual strata

The general-position connectivity theorem and the proved homotopy-to-homology
bridge supply the ambient and base vanishing. The genuine normal-pair and
excision calculations then compute the single-deletion and pair-deletion
groups. Every relative group is evaluated on the actual original quadratic
space pair.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace AkopyanResearch.QuadraticStratumHomology

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticFlatRank QuadraticDeletion QuadraticMayerVietorisSets
open QuadraticDeletedPairs ArrangementConnectivity ProductSphereKernel
open ComplementMayerVietoris Submission PairPathCoordinates

abbrev coefficients : AddCommGrpCat := AddCommGrpCat.of ℤ
abbrev relativeHomology (i : ℕ) (P : TopPair) : AddCommGrpCat :=
  (Hatcher.Relative.homologyFunctor coefficients i).obj P

variable {S : Finset (Fin 15)}

theorem isZero_homology_of_finrank {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type} [Fintype ι] (L : ι → Submodule ℝ E)
    (n k : ℕ) (hdim : ∀ j, Module.finrank ℝ (L j) + n + 2 ≤ Module.finrank ℝ E)
    (hk : k ≤ n) (hk0 : k ≠ 0) :
    IsZero (Hgrp k (TopCat.of (Complement L))) := by
  apply isZero_homology_complement L n k _ hk hk0
  intro j
  have hq := (L j).finrank_quotient_add_finrank
  have hj := hdim j
  omega

theorem openAmbient_homology_zero (k : ℕ) (hk : k ≤ 14) (hk0 : k ≠ 0) :
    IsZero (Hgrp k (TopCat.of (OpenAmbient S))) :=
  isZero_homology_complement (deletedFlat S) 14 k (fun j => deletedFlat_codim j) hk hk0

theorem atomBase_pathConnected (hS : S.Nonempty) (m : MatchingIndex S) :
    PathConnectedSpace (ExceptionalBase (L_M S m.val)) := by
  let : PathConnectedSpace (OpenAtom S m) := openAtom_pathConnected hS m
  exact (baseComplementHomeomorph (L_M S m.val)).surjective.pathConnectedSpace
    (baseComplementHomeomorph (L_M S m.val)).continuous

theorem atomBase_homology_zero (hS : S.Nonempty) (m : MatchingIndex S)
    (k : ℕ) (hk : k ≤ 4) (hk0 : k ≠ 0) :
    IsZero (Hgrp k (TopCat.of (ExceptionalBase (L_M S m.val)))) := by
  have hz : IsZero (Hgrp k (TopCat.of (OpenAtom S m))) :=
    isZero_homology_of_finrank _ 4 k
      (fun j => by simpa using deletedFlat_in_atom_codim hS m j) hk hk0
  exact hz.of_iso ((HgrpFunctor k).mapIso
    (TopCat.isoOfHomeo (baseComplementHomeomorph (L_M S m.val))).symm)

theorem deletedFlat_in_criticalFlat_finrank (hS : S.Nonempty)
    (e : CriticalPairIndex S) (j : DeletedIndex S) :
    Module.finrank ℝ ((deletedFlat S j).comap (criticalFlat e).subtype) + 4 ≤
      Module.finrank ℝ (criticalFlat e) := by
  obtain ⟨m, n, hm, hn, hcommon, -, he⟩ := index_spec hS e
  let a : MatchingIndex S := ⟨m, hm⟩
  let b : MatchingIndex S := ⟨n, hn⟩
  have hc : scalarRank {a, b} = 7 :=
    (QuadraticPairRank.scalarRank_pair_eq_seven_iff hS a b).mpr hcommon
  have hf : criticalFlat e = familyFlat {a, b} :=
    (criticalFlat_eq_inf e a b he).trans (familyFlat_pair a b).symm
  rw [hf]
  exact deletedFlat_in_critical_pair_codim hS a b hc j

theorem base_pathConnected_of_finrank (U : Submodule ℝ (QuadSpace S))
    (hdim : ∀ j : DeletedIndex S,
      Module.finrank ℝ ((deletedFlat S j).comap U.subtype) + 2 ≤ Module.finrank ℝ U) :
    PathConnectedSpace (ExceptionalBase U) := by
  have : PathConnectedSpace (Complement (E := ↥U)
      (fun j : DeletedIndex S => (deletedFlat S j).comap U.subtype)) := by
    apply pathConnectedSpace_complement
    intro j
    have h := hdim j
    omega
  exact (baseComplementHomeomorph U).surjective.pathConnectedSpace
    (baseComplementHomeomorph U).continuous

theorem base_homology_zero_of_finrank (U : Submodule ℝ (QuadSpace S))
    (n k : ℕ)
    (hdim : ∀ j : DeletedIndex S,
      Module.finrank ℝ ((deletedFlat S j).comap U.subtype) + n + 2 ≤ Module.finrank ℝ U)
    (hk : k ≤ n) (hk0 : k ≠ 0) :
    IsZero (Hgrp k (TopCat.of (ExceptionalBase U))) := by
  have hz : IsZero (Hgrp k (TopCat.of (Complement (E := ↥U)
      (fun j : DeletedIndex S => (deletedFlat S j).comap U.subtype)))) :=
    isZero_homology_of_finrank (E := ↥U) _ n k hdim hk hk0
  exact hz.of_iso ((HgrpFunctor k).mapIso
    (TopCat.isoOfHomeo (baseComplementHomeomorph U)).symm)

theorem criticalBase_pathConnected (hS : S.Nonempty) (e : CriticalPairIndex S) :
    PathConnectedSpace (ExceptionalBase (criticalFlat e)) := by
  apply base_pathConnected_of_finrank
  intro j
  have h := deletedFlat_in_criticalFlat_finrank hS e j
  omega

theorem criticalBase_homology_zero (hS : S.Nonempty) (e : CriticalPairIndex S)
    (k : ℕ) (hk : k ≤ 2) (hk0 : k ≠ 0) :
    IsZero (Hgrp k (TopCat.of (ExceptionalBase (criticalFlat e)))) := by
  exact base_homology_zero_of_finrank (criticalFlat e) 2 k
    (fun j => by have h := deletedFlat_in_criticalFlat_finrank hS e j; omega) hk hk0

def atomBaseZeroIso (hS : S.Nonempty) (m : MatchingIndex S) :
    Hgrp 0 (TopCat.of (ExceptionalBase (L_M S m.val))) ≅ coefficients := by
  let := atomBase_pathConnected hS m
  exact hgrpZeroIso _

def criticalBaseZeroIso (hS : S.Nonempty) (e : CriticalPairIndex S) :
    Hgrp 0 (TopCat.of (ExceptionalBase (criticalFlat e))) ≅ coefficients := by
  let := criticalBase_pathConnected hS e
  exact hgrpZeroIso _

def atomRelativeThomIso (hS : S.Nonempty) (m : MatchingIndex S) (i : ℕ) :
    relativeHomology (10 + i) (deletionPair (L_M S m.val)) ≅
      Hgrp i (TopCat.of (ExceptionalBase (L_M S m.val))) :=
  (Hatcher.Relative.homologyFunctor coefficients (10 + i)).mapIso
      (deletionPairIso (L_M S m.val)) ≪≫
    NormedLinearThom.relativeThomIso (QuadSpace S) (L_M S m.val) (deletedLocus S)
      isClosed_deletedLocus 10 (by norm_num) (codim_L_M_eq_ten S hS m.val m.property)
      coefficients i

def criticalRelativeThomIso (hS : S.Nonempty) (e : CriticalPairIndex S) (i : ℕ) :
    relativeHomology (14 + i) (deletionPair (criticalFlat e)) ≅
      Hgrp i (TopCat.of (ExceptionalBase (criticalFlat e))) :=
  (Hatcher.Relative.homologyFunctor coefficients (14 + i)).mapIso
      (deletionPairIso (criticalFlat e)) ≪≫
    NormedLinearThom.relativeThomIso (QuadSpace S) (criticalFlat e) (deletedLocus S)
      isClosed_deletedLocus 14 (by norm_num) (criticalFlat_codim hS e) coefficients i

theorem atomRelative_homology_zero (hS : S.Nonempty) (m : MatchingIndex S)
    (k : ℕ) (hk : k ≤ 14) (hk10 : k ≠ 10) :
    IsZero (relativeHomology k (deletionPair (L_M S m.val))) := by
  by_cases hlt : k < 10
  · exact (NormedLinearThom.isZero_relative_below_codim (QuadSpace S) (L_M S m.val)
      (deletedLocus S) isClosed_deletedLocus 10 (by norm_num)
      (codim_L_M_eq_ten S hS m.val m.property) coefficients k hlt).of_iso
        ((Hatcher.Relative.homologyFunctor coefficients k).mapIso
          (deletionPairIso (L_M S m.val)))
  · have hbase := atomBase_homology_zero hS m (k - 10) (by omega) (by omega)
    have hz := hbase.of_iso (atomRelativeThomIso hS m (k - 10))
    simpa only [Nat.add_sub_of_le (show 10 ≤ k by omega)] using hz

theorem criticalRelative_homology_zero (hS : S.Nonempty) (e : CriticalPairIndex S)
    (k : ℕ) (hk : k ≤ 16) (hk14 : k ≠ 14) :
    IsZero (relativeHomology k (deletionPair (criticalFlat e))) := by
  by_cases hlt : k < 14
  · exact (NormedLinearThom.isZero_relative_below_codim (QuadSpace S) (criticalFlat e)
      (deletedLocus S) isClosed_deletedLocus 14 (by norm_num) (criticalFlat_codim hS e)
      coefficients k hlt).of_iso
        ((Hatcher.Relative.homologyFunctor coefficients k).mapIso
          (deletionPairIso (criticalFlat e)))
  · have hbase := criticalBase_homology_zero hS e (k - 14) (by omega) (by omega)
    have hz := hbase.of_iso (criticalRelativeThomIso hS e (k - 14))
    simpa only [Nat.add_sub_of_le (show 14 ≤ k by omega)] using hz

theorem atomComplement_homology_zero (hS : S.Nonempty) (m : MatchingIndex S)
    (k : ℕ) (hk : k ≤ 13) (hk0 : k ≠ 0) (hk9 : k ≠ 9) :
    IsZero (Hgrp k (TopCat.of ↥((atomSet S m)ᶜ))) :=
  isZero_subspace_of_relative_and_ambient_zero (deletionPair (L_M S m.val)) coefficients k
    (atomRelative_homology_zero hS m (k + 1) (by omega) (by omega))
    (openAmbient_homology_zero k (by omega) hk0)

def atomComplementNineIso (hS : S.Nonempty) (m : MatchingIndex S) :
    Hgrp 9 (TopCat.of ↥((atomSet S m)ᶜ)) ≅ coefficients := by
  have := isIso_pairConnecting_of_ambient_zero (deletionPair (L_M S m.val)) coefficients 9
    (openAmbient_homology_zero 10 (by norm_num) (by norm_num))
    (openAmbient_homology_zero 9 (by norm_num) (by norm_num))
  exact (asIso (Hatcher.Relative.pairConnecting (deletionPair (L_M S m.val))
    coefficients 10 9 rfl)).symm ≪≫ atomRelativeThomIso hS m 0 ≪≫ atomBaseZeroIso hS m

end AkopyanResearch.QuadraticStratumHomology
