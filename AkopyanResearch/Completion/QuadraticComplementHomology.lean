module

public import AkopyanResearch.Completion.QuadraticStratumHomology
public import AkopyanResearch.Completion.DisjointComplementHomology
public import AkopyanResearch.Completion.OpenUnionMayerVietoris

/-!
# Low integral homology of the original quadratic arrangement complement

The proof uses the actual open cover obtained when one atom is added. Its
union is the complement of the new critical strata, which are disjoint in
the deleted ambient space. Thus ordinary Mayer--Vietoris and the single
linear-stratum calculation suffice; no arrangement homology formula is
assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticComplementHomology

open CategoryTheory CategoryTheory.Limits
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets QuadraticDeletedPairs
open QuadraticStratumHomology DisjointComplementHomology ProductSphereKernel Submission
open PairPathCoordinates

variable {S : Finset (Fin 15)}

instance matchingIndexFintype : Fintype (MatchingIndex S) := Fintype.ofFinite _

abbrev pairComplementSet (S : Finset (Fin 15)) (F : Finset (CriticalPairIndex S)) :
    Set (OpenAmbient S) :=
  complementSet (X := TopCat.of (OpenAmbient S)) (criticalPairSet S) F

/-- The degree-fourteen endpoint follows from the genuine relative group
in degree fifteen; it makes no assumption about `H₁₅` of the ambient space. -/
theorem pairComplement_homology_zero (hS : S.Nonempty)
    (F : Finset (CriticalPairIndex S)) (k : ℕ)
    (hk : k ≤ 14) (hk0 : k ≠ 0) (hk13 : k ≠ 13) :
    IsZero (Hgrp k (TopCat.of ↥(pairComplementSet S F))) := by
  apply isZero_finiteComplement_of_relative_zero (X := TopCat.of (OpenAmbient S))
    (criticalPairSet S) F coefficients k
    (fun e _ => criticalPairSet_isClosed hS e)
    (fun e _ f _ hef => criticalPairSet_disjoint hS e f hef)
    (openAmbient_homology_zero k hk hk0)
  intro e he
  exact (criticalRelative_homology_zero hS e (k + 1) (by omega) (by omega)).of_iso
    ((Hatcher.Relative.homologyFunctor coefficients (k + 1)).mapIso
      (criticalDeletionPairIso e))

def emptyPartialHomeomorph : ↥(partialComplementSet S ∅) ≃ₜ OpenAmbient S :=
  (Homeomorph.setCongr (by ext x; simp [partialComplementSet])).trans
    (Homeomorph.Set.univ (OpenAmbient S))

theorem atomCoverUnion_homology_zero (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) (m : MatchingIndex S) (hm : m ∉ F)
    (k : ℕ) (hk : k ≤ 14) (hk0 : k ≠ 0) (hk13 : k ≠ 13) :
    IsZero (Hgrp k
      (OpenUnionMayerVietoris.unionSpace (X := TopCat.of (OpenAmbient S))
        (partialComplementSet S F) (atomSet S m)ᶜ)) :=
  (pairComplement_homology_zero hS (newPairs S F m) k hk hk0 hk13).of_iso
    ((HgrpFunctor k).mapIso (TopCat.isoOfHomeo
      (Homeomorph.setCongr (actual_atom_cover_union hS F m hm))))

/-- Every finite partial atom complement has no positive homology through
degree thirteen except possibly in degrees nine and twelve. -/
theorem partialComplement_homology_zero (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) (k : ℕ)
    (hk : k ≤ 13) (hk0 : k ≠ 0) (hk9 : k ≠ 9) (hk12 : k ≠ 12) :
    IsZero (Hgrp k (TopCat.of ↥(partialComplementSet S F))) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact (openAmbient_homology_zero k (by omega) hk0).of_iso
        ((HgrpFunctor k).mapIso (TopCat.isoOfHomeo emptyPartialHomeomorph))
  | @insert m F hm ih =>
      have hU : IsZero (Hgrp (k + 1)
          (OpenUnionMayerVietoris.unionSpace (X := TopCat.of (OpenAmbient S))
            (partialComplementSet S F) (atomSet S m)ᶜ)) :=
        (pairComplement_homology_zero hS (newPairs S F m) (k + 1)
          (by omega) (by omega) (by omega)).of_iso
            ((HgrpFunctor (k + 1)).mapIso (TopCat.isoOfHomeo
              (Homeomorph.setCongr (actual_atom_cover_union hS F m hm))))
      have hz := OpenUnionMayerVietoris.isZero_intersection_of_zero_union
        (X := TopCat.of (OpenAmbient S))
        (partialComplementSet S F) (atomSet S m)ᶜ
        (partialComplementSet_isOpen F) (isClosed_atomSet m).isOpen_compl
        coefficients k hU ih (atomComplement_homology_zero hS m k hk hk0 hk9)
      exact hz.of_iso ((HgrpFunctor k).mapIso (TopCat.isoOfHomeo
        (Homeomorph.setCongr (partialComplementSet_insert F m))))

def fullComplementHomeomorph :
    QuadComplement S ≃ₜ ↥(partialComplementSet S Finset.univ) :=
  originalComplementHomeomorph.trans (Homeomorph.setCongr (by
    ext x
    change (∀ m : MatchingIndex S, x ∉ atomSet S m) ↔
      ∀ m ∈ (Finset.univ : Finset (MatchingIndex S)), x ∉ atomSet S m
    simp))

/-- The statement is evaluated on the original source of the comparison
map, not on a substituted complement. -/
theorem originalComplement_homology_zero (hS : S.Nonempty) (k : ℕ)
    (hk : k ≤ 13) (hk0 : k ≠ 0) (hk9 : k ≠ 9) (hk12 : k ≠ 12) :
    IsZero (Hgrp k (TopCat.of (QuadComplement S))) :=
  (partialComplement_homology_zero hS Finset.univ k hk hk0 hk9 hk12).of_iso
    ((HgrpFunctor k).mapIso (TopCat.isoOfHomeo fullComplementHomeomorph))

theorem originalComplement_thirteenth_zero (hS : S.Nonempty) :
    IsZero (Hgrp 13 (TopCat.of (QuadComplement S))) :=
  originalComplement_homology_zero hS 13 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end AkopyanResearch.QuadraticComplementHomology
