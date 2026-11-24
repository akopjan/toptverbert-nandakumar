module

public import AkopyanResearch.Completion.QuadraticPairRank
public import AkopyanResearch.Completion.ArrangementConnectivity

/-!
# Deleting the higher strata of the actual quadratic arrangement

Delete every flat of scalar rank at least eight. The ambient complement has
vanishing homotopy groups through degree fourteen; each remaining atom through
degree four; and each remaining critical pair stratum through degree two.
These statements concern the actual spaces, not assumed connectivity data.

This deletion leaves only the codimension-ten atoms and their codimension-
fourteen pair intersections. In particular no point of the remaining ambient
space lies in three distinct atoms.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticDeletion

open AkopyanQuadratic QuadraticFlatRank ArrangementConnectivity
open Module
open scoped Topology.Homotopy

variable {S : Finset (Fin 15)}

/-- The finite index set of the higher flats that are removed. -/
abbrev DeletedIndex (S : Finset (Fin 15)) :=
  {F : Finset (MatchingIndex S) // 8 ≤ scalarRank F}

noncomputable instance (S : Finset (Fin 15)) : Fintype (DeletedIndex S) :=
  Fintype.ofFinite _

/-- A deleted flat in the original quadratic table space. -/
abbrev deletedFlat (S : Finset (Fin 15)) (j : DeletedIndex S) :
    Submodule ℝ (QuadSpace S) := familyFlat j.1

/-- The ambient vector space after deleting all higher flats. -/
abbrev OpenAmbient (S : Finset (Fin 15)) := Complement (deletedFlat S)

/-- The surviving part of one atom, expressed as a linear-arrangement complement. -/
abbrev OpenAtom (S : Finset (Fin 15)) (m : MatchingIndex S) :=
  Complement (E := ↥(L_M S m.1))
    (fun j : DeletedIndex S => (deletedFlat S j).comap (L_M S m.1).subtype)

/-- The surviving part of a pair flat. Its connectivity is asserted only for
critical pairs of scalar rank seven. -/
abbrev OpenPair (S : Finset (Fin 15)) (m n : MatchingIndex S) :=
  Complement (E := ↥(familyFlat {m, n})) (fun j : DeletedIndex S =>
    (deletedFlat S j).comap (familyFlat {m, n}).subtype)

theorem familyFlat_union (F G : Finset (MatchingIndex S)) :
    familyFlat (F ∪ G) = familyFlat F ⊓ familyFlat G := by
  classical
  ext x
  simp only [familyFlat, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, Finset.mem_union, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩
  · rintro ⟨hF, hG⟩ m (hm | hm)
    · exact hF m hm
    · exact hG m hm

/-- Codimension inside a linear subspace is ambient codimension minus the
codimension of that subspace. This form avoids subtraction. -/
theorem codim_comap_subtype_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (U V : Submodule ℝ E) :
    finrank ℝ (U ⧸ V.comap U.subtype) + finrank ℝ (E ⧸ U) =
      finrank ℝ (E ⧸ (U ⊓ V)) := by
  let e : ↥(V.comap U.subtype) ≃ₗ[ℝ] ↥(U ⊓ V) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h₁ := (V.comap U.subtype).finrank_quotient_add_finrank
  have h₂ := U.finrank_quotient_add_finrank
  have h₃ := (U ⊓ V).finrank_quotient_add_finrank
  have he := e.finrank_eq
  omega

theorem finrank_comap_subtype_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (U V : Submodule ℝ E) :
    finrank ℝ (V.comap U.subtype) = finrank ℝ ↥(U ⊓ V) := by
  let e : ↥(V.comap U.subtype) ≃ₗ[ℝ] ↥(U ⊓ V) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq

theorem pi_vanish_of_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ E) (n : ℕ)
    (hdim : ∀ j, finrank ℝ (L j) + n + 1 < finrank ℝ E)
    (b : Complement L) : Subsingleton (HomotopyGroup.Pi n (Complement L) b) := by
  exact subsingleton_homotopyGroup_of_codim L n (fun j => by
    have hq := (L j).finrank_quotient_add_finrank
    have hj := hdim j
    omega) b

theorem deletedFlat_codim (j : DeletedIndex S) :
    16 ≤ finrank ℝ (QuadSpace S ⧸ deletedFlat S j) := by
  rw [codimension_familyFlat]
  have h := j.2
  omega

theorem deletedFlat_in_atom_codim (hS : S.Nonempty)
    (m : MatchingIndex S) (j : DeletedIndex S) :
    finrank ℝ ((deletedFlat S j).comap (L_M S m.1).subtype) + 6 ≤
      finrank ℝ (L_M S m.1) := by
  rw [finrank_comap_subtype_eq]
  have h := (L_M S m.1).finrank_quotient_add_finrank
  rw [codim_L_M_eq_ten S hS m.1 m.2] at h
  have hq := (L_M S m.1 ⊓ deletedFlat S j).finrank_quotient_add_finrank
  have hmono := codimension_antitone
    (show L_M S m.1 ⊓ deletedFlat S j ≤ deletedFlat S j from inf_le_right)
  have hdel := deletedFlat_codim j
  omega

theorem critical_pair_inter_deleted_codim (hS : S.Nonempty)
    (m n : MatchingIndex S) (hcrit : scalarRank {m, n} = 7)
    (j : DeletedIndex S) :
    18 ≤ finrank ℝ (QuadSpace S ⧸ (familyFlat {m, n} ⊓ deletedFlat S j)) := by
  classical
  have hlarge : 9 ≤ scalarRank ({m, n} ∪ j.1) := by
    by_contra hsmall
    have hlt : scalarRank ({m, n} ∪ j.1) < 9 := by omega
    have hle : familyFlat ({m, n} ∪ j.1) ≤ familyFlat {m, n} := by
      rw [familyFlat_union]
      exact inf_le_left
    have heq := low_rank_nonatomic_comparable_eq hS _ _ hle hlt (by omega)
    have hpair : familyFlat {m, n} ≤ deletedFlat S j := by
      rw [← heq, familyFlat_union]
      exact inf_le_right
    have hmono := codimension_antitone hpair
    rw [codimension_familyFlat, codimension_familyFlat, hcrit] at hmono
    have hj := j.2
    omega
  rw [← familyFlat_union, codimension_familyFlat]
  omega

theorem deletedFlat_in_critical_pair_codim (hS : S.Nonempty)
    (m n : MatchingIndex S) (hcrit : scalarRank {m, n} = 7)
    (j : DeletedIndex S) :
    finrank ℝ ((deletedFlat S j).comap (familyFlat {m, n}).subtype) + 4 ≤
      finrank ℝ (familyFlat {m, n}) := by
  rw [finrank_comap_subtype_eq]
  have h := (familyFlat {m, n}).finrank_quotient_add_finrank
  rw [codimension_familyFlat, hcrit] at h
  have hq := (familyFlat {m, n} ⊓ deletedFlat S j).finrank_quotient_add_finrank
  have hlarge := critical_pair_inter_deleted_codim hS m n hcrit j
  omega

theorem openAmbient_pi_vanish (n : ℕ) (hn : n ≤ 14) (b : OpenAmbient S) :
    Subsingleton (HomotopyGroup.Pi n (OpenAmbient S) b) := by
  exact subsingleton_homotopyGroup_of_codim (deletedFlat S) n
    (fun j => by have h := deletedFlat_codim j; omega) b

theorem openAtom_pi_vanish (hS : S.Nonempty) (m : MatchingIndex S)
    (n : ℕ) (hn : n ≤ 4) (b : OpenAtom S m) :
    Subsingleton (HomotopyGroup.Pi n (OpenAtom S m) b) := by
  exact pi_vanish_of_finrank (E := ↥(L_M S m.1)) _ n
    (fun j => by have h := deletedFlat_in_atom_codim hS m j; omega) b

theorem openPair_pi_vanish (hS : S.Nonempty) (m k : MatchingIndex S)
    (hcrit : scalarRank {m, k} = 7) (n : ℕ) (hn : n ≤ 2)
    (b : OpenPair S m k) :
    Subsingleton (HomotopyGroup.Pi n (OpenPair S m k) b) := by
  exact pi_vanish_of_finrank (E := ↥(familyFlat {m, k})) _ n
    (fun j => by have h := deletedFlat_in_critical_pair_codim hS m k hcrit j; omega) b

theorem openAmbient_pathConnected : PathConnectedSpace (OpenAmbient S) := by
  apply pathConnectedSpace_complement
  intro j
  have h := deletedFlat_codim j
  have hq := (deletedFlat S j).finrank_quotient_add_finrank
  omega

theorem openAtom_pathConnected (hS : S.Nonempty) (m : MatchingIndex S) :
    PathConnectedSpace (OpenAtom S m) := by
  apply pathConnectedSpace_complement
  intro j
  have h := deletedFlat_in_atom_codim hS m j
  omega

theorem openPair_pathConnected (hS : S.Nonempty) (m n : MatchingIndex S)
    (hcrit : scalarRank {m, n} = 7) : PathConnectedSpace (OpenPair S m n) := by
  apply pathConnectedSpace_complement
  intro j
  have h := deletedFlat_in_critical_pair_codim hS m n hcrit j
  omega

/-- The deleted locus is a finite union of actual matching flats. -/
def deletedLocus (S : Finset (Fin 15)) : Set (QuadSpace S) :=
  ⋃ j : DeletedIndex S, (deletedFlat S j : Set (QuadSpace S))

theorem isClosed_deletedLocus : IsClosed (deletedLocus S) :=
  isClosed_iUnion_of_finite fun j => (deletedFlat S j).closed_of_finiteDimensional

theorem deletedIndex_nonempty_family (j : DeletedIndex S) : j.1.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hj := j.2
  rw [he, scalarRank_empty] at hj
  omega

/-- No point of the original complement is deleted. -/
theorem deletedLocus_subset_union_atoms :
    deletedLocus S ⊆ ⋃ m : MatchingIndex S, (L_M S m.1 : Set (QuadSpace S)) := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨m, hm⟩ := deletedIndex_nonempty_family j
  exact Set.mem_iUnion.mpr ⟨m, familyFlat_le_matching hm hj⟩

/-- A surviving atom as a closed subset of the actual remaining ambient space. -/
def atomSet (S : Finset (Fin 15)) (m : MatchingIndex S) : Set (OpenAmbient S) :=
  {x | x.1 ∈ L_M S m.1}

theorem isClosed_atomSet (m : MatchingIndex S) : IsClosed (atomSet S m) :=
  (L_M S m.1).closed_of_finiteDimensional.preimage continuous_subtype_val

/-- The genuine complement of all surviving atoms in the remaining ambient space. -/
abbrev RemainingComplement (S : Finset (Fin 15)) :=
  {x : OpenAmbient S // ∀ m : MatchingIndex S, x ∉ atomSet S m}

theorem remainingComplement_set_eq :
    {x : OpenAmbient S | ∀ m : MatchingIndex S, x ∉ atomSet S m} =
      (⋃ m : MatchingIndex S, atomSet S m)ᶜ := by
  ext x
  simp

/-- Removing the higher strata from the ambient space leaves the original
quadratic complement unchanged, with its original topology. -/
def originalComplementHomeomorph : QuadComplement S ≃ₜ RemainingComplement S where
  toFun x := ⟨⟨x.1, fun j hj => by
    obtain ⟨m, hm⟩ := deletedIndex_nonempty_family j
    exact x.2 m.1 m.2 (familyFlat_le_matching hm hj)⟩,
    fun m hm => x.2 m.1 m.2 hm⟩
  invFun x := ⟨x.1.1, fun m hm hmem => x.2 ⟨m, hm⟩ hmem⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Restricting the deleted linear arrangement inside a subspace gives exactly
the surviving part of that subspace in `OpenAmbient`. -/
def restrictedComplementHomeomorph (U : Submodule ℝ (QuadSpace S)) :
    Complement (E := ↥U) (fun j : DeletedIndex S => (deletedFlat S j).comap U.subtype) ≃ₜ
      {x : OpenAmbient S // x.1 ∈ U} where
  toFun x := ⟨⟨x.1.1, fun j hj => x.2 j hj⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, fun j hj => x.1.2 j hj⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def openAtomHomeomorph (m : MatchingIndex S) :
    OpenAtom S m ≃ₜ ↥(atomSet S m) := restrictedComplementHomeomorph (L_M S m.1)

def openPairHomeomorph (m n : MatchingIndex S) :
    OpenPair S m n ≃ₜ ↥(atomSet S m ∩ atomSet S n) := by
  have hset : {x : OpenAmbient S | x.1 ∈ familyFlat {m, n}} =
      atomSet S m ∩ atomSet S n := by
    ext x
    simp [familyFlat_pair, atomSet]
  exact (restrictedComplementHomeomorph (familyFlat {m, n})).trans
    (Homeomorph.setCongr hset)

theorem scalarRank_le_seven_of_mem (x : OpenAmbient S)
    (F : Finset (MatchingIndex S)) (hF : x.1 ∈ familyFlat F) : scalarRank F ≤ 7 := by
  by_contra h
  have h8 : 8 ≤ scalarRank F := by omega
  exact x.2 ⟨F, h8⟩ hF

/-- Any two different surviving atoms meet only in a critical pair stratum. -/
theorem critical_of_mem_two (hS : S.Nonempty) (x : OpenAmbient S)
    (m n : MatchingIndex S) (hne : m ≠ n)
    (hm : x ∈ atomSet S m) (hn : x ∈ atomSet S n) : scalarRank {m, n} = 7 := by
  have hmem : x.1 ∈ familyFlat {m, n} := by
    rw [familyFlat_pair]
    exact ⟨hm, hn⟩
  have hupper := scalarRank_le_seven_of_mem x {m, n} hmem
  have hlower := codim_L_M_inf_two_ge_fourteen S hS m.1 n.1 m.2 n.2
    (fun h => hne (Subtype.ext h))
  rw [← familyFlat_pair, codimension_familyFlat] at hlower
  omega

theorem no_three_atoms (hS : S.Nonempty) (x : OpenAmbient S)
    (m n k : MatchingIndex S) (hmn : m ≠ n) (hmk : m ≠ k) (hnk : n ≠ k)
    (hm : x ∈ atomSet S m) (hn : x ∈ atomSet S n) (hk : x ∈ atomSet S k) : False := by
  classical
  have hmem : x.1 ∈ familyFlat {m, n, k} := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hm
    · exact hn
    · exact hk
  have hrank := scalarRank_le_seven_of_mem x {m, n, k} hmem
  have hcard := card_generators_le_two hS {m, n, k} (by omega)
  have hthree : ({m, n, k} : Finset (MatchingIndex S)).card = 3 := by
    simp [hmn, hmk, hnk]
  omega

theorem noncritical_atoms_disjoint (hS : S.Nonempty)
    (m n : MatchingIndex S) (hne : m ≠ n) (hcrit : scalarRank {m, n} ≠ 7) :
    Disjoint (atomSet S m) (atomSet S n) := by
  rw [Set.disjoint_left]
  intro x hm hn
  exact hcrit (critical_of_mem_two hS x m n hne hm hn)

/-- Every surviving pair stratum is disjoint from each other atom. -/
theorem pair_disjoint_other_atom (hS : S.Nonempty)
    (m n k : MatchingIndex S) (hmn : m ≠ n) (hmk : m ≠ k) (hnk : n ≠ k) :
    Disjoint (atomSet S m ∩ atomSet S n) (atomSet S k) := by
  rw [Set.disjoint_left]
  intro x hx hk
  exact no_three_atoms hS x m n k hmn hmk hnk hx.1 hx.2 hk

end AkopyanResearch.QuadraticDeletion
