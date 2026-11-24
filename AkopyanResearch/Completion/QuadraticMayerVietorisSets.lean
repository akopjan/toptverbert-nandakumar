module

public import AkopyanResearch.Completion.QuadraticDeletion
public import AkopyanResearch.Completion.PairPathCoordinates
public import Hatcher.Excision.BinaryCover

/-!
# The actual sets used in the quadratic arrangement Mayer--Vietoris induction

Critical pair strata use the same unordered-pair index as the concrete
homotopy-fiber target. No independent pair labels or additional factors are
introduced. Partial atom complements and their open covers remain subspaces
of the actual deleted ambient quadratic table space.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticMayerVietorisSets

open CategoryTheory
open AkopyanQuadratic QuadraticFlatRank QuadraticDeletion
open PairPathCoordinates PairOrbit

variable {S : Finset (Fin 15)}

noncomputable instance (S : Finset (Fin 15)) : Fintype (CriticalPairIndex S) :=
  Fintype.ofFinite _

/-- The closed stratum belonging to the exact critical-pair coordinate of
the concrete target. -/
def criticalPairSet (S : Finset (Fin 15)) (e : CriticalPairIndex S) :
    Set (OpenAmbient S) := {x | ∀ m ∈ e.val, x.val ∈ L_M S m}

/-- The actual linear pair flat, independent of the chosen enumeration. -/
def criticalFlat (e : CriticalPairIndex S) : Submodule ℝ (QuadSpace S) :=
  ⨅ m ∈ e.val, L_M S m

theorem criticalFlat_eq_inf (e : CriticalPairIndex S)
    (m n : MatchingIndex S) (he : e.val = {m.val, n.val}) :
    criticalFlat e = L_M S m.val ⊓ L_M S n.val := by
  ext x
  simp [criticalFlat, he]

theorem criticalPairSet_eq_subspace (e : CriticalPairIndex S) :
    criticalPairSet S e = {x : OpenAmbient S | x.val ∈ criticalFlat e} := by
  ext x
  simp [criticalPairSet, criticalFlat]

theorem criticalFlat_codim (hS : S.Nonempty) (e : CriticalPairIndex S) :
    Module.finrank ℝ (QuadSpace S ⧸ criticalFlat e) = 14 := by
  obtain ⟨m, n, hm, hn, hcommon, -, he⟩ := index_spec hS e
  rw [criticalFlat_eq_inf e ⟨m, hm⟩ ⟨n, hn⟩ he]
  exact (QuadraticPairRank.codim_pair_eq_fourteen_iff S hS m n hm hn).mpr hcommon

theorem criticalPairSet_eq_inter (e : CriticalPairIndex S)
    (m n : MatchingIndex S) (he : e.val = {m.val, n.val}) :
    criticalPairSet S e = atomSet S m ∩ atomSet S n := by
  ext x
  simp [criticalPairSet, he, atomSet]

theorem criticalPairSet_isClosed (hS : S.Nonempty) (e : CriticalPairIndex S) :
    IsClosed (criticalPairSet S e) := by
  obtain ⟨m, n, hm, hn, -, -, he⟩ := index_spec hS e
  rw [criticalPairSet_eq_inter e ⟨m, hm⟩ ⟨n, hn⟩ he]
  exact (isClosed_atomSet ⟨m, hm⟩).inter (isClosed_atomSet ⟨n, hn⟩)

/-- Distinct target pair indices have disjoint surviving strata. -/
theorem criticalPairSet_disjoint (hS : S.Nonempty) (e f : CriticalPairIndex S)
    (hef : e ≠ f) : Disjoint (criticalPairSet S e) (criticalPairSet S f) := by
  obtain ⟨m, n, hm, hn, -, hmn, he⟩ := index_spec hS e
  obtain ⟨k, l, hk, hl, -, hkl, hf⟩ := index_spec hS f
  rw [criticalPairSet_eq_inter e ⟨m, hm⟩ ⟨n, hn⟩ he,
    criticalPairSet_eq_inter f ⟨k, hk⟩ ⟨l, hl⟩ hf]
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hk' : k = m ∨ k = n := by
    by_contra h
    push Not at h
    exact no_three_atoms hS x ⟨m, hm⟩ ⟨n, hn⟩ ⟨k, hk⟩
      (fun h => hmn (congrArg Subtype.val h))
      (fun heq => h.1 (congrArg Subtype.val heq).symm)
      (fun heq => h.2 (congrArg Subtype.val heq).symm) hx.1 hx.2 hy.1
  have hl' : l = m ∨ l = n := by
    by_contra h
    push Not at h
    exact no_three_atoms hS x ⟨m, hm⟩ ⟨n, hn⟩ ⟨l, hl⟩
      (fun h => hmn (congrArg Subtype.val h))
      (fun heq => h.1 (congrArg Subtype.val heq).symm)
      (fun heq => h.2 (congrArg Subtype.val heq).symm) hx.1 hx.2 hy.2
  apply hef
  apply Subtype.ext
  rw [he, hf]
  rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
  · exact (hkl rfl).elim
  · rfl
  · exact Finset.pair_comm _ _
  · exact (hkl rfl).elim

/-- A finite partial complement, still inside the original deleted ambient
space. -/
def partialComplementSet (S : Finset (Fin 15)) (F : Finset (MatchingIndex S)) :
    Set (OpenAmbient S) := {x | ∀ m ∈ F, x ∉ atomSet S m}

theorem partialComplementSet_eq_compl_union (F : Finset (MatchingIndex S)) :
    partialComplementSet S F = (⋃ m ∈ F, atomSet S m)ᶜ := by
  ext x
  simp [partialComplementSet]

theorem partialComplementSet_isOpen (F : Finset (MatchingIndex S)) :
    IsOpen (partialComplementSet S F) := by
  rw [partialComplementSet_eq_compl_union]
  exact (isClosed_biUnion_finset (fun m _ => isClosed_atomSet m)).isOpen_compl

theorem partialComplementSet_insert (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    partialComplementSet S (insert m F) = partialComplementSet S F ∩ (atomSet S m)ᶜ := by
  classical
  ext x
  simp only [partialComplementSet, Set.mem_ofPred_eq, Finset.mem_insert,
    Set.mem_inter_iff, Set.mem_compl_iff]
  aesop

theorem partialComplementSet_union_single (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) :
    partialComplementSet S F ∪ (atomSet S m)ᶜ =
      (⋃ n ∈ F, atomSet S m ∩ atomSet S n)ᶜ := by
  ext x
  simp only [partialComplementSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
    Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro (hF | hm) ⟨n, hn, hxm, hxn⟩
    · exact hF n hn hxn
    · exact hm hxm
  · intro h
    by_cases hm : x ∈ atomSet S m
    · left
      intro n hn hxn
      exact h ⟨n, hn, hm, hxn⟩
    · exact Or.inr hm

/-- The new critical-pair coordinates appearing when `m` is added to `F`. -/
def newPairs (S : Finset (Fin 15)) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) : Finset (CriticalPairIndex S) := by
  classical
  exact Finset.univ.filter fun e => ∃ n ∈ F, e.val = {m.val, n.val}

theorem mem_newPairs (F : Finset (MatchingIndex S)) (m : MatchingIndex S)
    (e : CriticalPairIndex S) : e ∈ newPairs S F m ↔ ∃ n ∈ F, e.val = {m.val, n.val} := by
  classical
  simp [newPairs]

theorem newPairUnion_eq (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    (⋃ e ∈ newPairs S F m, criticalPairSet S e) =
      ⋃ n ∈ F, atomSet S m ∩ atomSet S n := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    obtain ⟨n, hn, heq⟩ := (mem_newPairs F m e).mp he
    exact ⟨n, hn, by simpa only [criticalPairSet_eq_inter e m n heq] using hx⟩
  · rintro ⟨n, hn, hx⟩
    have hmn : m ≠ n := fun h => hm (h ▸ hn)
    have hrank := critical_of_mem_two hS x m n hmn hx.1 hx.2
    have hcommon := (QuadraticPairRank.scalarRank_pair_eq_seven_iff hS m n).mp hrank
    obtain ⟨e, he⟩ := exists_index_of_matchings m.val n.val m.property n.property hcommon
    refine ⟨e, (mem_newPairs F m e).mpr ⟨n, hn, he⟩, ?_⟩
    simpa only [criticalPairSet_eq_inter e m n he] using hx

theorem actual_atom_cover_union (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    partialComplementSet S F ∪ (atomSet S m)ᶜ =
      (⋃ e ∈ newPairs S F m, criticalPairSet S e)ᶜ := by
  rw [partialComplementSet_union_single, newPairUnion_eq hS F m hm]

end AkopyanResearch.QuadraticMayerVietorisSets
