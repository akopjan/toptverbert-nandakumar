module

public import AkopyanResearch.Completion.QuadraticMayerVietorisSets
public import Mathlib.Logic.Equiv.Set

/-!
# Critical pairs in a finite partial atom complement

The actual target pair indices split into old pairs and the new pairs
incident to a newly added atom. This keeps the indexing in the homology
induction identical to the indexing of the original comparison target.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.QuadraticPairEnumeration

open AkopyanQuadratic QuadraticMayerVietorisSets PairPathCoordinates

variable {S : Finset (Fin 15)}

def containedPairs (S : Finset (Fin 15)) (F : Finset (MatchingIndex S)) :
    Finset (CriticalPairIndex S) := by
  classical
  exact Finset.univ.filter fun e => e.val ⊆ F.image Subtype.val

theorem mem_containedPairs (F : Finset (MatchingIndex S)) (e : CriticalPairIndex S) :
    e ∈ containedPairs S F ↔ e.val ⊆ F.image Subtype.val := by
  classical
  simp [containedPairs]

theorem matching_mem_image (F : Finset (MatchingIndex S)) (m : MatchingIndex S) :
    m.val ∈ F.image Subtype.val ↔ m ∈ F := by
  classical
  constructor
  · intro hm
    obtain ⟨n, hn, hnm⟩ := Finset.mem_image.mp hm
    have h : n = m := Subtype.ext hnm
    exact h ▸ hn
  · intro hm
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

theorem mem_containedPairs_iff (F : Finset (MatchingIndex S)) (e : CriticalPairIndex S)
    (m n : MatchingIndex S) (he : e.val = {m.val, n.val}) :
    e ∈ containedPairs S F ↔ m ∈ F ∧ n ∈ F := by
  classical
  rw [mem_containedPairs, he]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, matching_mem_image]

theorem containedPairs_mono {F G : Finset (MatchingIndex S)} (h : F ⊆ G) :
    containedPairs S F ⊆ containedPairs S G := by
  intro e he
  rw [mem_containedPairs] at he ⊢
  exact he.trans (Finset.image_subset_image h)

theorem containedPairs_empty (hS : S.Nonempty) : containedPairs S ∅ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨m, n, hm, hn, -, -, heq⟩ := index_spec hS e
  have h := (mem_containedPairs_iff ∅ e ⟨m, hm⟩ ⟨n, hn⟩ heq).mp he
  exact Finset.notMem_empty _ h.1

theorem containedPairs_insert (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) :
    containedPairs S (insert m F) = containedPairs S F ∪ newPairs S F m := by
  classical
  ext e
  rw [Finset.mem_union]
  constructor
  · intro he
    obtain ⟨a, b, ha, hb, -, hab, heq⟩ := index_spec hS e
    let p : MatchingIndex S := ⟨a, ha⟩
    let q : MatchingIndex S := ⟨b, hb⟩
    change e.val = {p.val, q.val} at heq
    obtain ⟨hp, hq⟩ := (mem_containedPairs_iff (insert m F) e p q heq).mp he
    rcases Finset.mem_insert.mp hp with hp | hp
    · right
      have hqF : q ∈ F := (Finset.mem_insert.mp hq).resolve_left (by
        intro hqm
        apply hab
        exact congrArg Subtype.val (hp.trans hqm.symm))
      apply (mem_newPairs F m e).mpr
      exact ⟨q, hqF, by simpa only [hp] using heq⟩
    · rcases Finset.mem_insert.mp hq with hq | hq
      · right
        apply (mem_newPairs F m e).mpr
        refine ⟨p, hp, ?_⟩
        rw [heq, ← hq]
        exact Finset.pair_comm _ _
      · exact Or.inl ((mem_containedPairs_iff F e p q heq).mpr ⟨hp, hq⟩)
  · rintro (he | he)
    · exact containedPairs_mono (Finset.subset_insert m F) he
    · obtain ⟨n, hn, heq⟩ := (mem_newPairs F m e).mp he
      exact (mem_containedPairs_iff (insert m F) e m n heq).mpr
        ⟨Finset.mem_insert_self m F, Finset.mem_insert_of_mem hn⟩

theorem containedPairs_disjoint_new (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    Disjoint (containedPairs S F) (newPairs S F m) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hnew
  obtain ⟨n, hn, heq⟩ := (mem_newPairs F m e).mp hnew
  exact hm ((mem_containedPairs_iff F e m n heq).mp he).1

def insertionEquiv (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (m : MatchingIndex S) (hm : m ∉ F) :
    containedPairs S (insert m F) ≃ containedPairs S F ⊕ newPairs S F m := by
  classical
  let e : containedPairs S (insert m F) ≃
      ↥((containedPairs S F : Set (CriticalPairIndex S)) ∪
        (newPairs S F m : Set (CriticalPairIndex S))) :=
    Equiv.subtypeEquivRight (fun e => by
      change e ∈ containedPairs S (insert m F) ↔
        e ∈ containedPairs S F ∨ e ∈ newPairs S F m
      rw [containedPairs_insert hS F m, Finset.mem_union])
  exact e.trans (Equiv.Set.union (Set.disjoint_left.mpr (fun _ hx hy =>
    Finset.disjoint_left.mp (containedPairs_disjoint_new F m hm) hx hy)))

theorem containedPairs_univ [Fintype (MatchingIndex S)] (hS : S.Nonempty) :
    containedPairs S Finset.univ = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro e
  obtain ⟨m, n, hm, hn, -, -, he⟩ := index_spec hS e
  exact (mem_containedPairs_iff Finset.univ e ⟨m, hm⟩ ⟨n, hn⟩ he).mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _⟩

end AkopyanResearch.QuadraticPairEnumeration
