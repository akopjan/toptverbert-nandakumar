module

public import AkopyanResearch.Completion.MatchingSphereMap

/-!
# Matching intersections represented by the actual pair source

A mixed family of actual pair states has exactly four common matching words.
A pure family represents one matching twice. These statements identify the
critical pairs indexed by the concrete comparison target.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairIntersection

open scoped Classical
open OriginalJoinBridge PairSphereAction PairSourceProjections MatchingSphereMap

theorem word_eq_iff_of_mixed {S : Finset (Fin 15)} (ω : S → PairState)
    (h0 : ∃ c, (ω c).2 = false) (h1 : ∃ c, (ω c).2 = true)
    (i j : Fin 6) :
    matchingWord (firstVertex ∘ ω) i = matchingWord (secondVertex ∘ ω) j ↔
      i = j ∧ i.val < 4 := by
  constructor
  · intro he
    obtain ⟨c0, hc0⟩ := h0
    obtain ⟨c1, hc1⟩ := h1
    have hij : i = j := (ω c0).1.injective (by
      simpa [matchingWord, firstVertex, secondVertex, hc0, blockPerm,
        liftPerm4_one] using congrFun he c0)
    have ht : i = swap45 j := (ω c1).1.injective (by
      simpa [matchingWord, firstVertex, secondVertex, hc1, blockPerm,
        liftPerm4_one] using congrFun he c1)
    refine ⟨hij, ?_⟩
    subst j
    fin_cases i <;> norm_num [swap45] at *
  · rintro ⟨hij, hi⟩
    subst j
    let k : Fin 4 := ⟨i.val, hi⟩
    have hk : k.castAdd 2 = i := rfl
    rw [← hk]
    funext c
    simp [matchingWord, firstVertex, secondVertex, blockPerm_castAdd]

def commonWords {S : Finset (Fin 15)} (ω : S → PairState) : Finset (S → Fin 6) :=
  Finset.univ.image (fun i : Fin 4 => matchingWord (firstVertex ∘ ω) (i.castAdd 2))

theorem intersection_of_mixed {S : Finset (Fin 15)} (ω : S → PairState)
    (h0 : ∃ c, (ω c).2 = false) (h1 : ∃ c, (ω c).2 = true) :
    matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω) =
      commonWords ω := by
  ext w
  constructor
  · intro hw
    obtain ⟨hm, hn⟩ := Finset.mem_inter.mp hw
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hn
    have hij := (word_eq_iff_of_mixed ω h0 h1 i j).mp (hi.trans hj.symm)
    apply Finset.mem_image.mpr
    refine ⟨⟨i.val, hij.2⟩, Finset.mem_univ _, ?_⟩
    exact hi
  · intro hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨i.castAdd 2, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_image.mpr
      refine ⟨i.castAdd 2, Finset.mem_univ _, ?_⟩
      exact ((word_eq_iff_of_mixed ω h0 h1 _ _).mpr ⟨rfl, i.isLt⟩).symm

theorem intersection_card_of_mixed {S : Finset (Fin 15)} (ω : S → PairState)
    (h0 : ∃ c, (ω c).2 = false) (h1 : ∃ c, (ω c).2 = true) :
    (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4 := by
  rw [intersection_of_mixed ω h0 h1, commonWords]
  have hinj : Function.Injective
      (fun i : Fin 4 => matchingWord (firstVertex ∘ ω) (i.castAdd 2)) := by
    intro i j he
    obtain ⟨c, hc⟩ := h0
    have hij := (ω c).1.injective (congrFun he c)
    exact Fin.ext (congrArg (fun k : Fin 6 => k.val) hij)
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem matchingWords_eq_of_pure {S : Finset (Fin 15)} (ω : S → PairState)
    (b : Bool) (hb : ∀ c, (ω c).2 = b) :
    matchingWords (firstVertex ∘ ω) = matchingWords (secondVertex ∘ ω) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_image.mpr
    refine ⟨(blockPerm 1 b)⁻¹ j, Finset.mem_univ _, ?_⟩
    funext c
    simp [matchingWord, firstVertex, secondVertex, hb c]
  · intro hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_image.mpr
    refine ⟨blockPerm 1 b j, Finset.mem_univ _, ?_⟩
    funext c
    simp [matchingWord, firstVertex, secondVertex, hb c]


/-- Every critical pair uses both phases of the actual pair source. -/
theorem mixed_of_intersection_card_four {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) :
    (∃ c, (ω c).2 = false) ∧ (∃ c, (ω c).2 = true) := by
  have hpure : ∀ b : Bool, ¬ (∀ c, (ω c).2 = b) := by
    intro b hb
    have he := matchingWords_eq_of_pure ω b hb
    rw [he, Finset.inter_self] at hcard
    have hc := (matchingWords_sixMatching hS (secondVertex ∘ ω)).1
    omega
  constructor
  · by_contra hn
    apply hpure true
    intro c
    cases hc : (ω c).2
    · exact False.elim (hn ⟨c, hc⟩)
    · rfl
  · by_contra hn
    apply hpure false
    intro c
    cases hc : (ω c).2
    · rfl
    · exact False.elim (hn ⟨c, hc⟩)

theorem intersection_card_four_iff_mixed {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState) :
    (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4 ↔
      (∃ c, (ω c).2 = false) ∧ (∃ c, (ω c).2 = true) :=
  ⟨mixed_of_intersection_card_four hS ω, fun h => intersection_card_of_mixed ω h.1 h.2⟩


end AkopyanResearch.PairIntersection
