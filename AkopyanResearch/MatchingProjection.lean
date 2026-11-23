module

public import AkopyanResearch.MatchingCombinatorics

@[expose] public section

/-!
# Restricting matchings to a nonempty set of colors

A pair of six-matchings with four common words either keeps exactly four
common words after projection, or the two projected matchings coincide.
Thus there is no intermediate five-word overlap on a boundary face.
-/

namespace AkopyanQuadratic

open scoped Classical

variable {I J K : Type*}

noncomputable def projectMatching (f : J → I) (s : Finset (I → Fin 6)) :
    Finset (J → Fin 6) := s.image (fun w => w ∘ f)

lemma projectMatching_injectiveOn (f : J → I) (j₀ : J)
    {s : Finset (I → Fin 6)} (hs : SixMatching s) :
    Set.InjOn (fun w : I → Fin 6 => w ∘ f) (s : Set (I → Fin 6)) := by
  intro u hu v hv h
  exact hs.2.1 (f j₀) u hu v hv (congrFun h j₀)

lemma SixMatching.project (f : J → I) (j₀ : J)
    {s : Finset (I → Fin 6)} (hs : SixMatching s) :
    SixMatching (projectMatching f s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [projectMatching, Finset.card_image_iff.mpr (projectMatching_injectiveOn f j₀ hs)]
    exact hs.1
  · intro j u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    have h : u' = v' := hs.2.1 (f j) u' hu' v' hv' huv
    rw [h]
  · intro j a
    obtain ⟨u, hu, hua⟩ := hs.2.2 (f j) a
    exact ⟨u ∘ f, Finset.mem_image.mpr ⟨u, hu, rfl⟩, hua⟩

lemma common_words_survive_projection (f : J → I) (j₀ : J)
    (m n : Finset (I → Fin 6)) (hm : SixMatching m) :
    (m ∩ n).card ≤ (projectMatching f m ∩ projectMatching f n).card := by
  classical
  have hi : Set.InjOn (fun w : I → Fin 6 => w ∘ f)
      ((m ∩ n : Finset (I → Fin 6)) : Set (I → Fin 6)) := by
    intro u hu v hv h
    exact projectMatching_injectiveOn f j₀ hm (Finset.mem_inter.mp hu).1
      (Finset.mem_inter.mp hv).1 h
  have hc : (projectMatching f (m ∩ n)).card = (m ∩ n).card :=
    Finset.card_image_iff.mpr hi
  rw [← hc]
  apply Finset.card_le_card
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩,
      Finset.mem_image.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩⟩

/-- Every face restriction of a minimal pair is a minimal pair or a diagonal. -/
theorem minimal_pair_projection (f : J → I) (j₀ : J)
    (m n : Finset (I → Fin 6)) (hm : SixMatching m) (hn : SixMatching n)
    (hfour : (m ∩ n).card = 4) :
    projectMatching f m = projectMatching f n ∨
      (projectMatching f m ∩ projectMatching f n).card = 4 := by
  classical
  by_cases heq : projectMatching f m = projectMatching f n
  · exact Or.inl heq
  · right
    have hlow := common_words_survive_projection f j₀ m n hm
    have hupp := distinct_sixMatchings_inter_card_le_four
      (projectMatching f m) (projectMatching f n) j₀
      (hm.project f j₀) (hn.project f j₀) heq
    omega

lemma projectMatching_comp (f : J → I) (g : K → J)
    (s : Finset (I → Fin 6)) :
    projectMatching g (projectMatching f s) = projectMatching (f ∘ g) s := by
  classical
  simp only [projectMatching, Finset.image_image, Function.comp_def]

end AkopyanQuadratic
