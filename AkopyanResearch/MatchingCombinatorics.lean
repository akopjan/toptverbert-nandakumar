module

public import AkopyanResearch.QuadraticInterpolation

@[expose] public section

/-!
# Two different six-matchings share at most four words

This elementary fact is the input behind the codimension bound for pairs of
matching kernels. No enumeration of words or permutations is used.
-/

namespace AkopyanQuadratic

open scoped Classical

variable {I : Type*}

def SixMatching (s : Finset (I → Fin 6)) : Prop :=
  s.card = 6 ∧
  (∀ i, ∀ u ∈ s, ∀ v ∈ s, u i = v i → u = v) ∧
  (∀ i, ∀ a : Fin 6, ∃ u ∈ s, u i = a)

lemma SixMatching.coordinateInjectiveOn {s : Finset (I → Fin 6)}
    (hs : SixMatching s) (i₀ : I) : CoordinateInjectiveOn s i₀ :=
  fun _ hu _ hv h => hs.2.1 i₀ _ hu _ hv h

lemma sixMatching_difference_card_ge_two
    (m n : Finset (I → Fin 6)) (i₀ : I)
    (hm : SixMatching m) (hn : SixMatching n)
    (u : I → Fin 6) (hum : u ∈ m) (hun : u ∉ n) :
    2 ≤ (n \ m).card := by
  classical
  by_contra hcard
  have hc : (n \ m).card ≤ 1 := by omega
  have hout : ∀ i, ∀ v ∈ n, v i = u i → v ∉ m := by
    intro i v hvn hvi hvm
    have hvu : v = u := hm.2.1 i v hvm u hum hvi
    exact hun (hvu ▸ hvn)
  obtain ⟨v₀, hv₀n, hv₀i⟩ := hn.2.2 i₀ (u i₀)
  have hv₀ : v₀ ∈ n \ m := Finset.mem_sdiff.mpr
    ⟨hv₀n, hout i₀ v₀ hv₀n hv₀i⟩
  have huv₀ : u = v₀ := by
    funext i
    obtain ⟨v, hvn, hvi⟩ := hn.2.2 i (u i)
    have hv : v ∈ n \ m := Finset.mem_sdiff.mpr ⟨hvn, hout i v hvn hvi⟩
    have hvv₀ : v = v₀ := Finset.card_le_one.mp hc v hv v₀ hv₀
    simpa only [hvv₀] using hvi.symm
  exact hun (huv₀.symm ▸ hv₀n)

theorem distinct_sixMatchings_inter_card_le_four
    (m n : Finset (I → Fin 6)) (i₀ : I)
    (hm : SixMatching m) (hn : SixMatching n) (hne : m ≠ n) :
    (m ∩ n).card ≤ 4 := by
  classical
  have hex : ∃ u ∈ m, u ∉ n := by
    by_contra h
    apply hne
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      by_contra hun
      exact h ⟨u, hu, hun⟩
    · exact le_of_eq (hn.1.trans hm.1.symm)
  obtain ⟨u, hum, hun⟩ := hex
  have hdiff := sixMatching_difference_card_ge_two m n i₀ hm hn u hum hun
  have hsum := Finset.card_sdiff_add_card_inter n m
  rw [Finset.inter_comm] at hsum
  have hncard := hn.1
  omega

lemma distinct_sixMatchings_sdiff_card_ge_two
    (m n : Finset (I → Fin 6)) (i₀ : I)
    (hm : SixMatching m) (hn : SixMatching n) (hne : m ≠ n) :
    2 ≤ (m \ n).card := by
  classical
  have hex : ∃ u ∈ n, u ∉ m := by
    by_contra h
    apply hne
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      by_contra hum
      exact h ⟨u, hu, hum⟩
    · exact le_of_eq (hm.1.trans hn.1.symm)
  obtain ⟨u, hun, hum⟩ := hex
  exact sixMatching_difference_card_ge_two n m i₀ hn hm u hun hum

/-- If a third matching adds at most one word to the union of two matchings,
it must contain every common word of those two matchings. -/
lemma common_subset_of_few_outside
    (m n p : Finset (I → Fin 6)) (i₀ : I)
    (hm : SixMatching m) (hn : SixMatching n) (hp : SixMatching p)
    (hc : (p \ (m ∪ n)).card ≤ 1) : m ∩ n ⊆ p := by
  classical
  intro u hu
  obtain ⟨hum, hun⟩ := Finset.mem_inter.mp hu
  by_contra hup
  have hout : ∀ i, ∀ v ∈ p, v i = u i → v ∉ m ∪ n := by
    intro i v hvp hvi hvmn
    rcases Finset.mem_union.mp hvmn with hvm | hvn
    · have hvu : v = u := hm.2.1 i v hvm u hum hvi
      exact hup (hvu ▸ hvp)
    · have hvu : v = u := hn.2.1 i v hvn u hun hvi
      exact hup (hvu ▸ hvp)
  obtain ⟨v₀, hv₀p, hv₀i⟩ := hp.2.2 i₀ (u i₀)
  have hv₀ : v₀ ∈ p \ (m ∪ n) := Finset.mem_sdiff.mpr
    ⟨hv₀p, hout i₀ v₀ hv₀p hv₀i⟩
  have huv₀ : u = v₀ := by
    funext i
    obtain ⟨v, hvp, hvi⟩ := hp.2.2 i (u i)
    have hv : v ∈ p \ (m ∪ n) := Finset.mem_sdiff.mpr
      ⟨hvp, hout i v hvp hvi⟩
    have hvv₀ : v = v₀ := Finset.card_le_one.mp hc v hv v₀ hv₀
    simpa only [hvv₀] using hvi.symm
  exact hup (huv₀.symm ▸ hv₀p)

/-- Three different six-matchings contain at least ten different words.
The proof uses only finite-set cardinal arithmetic and the matching property. -/
theorem three_distinct_sixMatchings_union_card_ge_ten
    (m n p : Finset (I → Fin 6)) (i₀ : I)
    (hm : SixMatching m) (hn : SixMatching n) (hp : SixMatching p)
    (hmn : m ≠ n) (hmp : m ≠ p) (hnp : n ≠ p) :
    10 ≤ (m ∪ n ∪ p).card := by
  classical
  by_contra hcard
  have hsmall : (m ∪ n ∪ p).card ≤ 9 := by omega
  have hmn_inter := distinct_sixMatchings_inter_card_le_four m n i₀ hm hn hmn
  have hmn_cards := Finset.card_union_add_card_inter m n
  have houtside := Finset.card_sdiff_add_card p (m ∪ n)
  rw [Finset.union_comm p (m ∪ n)] at houtside
  have hmc := hm.1
  have hnc := hn.1
  have hpc := hp.1
  have hsmall_outside : (p \ (m ∪ n)).card ≤ 1 := by omega
  have hcommon := common_subset_of_few_outside m n p i₀ hm hn hp hsmall_outside
  have hremaining := Finset.card_sdiff_add_card_eq_card hcommon
  have hpm := distinct_sixMatchings_sdiff_card_ge_two p m i₀ hp hm (Ne.symm hmp)
  have hpn := distinct_sixMatchings_sdiff_card_ge_two p n i₀ hp hn (Ne.symm hnp)
  have hdiff_union : (p \ m) ∪ (p \ n) = p \ (m ∩ n) := by
    ext u
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdiff_inter : (p \ m) ∩ (p \ n) = p \ (m ∪ n) := by
    ext u
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdiff_cards := Finset.card_union_add_card_inter (p \ m) (p \ n)
  rw [hdiff_union, hdiff_inter] at hdiff_cards
  omega

end AkopyanQuadratic
