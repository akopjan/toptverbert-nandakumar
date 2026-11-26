module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import RequestProject.Boundary

@[expose] public section

/-!
# The obstacles `ℓ_m` and their mutual position

* `ellLin m`: `ell m` as a linear map `Table → ℝ^5`;
* `finrank_ker_ellLin`: `ker ℓ_m` has codimension `5`;
* `ellLin_rank_two`: if two matchings have different kernels, the second normal map has rank at
  least two on the kernel of the first (two matchings sharing five words share all six).
-/

open Matrix

namespace Tverberg6R

/-- `ell m` as a linear map. -/
def ellLin (m : Fin 6 → Word) : Table →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun := ell m
  map_add' T T' := by funext r; simp [ell]; ring
  map_smul' c T := by funext r; simp [ell]; ring

lemma ellLin_apply (m : Fin 6 → Word) (T : Table) : ellLin m T = ell m T := rfl

/-- The words of a matching. -/
def wordSet (m : Fin 6 → Word) : Finset Word := Finset.univ.image m

lemma matching_injective {m : Fin 6 → Word} (hm : IsMatching m) : Function.Injective m :=
  fun r s h => hm 0 (by simp [h])

lemma card_wordSet {m : Fin 6 → Word} (hm : IsMatching m) : (wordSet m).card = 6 := by
  rw [wordSet, Finset.card_image_of_injective _ (matching_injective hm)]; simp

lemma mem_ker_ellLin_iff (m : Fin 6 → Word) (T : Table) :
    T ∈ LinearMap.ker (ellLin m) ↔ ∀ w ∈ wordSet m, T w = T (m 5) := by
  rw [LinearMap.mem_ker, ellLin_apply]
  constructor
  · intro h w hw
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
    refine Fin.lastCases ?_ (fun s => ?_) r
    · rfl
    · have := congrFun h s; simp only [ell, Pi.zero_apply] at this; linarith
  · intro h; funext s
    simp only [ell, Pi.zero_apply]
    rw [h _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))]; ring

lemma ker_ellLin_eq_of_wordSet_eq {m n : Fin 6 → Word} (h : wordSet m = wordSet n) :
    LinearMap.ker (ellLin m) = LinearMap.ker (ellLin n) := by
  ext T
  rw [mem_ker_ellLin_iff, mem_ker_ellLin_iff, h]
  have h5 : m 5 ∈ wordSet n := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have h5' : n 5 ∈ wordSet n := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  constructor
  · intro H w hw; rw [H w hw, H _ h5']
  · intro H w hw; rw [H w hw, H _ h5]

/-- Letters in colour `p` of the words of a matching are all distinct. -/
lemma letter_inj {m : Fin 6 → Word} (hm : IsMatching m) (p : Fin 6) :
    Set.InjOn (fun w : Word => w p) (wordSet m) := by
  intro w hw w' hw' h
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw')
  rw [hm p h]

/-- Two matchings sharing five words share all six. -/
lemma wordSet_eq_of_card_sdiff_le {m n : Fin 6 → Word} (hm : IsMatching m) (hn : IsMatching n)
    (h : (wordSet m \ wordSet n).card ≤ 1) : wordSet m = wordSet n := by
  classical
  have hcm := card_wordSet hm
  have hcn := card_wordSet hn
  have hi := Finset.card_sdiff_add_card_inter (wordSet m) (wordSet n)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · have hsub : wordSet m ⊆ wordSet n := Finset.sdiff_eq_empty_iff_subset.1
      (Finset.card_eq_zero.1 h0)
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · exfalso
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    have hi' := Finset.card_sdiff_add_card_inter (wordSet n) (wordSet m)
    rw [Finset.inter_comm] at hi'
    have h1' : (wordSet n \ wordSet m).card = 1 := by omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1'
    have haS : a ∈ wordSet m ∧ a ∉ wordSet n := by
      have : a ∈ wordSet m \ wordSet n := by rw [ha]; exact Finset.mem_singleton_self a
      exact Finset.mem_sdiff.1 this
    have hbS : b ∈ wordSet n ∧ b ∉ wordSet m := by
      have : b ∈ wordSet n \ wordSet m := by rw [hb]; exact Finset.mem_singleton_self b
      exact Finset.mem_sdiff.1 this
    apply haS.2
    suffices hab : a = b by rw [hab]; exact hbS.1
    funext p
    set C := wordSet m ∩ wordSet n
    have hC : C.card = 5 := by omega
    -- letters at `p` of the common words
    set L := C.image (fun w : Word => w p)
    have hL : L.card = 5 := by
      rw [Finset.card_image_of_injOn]; exact hC
      exact (letter_inj hm p).mono (by intro w hw; exact Finset.mem_coe.2 (Finset.mem_inter.1 (Finset.mem_coe.1 hw)).1)
    have haL : a p ∉ L := by
      intro hx
      obtain ⟨w, hw, hwp⟩ := Finset.mem_image.1 hx
      have := letter_inj hm p (Finset.mem_inter.1 hw).1 haS.1 hwp
      exact haS.2 (this ▸ (Finset.mem_inter.1 hw).2)
    have hbL : b p ∉ L := by
      intro hx
      obtain ⟨w, hw, hwp⟩ := Finset.mem_image.1 hx
      have := letter_inj hn p (Finset.mem_inter.1 hw).2 hbS.1 hwp
      exact hbS.2 (this ▸ (Finset.mem_inter.1 hw).1)
    by_contra hne
    have hsub : insert (a p) (insert (b p) L) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hbL, hL] at this
    · simp at this
    · simp only [Finset.mem_insert, not_or]; exact ⟨hne, haL⟩

/-- The normal vector of a point mass on the `r`-th word. -/
lemma ell_single (m : Fin 6 → Word) (hm : IsMatching m) (r : Fin 6) (s : Fin 5) :
    ell m (fun w => if w = m r then (1:ℝ) else 0) s =
      (if s.castSucc = r then 1 else 0) - (if (5 : Fin 6) = r then 1 else 0) := by
  simp only [ell, (matching_injective hm).eq_iff]

/-- **Rank two on kernels.** -/
theorem ellLin_rank_two {m n : Fin 6 → Word} (hm : IsMatching m) (hn : IsMatching n)
    (h : LinearMap.ker (ellLin m) ≠ LinearMap.ker (ellLin n)) :
    ∃ u ∈ LinearMap.ker (ellLin n), ∃ w ∈ LinearMap.ker (ellLin n),
      LinearIndependent ℝ ![ellLin m u, ellLin m w] := by
  classical
  have hne : wordSet m ≠ wordSet n := fun he => h (ker_ellLin_eq_of_wordSet_eq he)
  have h2 : 1 < (wordSet m \ wordSet n).card := by
    by_contra hc; exact hne (wordSet_eq_of_card_sdiff_le hm hn (not_lt.1 hc))
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
  obtain ⟨ham, han⟩ := Finset.mem_sdiff.1 ha
  obtain ⟨hbm, hbn⟩ := Finset.mem_sdiff.1 hb
  obtain ⟨ra, -, rfl⟩ := Finset.mem_image.1 ham
  obtain ⟨rb, -, rfl⟩ := Finset.mem_image.1 hbm
  have hrab : ra ≠ rb := fun e => hab (by rw [e])
  let δ : Fin 6 → Table := fun r w => if w = m r then (1:ℝ) else 0
  have hker : ∀ r, m r ∉ wordSet n → δ r ∈ LinearMap.ker (ellLin n) := by
    intro r hr
    rw [mem_ker_ellLin_iff]
    intro w hw
    have h1 : w ≠ m r := fun e => hr (e ▸ hw)
    have h2 : n 5 ≠ m r := fun e => hr (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
    simp [δ, h1, h2]
  refine ⟨δ ra, hker ra han, δ rb, hker rb hbn, ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hv : ∀ c : Fin 5, s * ((if c.castSucc = ra then 1 else 0) - (if (5 : Fin 6) = ra then 1 else 0))
      + t * ((if c.castSucc = rb then 1 else 0) - (if (5 : Fin 6) = rb then 1 else 0)) = 0 := by
    intro c
    have := congrFun hst c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ellLin_apply, δ] at this
    rwa [ell_single m hm ra c, ell_single m hm rb c] at this
  have hc5 : ∀ c : Fin 5, c.castSucc ≠ (5 : Fin 6) := fun c => (Fin.castSucc_lt_last c).ne
  by_cases h5a : ra = 5
  · subst h5a
    have hb5 : rb ≠ 5 := fun e => hrab e.symm
    obtain ⟨c, hc⟩ : ∃ c : Fin 5, c.castSucc = rb := ⟨rb.castPred hb5, by simp⟩
    obtain ⟨c', hc'⟩ : ∃ c' : Fin 5, c'.castSucc ≠ rb := by
      by_cases h0 : rb = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun e => h0 e.symm⟩
    have e1 := hv c
    have e2 := hv c'
    rw [if_neg (hc5 c), if_pos rfl, if_pos hc, if_neg (Ne.symm hb5)] at e1
    rw [if_neg (hc5 c'), if_pos rfl, if_neg hc', if_neg (Ne.symm hb5)] at e2
    constructor <;> linarith
  · by_cases h5b : rb = 5
    · subst h5b
      obtain ⟨c, hc⟩ : ∃ c : Fin 5, c.castSucc = ra := ⟨ra.castPred h5a, by simp⟩
      obtain ⟨c', hc'⟩ : ∃ c' : Fin 5, c'.castSucc ≠ ra := by
        by_cases h0 : ra = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun e => h0 e.symm⟩
      have e1 := hv c
      have e2 := hv c'
      rw [if_neg (hc5 c), if_pos rfl, if_pos hc, if_neg (Ne.symm h5a)] at e1
      rw [if_neg (hc5 c'), if_pos rfl, if_neg hc', if_neg (Ne.symm h5a)] at e2
      constructor <;> linarith
    · obtain ⟨c, hc⟩ : ∃ c : Fin 5, c.castSucc = ra := ⟨ra.castPred h5a, by simp⟩
      obtain ⟨c', hc'⟩ : ∃ c' : Fin 5, c'.castSucc = rb := ⟨rb.castPred h5b, by simp⟩
      have e1 := hv c
      have e2 := hv c'
      have h1 : c.castSucc ≠ rb := by rw [hc]; exact hrab
      have h2 : c'.castSucc ≠ ra := by rw [hc']; exact Ne.symm hrab
      rw [if_pos hc, if_neg (Ne.symm h5a), if_neg h1, if_neg (Ne.symm h5b)] at e1
      rw [if_neg h2, if_neg (Ne.symm h5a), if_pos hc', if_neg (Ne.symm h5b)] at e2
      constructor <;> linarith

/-- The kernel of `ℓ_m` has codimension five. -/
theorem finrank_ker_ellLin {m : Fin 6 → Word} (hm : IsMatching m) :
    Module.finrank ℝ (LinearMap.ker (ellLin m)) + 3 ≤ Module.finrank ℝ Table := by
  have hsurj : LinearMap.range (ellLin m) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    refine ⟨fun w => ∑ s : Fin 5, y s * (if w = m s.castSucc then 1 else 0), ?_⟩
    funext s
    have h5 : ∀ x : Fin 5, (5 : Fin 6) ≠ x.castSucc := fun x => (Fin.castSucc_lt_last x).ne'
    simp only [ellLin_apply, ell, (matching_injective hm).eq_iff]
    simp [h5, Fin.castSucc_inj]
  have := LinearMap.finrank_range_add_finrank_ker (ellLin m)
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at this
  omega

end Tverberg6R
