module

public import AkopyanResearch.Completion.QuadraticFlatRank

/-!
# Exact pair codimensions in the actual quadratic arrangement

For two six-matchings, this module computes the codimension of the intersection
of their original quadratic kernels from the number of common words. In
particular, real codimensions fourteen and sixteen correspond exactly to four
and three common words. No comparison or extension statement is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.QuadraticPairRank

open AkopyanQuadratic QuadraticFlatRank

def constOnPairEquivOfInter {W : Type*} [DecidableEq W]
    (m n : Finset W) (h : (m ∩ n).Nonempty) :
    constOnSubmodule (m ∪ n) [m, n] ≃ₗ[ℝ] (Fin 2 → ℝ) := by
  let w₀ := h.choose
  have hw₀ : w₀ ∈ m ∩ n := h.choose_spec
  have hm₀ : w₀ ∈ m := (Finset.mem_inter.mp hw₀).1
  have hn₀ : w₀ ∈ n := (Finset.mem_inter.mp hw₀).2
  have hu₀ : w₀ ∈ m ∪ n := Finset.mem_union_left _ hm₀
  exact
    { toFun := fun g => g.1 ⟨w₀, hu₀⟩
      invFun := fun c => ⟨fun _ => c, fun _ _ _ _ _ _ _ _ => rfl⟩
      left_inv := fun g => by
        apply Subtype.ext
        funext ⟨w, hw⟩
        rcases Finset.mem_union.mp hw with hm | hn
        · exact (g.2 m (by simp) w hm w₀ hm₀ hw hu₀).symm
        · exact (g.2 n (by simp) w hn w₀ hn₀ hw hu₀).symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem finrank_constOn_pair_of_inter {W : Type*} [DecidableEq W]
    (m n : Finset W) (h : (m ∩ n).Nonempty) :
    Module.finrank ℝ (constOnSubmodule (m ∪ n) [m, n]) = 2 := by
  rw [(constOnPairEquivOfInter m n h).finrank_eq, Module.finrank_fin_fun]

def constOnPairEquivOfDisjoint {W : Type*} [DecidableEq W]
    (m n : Finset W) (hm : m.Nonempty) (hn : n.Nonempty) (hd : Disjoint m n) :
    constOnSubmodule (m ∪ n) [m, n] ≃ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) := by
  let w₁ := hm.choose
  let w₂ := hn.choose
  have hw₁ : w₁ ∈ m := hm.choose_spec
  have hw₂ : w₂ ∈ n := hn.choose_spec
  have hw₁u : w₁ ∈ m ∪ n := Finset.mem_union_left _ hw₁
  have hw₂u : w₂ ∈ m ∪ n := Finset.mem_union_right _ hw₂
  have hnm : ∀ w ∈ n, w ∉ m := fun w hwn hwm => Finset.disjoint_left.mp hd hwm hwn
  exact
    { toFun := fun g => (g.1 ⟨w₁, hw₁u⟩, g.1 ⟨w₂, hw₂u⟩)
      invFun := fun c => ⟨fun w => if w.1 ∈ m then c.1 else c.2, by
        intro a ha u hu v hv huu hvu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · simp only [hu, hv, ↓reduceIte]
        · simp only [hnm u hu, hnm v hv, ↓reduceIte]⟩
      left_inv := fun g => by
        apply Subtype.ext
        funext ⟨w, hw⟩
        by_cases hwm : w ∈ m
        · simp only [hwm, ↓reduceIte]
          exact (g.2 m (by simp) w hwm w₁ hw₁ hw hw₁u).symm
        · simp only [hwm, ↓reduceIte]
          have hwn : w ∈ n := (Finset.mem_union.mp hw).resolve_left hwm
          exact (g.2 n (by simp) w hwn w₂ hw₂ hw hw₂u).symm
      right_inv := fun c => by simp only [hw₁, hnm w₂ hw₂, ↓reduceIte]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem finrank_constOn_pair_of_disjoint {W : Type*} [DecidableEq W]
    (m n : Finset W) (hm : m.Nonempty) (hn : n.Nonempty) (hd : Disjoint m n) :
    Module.finrank ℝ (constOnSubmodule (m ∪ n) [m, n]) = 4 := by
  rw [(constOnPairEquivOfDisjoint m n hm hn hd).finrank_eq, Module.finrank_prod]
  norm_num

theorem codim_pair_via_union (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n) :
    Module.finrank ℝ (QuadSpace S ⧸ (L_M S m ⊓ L_M S n)) =
      2 * (m ∪ n).card - Module.finrank ℝ (constOnSubmodule (m ∪ n) [m, n]) := by
  classical
  let i₀ : S := ⟨hS.choose, hS.choose_spec⟩
  have h3 := three_matchings_fiber_card_le_three m n n i₀
    (hm.coordinateInjectiveOn i₀) (hn.coordinateInjectiveOn i₀)
    (hn.coordinateInjectiveOn i₀)
  have hU : @Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _))
      (@Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _)) m n) n =
      m ∪ n := by ext w; simp
  rw [hU] at h3
  have hev : Function.Surjective (vectorEvaluation (K := Fin 2) (m ∪ n)) :=
    vectorEvaluation_surjective (m ∪ n) i₀ h3
  let K := constOnSubmodule (m ∪ n) [m, n]
  have hcomap : K.comap (vectorEvaluation (K := Fin 2) (m ∪ n)) =
      L_M S m ⊓ L_M S n := by
    ext H
    simp only [Submodule.mem_comap, K, constOnSubmodule, List.mem_cons, List.not_mem_nil,
      or_false, Submodule.mem_inf, L_M, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, vectorEvaluation, LinearMap.coe_mk,
      AddHom.coe_mk, funext_iff]
    constructor
    · intro h
      refine ⟨fun a ha b hb t => h m (Or.inl rfl) a ha b hb (Finset.mem_union_left _ ha)
          (Finset.mem_union_left _ hb) t,
        fun a ha b hb t => h n (Or.inr rfl) a ha b hb (Finset.mem_union_right _ ha)
          (Finset.mem_union_right _ hb) t⟩
    · rintro ⟨h₁, h₂⟩ j (rfl | rfl) a ha b hb _ _ t
      · exact h₁ a ha b hb t
      · exact h₂ a ha b hb t
  rw [← hcomap, codim_comap_of_surjective _ hev K, finrank_arrow_fin2]

theorem codim_pair_eq_of_inter (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n)
    (hi : (m ∩ n).Nonempty) :
    Module.finrank ℝ (QuadSpace S ⧸ (L_M S m ⊓ L_M S n)) =
      2 * (11 - (m ∩ n).card) := by
  classical
  rw [codim_pair_via_union S hS m n hm hn, finrank_constOn_pair_of_inter m n hi]
  have hcard := Finset.card_union_add_card_inter m n
  have hbound := Finset.card_le_card (Finset.inter_subset_left : m ∩ n ⊆ m)
  have hmcard := hm.1
  have hncard := hn.1
  omega

theorem codim_pair_eq_of_disjoint (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n)
    (hd : Disjoint m n) :
    Module.finrank ℝ (QuadSpace S ⧸ (L_M S m ⊓ L_M S n)) = 20 := by
  classical
  have hmne : m.Nonempty := Finset.card_pos.mp (by rw [hm.1]; norm_num)
  have hnne : n.Nonempty := Finset.card_pos.mp (by rw [hn.1]; norm_num)
  rw [codim_pair_via_union S hS m n hm hn,
    finrank_constOn_pair_of_disjoint m n hmne hnne hd,
    Finset.card_union_of_disjoint hd, hm.1, hn.1]

theorem codim_pair_eq_fourteen_iff (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n) :
    Module.finrank ℝ (QuadSpace S ⧸ (L_M S m ⊓ L_M S n)) = 14 ↔
      (m ∩ n).card = 4 := by
  classical
  by_cases hi : (m ∩ n).Nonempty
  · rw [codim_pair_eq_of_inter S hS m n hm hn hi]
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hi
    have hd : Disjoint m n := Finset.disjoint_iff_inter_eq_empty.mpr he
    rw [codim_pair_eq_of_disjoint S hS m n hm hn hd, he]
    norm_num

theorem codim_pair_eq_sixteen_iff (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n) :
    Module.finrank ℝ (QuadSpace S ⧸ (L_M S m ⊓ L_M S n)) = 16 ↔
      (m ∩ n).card = 3 := by
  classical
  by_cases hi : (m ∩ n).Nonempty
  · rw [codim_pair_eq_of_inter S hS m n hm hn hi]
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hi
    have hd : Disjoint m n := Finset.disjoint_iff_inter_eq_empty.mpr he
    rw [codim_pair_eq_of_disjoint S hS m n hm hn hd, he]
    norm_num

theorem scalarRank_pair_eq_seven_iff {S : Finset (Fin 15)} (hS : S.Nonempty)
    (m n : MatchingIndex S) :
    scalarRank {m, n} = 7 ↔ (m.1 ∩ n.1).card = 4 := by
  classical
  have h := codimension_familyFlat ({m, n} : Finset (MatchingIndex S))
  rw [familyFlat_pair] at h
  calc
    scalarRank {m, n} = 7 ↔ 2 * scalarRank {m, n} = 14 := by omega
    _ ↔ (m.1 ∩ n.1).card = 4 := by
      rw [← h]
      exact codim_pair_eq_fourteen_iff S hS m.1 n.1 m.2 n.2

theorem scalarRank_pair_eq_eight_iff {S : Finset (Fin 15)} (hS : S.Nonempty)
    (m n : MatchingIndex S) :
    scalarRank {m, n} = 8 ↔ (m.1 ∩ n.1).card = 3 := by
  classical
  have h := codimension_familyFlat ({m, n} : Finset (MatchingIndex S))
  rw [familyFlat_pair] at h
  calc
    scalarRank {m, n} = 8 ↔ 2 * scalarRank {m, n} = 16 := by omega
    _ ↔ (m.1 ∩ n.1).card = 3 := by
      rw [← h]
      exact codim_pair_eq_sixteen_iff S hS m.1 n.1 m.2 n.2


end AkopyanResearch.QuadraticPairRank
