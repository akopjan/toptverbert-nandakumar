module

public import AkopyanResearch.Completion.QuadraticLink

/-!
# Ranks of all flats in the actual quadratic arrangement

The planar flat splits into two copies of a scalar flat. Consequently every
codimension is even. The single, pair, and triple estimates from the original
project give the low-rank classification for arbitrary finite intersections,
including all matching subspaces containing a flat, not only its generators.

These are linear-algebra statements. No homology formula or comparison
connectivity theorem is asserted in this module.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.QuadraticFlatRank

open AkopyanQuadratic

abbrev ScalarSpace (S : Finset (Fin 15)) := ↥(quadraticLabelSpace S (Fin 6))

def scalarFlat {S : Finset (Fin 15)} (F : Finset (MatchingIndex S)) :
    Submodule ℝ (ScalarSpace S) where
  carrier := {H | ∀ m ∈ F, ∀ u ∈ m.1, ∀ v ∈ m.1, H.1 u = H.1 v}
  zero_mem' _ _ _ _ _ _ := rfl
  add_mem' := by
    intro a b ha hb m hm u hu v hv
    change a.1 u + b.1 u = a.1 v + b.1 v
    rw [ha m hm u hu v hv, hb m hm u hu v hv]
  smul_mem' := by
    intro c a ha m hm u hu v hv
    change c * a.1 u = c * a.1 v
    rw [ha m hm u hu v hv]

def familyFlat {S : Finset (Fin 15)} (F : Finset (MatchingIndex S)) :
    Submodule ℝ (QuadSpace S) where
  carrier := {H | ∀ m ∈ F, H ∈ L_M S m.1}
  zero_mem' m _ := (L_M S m.1).zero_mem
  add_mem' ha hb m hm := (L_M S m.1).add_mem (ha m hm) (hb m hm)
  smul_mem' c _ ha m hm := (L_M S m.1).smul_mem c (ha m hm)

def scalarRank {S : Finset (Fin 15)} (F : Finset (MatchingIndex S)) : ℕ :=
  Module.finrank ℝ (ScalarSpace S ⧸ scalarFlat F)

def splitFlat {S : Finset (Fin 15)} (F : Finset (MatchingIndex S)) :
    familyFlat F ≃ₗ[ℝ] (Fin 2 → scalarFlat F) where
  toFun H t := ⟨H.1 t, fun m hm u hu v hv => H.2 m hm u hu v hv t⟩
  invFun H := ⟨fun t => (H t).1, fun m hm u hu v hv t => (H t).2 m hm u hu v hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem codimension_familyFlat {S : Finset (Fin 15)} (F : Finset (MatchingIndex S)) :
    Module.finrank ℝ (QuadSpace S ⧸ familyFlat F) = 2 * scalarRank F := by
  have hspace : Module.finrank ℝ (QuadSpace S) = 2 * Module.finrank ℝ (ScalarSpace S) := by
    simp [QuadSpace, ScalarSpace, Module.finrank_pi_fintype, Finset.sum_const]
  have hflat : Module.finrank ℝ (familyFlat F) = 2 * Module.finrank ℝ (scalarFlat F) := by
    let _ : Module.Free ℝ ↥(scalarFlat F) := Module.Free.of_divisionRing ℝ ↥(scalarFlat F)
    let _ : ∀ _ : Fin 2, Module.Free ℝ ↥(scalarFlat F) := fun _ => inferInstance
    let _ : ∀ _ : Fin 2, Module.Finite ℝ ↥(scalarFlat F) := fun _ => inferInstance
    calc
      Module.finrank ℝ (familyFlat F) = Module.finrank ℝ (Fin 2 → scalarFlat F) :=
        (splitFlat F).finrank_eq
      _ = ∑ _ : Fin 2, Module.finrank ℝ (scalarFlat F) :=
        Module.finrank_pi_fintype ℝ (M := fun _ : Fin 2 => ↥(scalarFlat F))
      _ = 2 * Module.finrank ℝ (scalarFlat F) := by simp
  have htotal := (familyFlat F).finrank_quotient_add_finrank
  have hscalar := (scalarFlat F).finrank_quotient_add_finrank
  change scalarRank F + Module.finrank ℝ (scalarFlat F) =
    Module.finrank ℝ (ScalarSpace S) at hscalar
  rw [hspace, hflat] at htotal
  omega

theorem familyFlat_empty (S : Finset (Fin 15)) :
    familyFlat (∅ : Finset (MatchingIndex S)) = ⊤ := by
  ext H
  simp [familyFlat]

theorem familyFlat_le_matching {S : Finset (Fin 15)}
    {F : Finset (MatchingIndex S)} {m : MatchingIndex S} (hm : m ∈ F) :
    familyFlat F ≤ L_M S m.1 := fun _ h => h m hm

theorem familyFlat_singleton {S : Finset (Fin 15)} (m : MatchingIndex S) :
    familyFlat {m} = L_M S m.1 := by
  ext H
  simp [familyFlat]

theorem codimension_antitone {S : Finset (Fin 15)}
    {V W : Submodule ℝ (QuadSpace S)} (h : V ≤ W) :
    Module.finrank ℝ (QuadSpace S ⧸ W) ≤ Module.finrank ℝ (QuadSpace S ⧸ V) := by
  have hdim := Submodule.finrank_mono h
  have hV := V.finrank_quotient_add_finrank
  have hW := W.finrank_quotient_add_finrank
  omega

theorem scalarRank_empty (S : Finset (Fin 15)) :
    scalarRank (∅ : Finset (MatchingIndex S)) = 0 := by
  have h := codimension_familyFlat (∅ : Finset (MatchingIndex S))
  have htop := (⊤ : Submodule ℝ (QuadSpace S)).finrank_quotient_add_finrank
  rw [finrank_top] at htop
  rw [familyFlat_empty] at h
  omega

theorem scalarRank_singleton {S : Finset (Fin 15)} (hS : S.Nonempty)
    (m : MatchingIndex S) : scalarRank {m} = 5 := by
  have h := codimension_familyFlat ({m} : Finset (MatchingIndex S))
  rw [familyFlat_singleton, codim_L_M_eq_ten S hS m.1 m.2] at h
  omega

theorem scalarRank_dichotomy {S : Finset (Fin 15)} (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) :
    scalarRank F = 0 ∨ scalarRank F = 5 ∨ 7 ≤ scalarRank F := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨m, hm⟩ := hF
    by_cases hall : ∀ j ∈ F, j = m
    · have heq : F = {m} := by
        ext j
        simp only [Finset.mem_singleton]
        exact ⟨hall j, fun h => h ▸ hm⟩
      rw [heq, scalarRank_singleton hS m]
      exact Or.inr (Or.inl rfl)
    · push Not at hall
      obtain ⟨j, hj, hne⟩ := hall
      have hvalues : m.1 ≠ j.1 := fun h => hne (Subtype.ext h.symm)
      have hpair := codim_L_M_inf_two_ge_fourteen S hS m.1 j.1 m.2 j.2 hvalues
      have hle := codimension_antitone
        (le_inf (familyFlat_le_matching hm) (familyFlat_le_matching hj))
      rw [codimension_familyFlat] at hle
      exact Or.inr (Or.inr (by omega))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF, scalarRank_empty]
    exact Or.inl rfl

theorem scalarRank_ne_six {S : Finset (Fin 15)} (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) : scalarRank F ≠ 6 := by
  have h := scalarRank_dichotomy hS F
  omega

theorem scalarRank_strict_antitone {S : Finset (Fin 15)}
    {F G : Finset (MatchingIndex S)} (h : familyFlat F < familyFlat G) :
    scalarRank G < scalarRank F := by
  have hdim := Submodule.finrank_lt_finrank_of_lt h
  have hF := (familyFlat F).finrank_quotient_add_finrank
  have hG := (familyFlat G).finrank_quotient_add_finrank
  rw [codimension_familyFlat] at hF hG
  omega

/-- This applies to all matching subspaces containing the flat. -/
theorem no_three_containing_flat_of_rank_lt_nine
    {S : Finset (Fin 15)} (hS : S.Nonempty) (F : Finset (MatchingIndex S))
    (hF : scalarRank F < 9) (m₁ m₂ m₃ : MatchingIndex S)
    (h₁ : familyFlat F ≤ L_M S m₁.1) (h₂ : familyFlat F ≤ L_M S m₂.1)
    (h₃ : familyFlat F ≤ L_M S m₃.1)
    (h₁₂ : m₁ ≠ m₂) (h₁₃ : m₁ ≠ m₃) (h₂₃ : m₂ ≠ m₃) : False := by
  have hlow := codim_L_M_inf_three_ge_eighteen S hS m₁.1 m₂.1 m₃.1 m₁.2 m₂.2 m₃.2
    (fun h => h₁₂ (Subtype.ext h)) (fun h => h₁₃ (Subtype.ext h))
    (fun h => h₂₃ (Subtype.ext h))
  have hhigh := codimension_antitone (le_inf (le_inf h₁ h₂) h₃)
  rw [codimension_familyFlat] at hhigh
  omega

theorem card_generators_le_two {S : Finset (Fin 15)} (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) (hF : scalarRank F < 9) : F.card ≤ 2 := by
  by_contra h
  obtain ⟨m₁, m₂, m₃, hm₁, hm₂, hm₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  exact no_three_containing_flat_of_rank_lt_nine hS F hF m₁ m₂ m₃
    (familyFlat_le_matching hm₁) (familyFlat_le_matching hm₂)
    (familyFlat_le_matching hm₃) h₁₂ h₁₃ h₂₃

theorem card_containing_matchings_le_two {S : Finset (Fin 15)} (hS : S.Nonempty)
    (F T : Finset (MatchingIndex S)) (hF : scalarRank F < 9)
    (hT : ∀ m ∈ T, familyFlat F ≤ L_M S m.1) : T.card ≤ 2 := by
  by_contra h
  obtain ⟨m₁, m₂, m₃, hm₁, hm₂, hm₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  exact no_three_containing_flat_of_rank_lt_nine hS F hF m₁ m₂ m₃
    (hT m₁ hm₁) (hT m₂ hm₂) (hT m₃ hm₃) h₁₂ h₁₃ h₂₃

theorem familyFlat_pair {S : Finset (Fin 15)} (m₁ m₂ : MatchingIndex S) :
    familyFlat {m₁, m₂} = L_M S m₁.1 ⊓ L_M S m₂.1 := by
  ext H
  simp [familyFlat]

/-- Every non-atomic flat of scalar rank below nine is the intersection of
exactly two distinct matching subspaces. -/
theorem low_rank_flat_eq_pair {S : Finset (Fin 15)} (hS : S.Nonempty)
    (F : Finset (MatchingIndex S)) (hlo : 7 ≤ scalarRank F) (hhi : scalarRank F < 9) :
    ∃ m₁ m₂ : MatchingIndex S, m₁ ≠ m₂ ∧
      familyFlat F = L_M S m₁.1 ⊓ L_M S m₂.1 := by
  classical
  have hnonempty : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, scalarRank_empty] at hlo
    omega
  obtain ⟨m₁, hm₁⟩ := hnonempty
  have hsecond : ∃ m₂ ∈ F, m₂ ≠ m₁ := by
    by_contra h
    push Not at h
    have heq : F = {m₁} := by
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨h j, fun hj => hj ▸ hm₁⟩
    rw [heq, scalarRank_singleton hS m₁] at hlo
    omega
  obtain ⟨m₂, hm₂, h₂₁⟩ := hsecond
  have heq : F = {m₁, m₂} := by
    apply Finset.Subset.antisymm
    · intro j hj
      by_cases h₁ : j = m₁
      · simp [h₁]
      by_cases h₂ : j = m₂
      · simp [h₂]
      exact False.elim (no_three_containing_flat_of_rank_lt_nine hS F hhi m₁ m₂ j
        (familyFlat_le_matching hm₁) (familyFlat_le_matching hm₂)
        (familyFlat_le_matching hj) h₂₁.symm (Ne.symm h₁) (Ne.symm h₂))
    · intro j hj
      rcases Finset.mem_insert.mp hj with hj | hj
      · simpa [hj] using hm₁
      · simpa only [Finset.mem_singleton.mp hj] using hm₂
  exact ⟨m₁, m₂, h₂₁.symm, by rw [heq, familyFlat_pair]⟩

/-- Below scalar rank nine there is no proper inclusion between two
non-atomic flats. In particular, ranks seven and eight cannot both occur
in one strict chain below a rank-nine flat. -/
theorem low_rank_nonatomic_comparable_eq {S : Finset (Fin 15)} (hS : S.Nonempty)
    (F G : Finset (MatchingIndex S)) (hFG : familyFlat F ≤ familyFlat G)
    (hF : scalarRank F < 9) (hG : 7 ≤ scalarRank G) :
    familyFlat F = familyFlat G := by
  classical
  have hrank : scalarRank G ≤ scalarRank F := by
    have h := codimension_antitone hFG
    rw [codimension_familyFlat, codimension_familyFlat] at h
    omega
  obtain ⟨m₁, m₂, h₁₂, hpair⟩ := low_rank_flat_eq_pair hS G hG (by omega)
  have h₁ : familyFlat F ≤ L_M S m₁.1 := by rw [hpair] at hFG; exact hFG.trans inf_le_left
  have h₂ : familyFlat F ≤ L_M S m₂.1 := by rw [hpair] at hFG; exact hFG.trans inf_le_right
  apply le_antisymm hFG
  intro H hH j hj
  by_cases hji : j = m₁
  · subst j
    exact (show H ∈ L_M S m₁.1 ⊓ L_M S m₂.1 from hpair ▸ hH).1
  by_cases hjj : j = m₂
  · subst j
    exact (show H ∈ L_M S m₁.1 ⊓ L_M S m₂.1 from hpair ▸ hH).2
  exact False.elim (no_three_containing_flat_of_rank_lt_nine hS F hF m₁ m₂ j
    h₁ h₂ (familyFlat_le_matching hj) h₁₂ (Ne.symm hji) (Ne.symm hjj))

theorem strict_low_rank_chain_length_le_two
    {S : Finset (Fin 15)} (hS : S.Nonempty) {n : ℕ}
    (c : Fin n → Finset (MatchingIndex S))
    (hc : StrictAnti (fun i => familyFlat (c i)))
    (hpos : ∀ i, 0 < scalarRank (c i)) (hsmall : ∀ i, scalarRank (c i) < 9) : n ≤ 2 := by
  by_contra h
  have hn : 3 ≤ n := by omega
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have h₀₁ : i₀ < i₁ := by change (0 : ℕ) < 1; omega
  have h₁₂ : i₁ < i₂ := by change (1 : ℕ) < 2; omega
  have hfirst := scalarRank_dichotomy hS (c i₀)
  have hsecond := scalarRank_dichotomy hS (c i₁)
  have hrank := scalarRank_strict_antitone (hc h₀₁)
  have h₁ : 7 ≤ scalarRank (c i₁) := by have := hpos i₀; omega
  have heq := low_rank_nonatomic_comparable_eq hS (c i₂) (c i₁)
    (hc h₁₂).le (hsmall i₂) h₁
  exact (hc h₁₂).ne heq

theorem rank_set_card_bound (T : Finset ℕ) (t : ℕ)
    (hmin : ∀ r ∈ T, 5 ≤ r) (hskip : ∀ r ∈ T, r ≠ 6)
    (hmax : ∀ r ∈ T, r < t) : T.card ≤ 1 + (t - 7) := by
  have hsub : T ⊆ {5} ∪ Finset.Ico 7 t := by
    intro r hr
    by_cases he : r = 5
    · simp [he]
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_Ico.mpr
        ⟨by have := hmin r hr; have := hskip r hr; omega, hmax r hr⟩
  calc
    T.card ≤ ({5} ∪ Finset.Ico 7 t).card := Finset.card_le_card hsub
    _ ≤ ({5} : Finset ℕ).card + (Finset.Ico 7 t).card := Finset.card_union_le _ _
    _ = 1 + (t - 7) := by simp

/-- The strict-flat-chain bound for the actual quadratic intersection poset. -/
theorem strict_flat_chain_length_bound {S : Finset (Fin 15)} (hS : S.Nonempty)
    {n t : ℕ} (ht : 7 ≤ t) (c : Fin n → Finset (MatchingIndex S))
    (hc : StrictAnti (fun i => familyFlat (c i)))
    (hpos : ∀ i, 0 < scalarRank (c i)) (hmax : ∀ i, scalarRank (c i) < t) :
    n ≤ t - 6 := by
  classical
  let r : Fin n → ℕ := fun i => scalarRank (c i)
  have hr : StrictMono r := fun _ _ h => scalarRank_strict_antitone (hc h)
  have hmin : ∀ i, 5 ≤ r i := by
    intro i
    have hd := scalarRank_dichotomy hS (c i)
    have hp := hpos i
    dsimp [r]
    omega
  have hskip : ∀ i, r i ≠ 6 := fun i => scalarRank_ne_six hS (c i)
  have h := rank_set_card_bound (Finset.univ.image r) t
    (by simpa using hmin) (by simpa using hskip) (by simpa [r] using hmax)
  rw [Finset.card_image_of_injective _ hr.injective, Finset.card_univ, Fintype.card_fin] at h
  omega

end AkopyanResearch.QuadraticFlatRank
