module

public import AkopyanResearch.Completion.PairRepresentation
public import AkopyanResearch.Completion.PairIntersection

/-! Finite orbit classification for the actual universal pair labels. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairOrbit

open scoped Classical
open AkopyanQuadratic OriginalJoinBridge PairSphereAction PairSourceProjections
open MatchingSphereMap PairRepresentation

theorem matchingWords_reindex {S : Finset (Fin 15)}
    (σ : S → RowGroup) (ρ : RowGroup) :
    matchingWords (fun c => σ c * ρ) = matchingWords σ := by
  ext w
  simp only [matchingWords, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨ρ j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨ρ.symm j, ?_⟩
    funext c
    exact congrArg (σ c) (ρ.apply_symm_apply j)

theorem exists_row_reindex {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ τ : S → RowGroup) (he : matchingWords σ = matchingWords τ) :
    ∃ ρ : RowGroup, ∀ c, τ c = σ c * ρ := by
  let c₀ : S := ⟨hS.choose, hS.choose_spec⟩
  let ρ : RowGroup := (σ c₀)⁻¹ * τ c₀
  refine ⟨ρ, fun c => ?_⟩
  apply Equiv.ext
  intro j
  have hj : matchingWord τ j ∈ matchingWords σ := by
    rw [he]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
  have hji : ρ j = i := by
    change (σ c₀).symm (τ c₀ j) = i
    have hc := congrFun hi c₀
    change σ c₀ i = τ c₀ j at hc
    rw [← hc, Equiv.symm_apply_apply]
  change τ c j = σ c (ρ j)
  rw [hji]
  exact (congrFun hi c).symm

theorem existsUnique_row_reindex {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ τ : S → RowGroup) (he : matchingWords σ = matchingWords τ) :
    ∃! ρ : RowGroup, ∀ c, τ c = σ c * ρ := by
  obtain ⟨ρ, hρ⟩ := exists_row_reindex hS σ τ he
  refine ⟨ρ, hρ, fun γ hγ => ?_⟩
  let c : S := ⟨hS.choose, hS.choose_spec⟩
  apply mul_left_cancel (a := σ c)
  exact (hγ c).symm.trans (hρ c)

theorem common_word_eq {S : Finset (Fin 15)} (ω : S → PairState) (i : Fin 4) :
    matchingWord (firstVertex ∘ ω) (i.castAdd 2) =
      matchingWord (secondVertex ∘ ω) (i.castAdd 2) := by
  funext c
  change (ω c).1 (i.castAdd 2) =
    ((ω c).1 * blockPerm 1 (ω c).2) (i.castAdd 2)
  simp only [Equiv.Perm.mul_apply, blockPerm_castAdd, Equiv.Perm.one_apply]

theorem first_four_image_eq_intersection {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ τ : S → RowGroup)
    (hcommon : ∀ i : Fin 4, matchingWord σ (i.castAdd 2) = matchingWord τ (i.castAdd 2))
    (hcard : (matchingWords σ ∩ matchingWords τ).card = 4) :
    Finset.univ.image (fun i : Fin 4 => matchingWord σ (i.castAdd 2)) =
      matchingWords σ ∩ matchingWords τ := by
  have hinj : Function.Injective (fun i : Fin 4 => matchingWord σ (i.castAdd 2)) := by
    intro i j hij
    have he := (matchingWord_injective hS σ) hij
    exact Fin.ext (congrArg (fun z : Fin 6 => z.val) he)
  have hc : (Finset.univ.image (fun i : Fin 4 => matchingWord σ (i.castAdd 2))).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hcommon i]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · rw [hc, hcard]

theorem row_index_lt_four_iff_mem_other {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ τ : S → RowGroup)
    (hcommon : ∀ i : Fin 4, matchingWord σ (i.castAdd 2) = matchingWord τ (i.castAdd 2))
    (hcard : (matchingWords σ ∩ matchingWords τ).card = 4) (j : Fin 6) :
    matchingWord σ j ∈ matchingWords τ ↔ j.val < 4 := by
  constructor
  · intro hj
    have hi : matchingWord σ j ∈ matchingWords σ ∩ matchingWords τ :=
      Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩
    rw [← first_four_image_eq_intersection hS σ τ hcommon hcard] at hi
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hi
    have he := congrArg Fin.val ((matchingWord_injective hS σ) hi)
    change i.val = j.val at he
    have := i.isLt
    omega
  · intro hj
    let i : Fin 4 := ⟨j.val, hj⟩
    have hi : i.castAdd 2 = j := Fin.ext rfl
    rw [← hi, hcommon i]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem permutation_eq_blockPerm_of_castAdd (ρ : RowGroup) (g : Equiv.Perm (Fin 4))
    (hg : ∀ i : Fin 4, ρ (i.castAdd 2) = (g i).castAdd 2) :
    ∃ b : Bool, ρ = blockPerm g b := by
  let δ : RowGroup := (blockPerm g false)⁻¹ * ρ
  have hδ : ∀ i : Fin 4, δ (i.castAdd 2) = i.castAdd 2 := by
    intro i
    change (blockPerm g false)⁻¹ (ρ (i.castAdd 2)) = i.castAdd 2
    rw [hg i, blockPerm_inv, blockPerm_castAdd]
    simp
  obtain ⟨b, hb⟩ := permutation_fixing_four δ hδ
  refine ⟨b, ?_⟩
  calc
    ρ = blockPerm g false * δ := by dsimp [δ]; group
    _ = blockPerm g false * blockPerm 1 b := by rw [hb]
    _ = blockPerm g b := by rw [blockPerm_mul]; simp

theorem permutation_preserving_four (ρ : RowGroup)
    (hρ : ∀ i : Fin 4, (ρ (i.castAdd 2)).val < 4) :
    ∃ (g : Equiv.Perm (Fin 4)) (b : Bool), ρ = blockPerm g b := by
  let f : Fin 4 → Fin 4 := fun i => ⟨(ρ (i.castAdd 2)).val, hρ i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : ρ (i.castAdd 2) = ρ (j.castAdd 2) :=
      Fin.ext (congrArg (fun z : Fin 4 => z.val) hij)
    exact Fin.ext (congrArg (fun z : Fin 6 => z.val) (ρ.injective he))
  let g : Equiv.Perm (Fin 4) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hg : ∀ i : Fin 4, ρ (i.castAdd 2) = (g i).castAdd 2 := fun i => Fin.ext rfl
  obtain ⟨b, hb⟩ := permutation_eq_blockPerm_of_castAdd ρ g hg
  exact ⟨g, b, hb⟩

theorem state_eq_of_projections {u v : PairState}
    (ha : firstVertex u = firstVertex v) (hb : secondVertex u = secondVertex v) : u = v := by
  rcases u with ⟨σ, b⟩
  rcases v with ⟨τ, c⟩
  change σ = τ at ha
  subst τ
  have he : blockPerm 1 b = blockPerm 1 c := mul_left_cancel hb
  have hi := congrArg (fun p : RowGroup => p (4 : Fin 6)) he
  cases b <;> cases c <;> try rfl
  all_goals norm_num [blockPerm, liftPerm4_one, swap45] at hi

theorem exists_action_of_ordered_pairs_eq {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω υ : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4)
    (hA : matchingWords (firstVertex ∘ ω) = matchingWords (firstVertex ∘ υ))
    (hB : matchingWords (secondVertex ∘ ω) = matchingWords (secondVertex ∘ υ)) :
    ∃ h : PairGroup, h.2.ex = false ∧ ∀ c, h • ω c = υ c := by
  obtain ⟨ρ, hρ⟩ := exists_row_reindex hS (firstVertex ∘ ω) (firstVertex ∘ υ) hA
  obtain ⟨τ, hτ⟩ := exists_row_reindex hS (secondVertex ∘ ω) (secondVertex ∘ υ) hB
  have hρw (j : Fin 6) : matchingWord (firstVertex ∘ υ) j =
      matchingWord (firstVertex ∘ ω) (ρ j) := by
    funext c
    change firstVertex (υ c) j = firstVertex (ω c) (ρ j)
    exact congrArg (fun p : RowGroup => p j) (hρ c)
  have hτw (j : Fin 6) : matchingWord (secondVertex ∘ υ) j =
      matchingWord (secondVertex ∘ ω) (τ j) := by
    funext c
    change secondVertex (υ c) j = secondVertex (ω c) (τ j)
    exact congrArg (fun p : RowGroup => p j) (hτ c)
  have hρsmall (i : Fin 4) : (ρ (i.castAdd 2)).val < 4 := by
    apply (row_index_lt_four_iff_mem_other hS (firstVertex ∘ ω) (secondVertex ∘ ω)
      (common_word_eq ω) hcard _).mp
    rw [← hρw, common_word_eq υ i, hτw]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hτsmall (i : Fin 4) : (τ (i.castAdd 2)).val < 4 := by
    apply (row_index_lt_four_iff_mem_other hS (secondVertex ∘ ω) (firstVertex ∘ ω)
      (fun j => (common_word_eq ω j).symm) (by simpa [Finset.inter_comm] using hcard) _).mp
    rw [← hτw, ← common_word_eq υ i, hρw]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hsame (i : Fin 4) : ρ (i.castAdd 2) = τ (i.castAdd 2) := by
    apply matchingWord_injective hS (firstVertex ∘ ω)
    rw [← hρw, common_word_eq υ i, hτw]
    let j : Fin 4 := ⟨(τ (i.castAdd 2)).val, hτsmall i⟩
    have hj : j.castAdd 2 = τ (i.castAdd 2) := Fin.ext rfl
    rw [← hj]
    exact (common_word_eq ω j).symm
  obtain ⟨g, a, hp⟩ := permutation_preserving_four ρ hρsmall
  have hτg (i : Fin 4) : τ (i.castAdd 2) = (g i).castAdd 2 := by
    rw [← hsame i, hp, blockPerm_castAdd]
  obtain ⟨b, hq⟩ := permutation_eq_blockPerm_of_castAdd τ g hτg
  let h : PairGroup := (g⁻¹, ⟨a, b, false⟩)
  refine ⟨h, rfl, fun c => state_eq_of_projections ?_ ?_⟩
  · calc
      firstVertex (h • ω c) = firstVertex (ω c) * (blockPerm g⁻¹ a)⁻¹ := by
        simpa only [h, Bool.false_eq_true, ↓reduceIte, statePerm, Equiv.coe_fn_mk]
          using firstVertex_action h (ω c)
      _ = firstVertex (ω c) * ρ := by rw [blockPerm_inv, inv_inv, ← hp]
      _ = firstVertex (υ c) := (hρ c).symm
  · calc
      secondVertex (h • ω c) = secondVertex (ω c) * (blockPerm g⁻¹ b)⁻¹ := by
        simpa only [h, Bool.false_eq_true, ↓reduceIte, statePerm, Equiv.coe_fn_mk]
          using secondVertex_action h (ω c)
      _ = secondVertex (ω c) * τ := by rw [blockPerm_inv, inv_inv, ← hq]
      _ = secondVertex (υ c) := (hτ c).symm

def actLabels {S : Finset (Fin 15)} (h : PairGroup) (ω : S → PairState) : S → PairState :=
  fun c => h • ω c

def pairWords {S : Finset (Fin 15)} (ω : S → PairState) : Finset (Finset (S → Fin 6)) :=
  {matchingWords (firstVertex ∘ ω), matchingWords (secondVertex ∘ ω)}

theorem firstWords_action {S : Finset (Fin 15)} (h : PairGroup) (ω : S → PairState) :
    matchingWords (firstVertex ∘ actLabels h ω) =
      if h.2.ex then matchingWords (secondVertex ∘ ω) else matchingWords (firstVertex ∘ ω) := by
  cases he : h.2.ex
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hf : firstVertex ∘ actLabels h ω =
        fun c => (firstVertex ∘ ω) c * (blockPerm h.1 h.2.sa)⁻¹ := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk,
        he, Bool.false_eq_true, ↓reduceIte] using firstVertex_action h (ω c)
    rw [hf, matchingWords_reindex]
  · simp only [↓reduceIte]
    have hf : firstVertex ∘ actLabels h ω =
        fun c => (secondVertex ∘ ω) c * (blockPerm h.1 h.2.sb)⁻¹ := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk,
        he, ↓reduceIte] using firstVertex_action h (ω c)
    rw [hf, matchingWords_reindex]

theorem secondWords_action {S : Finset (Fin 15)} (h : PairGroup) (ω : S → PairState) :
    matchingWords (secondVertex ∘ actLabels h ω) =
      if h.2.ex then matchingWords (firstVertex ∘ ω) else matchingWords (secondVertex ∘ ω) := by
  cases he : h.2.ex
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hf : secondVertex ∘ actLabels h ω =
        fun c => (secondVertex ∘ ω) c * (blockPerm h.1 h.2.sb)⁻¹ := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk,
        he, Bool.false_eq_true, ↓reduceIte] using secondVertex_action h (ω c)
    rw [hf, matchingWords_reindex]
  · simp only [↓reduceIte]
    have hf : secondVertex ∘ actLabels h ω =
        fun c => (firstVertex ∘ ω) c * (blockPerm h.1 h.2.sa)⁻¹ := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk,
        he, ↓reduceIte] using secondVertex_action h (ω c)
    rw [hf, matchingWords_reindex]

theorem pairWords_action {S : Finset (Fin 15)} (h : PairGroup) (ω : S → PairState) :
    pairWords (actLabels h ω) = pairWords ω := by
  unfold pairWords
  rw [firstWords_action, secondWords_action]
  cases h.2.ex <;> simp [Finset.pair_comm]

theorem exists_action_of_unordered_pairs_eq {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω υ : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4)
    (he : pairWords ω = pairWords υ) :
    ∃ h : PairGroup, ∀ c, h • ω c = υ c := by
  have hs := congrArg (fun t : Finset (Finset (S → Fin 6)) => (t : Set (Finset (S → Fin 6)))) he
  have hp : ({matchingWords (firstVertex ∘ ω), matchingWords (secondVertex ∘ ω)} :
      Set (Finset (S → Fin 6))) =
      {matchingWords (firstVertex ∘ υ), matchingWords (secondVertex ∘ υ)} := by
    simpa only [pairWords, Finset.coe_insert, Finset.coe_singleton] using hs
  rcases Set.pair_eq_pair_iff.mp hp with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · obtain ⟨h, _, hh⟩ := exists_action_of_ordered_pairs_eq hS ω υ hcard hA hB
    exact ⟨h, hh⟩
  · let s : PairGroup := (1, tau0)
    have hA' : matchingWords (firstVertex ∘ ω) =
        matchingWords (firstVertex ∘ actLabels s υ) := by
      rw [firstWords_action]
      simpa only [s, tau0, ↓reduceIte] using hA
    have hB' : matchingWords (secondVertex ∘ ω) =
        matchingWords (secondVertex ∘ actLabels s υ) := by
      rw [secondWords_action]
      simpa only [s, tau0, ↓reduceIte] using hB
    obtain ⟨h, _, hh⟩ := exists_action_of_ordered_pairs_eq hS ω (actLabels s υ) hcard hA' hB'
    refine ⟨s⁻¹ * h, fun c => ?_⟩
    rw [mul_smul, hh c]
    exact inv_smul_smul s (υ c)

theorem stabilizer_eq_one {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4)
    (h : PairGroup) (hh : ∀ c, h • ω c = ω c) : h = 1 := by
  obtain ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩⟩ :=
    PairIntersection.mixed_of_intersection_card_four hS ω hcard
  have h₀ : h.1 = 1 ∧ (h.2 = 1 ∨ h.2 = tau0) := by
    simpa only [hc₀, Bool.false_eq_true, false_and, true_and, or_false] using
      (stabilizer_PairState_iff h (ω c₀)).mp (hh c₀)
  have h₁ : h.1 = 1 ∧ (h.2 = 1 ∨ h.2 = tau1) := by
    simpa only [hc₁, Bool.true_eq_false, false_and, true_and, false_or] using
      (stabilizer_PairState_iff h (ω c₁)).mp (hh c₁)
  apply Prod.ext h₀.1
  change h.2 = 1
  rcases h₀.2 with he | he
  · exact he
  · rcases h₁.2 with hf | hf
    · exact hf
    · exact False.elim ((by decide : tau0 ≠ tau1) (he.symm.trans hf))

theorem action_injective {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4)
    (h g : PairGroup) (he : ∀ c, h • ω c = g • ω c) : h = g := by
  have hs : g⁻¹ * h = 1 := stabilizer_eq_one hS ω hcard _ (fun c => by
    rw [mul_smul, he c, inv_smul_smul])
  calc
    h = g * (g⁻¹ * h) := by group
    _ = g := by rw [hs, mul_one]

/-- Actual labels over one unordered critical matching pair form a free,
transitive `PairGroup`-orbit. -/
theorem existsUnique_action_of_unordered_pairs_eq {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω υ : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4)
    (he : pairWords ω = pairWords υ) :
    ∃! h : PairGroup, ∀ c, h • ω c = υ c := by
  obtain ⟨h, hh⟩ := exists_action_of_unordered_pairs_eq hS ω υ hcard he
  refine ⟨h, hh, fun g hg => ?_⟩
  exact action_injective hS ω hcard g h (fun c => (hg c).trans (hh c).symm)

theorem pairWords_eq_iff_exists_action {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω υ : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4) :
    pairWords ω = pairWords υ ↔ ∃ h : PairGroup, ∀ c, h • ω c = υ c := by
  constructor
  · exact exists_action_of_unordered_pairs_eq hS ω υ hcard
  · rintro ⟨h, hh⟩
    have hu : υ = actLabels h ω := funext fun c => (hh c).symm
    rw [hu, pairWords_action]

abbrev LabelsOverPair {S : Finset (Fin 15)} (ω : S → PairState) :=
  {υ : S → PairState // pairWords υ = pairWords ω}

def labelsOverPairEquiv {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4) :
    PairGroup ≃ LabelsOverPair ω := by
  refine Equiv.ofBijective
    (fun h : PairGroup => (⟨actLabels h ω, pairWords_action h ω⟩ : LabelsOverPair ω)) ⟨?_, ?_⟩
  · intro h g hh
    apply action_injective hS ω hcard h g
    intro c
    exact congrFun (congrArg (fun z : LabelsOverPair ω => (z : S → PairState)) hh) c
  · intro υ
    obtain ⟨h, hh⟩ := exists_action_of_unordered_pairs_eq hS ω υ.1 hcard υ.2.symm
    exact ⟨h, Subtype.ext (funext hh)⟩

theorem card_labelsOverPair {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hcard : (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4) :
    Fintype.card (LabelsOverPair ω) = 192 :=
  (Fintype.card_congr (labelsOverPairEquiv hS ω hcard)).symm.trans card_PairGroup


end AkopyanResearch.PairOrbit
