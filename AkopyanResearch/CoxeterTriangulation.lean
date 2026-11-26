module

public import AkopyanResearch.RowSylowGeometry
public import AkopyanResearch.CoxeterChamber
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Covering.FundamentalGroupCircle

@[expose] public section

/-!
# Coxeter chains, codimension-2 sphere complements, exact strata, and circle degree

1. Avoiding finitely many proper subspaces (`exists_notMem_biUnion_proper_subspaces`) and
   path-connectivity of the complement of finitely many codimension `≥ 2` subspaces in a sphere
   (`pathConnected_sphere_diff_finite_codim2`).
2. Superlevel flags `superlevelChain` and join flags `joinChain` on `Rep10`, proving both
   elementwise and setwise invariance equivalence with `perm10 g x = x` (`perm10_fixes_joinChain_iff`).
3. Complex structure `ComplexFixed K` on every fixed subspace `fixedSubspace K` via `J10`,
   proving every strict inclusion `fixedSubspace K < fixedSubspace H` has codimension `≥ 2`,
   and concluding `IsPathConnected (exactStratum H)` for all `H ≤ P_row`.
4. Winding-number degree `circleDegree` on `AddCircle (2 * Real.pi)` and `fixedP_rowDegree`
   on `FixedP_row`, descending path-homotopy of loops to based `HomotopicRel` of maps.
-/

noncomputable section

open scoped BigOperators InnerProductSpace Classical unitInterval
open Metric Set Topology

namespace AkopyanResearch

/-! ### 1. Avoiding finite unions of proper subspaces and codimension-2 complements -/

section ProperSubspaces

theorem exists_notMem_biUnion_proper_subspaces {k E ι : Type*}
    [Field k] [Infinite k] [AddCommGroup E] [Module k E]
    (s : Finset ι) (W : ι → Submodule k E) (hW : ∀ i ∈ s, W i ≠ ⊤) :
    ∃ x : E, ∀ i ∈ s, x ∉ W i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert j s hj ih =>
    have hWs : ∀ i ∈ s, W i ≠ ⊤ := fun i hi => hW i (Finset.mem_insert_of_mem hi)
    obtain ⟨x, hx⟩ := ih hWs
    by_cases hxj : x ∉ W j
    · refine ⟨x, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact hxj
      · exact hx i his
    · rw [not_not] at hxj
      have hjtop : W j ≠ ⊤ := hW j (Finset.mem_insert_self j s)
      have hyex : ∃ y : E, y ∉ W j := by
        by_contra h
        push Not at h
        apply hjtop
        ext y
        simp [h y]
      obtain ⟨y, hyj⟩ := hyex
      let bad : ι → Finset k := fun i =>
        if h : ∃ c : k, x + c • y ∈ W i then {h.choose} else ∅
      let B : Finset k := insert 0 (s.biUnion bad)
      obtain ⟨c, hcB⟩ := Infinite.exists_notMem_finset B
      have hc0 : c ≠ 0 := fun hc => hcB (by simp [B, hc])
      refine ⟨x + c • y, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with hij | his
      · subst hij
        intro hmem
        have hcy : c • y ∈ W i := by
          have : c • y = (x + c • y) - x := by abel
          rw [this]
          exact (W i).sub_mem hmem hxj
        exact hyj (by simpa [hc0] using (W i).smul_mem c⁻¹ hcy)
      · intro hmem
        have hex : ∃ c' : k, x + c' • y ∈ W i := ⟨c, hmem⟩
        let c₀ : k := hex.choose
        have hc₀mem : x + c₀ • y ∈ W i := hex.choose_spec
        have hc₀in : c₀ ∈ bad i := by simp [bad, hex, c₀]
        have hcc₀ : c ≠ c₀ := fun h => hcB (by
          apply Finset.mem_insert_of_mem
          exact Finset.mem_biUnion.mpr ⟨i, his, h ▸ hc₀in⟩)
        have hdiff : c - c₀ ≠ 0 := sub_ne_zero.mpr hcc₀
        have hyi : (c - c₀) • y ∈ W i := by
          have : (c - c₀) • y = (x + c • y) - (x + c₀ • y) := by
            rw [sub_smul]; abel
          rw [this]
          exact (W i).sub_mem hmem hc₀mem
        have hyW : y ∈ W i := by
          simpa [hdiff] using (W i).smul_mem (c - c₀)⁻¹ hyi
        have hxW : x ∈ W i := by
          have : x = (x + c • y) - c • y := by abel
          rw [this]
          exact (W i).sub_mem hmem ((W i).smul_mem c hyW)
        exact hx i his hxW

theorem exists_unit_notMem_biUnion_proper_subspaces {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hpos : 0 < Module.finrank ℝ E)
    (s : Finset ι) (W : ι → Submodule ℝ E) (hW : ∀ i ∈ s, W i ≠ ⊤) :
    ∃ x : Metric.sphere (0 : E) 1, ∀ i ∈ s, x.1 ∉ W i := by
  by_cases hs : s = ∅
  · subst hs
    have hnt : Nontrivial E := Module.finrank_pos_iff.mp hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨⟨‖v‖⁻¹ • v, ?_⟩, by simp⟩
    simp [norm_smul, norm_ne_zero_iff.mpr hv]
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨v, hv⟩ := exists_notMem_biUnion_proper_subspaces s W hW
    have hv0 : v ≠ 0 := fun h => hv i₀ hi₀ (h ▸ (W i₀).zero_mem)
    refine ⟨⟨‖v‖⁻¹ • v, ?_⟩, fun i hi hmem => hv i hi ?_⟩
    · simp [norm_smul, norm_ne_zero_iff.mpr hv0]
    · simpa [norm_ne_zero_iff.mpr hv0] using (W i).smul_mem ‖v‖ hmem

private lemma joinedIn_chord {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (W : ι → Submodule ℝ E)
    {u v : Metric.sphere (0 : E) 1}
    (hu : ∀ i ∈ s, u.1 ∉ W i)
    (hv_span : v.1 ∉ (ℝ ∙ u.1))
    (hv_sup : ∀ i ∈ s, v.1 ∉ W i ⊔ (ℝ ∙ u.1)) :
    JoinedIn {x : Metric.sphere (0 : E) 1 | ∀ i ∈ s, x.1 ∉ W i} u v := by
  let chord : I → E := fun t => (1 - (t : ℝ)) • u.1 + (t : ℝ) • v.1
  have hchord_ne : ∀ t : I, chord t ≠ 0 := by
    intro t h0
    by_cases ht0 : (t : ℝ) = 0
    · have hu0 : u.1 = 0 := by simpa [chord, ht0] using h0
      have hnorm := mem_sphere_zero_iff_norm.mp u.2
      simp [hu0] at hnorm
    · apply hv_span
      have hvm : v.1 = (-(1 - (t : ℝ)) / (t : ℝ)) • u.1 := by
        have h1 : (t : ℝ) • v.1 = -(1 - (t : ℝ)) • u.1 := by
          have : (1 - (t : ℝ)) • u.1 + (t : ℝ) • v.1 = 0 := h0
          rw [neg_smul]
          exact eq_neg_of_add_eq_zero_right this
        calc
          v.1 = (t : ℝ)⁻¹ • ((t : ℝ) • v.1) := by
            rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
          _ = (t : ℝ)⁻¹ • (-(1 - (t : ℝ)) • u.1) := by rw [h1]
          _ = (-(1 - (t : ℝ)) / (t : ℝ)) • u.1 := by
            rw [smul_smul]
            congr 1
            ring
      rw [hvm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u.1))
  have hcont_chord : Continuous chord := by
    dsimp only [chord]
    fun_prop
  let γFun : I → Metric.sphere (0 : E) 1 := fun t =>
    ⟨‖chord t‖⁻¹ • chord t, by
      simp [norm_smul, norm_ne_zero_iff.mpr (hchord_ne t)]⟩
  have hcont_γ : Continuous γFun := by
    refine Continuous.subtype_mk ?_ _
    exact (Continuous.inv₀ hcont_chord.norm fun t => norm_ne_zero_iff.mpr (hchord_ne t)).smul
      hcont_chord
  let γ : Path u v :=
    { toFun := γFun
      continuous_toFun := hcont_γ
      source' := by
        ext
        have hu1 : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
        simp [γFun, chord, hu1]
      target' := by
        ext
        have hv1 : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
        simp [γFun, chord, hv1] }
  refine ⟨γ, fun t i hi hmem => ?_⟩
  have hmem' : ‖chord t‖⁻¹ • chord t ∈ W i := hmem
  have hchord_mem : chord t ∈ W i := by
    have hsm := (W i).smul_mem ‖chord t‖ hmem'
    rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hchord_ne t)), one_smul] at hsm
  by_cases ht0 : (t : ℝ) = 0
  · apply hu i hi
    simpa [chord, ht0] using hchord_mem
  · apply hv_sup i hi
    have htv : (t : ℝ) • v.1 ∈ W i ⊔ (ℝ ∙ u.1) := by
      have h1 : chord t ∈ W i ⊔ (ℝ ∙ u.1) := Submodule.mem_sup_left hchord_mem
      have h2 : (1 - (t : ℝ)) • u.1 ∈ W i ⊔ (ℝ ∙ u.1) :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u.1)))
      have hsub : (t : ℝ) • v.1 = chord t - (1 - (t : ℝ)) • u.1 := by
        dsimp only [chord]; abel
      rw [hsub]
      exact (W i ⊔ (ℝ ∙ u.1)).sub_mem h1 h2
    simpa [ht0] using (W i ⊔ (ℝ ∙ u.1)).smul_mem (t : ℝ)⁻¹ htv

theorem pathConnected_sphere_diff_finite_codim2 {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (s : Finset ι) (W : ι → Submodule ℝ E)
    (hcodim : ∀ i ∈ s, Module.finrank ℝ (W i) + 2 ≤ Module.finrank ℝ E) :
    IsPathConnected {x : Metric.sphere (0 : E) 1 | ∀ i ∈ s, x.1 ∉ W i} := by
  have hW_proper : ∀ i ∈ s, W i ≠ ⊤ := by
    intro i hi htop
    have hc := hcodim i hi
    rw [htop, finrank_top] at hc
    omega
  have hpos : 0 < Module.finrank ℝ E := by omega
  obtain ⟨x₀, hx₀⟩ := exists_unit_notMem_biUnion_proper_subspaces hpos s W hW_proper
  refine ⟨x₀, hx₀, fun {y} hy => ?_⟩
  let x := x₀
  have hx := hx₀
  let ι' := Sum Bool (Bool × ι)
  let s' : Finset ι' :=
    insert (Sum.inl false) (insert (Sum.inl true)
      ((s.image fun i => Sum.inr (false, i)) ∪ (s.image fun i => Sum.inr (true, i))))
  let W' : ι' → Submodule ℝ E := fun
    | Sum.inl false => ℝ ∙ x.1
    | Sum.inl true => ℝ ∙ y.1
    | Sum.inr (false, i) => W i ⊔ (ℝ ∙ x.1)
    | Sum.inr (true, i) => W i ⊔ (ℝ ∙ y.1)
  have hspan_le : ∀ v : E, Module.finrank ℝ ↥(ℝ ∙ v) ≤ 1 := by
    intro v
    by_cases hv : v = 0
    · rw [hv, show (ℝ ∙ (0 : E)) = ⊥ from Submodule.span_eq_bot.mpr (by simp), finrank_bot]
      omega
    · simp [finrank_span_singleton hv]
  have hsup_proper : ∀ i ∈ s, ∀ v : E, W i ⊔ (ℝ ∙ v) ≠ ⊤ := by
    intro i hi v htop
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W i) (ℝ ∙ v)
    have h2 : Module.finrank ℝ ↥(W i ⊔ (ℝ ∙ v)) = Module.finrank ℝ E := by
      rw [htop, finrank_top]
    have h3 := hcodim i hi
    have h4 := hspan_le v
    omega
  have hW'_proper : ∀ a ∈ s', W' a ≠ ⊤ := by
    intro a ha
    rcases a with b | ⟨b, i⟩
    · cases b <;> intro htop
      · have hle := hspan_le x.1
        change (ℝ ∙ x.1) = ⊤ at htop
        rw [htop, finrank_top] at hle
        omega
      · have hle := hspan_le y.1
        change (ℝ ∙ y.1) = ⊤ at htop
        rw [htop, finrank_top] at hle
        omega
    · have hi : i ∈ s := by
        rcases Finset.mem_insert.mp ha with h | h
        · cases h
        · rcases Finset.mem_insert.mp h with h | h
          · cases h
          · rcases Finset.mem_union.mp h with h | h <;>
              rcases Finset.mem_image.mp h with ⟨j, hj, hj_eq⟩ <;>
              cases hj_eq <;> exact hj
      cases b
      · exact hsup_proper i hi x.1
      · exact hsup_proper i hi y.1
  obtain ⟨z, hz⟩ := exists_notMem_biUnion_proper_subspaces s' W' hW'_proper
  have hzx : z ∉ ℝ ∙ x.1 := hz (Sum.inl false) (by simp [s'])
  have hzy : z ∉ ℝ ∙ y.1 := hz (Sum.inl true) (by simp [s'])
  have hz0 : z ≠ 0 := fun h0 => hzx (h0 ▸ (ℝ ∙ x.1).zero_mem)
  let w : Metric.sphere (0 : E) 1 := ⟨‖z‖⁻¹ • z, by
    simp [norm_smul, norm_ne_zero_iff.mpr hz0]⟩
  have hwx : w.1 ∉ ℝ ∙ x.1 := fun hmem =>
    hzx (by simpa [w, norm_ne_zero_iff.mpr hz0] using (ℝ ∙ x.1).smul_mem ‖z‖ hmem)
  have hwy : w.1 ∉ ℝ ∙ y.1 := fun hmem =>
    hzy (by simpa [w, norm_ne_zero_iff.mpr hz0] using (ℝ ∙ y.1).smul_mem ‖z‖ hmem)
  have hwx_sup : ∀ i ∈ s, w.1 ∉ W i ⊔ (ℝ ∙ x.1) := by
    intro i hi hmem
    apply hz (Sum.inr (false, i)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi))))
    simpa [W', w, norm_ne_zero_iff.mpr hz0] using (W i ⊔ (ℝ ∙ x.1)).smul_mem ‖z‖ hmem
  have hwy_sup : ∀ i ∈ s, w.1 ∉ W i ⊔ (ℝ ∙ y.1) := by
    intro i hi hmem
    apply hz (Sum.inr (true, i)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))))
    simpa [W', w, norm_ne_zero_iff.mpr hz0] using (W i ⊔ (ℝ ∙ y.1)).smul_mem ‖z‖ hmem
  exact (joinedIn_chord s W hx hwx hwx_sup).trans (joinedIn_chord s W hy hwy hwy_sup).symm

end ProperSubspaces

/-! ### 2. Coxeter superlevel chains and join chains on `Rep10` -/

section JoinChains

def left6 (x : Rep10) : Fin 6 → ℝ :=
  fun i => (iso10.symm x).1 (i.castAdd 6)

def right6 (x : Rep10) : Fin 6 → ℝ :=
  fun i => (iso10.symm x).1 (Fin.natAdd 6 i)

def superlevelChain (u : Fin 6 → ℝ) : Finset (Finset (Fin 6)) :=
  ((Finset.univ.image u).image (fun r => Finset.univ.filter (fun i => r ≤ u i))).erase Finset.univ

def joinChain (x : Rep10) : Finset (Finset (Fin 6)) × Finset (Finset (Fin 6)) :=
  (superlevelChain (left6 x), superlevelChain (right6 x))

lemma isChain_superlevelChain (u : Fin 6 → ℝ) :
    ∀ A ∈ superlevelChain u, ∀ B ∈ superlevelChain u, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hA) with ⟨r₁, _, rfl⟩
  rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hB) with ⟨r₂, _, rfl⟩
  rcases le_total r₁ r₂ with h12 | h21
  · right
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans h12 hi
  · left
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans h21 hi

lemma chain_image_eq_iff (C : Finset (Finset (Fin 6)))
    (hC : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) (g : Equiv.Perm (Fin 6)) :
    C.image (Finset.image g) = C ↔ ∀ A ∈ C, A.image g = A := by
  constructor
  · intro hset A hA
    have himg : A.image g ∈ C := hset ▸ Finset.mem_image_of_mem _ hA
    have hcard : (A.image g).card = A.card := Finset.card_image_of_injective A g.injective
    rcases hC (A.image g) himg A hA with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    · exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)).symm
  · intro hel
    ext B
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨A, hA, rfl⟩
      rwa [hel A hA]
    · intro hB
      exact ⟨B, hB, hel B hB⟩

lemma comp_inv_eq_iff_superlevelChain (u : Fin 6 → ℝ) (g : Equiv.Perm (Fin 6)) :
    (∀ i : Fin 6, u (g⁻¹ i) = u i) ↔ ∀ A ∈ superlevelChain u, A.image g = A := by
  constructor
  · intro hu A hA
    rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hA) with ⟨r, _, rfl⟩
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hgu : u i = u (g i) := by simpa using hu (g i)
      rw [← hgu]
      exact hi
    · intro hj
      refine ⟨g⁻¹ j, ?_, by simp⟩
      rwa [hu j]
  · intro hA i
    have h_univ : (Finset.univ : Finset (Fin 6)).image g = Finset.univ := by
      ext j
      simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
      exact ⟨g⁻¹ j, by simp⟩
    have hF : ∀ k : Fin 6,
        (Finset.univ.filter (fun j => u k ≤ u j)).image g =
          Finset.univ.filter (fun j => u k ≤ u j) := by
      intro k
      let F := Finset.univ.filter (fun j => u k ≤ u j)
      by_cases hFu : F = Finset.univ
      · change F.image g = F
        rw [hFu, h_univ]
      · exact hA F (Finset.mem_erase.mpr
          ⟨hFu, Finset.mem_image.mpr ⟨u k, Finset.mem_image_of_mem u (Finset.mem_univ k), rfl⟩⟩)
    have h1 : u i ≤ u (g⁻¹ i) := by
      have hi_mem : i ∈ Finset.univ.filter (fun j => u i ≤ u j) := by simp
      rw [← hF i] at hi_mem
      rcases Finset.mem_image.mp hi_mem with ⟨a, ha, ha_eq⟩
      have ha' : a = g⁻¹ i := by rw [← ha_eq]; simp
      subst ha'
      simpa using ha
    have h2 : u (g⁻¹ i) ≤ u i := by
      have hgi_mem : g⁻¹ i ∈ Finset.univ.filter (fun j => u (g⁻¹ i) ≤ u j) := by simp
      have hi_img : i ∈ (Finset.univ.filter (fun j => u (g⁻¹ i) ≤ u j)).image g :=
        Finset.mem_image.mpr ⟨g⁻¹ i, hgi_mem, by simp⟩
      rw [hF (g⁻¹ i)] at hi_img
      simpa using hi_img
    exact le_antisymm h2 h1

theorem perm10_fixes_joinChain_elementwise_iff (g : Equiv.Perm (Fin 6)) (x : Rep10) :
    perm10 g x = x ↔
      (∀ A ∈ (joinChain x).1, A.image g = A) ∧
      (∀ B ∈ (joinChain x).2, B.image g = B) := by
  have hperm : perm10 g x = x ↔ permSub g (iso10.symm x) = iso10.symm x := by
    constructor
    · intro h
      apply iso10.injective
      simpa [perm10] using h
    · intro h
      change iso10 (permSub g (iso10.symm x)) = x
      rw [h, iso10.apply_symm_apply]
  rw [hperm, permSub_eq_self_iff]
  change ((∀ i : Fin 6, left6 x (g⁻¹ i) = left6 x i) ∧
      (∀ i : Fin 6, right6 x (g⁻¹ i) = right6 x i)) ↔
    (∀ A ∈ superlevelChain (left6 x), A.image g = A) ∧
    (∀ B ∈ superlevelChain (right6 x), B.image g = B)
  rw [comp_inv_eq_iff_superlevelChain (left6 x) g,
    comp_inv_eq_iff_superlevelChain (right6 x) g]

theorem perm10_fixes_joinChain_iff (g : Equiv.Perm (Fin 6)) (x : Rep10) :
    perm10 g x = x ↔
      (joinChain x).1.image (Finset.image g) = (joinChain x).1 ∧
      (joinChain x).2.image (Finset.image g) = (joinChain x).2 := by
  rw [perm10_fixes_joinChain_elementwise_iff,
    chain_image_eq_iff (joinChain x).1 (isChain_superlevelChain (left6 x)) g,
    chain_image_eq_iff (joinChain x).2 (isChain_superlevelChain (right6 x)) g]

end JoinChains

/-! ### 3. Complex structure on `fixedSubspace K` and exact strata -/

section ExactStrata

structure ComplexFixed (K : Subgroup (Equiv.Perm (Fin 6))) where
  val : fixedSubspace K

namespace ComplexFixed

variable {K : Subgroup (Equiv.Perm (Fin 6))}

@[ext] lemma ext {x y : ComplexFixed K} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp only at h; subst h; rfl

instance : Add (ComplexFixed K) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Zero (ComplexFixed K) := ⟨⟨0⟩⟩
instance : Neg (ComplexFixed K) := ⟨fun x => ⟨-x.val⟩⟩
instance : Sub (ComplexFixed K) := ⟨fun x y => ⟨x.val - y.val⟩⟩
instance : SMul ℕ (ComplexFixed K) := ⟨fun n x => ⟨n • x.val⟩⟩
instance : SMul ℤ (ComplexFixed K) := ⟨fun n x => ⟨n • x.val⟩⟩
instance : SMul ℝ (ComplexFixed K) := ⟨fun r x => ⟨r • x.val⟩⟩

instance : AddCommGroup (ComplexFixed K) where
  add_assoc a b c := ComplexFixed.ext (add_assoc a.val b.val c.val)
  zero_add a := ComplexFixed.ext (zero_add a.val)
  add_zero a := ComplexFixed.ext (add_zero a.val)
  nsmul := nsmulRec
  neg_add_cancel a := ComplexFixed.ext (neg_add_cancel a.val)
  zsmul := zsmulRec
  sub_eq_add_neg a b := ComplexFixed.ext (sub_eq_add_neg a.val b.val)
  add_comm a b := ComplexFixed.ext (add_comm a.val b.val)

instance : Module ℝ (ComplexFixed K) where
  smul_zero r := ComplexFixed.ext (smul_zero r)
  smul_add r a b := ComplexFixed.ext (smul_add r a.val b.val)
  add_smul r s a := ComplexFixed.ext (add_smul r s a.val)
  zero_smul a := ComplexFixed.ext (zero_smul ℝ a.val)
  one_smul a := ComplexFixed.ext (one_smul ℝ a.val)
  mul_smul r s a := ComplexFixed.ext (mul_smul r s a.val)

def jOp (x : ComplexFixed K) : ComplexFixed K :=
  ⟨⟨J10 x.val.1, J10_mem_fixedSubspace x.val.2⟩⟩

@[simp] lemma jOp_jOp (x : ComplexFixed K) : jOp (jOp x) = -x := by
  apply ComplexFixed.ext
  apply Subtype.ext
  exact J10_J10 x.val.1

@[simp] lemma jOp_add (x y : ComplexFixed K) : jOp (x + y) = jOp x + jOp y := by
  apply ComplexFixed.ext
  apply Subtype.ext
  exact map_add J10 x.val.1 y.val.1

@[simp] lemma jOp_smul (r : ℝ) (x : ComplexFixed K) : jOp (r • x) = r • jOp x := by
  apply ComplexFixed.ext
  apply Subtype.ext
  exact map_smul J10 r x.val.1

instance : SMul ℂ (ComplexFixed K) :=
  ⟨fun z x => z.re • x + z.im • jOp x⟩

lemma smul_complex_def (z : ℂ) (x : ComplexFixed K) :
    z • x = z.re • x + z.im • jOp x := rfl

instance : Module ℂ (ComplexFixed K) where
  one_smul x := by simp [smul_complex_def]
  mul_smul z w x := by
    simp only [smul_complex_def, Complex.mul_re, Complex.mul_im, smul_add,
      jOp_add, jOp_smul, jOp_jOp, smul_smul, smul_neg]
    module
  smul_zero z := by
    apply ComplexFixed.ext
    apply Subtype.ext
    change z.re • (0 : Rep10) + z.im • J10 0 = 0
    simp
  smul_add z x y := by
    simp only [smul_complex_def, jOp_add, smul_add]
    abel
  add_smul z w x := by
    simp only [smul_complex_def, Complex.add_re, Complex.add_im, add_smul]
    abel
  zero_smul x := by simp [smul_complex_def]

instance : IsScalarTower ℝ ℂ (ComplexFixed K) where
  smul_assoc r z x := by
    simp only [smul_complex_def, Complex.smul_re, Complex.smul_im, smul_eq_mul,
      smul_add, smul_smul]

def equivFixedSubspace (K : Subgroup (Equiv.Perm (Fin 6))) :
    ComplexFixed K ≃ₗ[ℝ] fixedSubspace K where
  toFun := ComplexFixed.val
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : FiniteDimensional ℝ (ComplexFixed K) :=
  (equivFixedSubspace K).symm.finiteDimensional

end ComplexFixed

theorem finrank_fixedSubspace_eq_two_mul (K : Subgroup (Equiv.Perm (Fin 6))) :
    Module.finrank ℝ (fixedSubspace K) = 2 * Module.finrank ℂ (ComplexFixed K) := by
  rw [← (ComplexFixed.equivFixedSubspace K).finrank_eq,
    ← Module.finrank_mul_finrank ℝ ℂ (ComplexFixed K), Complex.finrank_real_complex]

theorem even_finrank_fixedSubspace (K : Subgroup (Equiv.Perm (Fin 6))) :
    Even (Module.finrank ℝ (fixedSubspace K)) := by
  refine ⟨Module.finrank ℂ (ComplexFixed K), ?_⟩
  rw [finrank_fixedSubspace_eq_two_mul, two_mul]

theorem finrank_fixedSubspace_add_two_le_of_lt {K H : Subgroup (Equiv.Perm (Fin 6))}
    (hlt : fixedSubspace K < fixedSubspace H) :
    Module.finrank ℝ (fixedSubspace K) + 2 ≤ Module.finrank ℝ (fixedSubspace H) := by
  have hrank : Module.finrank ℝ (fixedSubspace K) < Module.finrank ℝ (fixedSubspace H) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨m, hm⟩ := even_finrank_fixedSubspace K
  obtain ⟨n, hn⟩ := even_finrank_fixedSubspace H
  omega

def exactStratum (H : Subgroup (Equiv.Perm (Fin 6))) : Set (Metric.sphere (0 : Rep10) 1) :=
  {x | x.1 ∈ fixedSubspace H ∧
    ∀ K : Subgroup (Equiv.Perm (Fin 6)), fixedSubspace K < fixedSubspace H → x.1 ∉ fixedSubspace K}

theorem isPathConnected_exactStratum_of_two_le {H : Subgroup (Equiv.Perm (Fin 6))}
    (hdim : 2 ≤ Module.finrank ℝ (fixedSubspace H)) :
    IsPathConnected (exactStratum H) := by
  have : Finite (Subgroup (Equiv.Perm (Fin 6))) :=
    Finite.of_injective (fun K : Subgroup (Equiv.Perm (Fin 6)) => (K : Set (Equiv.Perm (Fin 6))))
      SetLike.coe_injective
  let badK : Finset (Subgroup (Equiv.Perm (Fin 6))) :=
    (Set.toFinite {K : Subgroup (Equiv.Perm (Fin 6)) | fixedSubspace K < fixedSubspace H}).toFinset
  let W : Subgroup (Equiv.Perm (Fin 6)) → Submodule ℝ (fixedSubspace H) :=
    fun K => (fixedSubspace K).comap (fixedSubspace H).subtype
  have hcodim : ∀ K ∈ badK, Module.finrank ℝ (W K) + 2 ≤ Module.finrank ℝ (fixedSubspace H) := by
    intro K hK
    have hlt : fixedSubspace K < fixedSubspace H := by
      simpa [badK] using hK
    have hle : fixedSubspace K ≤ fixedSubspace H := le_of_lt hlt
    let eK : W K ≃ₗ[ℝ] fixedSubspace K :=
      { toFun := fun v => ⟨v.1.1, Submodule.mem_comap.mp v.2⟩
        invFun := fun v => ⟨⟨v.1, hle v.2⟩, Submodule.mem_comap.mpr v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [eK.finrank_eq]
    exact finrank_fixedSubspace_add_two_le_of_lt hlt
  have hpc := pathConnected_sphere_diff_finite_codim2 hdim badK W hcodim
  let toSphere : Metric.sphere (0 : fixedSubspace H) 1 → Metric.sphere (0 : Rep10) 1 :=
    fun v => ⟨v.1.1, mem_sphere_zero_iff_norm.mpr (mem_sphere_zero_iff_norm.mp v.2)⟩
  have hcont : Continuous toSphere :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : toSphere '' {x : Metric.sphere (0 : fixedSubspace H) 1 | ∀ K ∈ badK, x.1 ∉ W K} =
      exactStratum H := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.1.2, fun K hlt hmem => hv K ?_ ?_⟩
      · simpa [badK] using hlt
      · exact Submodule.mem_comap.mpr hmem
    · rintro ⟨hxH, hxK⟩
      refine ⟨⟨⟨x.1, hxH⟩, mem_sphere_zero_iff_norm.mpr (mem_sphere_zero_iff_norm.mp x.2)⟩, ?_, rfl⟩
      intro K hK hmem
      have hlt : fixedSubspace K < fixedSubspace H := by
        simpa [badK] using hK
      exact hxK K hlt (Submodule.mem_comap.mp hmem)
  rw [← himg]
  exact hpc.image' hcont.continuousOn

theorem isPathConnected_exactStratum {H : Subgroup (Equiv.Perm (Fin 6))} (hH : H ≤ P_row) :
    IsPathConnected (exactStratum H) :=
  isPathConnected_exactStratum_of_two_le (two_le_finrank_fixedSubspace hH)

end ExactStrata

/-! ### 4. Circle degree and based `HomotopicRel` on `AddCircle (2 * Real.pi)` and `FixedP_row` -/

section CircleDegree

def coxeterHomToCont {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) :
    C(α, β) :=
  ⟨e, e.continuous⟩

def circleBaseLoop (x₀ : ℝ) : Path (x₀ : AddCircle (2 * Real.pi)) x₀ :=
  AddCircle.zsmulLoop (2 * Real.pi) x₀ 1

lemma circleBaseLoop_apply (x₀ : ℝ) (t : I) :
    circleBaseLoop x₀ t = (((t : ℝ) * (2 * Real.pi) + x₀ : ℝ) : AddCircle (2 * Real.pi)) := by
  simp [circleBaseLoop, AddCircle.zsmulLoop_apply]

def loopOfCircleMap (x₀ : ℝ)
    (f : C(AddCircle (2 * Real.pi), AddCircle (2 * Real.pi)))
    (hf : f (x₀ : AddCircle (2 * Real.pi)) = (x₀ : AddCircle (2 * Real.pi))) :
    Path (x₀ : AddCircle (2 * Real.pi)) x₀ :=
  ((circleBaseLoop x₀).map f.continuous).cast hf.symm hf.symm

def circleDegree (x₀ : ℝ)
    (f : C(AddCircle (2 * Real.pi), AddCircle (2 * Real.pi)))
    (hf : f (x₀ : AddCircle (2 * Real.pi)) = (x₀ : AddCircle (2 * Real.pi))) : ℤ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  AddCircle.windingNumber (x := (x₀ : AddCircle (2 * Real.pi)))
    (.of (.mk (loopOfCircleMap x₀ f hf)))

lemma circleBaseLoop_fiber_eq {x₀ : ℝ} {t₁ t₂ : I}
    (h : circleBaseLoop x₀ t₁ = circleBaseLoop x₀ t₂) :
    t₁ = t₂ ∨ (t₁ = 0 ∧ t₂ = 1) ∨ (t₁ = 1 ∧ t₂ = 0) := by
  simp only [circleBaseLoop_apply] at h
  have hsub : ((((t₁ : ℝ) - (t₂ : ℝ)) * (2 * Real.pi) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
    have hdiff :
        (((t₁ : ℝ) * (2 * Real.pi) + x₀ : ℝ) : AddCircle (2 * Real.pi)) -
          (((t₂ : ℝ) * (2 * Real.pi) + x₀ : ℝ) : AddCircle (2 * Real.pi)) = 0 :=
      sub_eq_zero.mpr h
    have hring : ((t₁ : ℝ) * (2 * Real.pi) + x₀) - ((t₂ : ℝ) * (2 * Real.pi) + x₀) =
        ((t₁ : ℝ) - (t₂ : ℝ)) * (2 * Real.pi) := by ring
    rwa [← QuotientAddGroup.mk_sub, hring] at hdiff
  rw [AddCircle.coe_eq_zero_iff] at hsub
  obtain ⟨n, hn⟩ := hsub
  have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hn_real : (n : ℝ) = (t₁ : ℝ) - (t₂ : ℝ) := by
    have hmul : (n : ℝ) * (2 * Real.pi) = ((t₁ : ℝ) - (t₂ : ℝ)) * (2 * Real.pi) := by
      simpa [zsmul_eq_mul] using hn
    exact mul_right_cancel₀ h2pi.ne' hmul
  have ht₁0 : (0 : ℝ) ≤ t₁ := t₁.2.1
  have ht₁1 : (t₁ : ℝ) ≤ 1 := t₁.2.2
  have ht₂0 : (0 : ℝ) ≤ t₂ := t₂.2.1
  have ht₂1 : (t₂ : ℝ) ≤ 1 := t₂.2.2
  have hn_bounds : (-1 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 1 := by
    constructor <;> linarith
  have hn_int : (-1 : ℤ) ≤ n ∧ n ≤ 1 :=
    ⟨by exact_mod_cast hn_bounds.1, by exact_mod_cast hn_bounds.2⟩
  rcases (by omega : n = 0 ∨ n = -1 ∨ n = 1) with rfl | rfl | rfl
  · left
    ext
    norm_num at hn_real
    linarith
  · right; left
    have h1 : (t₁ : ℝ) = 0 := by norm_num at hn_real; linarith
    have h2 : (t₂ : ℝ) = 1 := by norm_num at hn_real; linarith
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  · right; right
    have h1 : (t₁ : ℝ) = 1 := by norm_num at hn_real; linarith
    have h2 : (t₂ : ℝ) = 0 := by norm_num at hn_real; linarith
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩

theorem circle_homotopyRel_of_degree_eq (x₀ : ℝ)
    (f g : C(AddCircle (2 * Real.pi), AddCircle (2 * Real.pi)))
    (hf : f (x₀ : AddCircle (2 * Real.pi)) = (x₀ : AddCircle (2 * Real.pi)))
    (hg : g (x₀ : AddCircle (2 * Real.pi)) = (x₀ : AddCircle (2 * Real.pi)))
    (hdeg : circleDegree x₀ f hf = circleDegree x₀ g hg) :
    ContinuousMap.HomotopicRel f g {(x₀ : AddCircle (2 * Real.pi))} := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have heq_fg :
      (.of (.mk (loopOfCircleMap x₀ f hf)) :
        FundamentalGroup (AddCircle (2 * Real.pi)) (x₀ : AddCircle (2 * Real.pi))) =
      .of (.mk (loopOfCircleMap x₀ g hg)) := by
    apply (AddCircle.windingNumberIso (p := 2 * Real.pi) (x₀ : AddCircle (2 * Real.pi))).injective
    apply Multiplicative.toAdd.injective
    exact hdeg
  have hq :
      (Path.Homotopic.Quotient.mk (loopOfCircleMap x₀ f hf)) =
        Path.Homotopic.Quotient.mk (loopOfCircleMap x₀ g hg) :=
    congrArg CategoryTheory.End.asHom heq_fg
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hq
  let π : I × I → I × AddCircle (2 * Real.pi) := fun p => (p.1, circleBaseLoop x₀ p.2)
  have hcont_π : Continuous π := Continuous.prodMk continuous_fst
    ((circleBaseLoop x₀).continuous.comp continuous_snd)
  let sec : AddCircle (2 * Real.pi) → I := fun y =>
    ⟨((AddCircle.equivIco (2 * Real.pi) x₀ y : ℝ) - x₀) / (2 * Real.pi), by
      have hmem := (AddCircle.equivIco (2 * Real.pi) x₀ y).2
      have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
      constructor
      · exact div_nonneg (sub_nonneg.mpr hmem.1) h2pi.le
      · rw [div_le_one h2pi]
        linarith [hmem.2]⟩
  have hπ_sec : ∀ y : AddCircle (2 * Real.pi), circleBaseLoop x₀ (sec y) = y := by
    intro y
    rw [circleBaseLoop_apply]
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := Real.two_pi_pos.ne'
    have hcancel :
        (((AddCircle.equivIco (2 * Real.pi) x₀ y : ℝ) - x₀) / (2 * Real.pi)) * (2 * Real.pi) + x₀ =
          (AddCircle.equivIco (2 * Real.pi) x₀ y : ℝ) := by
      field_simp [h2pi]
      ring
    rw [hcancel]
    exact AddCircle.coe_equivIco (p := 2 * Real.pi) (a := x₀) (y := y)
  have hsurj_π : Function.Surjective π := fun ⟨s, y⟩ =>
    ⟨(s, sec y), Prod.ext rfl (hπ_sec y)⟩
  have hquot_π : IsQuotientMap π :=
    (hcont_π.isClosedMap).isQuotientMap hcont_π hsurj_π
  have hH_const : ∀ s : I, ∀ t₁ t₂ : I,
      circleBaseLoop x₀ t₁ = circleBaseLoop x₀ t₂ → H (s, t₁) = H (s, t₂) := by
    intro s t₁ t₂ ht
    rcases circleBaseLoop_fiber_eq ht with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · have h0 : H (s, 0) = (x₀ : AddCircle (2 * Real.pi)) :=
        (H.prop' s 0 (by simp)).trans (loopOfCircleMap x₀ f hf).source
      have h1 : H (s, 1) = (x₀ : AddCircle (2 * Real.pi)) :=
        (H.prop' s 1 (by simp)).trans (loopOfCircleMap x₀ f hf).target
      exact h0.trans h1.symm
    · have h0 : H (s, 0) = (x₀ : AddCircle (2 * Real.pi)) :=
        (H.prop' s 0 (by simp)).trans (loopOfCircleMap x₀ f hf).source
      have h1 : H (s, 1) = (x₀ : AddCircle (2 * Real.pi)) :=
        (H.prop' s 1 (by simp)).trans (loopOfCircleMap x₀ f hf).target
      exact h1.trans h0.symm
  let KFun : I × AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi) :=
    fun p => H (p.1, sec p.2)
  have hKFun_comp : KFun ∘ π = H := by
    funext p
    exact hH_const p.1 (sec (circleBaseLoop x₀ p.2)) p.2 (hπ_sec (circleBaseLoop x₀ p.2))
  have hcont_K : Continuous KFun := by
    rw [hquot_π.continuous_iff, hKFun_comp]
    exact H.continuous
  refine ⟨{
    toFun := KFun
    continuous_toFun := hcont_K
    map_zero_left := fun y => by
      dsimp [KFun]
      rw [H.apply_zero (sec y)]
      simp [loopOfCircleMap, hπ_sec y]
    map_one_left := fun y => by
      dsimp [KFun]
      rw [H.apply_one (sec y)]
      simp [loopOfCircleMap, hπ_sec y]
    prop' := fun s y hy => by
      rcases hy with rfl
      have h0 : circleBaseLoop x₀ 0 = (x₀ : AddCircle (2 * Real.pi)) := by
        simp [circleBaseLoop]
      calc
        KFun (s, (x₀ : AddCircle (2 * Real.pi)))
          = H (s, sec (x₀ : AddCircle (2 * Real.pi))) := rfl
        _ = H (s, 0) := hH_const s _ _ ((hπ_sec _).trans h0.symm)
        _ = (x₀ : AddCircle (2 * Real.pi)) :=
          (H.prop' s 0 (by simp)).trans (loopOfCircleMap x₀ f hf).source
        _ = f (x₀ : AddCircle (2 * Real.pi)) := hf.symm
  }⟩

lemma addCircleEquivFixedP_row_pi_div_two :
    addCircleEquivFixedP_row (((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))) = anchorS_P_row := by
  rw [addCircleEquivFixedP_row_apply_coe, circleParam_pi_div_two]

lemma addCircleEquivFixedP_row_conj_pi_div_two
    (f : C(FixedP_row, FixedP_row)) (hf : f anchorS_P_row = anchorS_P_row) :
    ((coxeterHomToCont addCircleEquivFixedP_row.symm).comp (f.comp (coxeterHomToCont addCircleEquivFixedP_row)))
        (((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))) =
      ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi)) := by
  change addCircleEquivFixedP_row.symm
    (f (addCircleEquivFixedP_row (((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))))) =
    ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))
  rw [addCircleEquivFixedP_row_pi_div_two, hf, ← addCircleEquivFixedP_row_pi_div_two]
  exact addCircleEquivFixedP_row.symm_apply_apply _

def fixedP_rowDegree (f : C(FixedP_row, FixedP_row))
    (hf : f anchorS_P_row = anchorS_P_row) : ℤ :=
  circleDegree (Real.pi / 2)
    ((coxeterHomToCont addCircleEquivFixedP_row.symm).comp (f.comp (coxeterHomToCont addCircleEquivFixedP_row)))
    (addCircleEquivFixedP_row_conj_pi_div_two f hf)

theorem fixedP_row_homotopyRel_of_degree_eq
    (f g : C(FixedP_row, FixedP_row))
    (hf : f anchorS_P_row = anchorS_P_row)
    (hg : g anchorS_P_row = anchorS_P_row)
    (hdeg : fixedP_rowDegree f hf = fixedP_rowDegree g hg) :
    ContinuousMap.HomotopicRel f g {anchorS_P_row} := by
  let e : AddCircle (2 * Real.pi) ≃ₜ FixedP_row := addCircleEquivFixedP_row
  let f' : C(AddCircle (2 * Real.pi), AddCircle (2 * Real.pi)) :=
    (coxeterHomToCont e.symm).comp (f.comp (coxeterHomToCont e))
  let g' : C(AddCircle (2 * Real.pi), AddCircle (2 * Real.pi)) :=
    (coxeterHomToCont e.symm).comp (g.comp (coxeterHomToCont e))
  obtain ⟨H'⟩ := circle_homotopyRel_of_degree_eq (Real.pi / 2) f' g'
    (addCircleEquivFixedP_row_conj_pi_div_two f hf)
    (addCircleEquivFixedP_row_conj_pi_div_two g hg) hdeg
  let H_mid : ContinuousMap.HomotopyRel (f.comp (coxeterHomToCont e)) (g.comp (coxeterHomToCont e))
      {((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))} := by
    have hef : (coxeterHomToCont e).comp f' = f.comp (coxeterHomToCont e) := by
      ext1 y
      exact e.apply_symm_apply (f (e y))
    have heg : (coxeterHomToCont e).comp g' = g.comp (coxeterHomToCont e) := by
      ext1 y
      exact e.apply_symm_apply (g (e y))
    exact (H'.compContinuousMap (coxeterHomToCont e)).cast hef heg
  refine ⟨{
    toContinuousMap := H_mid.toContinuousMap.comp
      ((ContinuousMap.id I).prodMap (coxeterHomToCont e.symm))
    map_zero_left := fun x => by
      change H_mid (0, e.symm x) = f x
      rw [H_mid.apply_zero]
      exact congrArg f (e.apply_symm_apply x)
    map_one_left := fun x => by
      change H_mid (1, e.symm x) = g x
      rw [H_mid.apply_one]
      exact congrArg g (e.apply_symm_apply x)
    prop' := fun s x hx => by
      rcases hx with rfl
      have hs : e.symm anchorS_P_row = ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi)) := by
        rw [← addCircleEquivFixedP_row_pi_div_two]
        exact e.symm_apply_apply _
      change H_mid (s, e.symm anchorS_P_row) = f anchorS_P_row
      rw [hs]
      have hprop := H_mid.prop' s ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi)) (by simp)
      change H_mid (s, ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))) =
        f (e (((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi)))) at hprop
      rwa [show e (((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))) = anchorS_P_row from
        addCircleEquivFixedP_row_pi_div_two] at hprop
  }⟩

end CircleDegree

end AkopyanResearch
