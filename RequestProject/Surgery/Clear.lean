module

public import RequestProject.Surgery.Separate

@[expose] public section

/-!
# Clearing the segment between two zeros
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
variable {ι : Type*}

lemma secB_lin {Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)} {a : Fin (k+1) → V}
    (h : (frameMat Q a).det ≠ 0) (x : ℝ × (Fin k → ℝ)) : secB Q a (lin a x) = x :=
  (eq_secB_of h rfl).symm

lemma span_pair_ne_top (hk : 2 ≤ k) (v w : ℝ × (Fin k → ℝ)) :
    Submodule.span ℝ (Set.range ![v, w]) ≠ ⊤ := by
  intro htop
  have h1 := finrank_range_le_card (R := ℝ) ![v, w]
  rw [Set.finrank, htop, finrank_top, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self,
    Fintype.card_fin] at h1
  omega

/-- **Clearing a segment.** -/
theorem clear_good [FiniteDimensional ℝ V] [Fintype ι] (hk : 2 ≤ k)
    {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    {U : Set (ℝ × (Fin k → ℝ))} (hU : IsOpen U) {F : ℝ × (Fin k → ℝ) → V}
    (hF : GoodMap Qs U F) {z z' : ℝ × (Fin k → ℝ)} {j₀ : ι} (hz : Qs j₀ (F z) = 0)
    (hsep : Sep Qs F j₀ z) (hz' : z' ∈ zeroPts Qs F) (hzz : z ≠ z') :
    ∃ G K z₁, GoodMap Qs U G ∧ count Qs G = count Qs F ∧ IsCompact K ∧ K ⊆ U ∧
      (∀ x ∉ K, G x = F x) ∧ z₁ ∈ K ∧ (∀ p ∈ zeroPts Qs F, p ≠ z → p ∉ K) ∧
      Qs j₀ (G z₁) = 0 ∧ Sep Qs G j₀ z₁ ∧ zsign (Qs j₀) G z₁ = zsign (Qs j₀) F z ∧
      ∀ x ∈ openSegment ℝ z₁ z', ∀ j, Qs j (G x) ≠ 0 := by
  classical
  set a := frameAt F z
  have hdet : (frameMat (Qs j₀) a).det ≠ 0 := (hF.frame j₀ z hz).2
  let P : Finset (ℝ × (Fin k → ℝ)) := hF.zeroPts_finite.toFinset.filter fun p => p ≠ z ∧ p ≠ z'
  let q : (ℝ × (Fin k → ℝ)) → Submodule ℝ V := fun p =>
    (Submodule.span ℝ (Set.range ![z - z', p - z'])).comap (secBLin (Qs j₀) a)
  obtain ⟨d, hd⟩ := exists_not_mem_finset_submodule P q (by
    intro p _ htop
    apply span_pair_ne_top hk (z - z') (p - z')
    rw [eq_top_iff]
    intro x _
    have : lin a x ∈ q p := by rw [htop]; exact Submodule.mem_top
    have h2 : secB (Qs j₀) a (lin a x) ∈ Submodule.span ℝ (Set.range ![z - z', p - z']) := this
    rwa [secB_lin hdet] at h2)
  obtain ⟨r, hr, hball, hfar, t, ht0, hGood, hcount, hGF, hG4, hsm, hiff⟩ :=
    shift_choose hU hF ⟨j₀, hz⟩ d
  obtain ⟨hK1, hK2, hK3, hK4, hK5, hK6, hK7⟩ :=
    shift_conclusions hF hz hr hball hfar hGF hG4 hsm hiff
  set G := shiftMap F z r (t • d)
  set z₁ := z - secB (Qs j₀) a (t • d) with hz₁
  have hz'K : z' ∉ Metric.closedBall z (r / 2) := hK5 z' hz' (Ne.symm hzz)
  have hz₁z' : z₁ ≠ z' := fun h => hz'K (h ▸ hK4)
  have hSep : Sep Qs G j₀ z₁ := by
    intro i hi h
    exact hsep i hi ((hiff i _ (by linarith [hsm j₀ hz])).1 h).1
  refine ⟨G, _, z₁, hGood, hcount, hK1, hK2, hK3, hK4, hK5, hK6, hSep, hK7, ?_⟩
  intro x hx j hxj
  by_cases hxd : dist x z < r / 2
  · obtain ⟨h0, hxe⟩ := (hiff j x hxd).1 hxj
    have hker : LinearMap.ker (Qs j) = LinearMap.ker (Qs j₀) := by
      by_contra hne; exact hsep j hne h0
    have hxj0 : Qs j₀ (G x) = 0 := by
      have : G x ∈ LinearMap.ker (Qs j) := hxj
      rw [hker] at this; exact this
    have hx1 : x = z₁ := ((hiff j₀ x hxd).1 hxj0).2
    rw [hx1, left_mem_openSegment_iff] at hx
    exact hz₁z' hx
  · have hFx : Qs j (F x) = 0 := by rwa [← hGF x (not_lt.1 hxd)]
    have hxz : x ≠ z := by
      rintro rfl; rw [dist_self] at hxd; exact hxd (by linarith)
    by_cases hxz' : x = z'
    · rw [hxz', right_mem_openSegment_iff] at hx
      exact hz₁z' hx
    · have hxP : x ∈ P := by
        simp only [P, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨j, hFx⟩, hxz, hxz'⟩
      apply hd x hxP
      obtain ⟨α, β, hα, hβ, hαβ, hxe⟩ := hx
      set b := secB (Qs j₀) a d
      have hz₁b : z₁ = z - t • b := by rw [hz₁, secB_smul]
      have key : (α * t) • b = α • (z - z') - (x - z') := by
        rw [← hxe, hz₁b, show β = 1 - α by linarith]
        module
      have hαt : α * t ≠ 0 := mul_ne_zero hα.ne' ht0
      have hb : b = (α * t)⁻¹ • (α • (z - z') - (x - z')) := by
        rw [← key, smul_smul, inv_mul_cancel₀ hαt, one_smul]
      show secB (Qs j₀) a d ∈ Submodule.span ℝ (Set.range ![z - z', x - z'])
      rw [show secB (Qs j₀) a d = b from rfl, hb]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) ?_)
      · exact Submodule.subset_span ⟨0, rfl⟩
      · exact Submodule.subset_span ⟨1, rfl⟩

end Surgery
