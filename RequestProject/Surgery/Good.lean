module

public import RequestProject.Surgery.Shift

@[expose] public section

/-!
# Maps with finitely many transverse, balanced zeros

`GoodMap Qs U F`: `F` is continuous, each `Qs j ∘ F` has finitely many zeros, all in `U`, `F` is
locally affine at them with invertible `Qs j`-matrix, and the signed count of zeros of every
`Qs j ∘ F` vanishes.
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
variable {ι : Type*}

/-- Zeros of `Qs j ∘ F`. -/
def zeros (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)) (F : ℝ × (Fin k → ℝ) → V) (j : ι) :
    Set (ℝ × (Fin k → ℝ)) := {x | Qs j (F x) = 0}

/-- All zero points. -/
def zeroPts (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)) (F : ℝ × (Fin k → ℝ) → V) :
    Set (ℝ × (Fin k → ℝ)) := {x | ∃ j, Qs j (F x) = 0}

/-- GoodMap maps. -/
structure GoodMap (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)) (U : Set (ℝ × (Fin k → ℝ)))
    (F : ℝ × (Fin k → ℝ) → V) : Prop where
  cont : Continuous F
  fin : ∀ j, (zeros Qs F j).Finite
  sub : ∀ j x, Qs j (F x) = 0 → x ∈ U
  frame : ∀ j x, Qs j (F x) = 0 →
    (∃ a, IsFrameAt F x a) ∧ (frameMat (Qs j) (frameAt F x)).det ≠ 0
  bal : ∀ j, ∑ᶠ x ∈ zeros Qs F j, zsign (Qs j) F x = 0

/-- Total number of zeros. -/
noncomputable def count [Fintype ι] (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ))
    (F : ℝ × (Fin k → ℝ) → V) : ℕ :=
  ∑ j, (zeros Qs F j).ncard

lemma GoodMap.zeroPts_finite [Finite ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)} {U} {F}
    (h : GoodMap Qs U F) : (zeroPts Qs F).Finite := by
  have : zeroPts Qs F = ⋃ j, zeros Qs F j := by ext x; simp [zeroPts, zeros]
  rw [this]; exact Set.finite_iUnion h.fin

/-- Frames agree where the maps agree on a neighbourhood. -/
lemma frameAt_congr_of_eventually {F G : ℝ × (Fin k → ℝ) → V} {x : ℝ × (Fin k → ℝ)}
    (hex : ∃ a, IsFrameAt F x a) (h : ∀ᶠ y in 𝓝 x, G y = F y) :
    (∃ a, IsFrameAt G x a) ∧ frameAt G x = frameAt F x := by
  obtain ⟨a, ha⟩ := hex
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 h
  have hG : IsFrameAt G x a := ha.congr hρ fun y hy => hball (by simpa [dist_eq_norm] using hy)
  exact ⟨⟨a, hG⟩, by rw [frameAt_eq hG, frameAt_eq ha]⟩

lemma eventually_eq_of_not_mem {F G : ℝ × (Fin k → ℝ) → V} {K : Set (ℝ × (Fin k → ℝ))}
    (hK : IsClosed K) (hGF : ∀ x ∉ K, G x = F x) {x : ℝ × (Fin k → ℝ)} (hx : x ∉ K) :
    ∀ᶠ y in 𝓝 x, G y = F y :=
  Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hx) fun y hy => hGF y hy

/-- **Transfer of goodness** through a modification supported in a closed set `K ⊆ U`. -/
lemma GoodMap.transfer {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)} {U} {F G : ℝ × (Fin k → ℝ) → V}
    (hF : GoodMap Qs U F) (hG : Continuous G) {K : Set (ℝ × (Fin k → ℝ))} (hK : IsClosed K)
    (hKU : K ⊆ U) (hGF : ∀ x ∉ K, G x = F x)
    (hfin : ∀ j, (zeros Qs G j ∩ K).Finite)
    (hfr : ∀ j x, x ∈ K → Qs j (G x) = 0 →
      (∃ a, IsFrameAt G x a) ∧ (frameMat (Qs j) (frameAt G x)).det ≠ 0)
    (hsum : ∀ j, ∑ᶠ x ∈ zeros Qs G j ∩ K, zsign (Qs j) G x =
      ∑ᶠ x ∈ zeros Qs F j ∩ K, zsign (Qs j) F x) : GoodMap Qs U G := by
  have hdiff : ∀ j, zeros Qs G j \ K = zeros Qs F j \ K := by
    intro j; ext x
    simp only [zeros, mem_diff, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [← hGF x h2], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [hGF x h2], h2⟩
  have hfinG : ∀ j, (zeros Qs G j).Finite := by
    intro j
    have : zeros Qs G j = (zeros Qs G j ∩ K) ∪ (zeros Qs G j \ K) := (inter_union_diff _ _).symm
    rw [this, hdiff]
    exact (hfin j).union ((hF.fin j).diff)
  refine ⟨hG, hfinG, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases hxK : x ∈ K
    · exact hKU hxK
    · exact hF.sub j x (by rwa [← hGF x hxK])
  · intro j x hx
    by_cases hxK : x ∈ K
    · exact hfr j x hxK hx
    · have hFx : Qs j (F x) = 0 := by rwa [← hGF x hxK]
      obtain ⟨hex, hdet⟩ := hF.frame j x hFx
      obtain ⟨hex', heq⟩ := frameAt_congr_of_eventually hex (eventually_eq_of_not_mem hK hGF hxK)
      exact ⟨hex', by rw [heq]; exact hdet⟩
  · intro j
    rw [← finsum_mem_inter_add_sdiff K (hfinG j), hsum j, hdiff j]
    have : ∑ᶠ x ∈ zeros Qs F j \ K, zsign (Qs j) G x = ∑ᶠ x ∈ zeros Qs F j \ K, zsign (Qs j) F x := by
      refine finsum_mem_congr rfl fun x hx => ?_
      have hFx : Qs j (F x) = 0 := hx.1
      obtain ⟨hex, -⟩ := hF.frame j x hFx
      obtain ⟨-, heq⟩ := frameAt_congr_of_eventually hex (eventually_eq_of_not_mem hK hGF hx.2)
      simp only [zsign, heq]
    rw [this, finsum_mem_inter_add_sdiff K (hF.fin j), hF.bal j]

lemma zeros_diff_eq {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)} {F G : ℝ × (Fin k → ℝ) → V}
    {K : Set (ℝ × (Fin k → ℝ))} (hGF : ∀ x ∉ K, G x = F x) (j : ι) :
    zeros Qs G j \ K = zeros Qs F j \ K := by
  ext x
  simp only [zeros, mem_diff, mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rwa [← hGF x h2], h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rwa [hGF x h2], h2⟩

/-- Counting zeros through a modification. -/
lemma ncard_zeros_eq {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)} {F G : ℝ × (Fin k → ℝ) → V}
    {K : Set (ℝ × (Fin k → ℝ))} (hGF : ∀ x ∉ K, G x = F x) (j : ι)
    (hFfin : (zeros Qs F j).Finite) (hGfin : (zeros Qs G j).Finite) :
    (zeros Qs G j).ncard + (zeros Qs F j ∩ K).ncard =
      (zeros Qs F j).ncard + (zeros Qs G j ∩ K).ncard := by
  have h1 := Set.ncard_inter_add_ncard_diff_eq_ncard (zeros Qs G j) K hGfin
  have h2 := Set.ncard_inter_add_ncard_diff_eq_ncard (zeros Qs F j) K hFfin
  rw [zeros_diff_eq hGF j] at h1
  omega

end Surgery
