module

public import RequestProject.Surgery.Clear
public import RequestProject.Surgery.Transport

@[expose] public section

/-!
# Cancelling a pair of zeros of a good map
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
variable {ι : Type*}

lemma sign_int_cases {d : ℝ} (h : d ≠ 0) :
    (SignType.sign d : ℤ) = 1 ∨ (SignType.sign d : ℤ) = -1 := by
  rcases lt_or_gt_of_ne h with h | h
  · right; simp [sign_neg h]
  · left; simp [sign_pos h]

lemma mul_neg_of_sign_ne {d e : ℝ} (hd : d ≠ 0) (he : e ≠ 0)
    (h : (SignType.sign d : ℤ) ≠ SignType.sign e) : d * e < 0 := by
  rcases lt_or_gt_of_ne hd with h1 | h1 <;> rcases lt_or_gt_of_ne he with h2 | h2 <;>
    simp [sign_neg, sign_pos, h1, h2] at h <;> nlinarith

lemma sign_add_eq_zero {d e : ℝ} (hd : d ≠ 0) (he : e ≠ 0)
    (h : (SignType.sign d : ℤ) ≠ SignType.sign e) :
    (SignType.sign d : ℤ) + SignType.sign e = 0 := by
  rcases sign_int_cases hd with h1 | h1 <;> rcases sign_int_cases he with h2 | h2 <;>
    rw [h1, h2] at h ⊢ <;> simp_all

/-- **Cancellation of a pair of separated zeros with opposite signs.** -/
theorem cancel_good [FiniteDimensional ℝ V] [Fintype ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    (hcodim : ∀ j, Module.finrank ℝ (LinearMap.ker (Qs j)) + 3 ≤ Module.finrank ℝ V)
    (hrank : ∀ i j, LinearMap.ker (Qs i) ≠ LinearMap.ker (Qs j) →
      ∃ u ∈ LinearMap.ker (Qs j), ∃ w ∈ LinearMap.ker (Qs j),
        LinearIndependent ℝ ![Qs i u, Qs i w])
    {U : Set (ℝ × (Fin k → ℝ))} (hU : IsOpen U) (hUc : Convex ℝ U)
    {F : ℝ × (Fin k → ℝ) → V} (hF : GoodMap Qs U F) {z z' : ℝ × (Fin k → ℝ)} {j₀ : ι}
    (hz : Qs j₀ (F z) = 0) (hz' : Qs j₀ (F z') = 0) (hzz : z ≠ z')
    (hs : Sep Qs F j₀ z) (hs' : Sep Qs F j₀ z')
    (hsign : zsign (Qs j₀) F z ≠ zsign (Qs j₀) F z')
    (hseg : ∀ x ∈ openSegment ℝ z z', ∀ j, Qs j (F x) ≠ 0) :
    ∃ G K, GoodMap Qs U G ∧ count Qs G < count Qs F ∧ IsCompact K ∧ K ⊆ U ∧
      ∀ x ∉ K, G x = F x := by
  classical
  obtain ⟨⟨b, hb⟩, hdet1⟩ := hF.frame j₀ z hz
  obtain ⟨⟨b', hb'⟩, hdet2⟩ := hF.frame j₀ z' hz'
  have ha : IsFrameAt F z (frameAt F z) := by rw [frameAt_eq hb]; exact hb
  have ha' : IsFrameAt F z' (frameAt F z') := by rw [frameAt_eq hb']; exact hb'
  obtain ⟨r1, hr1, ha1⟩ := ha
  obtain ⟨r2, hr2, ha2⟩ := ha'
  have hdet : (frameMat (Qs j₀) (frameAt F z)).det * (frameMat (Qs j₀) (frameAt F z')).det < 0 :=
    mul_neg_of_sign_ne hdet1 hdet2 hsign
  -- the open set avoiding the other zeros
  set P : Set (ℝ × (Fin k → ℝ)) := zeroPts Qs F \ {z, z'} with hP
  have hPc : IsClosed P := (hF.zeroPts_finite.diff).isClosed
  set W := U \ P with hW
  have hWo : IsOpen W := hU.sdiff hPc
  have hzU : z ∈ U := hF.sub j₀ z hz
  have hz'U : z' ∈ U := hF.sub j₀ z' hz'
  have hWseg : segment ℝ z z' ⊆ W := by
    intro x hx
    refine ⟨hUc.segment_subset hzU hz'U hx, fun hxP => ?_⟩
    obtain ⟨⟨j, hj⟩, hxne⟩ := hxP
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxne
    exact hseg x (mem_openSegment_of_ne_left_right (Ne.symm hxne.1) (Ne.symm hxne.2) hx) j hj
  have hseg' : ∀ t ∈ Ioo (0:ℝ) 1, ∀ j, Qs j (F (z + t • (z' - z))) ≠ 0 := by
    intro t ht j
    apply hseg _ _ j
    rw [openSegment_eq_image']
    exact ⟨t, ht, rfl⟩
  obtain ⟨G, hGc, K, T, hK, hKW, hTK, hzT, hz'T, hGFT, hGT⟩ :=
    pair_cancel_at (Qs j₀) Qs hcodim (fun j hj => hrank j j₀ hj) F hF.cont hzz
      (frameAt F z) (frameAt F z') (lt_min hr1 hr2)
      (fun x hx => ha1 x (lt_of_lt_of_le hx (min_le_left _ _)))
      (fun x hx => ha2 x (lt_of_lt_of_le hx (min_le_right _ _)))
      hz hz' hdet (fun j hj => hs j hj) (fun j hj => hs' j hj) hseg' hWo hWseg
  have hKU : K ⊆ U := fun x hx => (hKW hx).1
  have hGF : ∀ x ∉ K, G x = F x := fun x hx => hGFT x fun hxT => hx (hTK hxT)
  have hFK : ∀ x ∈ K, x ∈ zeroPts Qs F → x = z ∨ x = z' := by
    intro x hxK hx
    by_contra h
    push_neg at h
    exact (hKW hxK).2 ⟨hx, by simp [h.1, h.2]⟩
  have hGK : ∀ j, zeros Qs G j ∩ K = ∅ := by
    intro j
    ext x
    simp only [zeros, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx hxK
    by_cases hxT : x ∈ T
    · exact hGT x hxT j hx
    · rw [hGFT x hxT] at hx
      rcases hFK x hxK ⟨j, hx⟩ with rfl | rfl
      · exact hxT hzT
      · exact hxT hz'T
  have hzK : z ∈ K := hTK hzT
  have hz'K : z' ∈ K := hTK hz'T
  have hFK' : ∀ j, zeros Qs F j ∩ K =
      if LinearMap.ker (Qs j) = LinearMap.ker (Qs j₀) then {z, z'} else ∅ := by
    intro j
    split_ifs with hker
    · ext x
      simp only [zeros, mem_inter_iff, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hx, hxK⟩; exact hFK x hxK ⟨j, hx⟩
      · have h1 : ∀ y, Qs j₀ (F y) = 0 → Qs j (F y) = 0 := by
          intro y hy
          have : F y ∈ LinearMap.ker (Qs j₀) := hy
          rw [← hker] at this; exact this
        rintro (rfl | rfl)
        · exact ⟨h1 _ hz, hzK⟩
        · exact ⟨h1 _ hz', hz'K⟩
    · ext x
      simp only [zeros, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx hxK
      rcases hFK x hxK ⟨j, hx⟩ with rfl | rfl
      · exact hs j hker hx
      · exact hs' j hker hx
  have hGood : GoodMap Qs U G := by
    refine hF.transfer hGc hK.isClosed hKU hGF ?_ ?_ ?_
    · intro j; rw [hGK j]; exact finite_empty
    · intro j x hxK hx
      have : x ∈ zeros Qs G j ∩ K := ⟨hx, hxK⟩
      rw [hGK j] at this; exact this.elim
    · intro j
      rw [hGK j, hFK' j, finsum_mem_empty]
      split_ifs with hker
      · rw [finsum_mem_pair hzz]
        obtain ⟨s, hsd⟩ := sign_det_frameMat_of_ker_eq (Qs j₀) (Qs j) hdet1 hker.symm
        simp only [zsign, hsd, sign_mul, SignType.coe_mul]
        rw [← mul_add, sign_add_eq_zero hdet1 hdet2 hsign, mul_zero]
      · rw [finsum_mem_empty]
  refine ⟨G, K, hGood, ?_, hK, hKU, hGF⟩
  unfold count
  apply Finset.sum_lt_sum
  · intro j _
    have h := ncard_zeros_eq (Qs := Qs) hGF j (hF.fin j) (hGood.fin j)
    rw [hGK j, ncard_empty] at h
    omega
  · refine ⟨j₀, Finset.mem_univ _, ?_⟩
    have h := ncard_zeros_eq (Qs := Qs) hGF j₀ (hF.fin j₀) (hGood.fin j₀)
    rw [hGK j₀, ncard_empty, hFK' j₀, if_pos rfl, ncard_pair hzz] at h
    omega

end Surgery
