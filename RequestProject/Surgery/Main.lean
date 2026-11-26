module

public import RequestProject.Surgery.CancelGood

@[expose] public section

/-!
# Removing all zeros of a good map

`Surgery.surgery`: if all zeros of all `Qs j ∘ F` are transverse, finitely many, inside the open
convex set `U`, and their signed counts vanish, then `F` can be modified inside a compact subset
of `U` to a map avoiding `⋃ j, ker (Qs j)`.
-/

open Set Filter Topology

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
variable {ι : Type*}

lemma zsign_eq_of_not_mem {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)} {U} {F G : ℝ × (Fin k → ℝ) → V}
    (hF : GoodMap Qs U F) {K : Set (ℝ × (Fin k → ℝ))} (hK : IsClosed K)
    (hGF : ∀ x ∉ K, G x = F x) {x : ℝ × (Fin k → ℝ)} (hx : x ∉ K) {j : ι}
    (hzero : Qs j (F x) = 0) : zsign (Qs j) G x = zsign (Qs j) F x := by
  obtain ⟨hex, -⟩ := hF.frame j x hzero
  obtain ⟨-, heq⟩ := frameAt_congr_of_eventually hex (eventually_eq_of_not_mem hK hGF hx)
  simp only [zsign, heq]

lemma exists_opposite_zero [Finite ι] {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)} {U}
    {F : ℝ × (Fin k → ℝ) → V} (hF : GoodMap Qs U F) {z : ℝ × (Fin k → ℝ)} {j : ι}
    (hz : Qs j (F z) = 0) :
    ∃ z', Qs j (F z') = 0 ∧ zsign (Qs j) F z' ≠ zsign (Qs j) F z := by
  classical
  by_contra h
  push_neg at h
  have hbal := hF.bal j
  rw [finsum_mem_eq_finite_toFinset_sum _ (hF.fin j)] at hbal
  rw [Finset.sum_congr rfl (g := fun _ => zsign (Qs j) F z) (fun x hx => h x
    (by simpa [zeros] using hx))] at hbal
  rw [Finset.sum_const, nsmul_eq_mul] at hbal
  have hcard : (hF.fin j).toFinset.card ≠ 0 := by
    rw [Finset.card_ne_zero]
    exact ⟨z, by simpa [zeros] using hz⟩
  have hs : zsign (Qs j) F z ≠ 0 := by
    rcases sign_int_cases (hF.frame j z hz).2 with h1 | h1 <;> simp [zsign, h1]
  rcases mul_eq_zero.1 hbal with h1 | h1
  · exact hcard (by exact_mod_cast h1)
  · exact hs h1

/-- **Surgery theorem.** -/
theorem surgery [FiniteDimensional ℝ V] [Fintype ι] (hk : 2 ≤ k)
    {Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ)}
    (hcodim : ∀ j, Module.finrank ℝ (LinearMap.ker (Qs j)) + 3 ≤ Module.finrank ℝ V)
    (hrank : ∀ i j, LinearMap.ker (Qs i) ≠ LinearMap.ker (Qs j) →
      ∃ u ∈ LinearMap.ker (Qs j), ∃ w ∈ LinearMap.ker (Qs j),
        LinearIndependent ℝ ![Qs i u, Qs i w])
    {U : Set (ℝ × (Fin k → ℝ))} (hU : IsOpen U) (hUc : Convex ℝ U)
    {F : ℝ × (Fin k → ℝ) → V} (hF : GoodMap Qs U F) :
    ∃ G : ℝ × (Fin k → ℝ) → V, Continuous G ∧ ∃ K, IsCompact K ∧ K ⊆ U ∧
      (∀ x ∉ K, G x = F x) ∧ ∀ x j, Qs j (G x) ≠ 0 := by
  have hrank1 : ∀ i j, LinearMap.ker (Qs i) ≠ LinearMap.ker (Qs j) →
      ∃ u ∈ LinearMap.ker (Qs j), Qs i u ≠ 0 := by
    intro i j h
    obtain ⟨u, hu, w, -, hli⟩ := hrank i j h
    exact ⟨u, hu, by simpa using hli.ne_zero 0⟩
  suffices H : ∀ n, ∀ F : ℝ × (Fin k → ℝ) → V, GoodMap Qs U F → count Qs F = n →
      ∃ G : ℝ × (Fin k → ℝ) → V, Continuous G ∧ ∃ K, IsCompact K ∧ K ⊆ U ∧
        (∀ x ∉ K, G x = F x) ∧ ∀ x j, Qs j (G x) ≠ 0 from H _ F hF rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hn
  by_cases hzero : ∀ x j, Qs j (F x) ≠ 0
  · exact ⟨F, hF.cont, ∅, isCompact_empty, empty_subset _, fun _ _ => rfl, hzero⟩
  push_neg at hzero
  obtain ⟨z, j₀, hz⟩ := hzero
  obtain ⟨z', hz', hsgn⟩ := exists_opposite_zero hF hz
  have hzz : z ≠ z' := by rintro rfl; exact hsgn rfl
  -- step 1: separate at `z'`
  obtain ⟨G1, K1, z'1, hG1, hc1, hK1, hK1U, hGF1, hz'1K, hout1, hz'1, hsep'1, hsg'1⟩ :=
    separate_good hrank1 hU hF hz'
  have hzK1 : z ∉ K1 := hout1 z ⟨j₀, hz⟩ hzz
  have hz1 : Qs j₀ (G1 z) = 0 := by rw [hGF1 z hzK1]; exact hz
  have hsg1 : zsign (Qs j₀) G1 z = zsign (Qs j₀) F z :=
    zsign_eq_of_not_mem hF hK1.isClosed hGF1 hzK1 hz
  have hz'1z : z'1 ≠ z := fun h => hzK1 (h ▸ hz'1K)
  -- step 2: separate at `z`
  obtain ⟨G2, K2, z1, hG2, hc2, hK2, hK2U, hGF2, hz1K, hout2, hz1, hsep1, hsg2⟩ :=
    separate_good hrank1 hU hG1 hz1
  have hz'1K2 : z'1 ∉ K2 := hout2 z'1 ⟨j₀, hz'1⟩ hz'1z
  have hz'2 : Qs j₀ (G2 z'1) = 0 := by rw [hGF2 z'1 hz'1K2]; exact hz'1
  have hsep'2 : Sep Qs G2 j₀ z'1 := by
    intro i hi; rw [hGF2 z'1 hz'1K2]; exact hsep'1 i hi
  have hsg'2 : zsign (Qs j₀) G2 z'1 = zsign (Qs j₀) G1 z'1 :=
    zsign_eq_of_not_mem hG1 hK2.isClosed hGF2 hz'1K2 hz'1
  have hz1z'1 : z1 ≠ z'1 := fun h => hz'1K2 (h ▸ hz1K)
  -- step 3: clear the segment
  obtain ⟨G3, K3, z2, hG3, hc3, hK3, hK3U, hGF3, hz2K, hout3, hz2, hsep2, hsg3, hseg⟩ :=
    clear_good hk hU hG2 hz1 hsep1 ⟨j₀, hz'2⟩ hz1z'1
  have hz'1K3 : z'1 ∉ K3 := hout3 z'1 ⟨j₀, hz'2⟩ (Ne.symm hz1z'1)
  have hz'3 : Qs j₀ (G3 z'1) = 0 := by rw [hGF3 z'1 hz'1K3]; exact hz'2
  have hsep'3 : Sep Qs G3 j₀ z'1 := by
    intro i hi; rw [hGF3 z'1 hz'1K3]; exact hsep'2 i hi
  have hsg'3 : zsign (Qs j₀) G3 z'1 = zsign (Qs j₀) G2 z'1 :=
    zsign_eq_of_not_mem hG2 hK3.isClosed hGF3 hz'1K3 hz'2
  have hz2z'1 : z2 ≠ z'1 := fun h => hz'1K3 (h ▸ hz2K)
  -- step 4: cancel
  have hsign : zsign (Qs j₀) G3 z2 ≠ zsign (Qs j₀) G3 z'1 := by
    rw [hsg3, hsg2, hsg1, hsg'3, hsg'2, hsg'1]; exact Ne.symm hsgn
  obtain ⟨G4, K4, hG4, hc4, hK4, hK4U, hGF4⟩ :=
    cancel_good hcodim hrank hU hUc hG3 hz2 hz'3 hz2z'1 hsep2 hsep'3 hsign hseg
  have hlt : count Qs G4 < n := by rw [← hn, ← hc1, ← hc2, ← hc3]; exact hc4
  obtain ⟨G5, hG5c, K5, hK5, hK5U, hGF5, hG5⟩ := ih _ hlt G4 hG4 rfl
  refine ⟨G5, hG5c, K1 ∪ K2 ∪ K3 ∪ K4 ∪ K5,
    (((hK1.union hK2).union hK3).union hK4).union hK5,
    union_subset (union_subset (union_subset (union_subset hK1U hK2U) hK3U) hK4U) hK5U,
    fun x hx => ?_, hG5⟩
  simp only [mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hx
  rw [hGF5 x h5, hGF4 x h4, hGF3 x h3, hGF2 x h2, hGF1 x h1]

end Surgery
