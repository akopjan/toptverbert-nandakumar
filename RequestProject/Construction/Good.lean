module

public import RequestProject.Construction.PyrCell

@[expose] public section

/-!
# `Fmap` is a good map

Every zero of `ell m ∘ Fmap q` lies in the inner cell or in the zero cell of one pyramid; each
cell contains at most one transverse zero, and the signed count over all cells is
`-innerIndex + ∑ (-1)^k (±) φ = 0` by `degree_balance`.
-/

open Set Surgery Matrix

namespace Tverberg6R

noncomputable section

/-! ### The combinatorial identity -/

lemma anchors_eq : anchors = Finset.univ.powersetCard 1 ∪ Finset.univ.powersetCard 2 ∪
    Finset.univ.powersetCard 3 := by
  ext A
  simp only [anchors, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_powersetCard_univ]
  omega

lemma sum_anchors (f : Finset (Fin 6) → ℤ) :
    ∑ A ∈ anchors, f A = ∑ A ∈ Finset.univ.powersetCard 1, f A +
      ∑ A ∈ Finset.univ.powersetCard 2, f A + ∑ A ∈ Finset.univ.powersetCard 3, f A := by
  rw [anchors_eq, Finset.sum_union, Finset.sum_union]
  · rw [Finset.disjoint_left]; intro A h1 h2
    rw [Finset.mem_powersetCard_univ] at h1 h2; omega
  · rw [Finset.disjoint_left]; intro A h1 h2
    rw [Finset.mem_union, Finset.mem_powersetCard_univ, Finset.mem_powersetCard_univ] at h1
    rw [Finset.mem_powersetCard_univ] at h2; omega

lemma sum_powersetCard_sgn (c : ℕ) (g : Finset (Fin 6) → ℤ) :
    ∑ A ∈ Finset.univ.powersetCard c, (if A.card = 3 then -1 else 1) * g A =
      (if c = 3 then -1 else 1) * ∑ A ∈ Finset.univ.powersetCard c, g A := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mem_powersetCard_univ] at hA
  rw [hA]

theorem pyr_sum {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) :
    ∑ p ∈ Pyr, (-1 : ℤ) ^ (p.1 : ℕ) * (if p.2.card = 3 then -1 else 1) *
      facetIndex q m (rowSet m (p.1.succAbove 0) p.2) p.1 = innerIndex q m := by
  have hb := degree_balance hq hm
  rw [Pyr, Finset.sum_product]
  have : ∀ k : Fin 6, ∑ A ∈ anchors, (-1 : ℤ) ^ (k : ℕ) * (if A.card = 3 then -1 else 1) *
      facetIndex q m (rowSet m (k.succAbove 0) A) k =
      (-1 : ℤ) ^ (k : ℕ) * (facetSum q m 1 k + facetSum q m 2 k - facetSum q m 3 k) := by
    intro k
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_anchors, sum_powersetCard_sgn, sum_powersetCard_sgn,
      sum_powersetCard_sgn]
    simp only [facetSum]
    rw [sum_rowSet_eq hm (k.succAbove 0) 1 (fun P => facetIndex q m P k),
      sum_rowSet_eq hm (k.succAbove 0) 2 (fun P => facetIndex q m P k),
      sum_rowSet_eq hm (k.succAbove 0) 3 (fun P => facetIndex q m P k)]
    norm_num
    ring
  rw [Finset.sum_congr rfl fun k _ => this k]
  linarith

/-! ### Zeros lie in cells -/

lemma yv_pos_of_zero {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex) {k : Fin 6}
    {A : Finset (Fin 6)} (hp : (k, A) ∈ Pyr) (h : InPyr k A x)
    (hmin : ∀ t, gam k A 0 x ≤ gam k A t x) (h0 : ell m (F0 q x) = 0) :
    ∀ s, 0 < yv k A x s := by
  have he := ell_F0_zeroCell q m hm hx hp h hmin
  simp only at he
  rw [h0] at he
  have hsol : affMat (facetPts q m (rowSet m (k.succAbove 0) A) k) *ᵥ yv k A x =
      Pi.single 0 1 := (affMat_mulVec_iff _ _).2 ⟨sum_yv k A hx.2, he.symm⟩
  have hc := card_rowSet hm (k.succAbove 0) A
  have hA := mem_Pyr hp
  have hz : Indep5 (facetPts q m (rowSet m (k.succAbove 0) A) k) := by
    refine indep5_facetPts hq hm ?_ ?_ k
    · rw [← Finset.card_pos, hc]; exact hA.1
    · intro h
      have := congrArg Finset.card h
      rw [hc, Finset.card_univ, Fintype.card_fin] at this
      simp only at hA
      omega
  exact pos_of_sol hz hsol (yv_nonneg h hmin)

/-- The zero set of the pyramid cell `p` (empty if `p ∉ Pyr`). -/
def pyrZ {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word} (hm : IsMatching m)
    (p : Fin 6 × Finset (Fin 6)) : Set (ℝ × (Fin 4 → ℝ)) :=
  if h : p ∈ Pyr then (pyrCell hq hm (k := p.1) (A := p.2) h).zset else ∅

lemma mem_zset_of_zero {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {y : ℝ × (Fin 4 → ℝ)} (hy : ell m (Fmap q y) = 0) :
    y ∈ (innerCell hq hm).zset ∪ ⋃ p ∈ (Pyr : Set (Fin 6 × Finset (Fin 6))), pyrZ hq hm p := by
  have hx : toBary (ret y) ∈ massSimplex := toBary_ret_mem y
  have h0 : ell m (F0 q (toBary (ret y))) = 0 := hy
  rcases zero_cases hq hm hx h0 with hin | ⟨p, hp, hpin, hmin⟩
  · -- inner cell
    have hpos : ∀ s, 0 < innerY (toBary (ret y)) s := fun s => by
      have := min6_le (toBary (ret y)) s
      simp only [innerY]; linarith
    have hU : y ∈ Uo := by
      by_contra hn
      obtain ⟨i, hi⟩ := exists_toBary_ret_eq_zero hn
      have := one_twelfth_lt_of_innerY hpos i
      linarith
    left
    refine ⟨hy, ?_⟩
    rw [← ret_eq_self_of_mem hU]
    exact hpos
  · obtain ⟨k, A⟩ := p
    have hpos := yv_pos_of_zero hq hm hx hp hpin hmin h0
    have hU : y ∈ Uo := by
      by_contra hn
      obtain ⟨i, hi⟩ := exists_toBary_ret_eq_zero hn
      have := pos_of_yv_pos hx.2 hpos i
      linarith
    right
    simp only [mem_iUnion]
    refine ⟨(k, A), hp, ?_⟩
    simp only [pyrZ, dif_pos hp]
    refine ⟨hy, ?_⟩
    rw [ret_eq_self_of_mem hU] at hpos
    exact hpos

lemma zeros_eq {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) :
    {y | ell m (Fmap q y) = 0} =
      (innerCell hq hm).zset ∪ ⋃ p ∈ (Pyr : Set (Fin 6 × Finset (Fin 6))), pyrZ hq hm p := by
  ext y
  refine ⟨fun hy => mem_zset_of_zero hq hm hy, fun hy => ?_⟩
  rcases hy with hy | hy
  · exact hy.1
  · simp only [mem_iUnion] at hy
    obtain ⟨p, hp, hy⟩ := hy
    simp only [pyrZ, dif_pos (show p ∈ Pyr from hp)] at hy
    exact hy.1

lemma near_of_mem_pyrZ {q : Fin 6 → Fin 6 → ℝ} {hq : IsGeneric q} {m : Fin 6 → Word}
    {hm : IsMatching m} {p : Fin 6 × Finset (Fin 6)} {y : ℝ × (Fin 4 → ℝ)}
    (hy : y ∈ pyrZ hq hm p) : p ∈ Pyr ∧ Near p.1 p.2 (toBary y) := by
  by_cases hp : p ∈ Pyr
  · simp only [pyrZ, dif_pos hp] at hy
    exact ⟨hp, near_of_inPyr (sum_toBary y) (inPyr_of_pos hy.2).1⟩
  · simp [pyrZ, dif_neg hp] at hy

lemma pyrZ_finite {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) (p : Fin 6 × Finset (Fin 6)) : (pyrZ hq hm p).Finite := by
  by_cases hp : p ∈ Pyr
  · simp only [pyrZ, dif_pos hp]
    exact (CellData.zset_subsingleton _).finite
  · simp [pyrZ, dif_neg hp]

lemma finite_zeros {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) : {y | ell m (Fmap q y) = 0}.Finite := by
  rw [zeros_eq hq hm]
  exact (CellData.zset_subsingleton _).finite.union
    (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => pyrZ_finite hq hm p)

lemma frame_of_zero {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {y : ℝ × (Fin 4 → ℝ)} (hy : ell m (Fmap q y) = 0) :
    (∃ a, IsFrameAt (Fmap q) y a) ∧ (frameMat (ellLin m) (frameAt (Fmap q) y)).det ≠ 0 := by
  rcases mem_zset_of_zero hq hm hy with h | h
  · exact (innerCell hq hm).frame h
  · simp only [mem_iUnion] at h
    obtain ⟨p, hp, h⟩ := h
    simp only [pyrZ, dif_pos (show p ∈ Pyr from hp)] at h
    exact CellData.frame _ h

lemma mem_Uo_of_zero {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {y : ℝ × (Fin 4 → ℝ)} (hy : ell m (Fmap q y) = 0) : y ∈ Uo := by
  rcases mem_zset_of_zero hq hm hy with h | h
  · exact (innerCell hq hm).mem_Uo h.2
  · simp only [mem_iUnion] at h
    obtain ⟨p, hp, h⟩ := h
    simp only [pyrZ, dif_pos (show p ∈ Pyr from hp)] at h
    exact CellData.mem_Uo _ h.2

theorem balance_zeros {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) :
    ∑ᶠ y ∈ {y | ell m (Fmap q y) = 0}, zsign (ellLin m) (Fmap q) y = 0 := by
  rw [zeros_eq hq hm]
  have hdisj : Disjoint (innerCell hq hm).zset
      (⋃ p ∈ (Pyr : Set (Fin 6 × Finset (Fin 6))), pyrZ hq hm p) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [mem_iUnion] at hy'
    obtain ⟨p, -, hy'⟩ := hy'
    obtain ⟨hp, hnear⟩ := near_of_mem_pyrZ hy'
    have hmin := min6_gt_of_innerY hy.2
    exact far_of_inner hmin.le p hp hnear
  have hpd : (Pyr : Set (Fin 6 × Finset (Fin 6))).PairwiseDisjoint (pyrZ hq hm) := by
    intro p _ p' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    obtain ⟨-, h1⟩ := near_of_mem_pyrZ hy
    obtain ⟨-, h2⟩ := near_of_mem_pyrZ hy'
    obtain ⟨e1, e2⟩ := near_unique h1 h2
    exact hne (Prod.ext e1 e2)
  rw [finsum_mem_union hdisj (CellData.zset_subsingleton _).finite
    (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => pyrZ_finite hq hm p),
    finsum_mem_biUnion hpd (Finset.finite_toSet _) (fun p _ => pyrZ_finite hq hm p),
    finsum_mem_coe_finset, CellData.finsum_zsign, innerCell_eps]
  have hcell : ∀ p ∈ Pyr, ∑ᶠ y ∈ pyrZ hq hm p, zsign (ellLin m) (Fmap q) y =
      (-1 : ℤ) ^ (p.1 : ℕ) * (if p.2.card = 3 then -1 else 1) *
        facetIndex q m (rowSet m (p.1.succAbove 0) p.2) p.1 := by
    intro p hp
    simp only [pyrZ, dif_pos hp]
    rw [CellData.finsum_zsign, pyrCell_eps]
    simp only [pyrCell, facetIndex_eq]
    ring
  rw [Finset.sum_congr rfl hcell, pyr_sum hq hm]
  simp [innerCell, innerIndex]

theorem goodMap_Fmap' {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) : GoodMap Qs Uo (Fmap q) where
  cont := (continuous_F0 q).comp (continuous_toBary.comp continuous_ret)
  fin j := finite_zeros hq j.2
  sub j _ hx := mem_Uo_of_zero hq j.2 hx
  frame j _ hx := frame_of_zero hq j.2 hx
  bal j := balance_zeros hq j.2

end

end Tverberg6R
