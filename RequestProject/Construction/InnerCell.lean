module

public import RequestProject.Construction.CellCount
public import RequestProject.Construction.Safety

@[expose] public section

/-!
# The inner cell

On `{min x > 1/12}` we have `F0 x = H⁰(2x - ê)`; this is a cell with coordinates
`Y x = 2x - ê`, simplex `vvec q m` and orientation sign `+1`.
-/

open Set Surgery Matrix

namespace Tverberg6R

noncomputable section

lemma toBaryLin_fromVec_castSucc (v : Fin 5 → ℝ) (l : Fin 5) :
    toBaryLin (fromVec v) l.castSucc = v l := by
  refine Fin.cases ?_ (fun t => ?_) l
  · rfl
  · rw [← Fin.succ_castSucc]
    simp [toBaryLin, fromVec, Fin.tail]

lemma toBaryLin_unitE (i : Fin 5) :
    toBaryLin (unitE i) = Pi.single i.castSucc 1 - Pi.single 5 1 := by
  funext j
  by_cases hj : j = 5
  · subst hj
    simp only [toBaryLin, unitE, fromVec, Fin.tail, Fin.sum_univ_four, cons_snoc_five]
    fin_cases i <;> simp
  · obtain ⟨l, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    · rw [unitE, toBaryLin_fromVec_castSucc]
      have : (l.castSucc : Fin 6) ≠ 5 := (Fin.castSucc_lt_last l).ne
      simp [Pi.single_apply, this, Fin.castSucc_inj]
    · exact absurd rfl hj

lemma toBaryL_unitE (i : Fin 5) :
    toBaryL (unitE i) = Pi.single i.castSucc 1 - Pi.single 5 1 := toBaryLin_unitE i

/-- Coordinates of the inner cell. -/
def innerY (x : Fin 6 → ℝ) : Fin 6 → ℝ := fun i => 2 * x i - 1 / 6

lemma one_twelfth_lt_of_innerY {x : Fin 6 → ℝ} (h : ∀ s, 0 < innerY x s) (i : Fin 6) :
    1 / 12 < x i := by
  have := h i; simp only [innerY] at this; linarith

lemma min6_gt_of_innerY {x : Fin 6 → ℝ} (h : ∀ s, 0 < innerY x s) : 1 / 12 < min6 x := by
  obtain ⟨i, hi⟩ := exists_min6_eq x
  rw [hi]; exact one_twelfth_lt_of_innerY h i

lemma innerY_mem {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) (h : ∀ s, 0 < innerY x s) :
    x ∈ massSimplex :=
  ⟨fun i => by linarith [one_twelfth_lt_of_innerY h i], hx⟩

/-- The base point of the inner cell. -/
def innerX0 : Fin 6 → ℝ := fun i => ((Pi.single 5 1 : Fin 6 → ℝ) i + 1 / 6) / 2

lemma innerY_innerX0 : innerY innerX0 = Pi.single 5 1 := by
  funext i; simp only [innerY, innerX0]; ring

lemma innerDet : (snocMat (fun i => ((2 : ℝ) • (LinearMap.id : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)))
    (toBaryL (unitE i))) (Pi.single 5 1)).det = 32 := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [snocMat, toBaryL_unitE, Fin.snoc_castSucc]
    norm_num
  · intro s j hsj0
    have hsj : s < j := hsj0
    have hs5 : s ≠ 5 := (lt_of_lt_of_le hsj (Fin.le_last j)).ne
    obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    · have : s ≠ i.castSucc := (show s < i.castSucc from hsj).ne
      simp [snocMat, Fin.snoc_castSucc, toBaryL_unitE, Pi.single_apply, this, hs5]
    · simp [snocMat, Pi.single_apply, hs5]

/-- The inner cell. -/
def innerCell {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) : CellData q m where
  Y := innerY
  YL := (2 : ℝ) • LinearMap.id
  hY x w := by funext i; simp only [innerY, Pi.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]; ring
  hYL w hw := by simp [← Finset.mul_sum, hw]
  x0 := innerX0
  hx0 := by simp [innerX0, Fin.sum_univ_succ]; norm_num
  hYx0 := by rw [innerY_innerX0]; simp
  hdet := by rw [innerY_innerX0, innerDet]; norm_num
  z := vvec q m
  hz := indep5_vvec hq hm
  FL := (H0L q).comp ((2 : ℝ) • LinearMap.id)
  hlin w := by
    simp only [LinearMap.comp_apply, H0L_apply, ell_H0]
  hpos x _ h i := by linarith [one_twelfth_lt_of_innerY h i]
  hell x hx h := by
    rw [F0_inner q (innerY_mem hx h) (min6_gt_of_innerY h).le, ell_H0]
    rfl
  hloc x hx h := by
    have hmin := min6_gt_of_innerY h
    refine ⟨min6 x - 1 / 12, by linarith, fun w hw hw0 => ?_⟩
    have hcoord : ∀ i, 1 / 12 ≤ (x + w) i := by
      intro i
      have h1 := norm_le_pi_norm w i
      have h2 := neg_abs_le (w i)
      rw [Real.norm_eq_abs] at h1
      have h3 := min6_le x i
      simp only [Pi.add_apply]
      linarith
    have hmem : x + w ∈ massSimplex := by
      refine ⟨fun i => by linarith [hcoord i], ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hw0, add_zero]
    rw [F0_inner q hmem (le_min6 hcoord), F0_inner q (innerY_mem hx h) hmin.le]
    rw [LinearMap.comp_apply, ← H0L_apply, ← H0L_apply, ← map_add]
    congr 1
    funext i
    simp only [Pi.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

lemma innerCell_eps {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) : (innerCell hq hm).eps = 1 := by
  simp only [CellData.eps, innerCell]
  rw [innerY_innerX0, innerDet]
  simp

end

end Tverberg6R
