module

public import RequestProject.Construction.Frames
public import RequestProject.Construction.Indep

@[expose] public section

/-!
# Counting the zeros in one cell

A *cell* is a region of the hyperplane `∑ x = 1` on which `ell m ∘ F0` is the affine map
`x ↦ ∑ₛ (Y x)ₛ zₛ` for an affine bijection `Y` onto the vectors of sum one, the region being
`{x | Y x > 0}`.  In a cell there is at most one zero, it exists iff the simplex `z` contains the
origin, and its local sign is `-sign det [YL eᵢ | Y x0] * simplexIndex z`.
-/

open Set Surgery Matrix

namespace Tverberg6R

noncomputable section

lemma rsign_eq_sign (x : ℝ) : rsign x = (SignType.sign x : ℤ) := by
  unfold rsign
  rcases lt_trichotomy x 0 with h | h | h
  · simp [h, not_lt.2 h.le, sign_neg h]
  · simp [h]
  · simp [h, sign_pos h]

/-- Data of a cell. -/
structure CellData (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) where
  Y : (Fin 6 → ℝ) → (Fin 6 → ℝ)
  YL : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)
  hY : ∀ x w, Y (x + w) = Y x + YL w
  hYL : ∀ w, ∑ i, w i = 0 → ∑ s, YL w s = 0
  x0 : Fin 6 → ℝ
  hx0 : ∑ i, x0 i = 1
  hYx0 : ∑ s, Y x0 s = 1
  hdet : (snocMat (fun i => YL (toBaryL (unitE i))) (Y x0)).det ≠ 0
  z : Fin 6 → Fin 5 → ℝ
  hz : Indep5 z
  FL : (Fin 6 → ℝ) →ₗ[ℝ] Table
  hlin : ∀ w, ell m (FL w) = ∑ s, YL w s • z s
  hpos : ∀ x, ∑ i, x i = 1 → (∀ s, 0 < Y x s) → ∀ i, 0 < x i
  hell : ∀ x, ∑ i, x i = 1 → (∀ s, 0 < Y x s) → ell m (F0 q x) = ∑ s, Y x s • z s
  hloc : ∀ x, ∑ i, x i = 1 → (∀ s, 0 < Y x s) → ∃ r > 0, ∀ w : Fin 6 → ℝ, ‖w‖ < r →
    ∑ i, w i = 0 → F0 q (x + w) = F0 q x + FL w

namespace CellData

variable {q : Fin 6 → Fin 6 → ℝ} {m : Fin 6 → Word} (c : CellData q m)

/-- The zeros in the cell. -/
def zset : Set (ℝ × (Fin 4 → ℝ)) :=
  {y | ell m (Fmap q y) = 0 ∧ ∀ s, 0 < c.Y (toBary y) s}

/-- The orientation sign of the cell. -/
def eps : ℤ := SignType.sign (snocMat (fun i => c.YL (toBaryL (unitE i))) (c.Y c.x0)).det

/-- The frame columns. -/
def D : Fin 5 → Fin 6 → ℝ := fun i => c.YL (toBaryL (unitE i))

lemma sum_D' (i : Fin 5) : ∑ s, c.YL (toBaryL (unitE i)) s = 0 :=
  c.hYL _ (sum_toBaryLin _)

lemma toBary_sub_eq (y y' : ℝ × (Fin 4 → ℝ)) :
    toBary y = toBary y' + toBaryL (y - y') := by
  rw [toBaryL_apply, ← toBary_add, add_sub_cancel]

lemma toBaryL_eq_sum (u : ℝ × (Fin 4 → ℝ)) :
    toBaryL u = ∑ i, toVec u i • toBaryL (unitE i) := by
  conv_lhs => rw [← sum_toVec_smul_unitE u]
  simp only [map_sum, map_smul]

lemma Y_toBary (y : ℝ × (Fin 4 → ℝ)) :
    c.Y (toBary y) = c.Y c.x0 + ∑ i, toVec (y - fromBary c.x0) i • c.D i := by
  have h := toBary_sub_eq y (fromBary c.x0)
  rw [toBary_fromBary c.hx0] at h
  rw [h, c.hY, toBaryL_eq_sum, map_sum]
  simp only [map_smul, D]

lemma sum_Y_toBary (y : ℝ × (Fin 4 → ℝ)) : ∑ s, c.Y (toBary y) s = 1 := by
  rw [c.Y_toBary]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, D, sum_D', mul_zero, Finset.sum_const_zero,
    c.hYx0, add_zero]

lemma snocMat_mulVec (v : Fin 6 → ℝ) (a : Fin 6 → ℝ) :
    snocMat c.D v *ᵥ a = ∑ i, a i.castSucc • c.D i + a 5 • v := by
  ext s
  simp only [snocMat, mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, mul_comm]

lemma surj {v : Fin 6 → ℝ} (hv : ∑ s, v s = 1) : ∃ y, c.Y (toBary y) = v := by
  have hU : IsUnit (snocMat c.D (c.Y c.x0)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 c.hdet)
  obtain ⟨a, ha⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 hU) v
  rw [snocMat_mulVec] at ha
  have ha5 : a 5 = 1 := by
    have := congrArg (fun f : Fin 6 → ℝ => ∑ s, f s) ha
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib] at this
    rw [Finset.sum_comm] at this
    simp only [← Finset.mul_sum, D, sum_D', mul_zero, Finset.sum_const_zero,
      c.hYx0, zero_add, mul_one, hv] at this
    exact this
  refine ⟨fromBary c.x0 + fromVec (fun i : Fin 5 => a i.castSucc), ?_⟩
  rw [c.Y_toBary, add_sub_cancel_left, toVec_fromVec, ← ha, ha5, one_smul, add_comm]

lemma inj {y y' : ℝ × (Fin 4 → ℝ)} (h : c.Y (toBary y) = c.Y (toBary y')) : y = y' := by
  rw [c.Y_toBary, c.Y_toBary] at h
  have h2 := add_left_cancel h
  set u := toVec (y - fromBary c.x0)
  set u' := toVec (y' - fromBary c.x0)
  have hU : IsUnit (snocMat c.D (c.Y c.x0)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 c.hdet)
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hU
  have ha : snocMat c.D (c.Y c.x0) *ᵥ (Fin.snoc (u - u') 0 : Fin 6 → ℝ) =
      snocMat c.D (c.Y c.x0) *ᵥ 0 := by
    rw [snocMat_mulVec, Matrix.mulVec_zero]
    simp only [Fin.snoc_castSucc, snoc_six_five, zero_smul, add_zero, Pi.sub_apply, sub_smul,
      Finset.sum_sub_distrib, h2, sub_self]
  have h0 := hinj ha
  have huu : u = u' := by
    funext i
    have := congrFun h0 i.castSucc
    simp only [Fin.snoc_castSucc, Pi.sub_apply, Pi.zero_apply] at this
    linarith
  have : y - fromBary c.x0 = y' - fromBary c.x0 := by
    rw [← fromVec_toVec (y - fromBary c.x0), ← fromVec_toVec (y' - fromBary c.x0)]
    exact congrArg fromVec huu
  exact sub_left_injective this

lemma mem_Uo {y : ℝ × (Fin 4 → ℝ)} (hy : ∀ s, 0 < c.Y (toBary y) s) : y ∈ Uo :=
  c.hpos _ (sum_toBary y) hy

lemma sol_of_mem {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ c.zset) :
    affMat c.z *ᵥ c.Y (toBary y) = Pi.single 0 1 := by
  rw [affMat_mulVec_iff]
  refine ⟨c.sum_Y_toBary y, ?_⟩
  rw [← c.hell _ (sum_toBary y) hy.2, ← Fmap_of_mem (c.mem_Uo hy.2)]
  exact hy.1

lemma zset_subsingleton : c.zset.Subsingleton := by
  intro y hy y' hy'
  have h1 := c.sol_of_mem hy
  have h2 := c.sol_of_mem hy'
  have hdet := det_ne_zero_of_sol c.hz h1 (fun s => (hy.2 s).le)
  exact c.inj (sol_unique hdet h1 h2)

lemma frame_det_eq {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ c.zset) :
    (∃ a, IsFrameAt (Fmap q) y a) ∧
      (frameMat (ellLin m) (frameAt (Fmap q) y)).det =
        -(affMat c.z).det * (snocMat c.D (c.Y c.x0)).det := by
  have hsol := c.sol_of_mem hy
  obtain ⟨hs1, hs0⟩ := (affMat_mulVec_iff _ _).1 hsol
  obtain ⟨hex, hdet⟩ := frame_det (c.mem_Uo hy.2) c.FL (c.hloc _ (sum_toBary y) hy.2) c.YL c.z
    c.hlin c.hYL _ hs1 hs0
  refine ⟨hex, ?_⟩
  rw [hdet]
  congr 1
  rw [c.Y_toBary]
  exact det_snocMat_add _ _ _

lemma frame {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ c.zset) :
    (∃ a, IsFrameAt (Fmap q) y a) ∧ (frameMat (ellLin m) (frameAt (Fmap q) y)).det ≠ 0 := by
  obtain ⟨hex, h⟩ := c.frame_det_eq hy
  refine ⟨hex, ?_⟩
  rw [h]
  have := det_ne_zero_of_sol c.hz (c.sol_of_mem hy) (fun s => (hy.2 s).le)
  exact mul_ne_zero (neg_ne_zero.2 this) c.hdet

theorem finsum_zsign :
    ∑ᶠ y ∈ c.zset, zsign (ellLin m) (Fmap q) y = -c.eps * simplexIndex c.z := by
  by_cases hex : ∃ v : Fin 6 → ℝ, (∀ s, 0 < v s) ∧ affMat c.z *ᵥ v = Pi.single 0 1
  · obtain ⟨v, hvpos, hv⟩ := hex
    obtain ⟨hv1, hv0⟩ := (affMat_mulVec_iff _ _).1 hv
    obtain ⟨y, hy⟩ := c.surj hv1
    have hmem : y ∈ c.zset := by
      refine ⟨?_, by rw [hy]; exact hvpos⟩
      have hU : y ∈ Uo := c.mem_Uo (by rw [hy]; exact hvpos)
      rw [Fmap_of_mem hU, c.hell _ (sum_toBary y) (by rw [hy]; exact hvpos), hy, hv0]
    have hz : c.zset = {y} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨hmem, fun y' hy' => c.zset_subsingleton hy' hmem⟩
    rw [hz, finsum_mem_singleton, zsign, (c.frame_det_eq hmem).2, simplexIndex_of_sol hvpos hv,
      rsign_eq_sign, eps]
    simp only [sign_mul, Right.sign_neg, SignType.coe_mul, SignType.coe_neg]
    rw [show c.D = fun i => c.YL (toBaryL (unitE i)) from rfl]
    ring
  · have hz : c.zset = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      exact hex ⟨_, hy.2, c.sol_of_mem hy⟩
    rw [hz, finsum_mem_empty, simplexIndex_of_no_sol hex, mul_zero]

end CellData

end

end Tverberg6R
