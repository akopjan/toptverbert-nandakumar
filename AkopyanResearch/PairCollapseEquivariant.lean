module

public import AkopyanResearch.PairUniversalSource
public import AkopyanResearch.PairCollapse
public import AkopyanResearch.PlanarTestGlobal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

/-!
# Equivariant pair collapse map and cancellation homotopy

Constructs the orthogonal `PairGroup = S₄ × D₈` decomposition `Rep10 ≃ Priv4 ⊕ Comm6`,
verifies the `PairGroup`-equivariance and determinant `exchangeChar` of the collapse
target `PairTarget` of dimension `13`, proves equivariance of `pairCollapseMap` via
`PairNormalFrame.forward_natural`, and constructs the explicit `PairGroup`-equivariant
fold and radial-infty cancellation homotopy `invCancelHomotopy : unitInterval × OnePoint PairTarget → OnePoint PairTarget`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open scoped BigOperators InnerProductSpace OnePoint
open Metric

namespace AkopyanResearch

/-! ### 1. Orthogonal splitting `Rep10 ≃ Priv4 × Comm6` and orthonormal basis of `Priv4` -/

section Splitting

lemma linearIsometryEquiv_det_sq_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E ≃ₗᵢ[ℝ] E) : (LinearMap.det T.toLinearMap) ^ 2 = 1 := by
  let b := stdOrthonormalBasis ℝ E
  let M := LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap
  have hMtM : M.transpose * M = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hentry : ∀ k a, M k a = ⟪b k, T (b a)⟫_ℝ := fun k a => by
      simp only [M, LinearMap.toMatrix_apply,
        b.coe_toBasis_repr_apply, b.repr_apply_apply]
      rfl
    simp_rw [Matrix.transpose_apply, hentry]
    have hcomm : (∑ k, ⟪b k, T (b i)⟫_ℝ * ⟪b k, T (b j)⟫_ℝ) =
        ∑ k, ⟪T (b i), b k⟫_ℝ * ⟪b k, T (b j)⟫_ℝ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_comm (b k) (T (b i))]
    rw [hcomm, b.sum_inner_mul_inner, T.inner_map_map]
    by_cases hij : i = j
    · subst hij
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, Matrix.one_apply_eq]
    · rw [b.orthonormal.2 hij, Matrix.one_apply_ne hij]
  have hdet : M.det ^ 2 = 1 := by
    calc M.det ^ 2 = M.det * M.det := pow_two _
      _ = M.transpose.det * M.det := by rw [Matrix.det_transpose]
      _ = (M.transpose * M).det := (Matrix.det_mul _ _).symm
      _ = (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ).det := by rw [hMtM]
      _ = 1 := Matrix.det_one
  simpa [M, LinearMap.det_toMatrix] using hdet

lemma fin6_sum_castAdd (f : Fin 6 → ℝ) :
    (∑ j : Fin 6, f j) = (∑ i : Fin 4, f (i.castAdd 2)) + f 4 + f 5 := by
  simp [Fin.sum_univ_six, Fin.sum_univ_four]

lemma fin12_sum_split (f : Fin 12 → ℝ) :
    (∑ i : Fin 12, f i) = (∑ j : Fin 6, f (j.castAdd 6)) + ∑ j : Fin 6, f (Fin.natAdd 6 j) :=
  @Fin.sum_univ_add _ _ 6 6 f

def Comm6SubV10_map : ↥V10Sub →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := ![x.1 4, x.1 5, x.1 10, x.1 11]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

def Comm6SubV10 : Submodule ℝ (↥V10Sub) :=
  LinearMap.ker Comm6SubV10_map

lemma mem_Comm6SubV10_iff (x : ↥V10Sub) :
    x ∈ Comm6SubV10 ↔ x.1 4 = 0 ∧ x.1 5 = 0 ∧ x.1 10 = 0 ∧ x.1 11 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨h4, h5, h10, h11⟩
    ext i
    fin_cases i <;> simp [Comm6SubV10_map, h4, h5, h10, h11]

abbrev Comm6 := ↥Comm6SubV10
abbrev Priv4 := ↥Comm6SubV10ᗮ

def sum4Euc : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin 4, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

def W4Euc : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
  LinearMap.ker sum4Euc

lemma finrank_W4Euc : Module.finrank ℝ W4Euc = 3 := by
  have h1 := sum4Euc.finrank_range_add_finrank_ker
  have hsurj : Function.Surjective sum4Euc := fun y => by
    refine ⟨WithLp.toLp 2 (fun i : Fin 4 => if i = 0 then y else 0), ?_⟩
    simp [sum4Euc, Fin.sum_univ_four]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    finrank_euclideanSpace_fin] at h1
  change 1 + Module.finrank ℝ W4Euc = 4 at h1
  omega

lemma mem_V10Sub_of_W4 {a b : W4Euc} :
    (WithLp.equiv 2 (Fin 12 → ℝ)).symm
      (splitPair6
        (fun j : Fin 6 => if h : j.1 < 4 then a.1 ⟨j.1, h⟩ else 0)
        (fun j : Fin 6 => if h : j.1 < 4 then b.1 ⟨j.1, h⟩ else 0)) ∈ V10Sub := by
  rw [mem_V10Sub_iff]
  have ha : ∑ i : Fin 4, a.1 i = 0 := a.2
  have hb : ∑ i : Fin 4, b.1 i = 0 := b.2
  constructor
  · simp only [WithLp.equiv_symm_apply, splitPair6_castAdd]
    rw [fin6_sum_castAdd]
    have hsum : (∑ i : Fin 4, (if h : (i.castAdd 2).1 < 4 then a.1 ⟨(i.castAdd 2).1, h⟩ else 0)) =
        ∑ i : Fin 4, a.1 i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.isLt]
    rw [hsum, ha]
    simp
  · simp only [WithLp.equiv_symm_apply, splitPair6_natAdd]
    rw [fin6_sum_castAdd]
    have hsum : (∑ i : Fin 4, (if h : (i.castAdd 2).1 < 4 then b.1 ⟨(i.castAdd 2).1, h⟩ else 0)) =
        ∑ i : Fin 4, b.1 i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.isLt]
    rw [hsum, hb]
    simp

def comm6Equiv : Comm6 ≃ₗ[ℝ] (W4Euc × W4Euc) where
  toFun x :=
    (⟨WithLp.toLp 2 (fun i : Fin 4 => x.1.1 (i.castAdd 2 |>.castAdd 6)), by
        have hx := ((mem_V10Sub_iff x.1.1).mp x.1.2).1
        have hc := (mem_Comm6SubV10_iff x.1).mp x.2
        have hx' := fin6_sum_castAdd (fun j : Fin 6 => x.1.1 (j.castAdd 6))
        rw [hx] at hx'
        have h4 : x.1.1 ((4 : Fin 6).castAdd 6) = 0 := hc.1
        have h5 : x.1.1 ((5 : Fin 6).castAdd 6) = 0 := hc.2.1
        change (∑ i : Fin 4, x.1.1 ((i.castAdd 2).castAdd 6)) = 0
        linarith⟩,
      ⟨WithLp.toLp 2 (fun i : Fin 4 => x.1.1 (Fin.natAdd 6 (i.castAdd 2))), by
        have hx := ((mem_V10Sub_iff x.1.1).mp x.1.2).2
        have hc := (mem_Comm6SubV10_iff x.1).mp x.2
        have hx' := fin6_sum_castAdd (fun j : Fin 6 => x.1.1 (Fin.natAdd 6 j))
        rw [hx] at hx'
        have h4 : x.1.1 (Fin.natAdd 6 (4 : Fin 6)) = 0 := hc.2.2.1
        have h5 : x.1.1 (Fin.natAdd 6 (5 : Fin 6)) = 0 := hc.2.2.2
        change (∑ i : Fin 4, x.1.1 (Fin.natAdd 6 (i.castAdd 2))) = 0
        linarith⟩)
  invFun p :=
    ⟨⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm
        (splitPair6
          (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
          (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)),
        mem_V10Sub_of_W4⟩, by
      rw [mem_Comm6SubV10_iff]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (splitPair6
          (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
          (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)) ((4 : Fin 6).castAdd 6) = 0
        rw [splitPair6_castAdd]; simp
      · change (splitPair6
          (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
          (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)) ((5 : Fin 6).castAdd 6) = 0
        rw [splitPair6_castAdd]; simp
      · change (splitPair6
          (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
          (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)) (Fin.natAdd 6 (4 : Fin 6)) = 0
        rw [splitPair6_natAdd]; simp
      · change (splitPair6
          (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
          (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)) (Fin.natAdd 6 (5 : Fin 6)) = 0
        rw [splitPair6_natAdd]; simp⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext; ext i
    have hc := (mem_Comm6SubV10_iff x.1).mp x.2
    fin_cases i <;> simp [splitPair6, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> ext i
    · change (splitPair6
        (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
        (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)) ((i.castAdd 2).castAdd 6) = p.1.1 i
      rw [splitPair6_castAdd]; simp [i.isLt]
    · change (splitPair6
        (fun j : Fin 6 => if h : j.1 < 4 then p.1.1 ⟨j.1, h⟩ else 0)
        (fun j : Fin 6 => if h : j.1 < 4 then p.2.1 ⟨j.1, h⟩ else 0)) (Fin.natAdd 6 (i.castAdd 2)) = p.2.1 i
      rw [splitPair6_natAdd]; simp [i.isLt]
  map_add' x y := by apply Prod.ext <;> apply Subtype.ext <;> ext i <;> rfl
  map_smul' r x := by apply Prod.ext <;> apply Subtype.ext <;> ext i <;> rfl

theorem finrank_Comm6 : Module.finrank ℝ Comm6 = 6 := by
  rw [comm6Equiv.finrank_eq, Module.finrank_prod, finrank_W4Euc]

theorem finrank_Priv4 : Module.finrank ℝ Priv4 = 4 := by
  have h := Comm6SubV10.finrank_add_finrank_orthogonal
  have h1 : Module.finrank ℝ Comm6SubV10 = 6 := finrank_Comm6
  have h2 : Module.finrank ℝ ↥V10Sub = 10 := finrank_V10Sub
  change Module.finrank ℝ ↥Comm6SubV10ᗮ = 4
  omega

def diff45 (i : Fin 6) : ℝ :=
  if i = 4 then (Real.sqrt 2)⁻¹ else if i = 5 then -(Real.sqrt 2)⁻¹ else 0

lemma sum_diff45 : ∑ i : Fin 6, diff45 i = 0 := by
  simp [Fin.sum_univ_six, diff45]

def ePrivVec : Fin 4 → ↥V10Sub
  | 0 => ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 anchorVec6 (fun _ => 0)),
      embed6Left_mem anchorVec6 sum_anchorVec6⟩
  | 1 => anchorSub
  | 2 => ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 diff45 (fun _ => 0)),
      embed6Left_mem diff45 sum_diff45⟩
  | 3 => ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 (fun _ => 0) diff45),
      embed6Right_mem diff45 sum_diff45⟩

lemma ePrivVec_mem_Priv4 (k : Fin 4) : ePrivVec k ∈ Comm6SubV10ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hw' := (mem_Comm6SubV10_iff w).mp hw
  change ⟪w.1, (ePrivVec k).1⟫_ℝ = 0
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [fin12_sum_split]
  have h4 : w.1 4 = 0 := hw'.1
  have h5 : w.1 5 = 0 := hw'.2.1
  have h10 : w.1 10 = 0 := hw'.2.2.1
  have h11 : w.1 11 = 0 := hw'.2.2.2
  have hwL : w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5 = 0 := by
    simpa [Fin.sum_univ_six] using ((mem_V10Sub_iff w.1).mp w.2).1
  have hwR : w.1 6 + w.1 7 + w.1 8 + w.1 9 + w.1 10 + w.1 11 = 0 := by
    simpa [Fin.sum_univ_six] using ((mem_V10Sub_iff w.1).mp w.2).2
  fin_cases k
  · simp only [Fin.sum_univ_six, ePrivVec, WithLp.equiv_symm_apply, splitPair6_castAdd,
      splitPair6_natAdd, anchorVec6, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
    change (if (0 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 0 +
      (if (1 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 1 +
      (if (2 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 2 +
      (if (3 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 3 +
      (if (4 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 4 +
      (if (5 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 5 +
      (0 * w.1 6 + 0 * w.1 7 + 0 * w.1 8 + 0 * w.1 9 + 0 * w.1 10 + 0 * w.1 11) = 0
    rw [h4, h5] at hwL ⊢
    norm_num
    linear_combination (Real.sqrt 12)⁻¹ * hwL
  · simp only [Fin.sum_univ_six, ePrivVec, anchorSub, WithLp.equiv_symm_apply, splitPair6_castAdd,
      splitPair6_natAdd, anchorVec6, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
    change (0 * w.1 0 + 0 * w.1 1 + 0 * w.1 2 + 0 * w.1 3 + 0 * w.1 4 + 0 * w.1 5) +
      ((if (0 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 6 +
      (if (1 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 7 +
      (if (2 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 8 +
      (if (3 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 9 +
      (if (4 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 10 +
      (if (5 : ℕ) < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12) * w.1 11) = 0
    rw [h10, h11] at hwR ⊢
    norm_num
    linear_combination (Real.sqrt 12)⁻¹ * hwR
  · simp only [Fin.sum_univ_six, ePrivVec, WithLp.equiv_symm_apply, splitPair6_castAdd,
      splitPair6_natAdd, diff45, Fin.isValue]
    change (if (0 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (0 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 0 +
      (if (1 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (1 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 1 +
      (if (2 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (2 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 2 +
      (if (3 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (3 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 3 +
      (if (4 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (4 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 4 +
      (if (5 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (5 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 5 +
      (0 * w.1 6 + 0 * w.1 7 + 0 * w.1 8 + 0 * w.1 9 + 0 * w.1 10 + 0 * w.1 11) = 0
    rw [h4, h5]
    norm_num
  · simp only [Fin.sum_univ_six, ePrivVec, WithLp.equiv_symm_apply, splitPair6_castAdd,
      splitPair6_natAdd, diff45, Fin.isValue]
    change (0 * w.1 0 + 0 * w.1 1 + 0 * w.1 2 + 0 * w.1 3 + 0 * w.1 4 + 0 * w.1 5) +
      ((if (0 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (0 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 6 +
      (if (1 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (1 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 7 +
      (if (2 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (2 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 8 +
      (if (3 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (3 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 9 +
      (if (4 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (4 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 10 +
      (if (5 : Fin 6) = 4 then (Real.sqrt 2)⁻¹ else if (5 : Fin 6) = 5 then -(Real.sqrt 2)⁻¹ else 0) * w.1 11) = 0
    rw [h10, h11]
    norm_num

def ePriv (k : Fin 4) : Priv4 := ⟨ePrivVec k, ePrivVec_mem_Priv4 k⟩

lemma inner_ePriv (j k : Fin 4) : ⟪ePriv j, ePriv k⟫_ℝ = if j = k then 1 else 0 := by
  change ⟪(ePrivVec j).1, (ePrivVec k).1⟫_ℝ = if j = k then 1 else 0
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [fin12_sum_split, Fin.sum_univ_six, Fin.sum_univ_six]
  have hsq12 : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv12 : (Real.sqrt 12)⁻¹ * (Real.sqrt 12)⁻¹ = 1 / 12 := by
    rw [← mul_inv, ← pow_two, hsq12, one_div]
  have hinv2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← pow_two, hsq2, one_div]
  fin_cases j <;> fin_cases k <;>
    simp only [ePrivVec, anchorSub, WithLp.equiv_symm_apply, splitPair6_castAdd,
      splitPair6_natAdd, anchorVec6, diff45, Fin.isValue, Fin.ext_iff, Fin.val_zero,
      Fin.val_one, Fin.val_two, div_eq_mul_inv] <;>
    norm_num <;>
    nlinarith [hinv12, hinv2]

lemma orthonormal_ePriv : Orthonormal ℝ ePriv :=
  orthonormal_iff_ite.mpr fun i j => by simpa [eq_comm] using inner_ePriv i j

def privBasis4 : OrthonormalBasis (Fin 4) ℝ Priv4 :=
  Module.Basis.toOrthonormalBasis
    (basisOfOrthonormalOfCardEqFinrank orthonormal_ePriv (by simp [finrank_Priv4]))
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact orthonormal_ePriv)

@[simp] lemma privBasis4_apply (k : Fin 4) : privBasis4 k = ePriv k := by
  simp [privBasis4]

def swapWithLp (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    WithLp 2 (E × F) ≃ₗᵢ[ℝ] WithLp 2 (F × E) where
  toFun p := WithLp.toLp 2 (p.snd, p.fst)
  invFun p := WithLp.toLp 2 (p.snd, p.fst)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, add_comm]
    rfl

def splitRep10 : Rep10 ≃ₗᵢ[ℝ] WithLp 2 (Priv4 × Comm6) :=
  iso10.symm.trans (Comm6SubV10.orthogonalDecomposition.trans (swapWithLp Comm6 Priv4))

def spherePairEquiv :
    (Metric.sphere (0 : Rep10) 1 × Metric.sphere (0 : Rep10) 1) ≃ₜ
      PairCollapse.PairSpace Priv4 Priv4 Comm6 where
  toFun p :=
    (⟨WithLp.ofLp (splitRep10 p.1.1), by
        change ‖(splitRep10 p.1.1).fst‖ ^ 2 + ‖(splitRep10 p.1.1).snd‖ ^ 2 = 1
        have h := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Comm6 _ _ (splitRep10 p.1.1)
        rw [← h, splitRep10.norm_map, mem_sphere_zero_iff_norm.mp p.1.2, one_pow]⟩,
      ⟨WithLp.ofLp (splitRep10 p.2.1), by
        change ‖(splitRep10 p.2.1).fst‖ ^ 2 + ‖(splitRep10 p.2.1).snd‖ ^ 2 = 1
        have h := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Comm6 _ _ (splitRep10 p.2.1)
        rw [← h, splitRep10.norm_map, mem_sphere_zero_iff_norm.mp p.2.2, one_pow]⟩)
  invFun q :=
    (⟨splitRep10.symm (WithLp.toLp 2 q.1.1), by
        rw [mem_sphere_zero_iff_norm, splitRep10.symm.norm_map,
          ← sq_eq_sq₀ (norm_nonneg (WithLp.toLp 2 q.1.1)) zero_le_one, one_pow]
        have h := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Comm6 _ _ (WithLp.toLp 2 q.1.1)
        rw [h]
        exact q.1.2⟩,
      ⟨splitRep10.symm (WithLp.toLp 2 q.2.1), by
        rw [mem_sphere_zero_iff_norm, splitRep10.symm.norm_map,
          ← sq_eq_sq₀ (norm_nonneg (WithLp.toLp 2 q.2.1)) zero_le_one, one_pow]
        have h := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Comm6 _ _ (WithLp.toLp 2 q.2.1)
        rw [h]
        exact q.2.2⟩)
  left_inv p := by apply Prod.ext <;> apply Subtype.ext <;> simp
  right_inv q := by apply Prod.ext <;> apply Subtype.ext <;> simp
  continuous_toFun := by
    have h1 : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × Metric.sphere (0 : Rep10) 1 =>
        WithLp.ofLp (splitRep10 p.1.1)) :=
      (WithLp.homeomorphProd 2 Priv4 Comm6).continuous.comp
        (splitRep10.continuous.comp (continuous_subtype_val.comp continuous_fst))
    have h2 : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × Metric.sphere (0 : Rep10) 1 =>
        WithLp.ofLp (splitRep10 p.2.1)) :=
      (WithLp.homeomorphProd 2 Priv4 Comm6).continuous.comp
        (splitRep10.continuous.comp (continuous_subtype_val.comp continuous_snd))
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)
  continuous_invFun := by
    have h1 : Continuous (fun q : PairCollapse.PairSpace Priv4 Priv4 Comm6 =>
        splitRep10.symm (WithLp.toLp 2 q.1.1)) :=
      splitRep10.symm.continuous.comp
        ((WithLp.homeomorphProd 2 Priv4 Comm6).symm.continuous.comp
          (continuous_subtype_val.comp continuous_fst))
    have h2 : Continuous (fun q : PairCollapse.PairSpace Priv4 Priv4 Comm6 =>
        splitRep10.symm (WithLp.toLp 2 q.2.1)) :=
      splitRep10.symm.continuous.comp
        ((WithLp.homeomorphProd 2 Priv4 Comm6).symm.continuous.comp
          (continuous_subtype_val.comp continuous_snd))
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)

end Splitting

/-! ### 2. Left `PairGroup`-action on `Comm6`, `Priv4`, `PairSpace`, and `Residual` -/

section Actions

def liftPerm4 (g : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  colPerm4 g 1 false

lemma liftPerm4_castAdd (g : Equiv.Perm (Fin 4)) (i : Fin 4) :
    liftPerm4 g (i.castAdd 2) = (g i).castAdd 2 :=
  colPerm4_castAdd g 1 false i

lemma liftPerm4_natAdd (g : Equiv.Perm (Fin 4)) (j : Fin 2) :
    liftPerm4 g (Fin.natAdd 4 j) = Fin.natAdd 4 j := by
  simpa [liftPerm4, sResPerm] using colPerm4_natAdd g 1 false j

lemma liftPerm4_one : liftPerm4 1 = 1 := by
  ext i
  rcases Nat.lt_or_ge i.1 4 with hi | hi
  · let j : Fin 4 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 2 := Fin.ext rfl
    rw [hij, liftPerm4_castAdd]; rfl
  · let j : Fin 2 := ⟨i.1 - 4, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 4 j := Fin.ext (by simp [j]; omega)
    rw [hij, liftPerm4_natAdd]; rfl

lemma liftPerm4_mul (g₁ g₂ : Equiv.Perm (Fin 4)) :
    liftPerm4 (g₁ * g₂) = liftPerm4 g₁ * liftPerm4 g₂ := by
  ext i
  rcases Nat.lt_or_ge i.1 4 with hi | hi
  · let j : Fin 4 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 2 := Fin.ext rfl
    rw [hij]
    simp [liftPerm4_castAdd, Equiv.Perm.mul_apply]
  · let j : Fin 2 := ⟨i.1 - 4, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 4 j := Fin.ext (by simp [j]; omega)
    rw [hij, Equiv.Perm.mul_apply, liftPerm4_natAdd, liftPerm4_natAdd, liftPerm4_natAdd]

lemma liftPerm4_inv (g : Equiv.Perm (Fin 4)) : (liftPerm4 g)⁻¹ = liftPerm4 g⁻¹ := by
  apply mul_left_cancel (a := liftPerm4 g)
  rw [mul_inv_cancel, ← liftPerm4_mul, mul_inv_cancel, liftPerm4_one]

lemma permSub_liftPerm4_mem_Comm6 (g : Equiv.Perm (Fin 4)) {x : ↥V10Sub}
    (hx : x ∈ Comm6SubV10) : permSub (liftPerm4 g) x ∈ Comm6SubV10 := by
  rw [mem_Comm6SubV10_iff] at hx ⊢
  change x.1 ((perm12 (liftPerm4 g)).symm 4) = 0 ∧ x.1 ((perm12 (liftPerm4 g)).symm 5) = 0 ∧
    x.1 ((perm12 (liftPerm4 g)).symm 10) = 0 ∧ x.1 ((perm12 (liftPerm4 g)).symm 11) = 0
  have h4 : (perm12 (liftPerm4 g)).symm 4 = 4 := by
    rw [perm12_symm, liftPerm4_inv]
    change perm12 (liftPerm4 g⁻¹) ((Fin.natAdd 4 (0 : Fin 2)).castAdd 6) = _
    rw [perm12_castAdd, liftPerm4_natAdd]; rfl
  have h5 : (perm12 (liftPerm4 g)).symm 5 = 5 := by
    rw [perm12_symm, liftPerm4_inv]
    change perm12 (liftPerm4 g⁻¹) ((Fin.natAdd 4 (1 : Fin 2)).castAdd 6) = _
    rw [perm12_castAdd, liftPerm4_natAdd]; rfl
  have h10 : (perm12 (liftPerm4 g)).symm 10 = 10 := by
    rw [perm12_symm, liftPerm4_inv]
    change perm12 (liftPerm4 g⁻¹) (Fin.natAdd 6 (Fin.natAdd 4 (0 : Fin 2))) = _
    rw [perm12_natAdd, liftPerm4_natAdd]; rfl
  have h11 : (perm12 (liftPerm4 g)).symm 11 = 11 := by
    rw [perm12_symm, liftPerm4_inv]
    change perm12 (liftPerm4 g⁻¹) (Fin.natAdd 6 (Fin.natAdd 4 (1 : Fin 2))) = _
    rw [perm12_natAdd, liftPerm4_natAdd]; rfl
  rw [h4, h5, h10, h11]
  exact hx

def actComm (g : Equiv.Perm (Fin 4)) : Comm6 ≃ₗᵢ[ℝ] Comm6 where
  toFun x := ⟨permSub (liftPerm4 g) x.1, permSub_liftPerm4_mem_Comm6 g x.2⟩
  invFun x := ⟨permSub (liftPerm4 g⁻¹) x.1, permSub_liftPerm4_mem_Comm6 g⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    show permSub (liftPerm4 g⁻¹) (permSub (liftPerm4 g) x.1) = x.1
    rw [← liftPerm4_inv]
    exact (permSub (liftPerm4 g)).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    show permSub (liftPerm4 g) (permSub (liftPerm4 g⁻¹) x.1) = x.1
    rw [← liftPerm4_inv]
    exact (permSub (liftPerm4 g)).right_inv x.1
  map_add' x y := by apply Subtype.ext; exact map_add (permSub (liftPerm4 g)) x.1 y.1
  map_smul' r x := by apply Subtype.ext; exact map_smul (permSub (liftPerm4 g)) r x.1
  norm_map' x := (permSub (liftPerm4 g)).norm_map x.1

lemma actComm_one (w : Comm6) : actComm 1 w = w := by
  apply Subtype.ext; apply Subtype.ext; ext i
  show w.1.1 ((perm12 (liftPerm4 1)).symm i) = w.1.1 i
  rw [liftPerm4_one, perm12_one]; rfl

lemma actComm_mul (g₁ g₂ : Equiv.Perm (Fin 4)) (w : Comm6) :
    actComm (g₁ * g₂) w = actComm g₁ (actComm g₂ w) := by
  apply Subtype.ext; apply Subtype.ext; ext i
  show w.1.1 ((perm12 (liftPerm4 (g₁ * g₂))).symm i) =
    w.1.1 ((perm12 (liftPerm4 g₂)).symm ((perm12 (liftPerm4 g₁)).symm i))
  rw [liftPerm4_mul, perm12_mul]; rfl

def actW4Euc (g : Equiv.Perm (Fin 4)) : W4Euc ≃ₗᵢ[ℝ] W4Euc where
  toFun x := ⟨WithLp.toLp 2 (fun i => x.1 (g⁻¹ i)), by
    change ∑ i : Fin 4, x.1 (g⁻¹ i) = 0
    rw [Fintype.sum_equiv g⁻¹ _ (fun i => x.1 i) (fun _ => rfl)]
    exact x.2⟩
  invFun x := ⟨WithLp.toLp 2 (fun i => x.1 (g i)), by
    change ∑ i : Fin 4, x.1 (g i) = 0
    rw [Fintype.sum_equiv g _ (fun i => x.1 i) (fun _ => rfl)]
    exact x.2⟩
  left_inv x := by apply Subtype.ext; ext i; simp
  right_inv x := by apply Subtype.ext; ext i; simp
  map_add' x y := by apply Subtype.ext; ext i; rfl
  map_smul' r x := by apply Subtype.ext; ext i; rfl
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    change ‖WithLp.toLp 2 (fun i => x.1 (g⁻¹ i))‖ ^ 2 = ‖x.1‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Fintype.sum_equiv g⁻¹ _ _ fun i => rfl

lemma det_actComm (g : Equiv.Perm (Fin 4)) :
    LinearMap.det (actComm g).toLinearMap = 1 := by
  have hconj : comm6Equiv.toLinearMap ∘ₗ (actComm g).toLinearMap ∘ₗ comm6Equiv.symm.toLinearMap =
      LinearMap.prodMap (actW4Euc g).toLinearMap (actW4Euc g).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · apply Subtype.ext; ext i
      change (comm6Equiv.symm x).1.1 ((perm12 (liftPerm4 g)).symm ((i.castAdd 2).castAdd 6)) =
        x.1.1 (g⁻¹ i)
      rw [perm12_symm, liftPerm4_inv, perm12_castAdd, liftPerm4_castAdd]
      change (splitPair6
        (fun j : Fin 6 => if h : j.1 < 4 then x.1.1 ⟨j.1, h⟩ else 0)
        (fun j : Fin 6 => if h : j.1 < 4 then x.2.1 ⟨j.1, h⟩ else 0))
        ((g⁻¹ i).castAdd 2 |>.castAdd 6) = x.1.1 (g⁻¹ i)
      rw [splitPair6_castAdd]
      simp
    · apply Subtype.ext; ext i
      change (comm6Equiv.symm x).1.1 ((perm12 (liftPerm4 g)).symm (Fin.natAdd 6 (i.castAdd 2))) =
        x.2.1 (g⁻¹ i)
      rw [perm12_symm, liftPerm4_inv, perm12_natAdd, liftPerm4_castAdd]
      change (splitPair6
        (fun j : Fin 6 => if h : j.1 < 4 then x.1.1 ⟨j.1, h⟩ else 0)
        (fun j : Fin 6 => if h : j.1 < 4 then x.2.1 ⟨j.1, h⟩ else 0))
        (Fin.natAdd 6 ((g⁻¹ i).castAdd 2)) = x.2.1 (g⁻¹ i)
      rw [splitPair6_natAdd]
      simp
  have hdet_eq : LinearMap.det (actComm g).toLinearMap =
      (LinearMap.det (actW4Euc g).toLinearMap) ^ 2 := by
    calc LinearMap.det (actComm g).toLinearMap
        = LinearMap.det (comm6Equiv.toLinearMap ∘ₗ (actComm g).toLinearMap ∘ₗ
            comm6Equiv.symm.toLinearMap) := (LinearMap.det_conj _ comm6Equiv).symm
      _ = LinearMap.det (LinearMap.prodMap (actW4Euc g).toLinearMap (actW4Euc g).toLinearMap) := by
          rw [hconj]
      _ = LinearMap.det (actW4Euc g).toLinearMap * LinearMap.det (actW4Euc g).toLinearMap :=
          LinearMap.det_prodMap _ _
      _ = (LinearMap.det (actW4Euc g).toLinearMap) ^ 2 := (pow_two _).symm
  rw [hdet_eq]
  exact linearIsometryEquiv_det_sq_eq_one (actW4Euc g)

lemma perm12_swap45_Involutive (i : Fin 12) :
    (perm12 (Equiv.swap (4 : Fin 6) 5)).symm ((perm12 (Equiv.swap (4 : Fin 6) 5)).symm i) = i := by
  decide +revert

lemma permSub_swap45_mem_Priv4 {u : ↥V10Sub} (hu : u ∈ Comm6SubV10ᗮ) :
    permSub (Equiv.swap (4 : Fin 6) 5) u ∈ Comm6SubV10ᗮ := by
  rw [Submodule.mem_orthogonal] at hu ⊢
  intro w hw
  have hfix : permSub (Equiv.swap (4 : Fin 6) 5) w = w := by
    have hw' := (mem_Comm6SubV10_iff w).mp hw
    apply Subtype.ext; ext i
    change w.1 ((perm12 (Equiv.swap (4 : Fin 6) 5)).symm i) = w.1 i
    have h4 : (perm12 (Equiv.swap (4 : Fin 6) 5)).symm 4 = 5 := by decide
    have h5 : (perm12 (Equiv.swap (4 : Fin 6) 5)).symm 5 = 4 := by decide
    have h10 : (perm12 (Equiv.swap (4 : Fin 6) 5)).symm 10 = 11 := by decide
    have h11 : (perm12 (Equiv.swap (4 : Fin 6) 5)).symm 11 = 10 := by decide
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · change w.1 ((perm12 (Equiv.swap (4 : Fin 6) 5)).symm 4) = w.1 4
      rw [h4, hw'.1, hw'.2.1]
    · change w.1 ((perm12 (Equiv.swap (4 : Fin 6) 5)).symm 5) = w.1 5
      rw [h5, hw'.1, hw'.2.1]
    · rfl
    · rfl
    · rfl
    · rfl
    · change w.1 ((perm12 (Equiv.swap (4 : Fin 6) 5)).symm 10) = w.1 10
      rw [h10, hw'.2.2.1, hw'.2.2.2]
    · change w.1 ((perm12 (Equiv.swap (4 : Fin 6) 5)).symm 11) = w.1 11
      rw [h11, hw'.2.2.1, hw'.2.2.2]
  have hin : ⟪permSub (Equiv.swap (4 : Fin 6) 5) w, permSub (Equiv.swap (4 : Fin 6) 5) u⟫_ℝ =
      ⟪w, u⟫_ℝ := (permSub (Equiv.swap (4 : Fin 6) 5)).inner_map_map w u
  rw [hfix] at hin
  rw [hin]
  exact hu w hw

def swapPriv : Priv4 ≃ₗᵢ[ℝ] Priv4 where
  toFun u := ⟨permSub (Equiv.swap (4 : Fin 6) 5) u.1, permSub_swap45_mem_Priv4 u.2⟩
  invFun u := ⟨permSub (Equiv.swap (4 : Fin 6) 5) u.1, permSub_swap45_mem_Priv4 u.2⟩
  left_inv u := by
    apply Subtype.ext; apply Subtype.ext; ext i
    change u.1.1 ((perm12 (Equiv.swap 4 5)).symm ((perm12 (Equiv.swap 4 5)).symm i)) = u.1.1 i
    rw [perm12_swap45_Involutive]
  right_inv u := by
    apply Subtype.ext; apply Subtype.ext; ext i
    change u.1.1 ((perm12 (Equiv.swap 4 5)).symm ((perm12 (Equiv.swap 4 5)).symm i)) = u.1.1 i
    rw [perm12_swap45_Involutive]
  map_add' x y := by apply Subtype.ext; exact map_add (permSub (Equiv.swap 4 5)) x.1 y.1
  map_smul' r x := by apply Subtype.ext; exact map_smul (permSub (Equiv.swap 4 5)) r x.1
  norm_map' x := (permSub (Equiv.swap 4 5)).norm_map x.1

@[simp] lemma swapPriv_involutive (u : Priv4) : swapPriv (swapPriv u) = u :=
  swapPriv.left_inv u

lemma perm12_swap45_symm_apply (i : Fin 12) :
    (perm12 (Equiv.swap (4 : Fin 6) 5)).symm i =
      ![0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10] i := by
  decide +revert

lemma swapPriv_apply_ePriv0 : swapPriv (ePriv 0) = ePriv 0 := by
  apply Subtype.ext; apply Subtype.ext; ext i
  change (ePrivVec 0).1 ((perm12 (Equiv.swap 4 5)).symm i) = (ePrivVec 0).1 i
  rw [perm12_swap45_symm_apply]
  fin_cases i <;> simp [ePrivVec, splitPair6, anchorVec6]

lemma swapPriv_apply_ePriv1 : swapPriv (ePriv 1) = ePriv 1 := by
  apply Subtype.ext; apply Subtype.ext; ext i
  change (ePrivVec 1).1 ((perm12 (Equiv.swap 4 5)).symm i) = (ePrivVec 1).1 i
  rw [perm12_swap45_symm_apply]
  fin_cases i <;> simp [ePrivVec, anchorSub, splitPair6, anchorVec6]

lemma swapPriv_apply_ePriv2 : swapPriv (ePriv 2) = -ePriv 2 := by
  apply Subtype.ext; apply Subtype.ext; ext i
  change (ePrivVec 2).1 ((perm12 (Equiv.swap 4 5)).symm i) = -(ePrivVec 2).1 i
  rw [perm12_swap45_symm_apply]
  fin_cases i <;> simp [ePrivVec, splitPair6, diff45]

lemma swapPriv_apply_ePriv3 : swapPriv (ePriv 3) = -ePriv 3 := by
  apply Subtype.ext; apply Subtype.ext; ext i
  change (ePrivVec 3).1 ((perm12 (Equiv.swap 4 5)).symm i) = -(ePrivVec 3).1 i
  rw [perm12_swap45_symm_apply]
  fin_cases i <;> simp [ePrivVec, splitPair6, diff45]

lemma det_swapPriv : LinearMap.det swapPriv.toLinearMap = 1 := by
  let b := privBasis4.toBasis
  have hmat : LinearMap.toMatrix b b swapPriv.toLinearMap = Matrix.diagonal ![1, 1, -1, -1] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (swapPriv (privBasis4 j)) i = Matrix.diagonal ![1, 1, -1, -1] i j
    rw [privBasis4.coe_toBasis_repr_apply, privBasis4_apply j, privBasis4.repr_apply_apply,
      privBasis4_apply i]
    fin_cases j
    · change ⟪ePriv i, swapPriv (ePriv 0)⟫_ℝ = Matrix.diagonal ![1, 1, -1, -1] i 0
      rw [swapPriv_apply_ePriv0, inner_ePriv]; fin_cases i <;> rfl
    · change ⟪ePriv i, swapPriv (ePriv 1)⟫_ℝ = Matrix.diagonal ![1, 1, -1, -1] i 1
      rw [swapPriv_apply_ePriv1, inner_ePriv]; fin_cases i <;> rfl
    · change ⟪ePriv i, swapPriv (ePriv 2)⟫_ℝ = Matrix.diagonal ![1, 1, -1, -1] i 2
      rw [swapPriv_apply_ePriv2, inner_neg_right, inner_ePriv]; fin_cases i <;> norm_num [Matrix.diagonal]
    · change ⟪ePriv i, swapPriv (ePriv 3)⟫_ℝ = Matrix.diagonal ![1, 1, -1, -1] i 3
      rw [swapPriv_apply_ePriv3, inner_neg_right, inner_ePriv]; fin_cases i <;> norm_num [Matrix.diagonal]
  rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_four]

def privSign (b : Bool) : Priv4 ≃ₗᵢ[ℝ] Priv4 :=
  if b then swapPriv else LinearIsometryEquiv.refl ℝ Priv4

lemma privSign_false : privSign false = LinearIsometryEquiv.refl ℝ Priv4 := rfl
lemma privSign_true : privSign true = swapPriv := rfl

lemma privSign_xor (a b : Bool) (u : Priv4) :
    privSign (xor a b) u = privSign a (privSign b u) := by
  cases a <;> cases b <;> simp [privSign]

lemma det_privSign (b : Bool) : LinearMap.det (privSign b).toLinearMap = 1 := by
  cases b
  · simp [privSign]
  · simp [privSign, det_swapPriv]

def actY (h : PairGroup) (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    PairCollapse.PairSpace Priv4 Priv4 Comm6 :=
  let x₁ : PairCollapse.FullUnit Priv4 Comm6 :=
    ⟨(privSign h.2.sa x.1.1.1, actComm h.1 x.1.1.2), by
      rw [(privSign h.2.sa).norm_map, (actComm h.1).norm_map]; exact x.1.2⟩
  let x₂ : PairCollapse.FullUnit Priv4 Comm6 :=
    ⟨(privSign h.2.sb x.2.1.1, actComm h.1 x.2.1.2), by
      rw [(privSign h.2.sb).norm_map, (actComm h.1).norm_map]; exact x.2.2⟩
  if h.2.ex then (x₂, x₁) else (x₁, x₂)

lemma actY_one (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) : actY 1 x = x := by
  apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
  · change privSign false x.1.1.1 = x.1.1.1
    rw [privSign_false]; rfl
  · change actComm 1 x.1.1.2 = x.1.1.2
    exact actComm_one x.1.1.2
  · change privSign false x.2.1.1 = x.2.1.1
    rw [privSign_false]; rfl
  · change actComm 1 x.2.1.2 = x.2.1.2
    exact actComm_one x.2.1.2

lemma actY_mul (h₁ h₂ : PairGroup) (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    actY (h₁ * h₂) x = actY h₁ (actY h₂ x) := by
  rcases h₁ with ⟨g₁, ⟨sa₁, sb₁, ex₁⟩⟩
  rcases h₂ with ⟨g₂, ⟨sa₂, sb₂, ex₂⟩⟩
  cases ex₁ <;> cases ex₂
  · apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
    · exact privSign_xor sa₁ sa₂ x.1.1.1
    · exact actComm_mul g₁ g₂ x.1.1.2
    · exact privSign_xor sb₁ sb₂ x.2.1.1
    · exact actComm_mul g₁ g₂ x.2.1.2
  · apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
    · exact privSign_xor sa₁ sb₂ x.2.1.1
    · exact actComm_mul g₁ g₂ x.2.1.2
    · exact privSign_xor sb₁ sa₂ x.1.1.1
    · exact actComm_mul g₁ g₂ x.1.1.2
  · apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
    · exact privSign_xor sb₁ sb₂ x.2.1.1
    · exact actComm_mul g₁ g₂ x.2.1.2
    · exact privSign_xor sa₁ sa₂ x.1.1.1
    · exact actComm_mul g₁ g₂ x.1.1.2
  · apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
    · exact privSign_xor sb₁ sa₂ x.1.1.1
    · exact actComm_mul g₁ g₂ x.1.1.2
    · exact privSign_xor sa₁ sb₂ x.2.1.1
    · exact actComm_mul g₁ g₂ x.2.1.2

lemma continuous_actY (h : PairGroup) : Continuous (actY h) := by
  let f₁ : PairCollapse.PairSpace Priv4 Priv4 Comm6 → PairCollapse.FullUnit Priv4 Comm6 :=
    fun x => ⟨(privSign h.2.sa x.1.1.1, actComm h.1 x.1.1.2), by
      rw [(privSign h.2.sa).norm_map, (actComm h.1).norm_map]; exact x.1.2⟩
  let f₂ : PairCollapse.PairSpace Priv4 Priv4 Comm6 → PairCollapse.FullUnit Priv4 Comm6 :=
    fun x => ⟨(privSign h.2.sb x.2.1.1, actComm h.1 x.2.1.2), by
      rw [(privSign h.2.sb).norm_map, (actComm h.1).norm_map]; exact x.2.2⟩
  have hf₁ : Continuous f₁ := by
    apply Continuous.subtype_mk
    exact ((privSign h.2.sa).continuous.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))).prodMk
      ((actComm h.1).continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)))
  have hf₂ : Continuous f₂ := by
    apply Continuous.subtype_mk
    exact ((privSign h.2.sb).continuous.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))).prodMk
      ((actComm h.1).continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
  cases hex : h.2.ex
  · have heq : actY h = fun x => (f₁ x, f₂ x) := by
      funext x; simp [actY, f₁, f₂, hex]
    rw [heq]
    exact hf₁.prodMk hf₂
  · have heq : actY h = fun x => (f₂ x, f₁ x) := by
      funext x; simp [actY, f₁, f₂, hex]
    rw [heq]
    exact hf₂.prodMk hf₁

def actRes (h : PairGroup) :
    PairCollapse.Residual (U := Priv4) (V := Priv4) ≃ₗᵢ[ℝ]
      PairCollapse.Residual (U := Priv4) (V := Priv4) where
  toFun r := WithLp.toLp 2
    (if h.2.ex then (privSign h.2.sb r.snd, privSign h.2.sa r.fst)
     else (privSign h.2.sa r.fst, privSign h.2.sb r.snd))
  invFun r := WithLp.toLp 2
    (if h.2.ex then (privSign h.2.sa r.snd, privSign h.2.sb r.fst)
     else (privSign h.2.sa r.fst, privSign h.2.sb r.snd))
  left_inv r := by
    rcases h with ⟨g, ⟨sa, sb, ex⟩⟩
    apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
    apply Prod.ext
    · cases ex <;> cases sa <;> cases sb <;> simp [privSign, swapPriv_involutive]
    · cases ex <;> cases sa <;> cases sb <;> simp [privSign, swapPriv_involutive]
  right_inv r := by
    rcases h with ⟨g, ⟨sa, sb, ex⟩⟩
    apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
    apply Prod.ext
    · cases ex <;> cases sa <;> cases sb <;> simp [privSign, swapPriv_involutive]
    · cases ex <;> cases sa <;> cases sb <;> simp [privSign, swapPriv_involutive]
  map_add' r₁ r₂ := by
    apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
    apply Prod.ext <;> cases h.2.ex <;> simp [map_add]
  map_smul' c r := by
    apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
    apply Prod.ext <;> cases h.2.ex <;> simp [map_smul]
  norm_map' r := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h1 := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Priv4 _ _
      (WithLp.toLp 2
        (if h.2.ex then (privSign h.2.sb r.snd, privSign h.2.sa r.fst)
         else (privSign h.2.sa r.fst, privSign h.2.sb r.snd)))
    have h2 := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Priv4 _ _ r
    change ‖WithLp.toLp 2
        (if h.2.ex then (privSign h.2.sb r.snd, privSign h.2.sa r.fst)
         else (privSign h.2.sa r.fst, privSign h.2.sb r.snd))‖ ^ 2 = ‖r‖ ^ 2
    rw [h1, h2]
    cases h.2.ex
    · change ‖privSign h.2.sa r.fst‖ ^ 2 + ‖privSign h.2.sb r.snd‖ ^ 2 = ‖r.fst‖ ^ 2 + ‖r.snd‖ ^ 2
      rw [(privSign h.2.sa).norm_map, (privSign h.2.sb).norm_map]
    · change ‖privSign h.2.sb r.snd‖ ^ 2 + ‖privSign h.2.sa r.fst‖ ^ 2 = ‖r.fst‖ ^ 2 + ‖r.snd‖ ^ 2
      rw [(privSign h.2.sb).norm_map, (privSign h.2.sa).norm_map, add_comm]

lemma actRes_one (r : PairCollapse.Residual (U := Priv4) (V := Priv4)) :
    actRes 1 r = r := by
  apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
  apply Prod.ext
  · change privSign false r.fst = r.fst
    rw [privSign_false]; rfl
  · change privSign false r.snd = r.snd
    rw [privSign_false]; rfl

lemma actRes_mul (h₁ h₂ : PairGroup) (r : PairCollapse.Residual (U := Priv4) (V := Priv4)) :
    actRes (h₁ * h₂) r = actRes h₁ (actRes h₂ r) := by
  rcases h₁ with ⟨g₁, ⟨sa₁, sb₁, ex₁⟩⟩
  rcases h₂ with ⟨g₂, ⟨sa₂, sb₂, ex₂⟩⟩
  cases ex₁ <;> cases ex₂
  · apply (WithLp.equiv 2 (Priv4 × Priv4)).injective; apply Prod.ext
    · exact privSign_xor sa₁ sa₂ r.fst
    · exact privSign_xor sb₁ sb₂ r.snd
  · apply (WithLp.equiv 2 (Priv4 × Priv4)).injective; apply Prod.ext
    · exact privSign_xor sa₁ sb₂ r.snd
    · exact privSign_xor sb₁ sa₂ r.fst
  · apply (WithLp.equiv 2 (Priv4 × Priv4)).injective; apply Prod.ext
    · exact privSign_xor sb₁ sb₂ r.snd
    · exact privSign_xor sa₁ sa₂ r.fst
  · apply (WithLp.equiv 2 (Priv4 × Priv4)).injective; apply Prod.ext
    · exact privSign_xor sb₁ sa₂ r.fst
    · exact privSign_xor sa₁ sb₂ r.snd

lemma det_actRes (h : PairGroup) : LinearMap.det (actRes h).toLinearMap = 1 := by
  let B := OrthonormalBasis.prod privBasis4 privBasis4
  let b := B.toBasis
  let block : (Priv4 × Priv4) →ₗ[ℝ] (Priv4 × Priv4) :=
    LinearMap.prodMap (privSign h.2.sa).toLinearMap (privSign h.2.sb).toLinearMap
  have hblock_det : LinearMap.det block = 1 := by
    rw [LinearMap.det_prodMap, det_privSign, det_privSign, mul_one]
  let blockL : PairCollapse.Residual (U := Priv4) (V := Priv4) →ₗ[ℝ]
      PairCollapse.Residual (U := Priv4) (V := Priv4) :=
    (WithLp.linearEquiv 2 ℝ (Priv4 × Priv4)).symm.toLinearMap ∘ₗ
      block ∘ₗ (WithLp.linearEquiv 2 ℝ (Priv4 × Priv4)).toLinearMap
  have hblockL_det : LinearMap.det blockL = 1 :=
    (LinearMap.det_conj block (WithLp.linearEquiv 2 ℝ (Priv4 × Priv4)).symm).trans hblock_det
  cases hex : h.2.ex
  · have heq : (actRes h).toLinearMap = blockL := by
      apply LinearMap.ext; intro r
      apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
      apply Prod.ext <;> simp [blockL, block, actRes, hex]
    rw [heq, hblockL_det]
  · let Eswap : PairCollapse.Residual (U := Priv4) (V := Priv4) →ₗ[ℝ]
        PairCollapse.Residual (U := Priv4) (V := Priv4) :=
      (swapWithLp Priv4 Priv4).toLinearMap
    have heq : (actRes h).toLinearMap = Eswap ∘ₗ blockL := by
      apply LinearMap.ext; intro r
      apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
      apply Prod.ext <;> simp [Eswap, swapWithLp, blockL, block, actRes, hex]
    have hEB : ∀ j, Eswap (B j) = B (Equiv.sumComm (Fin 4) (Fin 4) j) := by
      rintro (j | j) <;>
        apply (WithLp.equiv 2 (Priv4 × Priv4)).injective <;>
        apply Prod.ext <;> simp [Eswap, swapWithLp, B]
    have hEmat : LinearMap.toMatrix b b Eswap =
        Equiv.Perm.permMatrix ℝ (Equiv.sumComm (Fin 4) (Fin 4)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, B.coe_toBasis_repr_apply, B.coe_toBasis, hEB j,
        B.repr_apply_apply]
      have hon := orthonormal_iff_ite.mp B.orthonormal i (Equiv.sumComm (Fin 4) (Fin 4) j)
      rw [hon]
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
    have hsign : Equiv.Perm.sign (Equiv.sumComm (Fin 4) (Fin 4)) = 1 := by decide
    have hEdet : LinearMap.det Eswap = 1 := by
      rw [← LinearMap.det_toMatrix b, hEmat, Matrix.det_permutation, hsign]
      norm_num
    rw [heq, LinearMap.det_comp, hEdet, hblockL_det, mul_one]

end Actions

/-! ### 3. Target `PairTarget`, equivariance of `pairCollapseMap`, and `det_actE'` -/

section CollapseEquivariance

def pairF : PairCollapse.Residual (U := Priv4) (V := Priv4) :=
  (Real.sqrt 2)⁻¹ • WithLp.toLp 2 (ePriv 0, -ePriv 0)

lemma norm_pairF : ‖pairF‖ = 1 := by
  have hsq : ‖pairF‖ ^ 2 = 1 := by
    have h0 : ‖ePriv 0‖ = 1 := orthonormal_ePriv.1 0
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [pairF, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsqrt2.le), mul_pow,
      WithLp.prod_norm_sq_eq_of_L2]
    change ((Real.sqrt 2)⁻¹) ^ 2 * (‖ePriv 0‖ ^ 2 + ‖-ePriv 0‖ ^ 2) = 1
    rw [norm_neg, h0, one_pow, inv_pow, h2]
    norm_num
  nlinarith [norm_nonneg pairF]

lemma actRes_pairF (h : PairGroup) :
    actRes h pairF = ((exchangeChar h : ℤ) : ℝ) • pairF := by
  have hs : ∀ b : Bool, privSign b (ePriv 0) = ePriv 0 := fun b => by
    cases b <;> simp [privSign, swapPriv_apply_ePriv0]
  apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
  apply Prod.ext <;> cases hex : h.2.ex <;>
    simp [pairF, actRes, hex, exchangeChar, map_smul, map_neg, hs]

def pairFixedPerpVec : PairCollapse.Residual (U := Priv4) (V := Priv4) :=
  (Real.sqrt 2)⁻¹ • WithLp.toLp 2 (ePriv 0, ePriv 0)

lemma inner_pairF_pairFixedPerpVec : ⟪pairF, pairFixedPerpVec⟫_ℝ = 0 := by
  rw [pairF, pairFixedPerpVec, real_inner_smul_left, real_inner_smul_right, WithLp.prod_inner_apply]
  simp

attribute [irreducible] pairF

abbrev PairTarget := PairCollapse.CollapseTarget (W := Comm6) pairF

theorem finrank_PairTarget : Module.finrank ℝ PairTarget = 13 := by
  have hU : Module.finrank ℝ Priv4 = 4 := finrank_Priv4
  have hW : Module.finrank ℝ Comm6 = 6 := finrank_Comm6
  exact PairCollapse.collapseTarget_finrank_thirteen (U := Priv4) (V := Priv4) (W := Comm6)
    pairF norm_pairF hU hU hW

lemma actRes_mem_perp (h : PairGroup) {u : PairCollapse.Residual (U := Priv4) (V := Priv4)}
    (hu : u ∈ (ℝ ∙ pairF)ᗮ) : actRes h u ∈ (ℝ ∙ pairF)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hu ⊢
  let sgn : ℝ := ((exchangeChar h : ℤ) : ℝ)
  have hsgn2 : sgn * sgn = 1 := by
    cases hex : h.2.ex <;> simp [sgn, exchangeChar, hex]
  have h1 : sgn * ⟪pairF, actRes h u⟫_ℝ = ⟪pairF, u⟫_ℝ := by
    calc sgn * ⟪pairF, actRes h u⟫_ℝ
        = ⟪sgn • pairF, actRes h u⟫_ℝ := (real_inner_smul_left _ _ _).symm
      _ = ⟪actRes h pairF, actRes h u⟫_ℝ := by rw [actRes_pairF h]
      _ = ⟪pairF, u⟫_ℝ := (actRes h).inner_map_map pairF u
  have h2 := congrArg (sgn * ·) h1
  rw [← mul_assoc, hsgn2, one_mul, hu, mul_zero] at h2
  exact h2

def actResPerp (h : PairGroup) : ↥(ℝ ∙ pairF)ᗮ ≃ₗᵢ[ℝ] ↥(ℝ ∙ pairF)ᗮ where
  toFun u := ⟨actRes h u.1, actRes_mem_perp h u.2⟩
  invFun u := ⟨actRes h⁻¹ u.1, actRes_mem_perp h⁻¹ u.2⟩
  left_inv u := by
    apply Subtype.ext
    change actRes h⁻¹ (actRes h u.1) = u.1
    rw [← actRes_mul, inv_mul_cancel, actRes_one]
  right_inv u := by
    apply Subtype.ext
    change actRes h (actRes h⁻¹ u.1) = u.1
    rw [← actRes_mul, mul_inv_cancel, actRes_one]
  map_add' x y := by apply Subtype.ext; exact (actRes h).map_add x.1 y.1
  map_smul' r x := by apply Subtype.ext; exact (actRes h).map_smul r x.1
  norm_map' x := (actRes h).norm_map x.1

def actE' (h : PairGroup) : PairTarget ≃ₗᵢ[ℝ] PairTarget where
  toFun x := (actComm h.1 x.1, actResPerp h x.2)
  invFun x := (actComm h.1⁻¹ x.1, actResPerp h⁻¹ x.2)
  left_inv x := by
    apply Prod.ext
    · change actComm (h.1⁻¹) (actComm h.1 x.1) = x.1
      rw [← actComm_mul, inv_mul_cancel, actComm_one]
    · apply Subtype.ext
      change actRes h⁻¹ (actRes h x.2.1) = x.2.1
      rw [← actRes_mul, inv_mul_cancel, actRes_one]
  right_inv x := by
    apply Prod.ext
    · change actComm h.1 (actComm (h.1⁻¹) x.1) = x.1
      rw [← actComm_mul, mul_inv_cancel, actComm_one]
    · apply Subtype.ext
      change actRes h (actRes h⁻¹ x.2.1) = x.2.1
      rw [← actRes_mul, mul_inv_cancel, actRes_one]
  map_add' x y := by apply Prod.ext <;> simp [map_add]
  map_smul' r x := by apply Prod.ext <;> simp [map_smul]
  norm_map' x := by
    change max ‖actComm h.1 x.1‖ ‖actResPerp h x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [(actComm h.1).norm_map, (actResPerp h).norm_map]

lemma actE'_one (x : PairTarget) : actE' 1 x = x := by
  apply Prod.ext
  · exact actComm_one x.1
  · apply Subtype.ext; exact actRes_one x.2.1

lemma actE'_mul (h₁ h₂ : PairGroup) (x : PairTarget) :
    actE' (h₁ * h₂) x = actE' h₁ (actE' h₂ x) := by
  apply Prod.ext
  · exact actComm_mul h₁.1 h₂.1 x.1
  · apply Subtype.ext; exact actRes_mul h₁ h₂ x.2.1

theorem det_actE' (h : PairGroup) :
    LinearMap.det (actE' h).toLinearMap = ((exchangeChar h : ℤ) : ℝ) := by
  let K := ℝ ∙ pairF
  let dec := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  let sgn : ℝ := ((exchangeChar h : ℤ) : ℝ)
  let actLine : ↥K →ₗ[ℝ] ↥K := sgn • LinearMap.id
  have hline_det : LinearMap.det actLine = sgn := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one,
      finrank_span_singleton (by intro h0; have := norm_pairF; rw [h0, norm_zero] at this; linarith),
      pow_one]
  have hconj : dec.symm.toLinearMap ∘ₗ ((actRes h).toLinearMap ∘ₗ dec.toLinearMap) =
      LinearMap.prodMap actLine (actResPerp h).toLinearMap := by
    apply LinearMap.ext
    rintro ⟨u, v⟩
    have hu : actRes h u.1 = sgn • u.1 := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp u.2
      rw [← hc, map_smul, actRes_pairF h, smul_comm]
    have hv : actRes h v.1 ∈ Kᗮ := actRes_mem_perp h v.2
    have hsum : dec.symm (actRes h (dec (u, v))) =
        (⟨sgn • u.1, Submodule.smul_mem K sgn u.2⟩, ⟨actRes h v.1, hv⟩) := by
      have h1 : actRes h (dec (u, v)) =
          dec (⟨sgn • u.1, Submodule.smul_mem K sgn u.2⟩, ⟨actRes h v.1, hv⟩) := by
        change actRes h (u.1 + v.1) = sgn • u.1 + actRes h v.1
        rw [map_add, hu]
      rw [h1, dec.symm_apply_apply]
    exact hsum
  have h1 : LinearMap.det (actRes h).toLinearMap =
      sgn * LinearMap.det (actResPerp h).toLinearMap := by
    have hconj_det := (LinearMap.det_conj (actRes h).toLinearMap dec.symm).symm
    have hprod_det : LinearMap.det (LinearMap.prodMap actLine (actResPerp h).toLinearMap) =
        sgn * LinearMap.det (actResPerp h).toLinearMap :=
      (LinearMap.det_prodMap actLine (actResPerp h).toLinearMap).trans
        (congrArg (· * LinearMap.det (actResPerp h).toLinearMap) hline_det)
    exact (hconj_det.trans (congrArg LinearMap.det hconj)).trans hprod_det
  have h1' : 1 = sgn * LinearMap.det (actResPerp h).toLinearMap :=
    (det_actRes h).symm.trans h1
  have hsgn2 : sgn * sgn = 1 := by cases hex : h.2.ex <;> simp [sgn, exchangeChar, hex]
  have hperp : LinearMap.det (actResPerp h).toLinearMap = sgn := by
    have := congrArg (sgn * ·) h1'
    rw [mul_one, ← mul_assoc, hsgn2, one_mul] at this
    exact this.symm
  have hprod : (actE' h).toLinearMap =
      LinearMap.prodMap (actComm h.1).toLinearMap (actResPerp h).toLinearMap := by
    apply LinearMap.ext; intro x; rfl
  calc LinearMap.det (actE' h).toLinearMap
      = LinearMap.det (LinearMap.prodMap (actComm h.1).toLinearMap (actResPerp h).toLinearMap) :=
        congrArg LinearMap.det hprod
    _ = LinearMap.det (actComm h.1).toLinearMap * LinearMap.det (actResPerp h).toLinearMap :=
        LinearMap.det_prodMap (actComm h.1).toLinearMap (actResPerp h).toLinearMap
    _ = 1 * sgn := congrArg₂ (· * ·) (det_actComm h.1) hperp
    _ = sgn := one_mul sgn

def actOnePoint (h : PairGroup) : OnePoint PairTarget → OnePoint PairTarget :=
  OnePoint.map (actE' h)

lemma continuous_actOnePoint (h : PairGroup) : Continuous (actOnePoint h) := by
  apply continuous_def.mpr
  intro s hs
  rw [OnePoint.isOpen_def] at hs ⊢
  have hpre : ((↑) : PairTarget → OnePoint PairTarget) ⁻¹' (actOnePoint h ⁻¹' s) =
      (actE' h) ⁻¹' (((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s) := rfl
  refine ⟨fun hi => ?_, ?_⟩
  · have hi' : ∞ ∈ s := hi
    have hK := hs.1 hi'
    have heq : (((↑) : PairTarget → OnePoint PairTarget) ⁻¹' (actOnePoint h ⁻¹' s))ᶜ =
        (actE' h).symm '' ((((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)ᶜ) := by
      ext x
      simp only [hpre, Set.mem_compl_iff, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        exact ⟨actE' h x, hx, (actE' h).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [heq]
    exact hK.image (actE' h).symm.continuous
  · rw [hpre]
    exact hs.2.preimage (actE' h).continuous

lemma actOnePoint_one (y : OnePoint PairTarget) : actOnePoint 1 y = y := by
  induction y using OnePoint.rec with
  | infty => rfl
  | coe x => simp [actOnePoint, actE'_one]

lemma actOnePoint_mul (h₁ h₂ : PairGroup) (y : OnePoint PairTarget) :
    actOnePoint (h₁ * h₂) y = actOnePoint h₁ (actOnePoint h₂ y) := by
  induction y using OnePoint.rec with
  | infty => rfl
  | coe x => simp [actOnePoint, actE'_mul]

def pairCollapseMap :
    PairCollapse.PairSpace Priv4 Priv4 Comm6 → OnePoint PairTarget :=
  PairCollapse.collapse (W := Comm6) pairF norm_pairF

theorem continuous_pairCollapseMap : Continuous pairCollapseMap :=
  PairCollapse.continuous_collapse pairF norm_pairF

lemma actY_fst_of_ex_false {h : PairGroup} (hex : h.2.ex = false)
    (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    (actY h x).1.1 = (privSign h.2.sa x.1.1.1, actComm h.1 x.1.1.2) := by
  simp [actY, hex]

lemma actY_snd_of_ex_false {h : PairGroup} (hex : h.2.ex = false)
    (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    (actY h x).2.1 = (privSign h.2.sb x.2.1.1, actComm h.1 x.2.1.2) := by
  simp [actY, hex]

lemma actY_fst_of_ex_true {h : PairGroup} (hex : h.2.ex = true)
    (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    (actY h x).1.1 = (privSign h.2.sb x.2.1.1, actComm h.1 x.2.1.2) := by
  simp [actY, hex]

lemma actY_snd_of_ex_true {h : PairGroup} (hex : h.2.ex = true)
    (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    (actY h x).2.1 = (privSign h.2.sa x.1.1.1, actComm h.1 x.1.1.2) := by
  simp [actY, hex]

lemma toParameters_base (y : PairCollapse.chartDomain (U := Priv4) (V := Priv4) (W := Comm6)) :
    (PairCollapse.toParameters y).1.1.1 =
      PairNormalChart.base
        (SplitSphereChart.normalizedDirection y.1.1.1.2)
        (SplitSphereChart.normalizedDirection y.1.2.1.2) := rfl

lemma toParameters_offset (y : PairCollapse.chartDomain (U := Priv4) (V := Priv4) (W := Comm6)) :
    (PairCollapse.toParameters y).1.1.2 =
      PairNormalChart.offset
        (SplitSphereChart.normalizedDirection y.1.1.1.2)
        (SplitSphereChart.normalizedDirection y.1.2.1.2) := rfl

lemma actY_mem_chartDomain_iff (h : PairGroup)
    (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    actY h x ∈ PairCollapse.chartDomain ↔ x ∈ PairCollapse.chartDomain := by
  change (‖(actY h x).2.1.2‖ • (actY h x).1.1.2 ≠ ‖(actY h x).1.1.2‖ • (actY h x).2.1.2) ↔
    (‖x.2.1.2‖ • x.1.1.2 ≠ ‖x.1.1.2‖ • x.2.1.2)
  cases hex : h.2.ex
  · rw [actY_fst_of_ex_false hex, actY_snd_of_ex_false hex]
    dsimp only
    rw [(actComm h.1).norm_map, (actComm h.1).norm_map, ← map_smul, ← map_smul, ne_eq,
      (actComm h.1).injective.eq_iff]
  · rw [actY_fst_of_ex_true hex, actY_snd_of_ex_true hex]
    dsimp only
    rw [(actComm h.1).norm_map, (actComm h.1).norm_map, ← map_smul, ← map_smul, ne_comm,
      ne_eq, (actComm h.1).injective.eq_iff]

theorem pairCollapseMap_equivariant (h : PairGroup)
    (x : PairCollapse.PairSpace Priv4 Priv4 Comm6) :
    pairCollapseMap (actY h x) = actOnePoint h (pairCollapseMap x) := by
  by_cases hx : x ∈ PairCollapse.chartDomain
  · have hx' : actY h x ∈ PairCollapse.chartDomain := (actY_mem_chartDomain_iff h x).mpr hx
    simp only [pairCollapseMap, PairCollapse.collapse, properCollapse_of_mem _ hx',
      properCollapse_of_mem _ hx, actOnePoint, OnePoint.map_some, OnePoint.coe_eq_coe]
    have hdir1 : SplitSphereChart.normalizedDirection (actComm h.1 x.1.1.2) =
        actComm h.1 (SplitSphereChart.normalizedDirection x.1.1.2) := by
      simp [SplitSphereChart.normalizedDirection, (actComm h.1).norm_map, map_smul]
    have hdir2 : SplitSphereChart.normalizedDirection (actComm h.1 x.2.1.2) =
        actComm h.1 (SplitSphereChart.normalizedDirection x.2.1.2) := by
      simp [SplitSphereChart.normalizedDirection, (actComm h.1).norm_map, map_smul]
    let p₀ := SplitSphereChart.normalizedDirection x.1.1.2
    let q₀ := SplitSphereChart.normalizedDirection x.2.1.2
    let r₁ := ‖x.1.1.2‖⁻¹ • x.1.1.1
    let r₂ := ‖x.2.1.2‖⁻¹ • x.2.1.1
    let r₀ : PairCollapse.Residual (U := Priv4) (V := Priv4) := WithLp.toLp 2 (r₁, r₂)
    let sgn : ℝ := ((exchangeChar h : ℤ) : ℝ)
    have hsgn2 : sgn * sgn = 1 := by
      cases hex : h.2.ex <;> simp [sgn, exchangeChar, hex]
    have hw_nat : actComm h.1 (PairNormalChart.base p₀ q₀) =
        sgn • (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.1 := by
      rw [toParameters_base]
      cases hex : h.2.ex
      · have hsgn1 : sgn = 1 := by simp [sgn, exchangeChar, hex]
        rw [actY_fst_of_ex_false hex, actY_snd_of_ex_false hex]
        dsimp only
        rw [hdir1, hdir2, hsgn1, one_smul]
        change actComm h.1 (‖p₀ - q₀‖⁻¹ • (p₀ - q₀)) =
          ‖actComm h.1 p₀ - actComm h.1 q₀‖⁻¹ • (actComm h.1 p₀ - actComm h.1 q₀)
        rw [map_smul, map_sub, ← map_sub (actComm h.1) p₀ q₀, (actComm h.1).norm_map]
      · have hsgn1 : sgn = -1 := by simp [sgn, exchangeChar, hex]
        rw [actY_fst_of_ex_true hex, actY_snd_of_ex_true hex]
        dsimp only
        rw [hdir1, hdir2, hsgn1]
        change actComm h.1 (‖p₀ - q₀‖⁻¹ • (p₀ - q₀)) =
          (-1 : ℝ) • (‖actComm h.1 q₀ - actComm h.1 p₀‖⁻¹ • (actComm h.1 q₀ - actComm h.1 p₀))
        rw [← map_sub (actComm h.1) q₀ p₀, (actComm h.1).norm_map, norm_sub_rev q₀ p₀,
          map_smul, map_sub, map_sub]
        module
    have hz_nat : (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.2 =
        actComm h.1 (PairNormalChart.offset p₀ q₀) := by
      rw [toParameters_offset]
      cases hex : h.2.ex
      · rw [actY_fst_of_ex_false hex, actY_snd_of_ex_false hex]
        dsimp only
        rw [hdir1, hdir2]
        change ‖actComm h.1 p₀ - actComm h.1 q₀‖⁻¹ • (actComm h.1 p₀ + actComm h.1 q₀) =
          actComm h.1 (‖p₀ - q₀‖⁻¹ • (p₀ + q₀))
        rw [← map_sub (actComm h.1) p₀ q₀, (actComm h.1).norm_map, map_smul, map_add]
      · rw [actY_fst_of_ex_true hex, actY_snd_of_ex_true hex]
        dsimp only
        rw [hdir1, hdir2]
        change ‖actComm h.1 q₀ - actComm h.1 p₀‖⁻¹ • (actComm h.1 q₀ + actComm h.1 p₀) =
          actComm h.1 (‖p₀ - q₀‖⁻¹ • (p₀ + q₀))
        rw [← map_sub (actComm h.1) q₀ p₀, (actComm h.1).norm_map, norm_sub_rev q₀ p₀,
          add_comm (actComm h.1 q₀), map_smul, map_add]
    have hr_nat : (PairCollapse.toParameters ⟨actY h x, hx'⟩).2 = actRes h r₀ := by
      apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
      apply Prod.ext <;> cases hex : h.2.ex <;>
        simp [PairCollapse.toParameters, PairCollapse.firstSplit, PairCollapse.secondSplit,
          SplitSphereChart.fromSplit, actY, actRes, hex, (actComm h.1).norm_map, r₀, r₁, r₂]
    have hf_nat : (actRes h).toLinearMap pairF = sgn • pairF := actRes_pairF h
    have hinner_nat : ∀ v, ⟪pairF, (actRes h).toLinearMap v⟫_ℝ = sgn * ⟪pairF, v⟫_ℝ := fun v => by
      have h1 : sgn * ⟪pairF, actRes h v⟫_ℝ = ⟪pairF, v⟫_ℝ := by
        calc sgn * ⟪pairF, actRes h v⟫_ℝ
            = ⟪sgn • pairF, actRes h v⟫_ℝ := (real_inner_smul_left _ _ _).symm
          _ = ⟪actRes h pairF, actRes h v⟫_ℝ := by rw [actRes_pairF h]
          _ = ⟪pairF, v⟫_ℝ := (actRes h).inner_map_map pairF v
      have h2 := congrArg (sgn * ·) h1
      rw [← mul_assoc, hsgn2, one_mul] at h2
      exact h2
    have hnat := PairNormalFrame.forward_natural (actRes h).toLinearMap (actComm h.1).toLinearMap
      pairF pairF (PairNormalChart.base p₀ q₀) (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.1
      sgn hf_nat hw_nat hinner_nat r₀ (PairNormalChart.offset p₀ q₀)
    have hlhs_eq : (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.2 =
        actComm h.1 (PairNormalChart.offset p₀ q₀) := hz_nat
    apply Prod.ext
    · change (PairNormalFrame.forward pairF (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.1
          (PairCollapse.toParameters ⟨actY h x, hx'⟩).2
          (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.2).1 =
        actComm h.1 (PairNormalFrame.forward pairF (PairNormalChart.base p₀ q₀) r₀
          (PairNormalChart.offset p₀ q₀)).1
      rw [hr_nat, hlhs_eq]
      exact congrArg Prod.fst hnat
    · apply Subtype.ext
      change (PairNormalFrame.forward pairF (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.1
          (PairCollapse.toParameters ⟨actY h x, hx'⟩).2
          (PairCollapse.toParameters ⟨actY h x, hx'⟩).1.1.2).2 =
        actRes h (PairNormalFrame.forward pairF (PairNormalChart.base p₀ q₀) r₀
          (PairNormalChart.offset p₀ q₀)).2
      rw [hr_nat, hlhs_eq]
      exact congrArg Prod.snd hnat
  · have hx' : actY h x ∉ PairCollapse.chartDomain := by
      rwa [actY_mem_chartDomain_iff]
    simp only [pairCollapseMap, PairCollapse.collapse_eq_infty_of_not_domain _ _ _ hx,
      PairCollapse.collapse_eq_infty_of_not_domain _ _ _ hx', actOnePoint, OnePoint.map_infty]

end CollapseEquivariance

/-! ### 4. Invariant unit vector `pairFixedE`, reflection, fold, and cancellation homotopy -/

section CancellationHomotopy

def pairFixedPerp : ↥(ℝ ∙ pairF)ᗮ :=
  ⟨pairFixedPerpVec, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    inner_pairF_pairFixedPerpVec⟩

lemma norm_pairFixedPerp : ‖pairFixedPerp‖ = 1 := by
  have hsq : ‖pairFixedPerp‖ ^ 2 = 1 := by
    have h0 : ‖ePriv 0‖ = 1 := orthonormal_ePriv.1 0
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    change ‖pairFixedPerpVec‖ ^ 2 = 1
    rw [pairFixedPerpVec, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsqrt2.le), mul_pow,
      WithLp.prod_norm_sq_eq_of_L2]
    change ((Real.sqrt 2)⁻¹) ^ 2 * (‖ePriv 0‖ ^ 2 + ‖ePriv 0‖ ^ 2) = 1
    rw [h0, one_pow, inv_pow, h2]
    norm_num
  nlinarith [norm_nonneg pairFixedPerp]

lemma actResPerp_pairFixedPerp (h : PairGroup) :
    actResPerp h pairFixedPerp = pairFixedPerp := by
  have hs : ∀ b : Bool, privSign b (ePriv 0) = ePriv 0 := fun b => by
    cases b <;> simp [privSign, swapPriv_apply_ePriv0]
  apply Subtype.ext
  change actRes h pairFixedPerpVec = pairFixedPerpVec
  apply (WithLp.equiv 2 (Priv4 × Priv4)).injective
  apply Prod.ext <;> cases hex : h.2.ex <;>
    simp [pairFixedPerpVec, actRes, hex, map_smul, hs]

attribute [irreducible] pairFixedPerp

def pairFixedE : PairTarget := (0, pairFixedPerp)

lemma norm_pairFixedE : ‖pairFixedE‖ = 1 := by
  change max ‖(0 : Comm6)‖ ‖pairFixedPerp‖ = 1
  rw [norm_zero, norm_pairFixedPerp, max_eq_right zero_le_one]

lemma actE'_pairFixedE (h : PairGroup) : actE' h pairFixedE = pairFixedE := by
  apply Prod.ext
  · exact map_zero (actComm h.1)
  · exact actResPerp_pairFixedPerp h

def reflectPerp : ↥(ℝ ∙ pairF)ᗮ ≃ₗᵢ[ℝ] ↥(ℝ ∙ pairF)ᗮ where
  toFun y := y - (2 * ⟪pairFixedPerp, y⟫_ℝ) • pairFixedPerp
  invFun y := y - (2 * ⟪pairFixedPerp, y⟫_ℝ) • pairFixedPerp
  left_inv y := by
    have hvv : ⟪pairFixedPerp, pairFixedPerp⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_pairFixedPerp, one_pow]
    simp only [inner_sub_right, real_inner_smul_right, hvv, mul_one]
    module
  right_inv y := by
    have hvv : ⟪pairFixedPerp, pairFixedPerp⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_pairFixedPerp, one_pow]
    simp only [inner_sub_right, real_inner_smul_right, hvv, mul_one]
    module
  map_add' x y := by
    simp only [inner_add_right]
    module
  map_smul' r x := by
    simp only [real_inner_smul_right, RingHom.id_apply]
    module
  norm_map' y := by
    have h1 : ‖pairFixedPerp.1‖ = 1 := norm_pairFixedPerp
    have hsq : ‖y.1 - (2 * ⟪pairFixedPerp.1, y.1⟫_ℝ) • pairFixedPerp.1‖ ^ 2 = ‖y.1‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, h1, mul_one, sq_abs,
        real_inner_smul_right, real_inner_comm y.1 pairFixedPerp.1]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def reflectFixedE : PairTarget ≃ₗᵢ[ℝ] PairTarget where
  toFun x := (x.1, reflectPerp x.2)
  invFun x := (x.1, reflectPerp x.2)
  left_inv x := by
    apply Prod.ext
    · rfl
    · exact reflectPerp.left_inv x.2
  right_inv x := by
    apply Prod.ext
    · rfl
    · exact reflectPerp.right_inv x.2
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact reflectPerp.map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · exact reflectPerp.map_smul r x.2
  norm_map' x := by
    change max ‖x.1‖ ‖reflectPerp x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [reflectPerp.norm_map]

lemma reflectFixedE_apply (x : PairTarget) :
    reflectFixedE x = (x.1, x.2 - (2 * ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp) := rfl

lemma reflectFixedE_equivariant (h : PairGroup) (x : PairTarget) :
    reflectFixedE (actE' h x) = actE' h (reflectFixedE x) := by
  have hfix := actResPerp_pairFixedPerp h
  have hin : ⟪pairFixedPerp, actResPerp h x.2⟫_ℝ = ⟪pairFixedPerp, x.2⟫_ℝ := by
    conv_lhs => rw [← hfix]
    exact (actResPerp h).inner_map_map pairFixedPerp x.2
  apply Prod.ext
  · rfl
  · change actResPerp h x.2 - (2 * ⟪pairFixedPerp, actResPerp h x.2⟫_ℝ) • pairFixedPerp =
      actResPerp h (x.2 - (2 * ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp)
    rw [(actResPerp h).map_sub, (actResPerp h).map_smul, hin, hfix]

def foldE (x : PairTarget) : PairTarget :=
  (x.1, x.2 + (|⟪pairFixedPerp, x.2⟫_ℝ| - ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp)

lemma continuous_foldE : Continuous foldE := by
  have hinner : Continuous (fun x : PairTarget => ⟪pairFixedPerp, x.2⟫_ℝ) :=
    Continuous.inner (continuous_const (y := pairFixedPerp)) continuous_snd
  have hcoef : Continuous (fun x : PairTarget => |⟪pairFixedPerp, x.2⟫_ℝ| - ⟪pairFixedPerp, x.2⟫_ℝ) :=
    hinner.abs.sub hinner
  exact continuous_fst.prodMk (continuous_snd.add (hcoef.smul (continuous_const (y := pairFixedPerp))))

lemma foldE_of_nonneg {x : PairTarget} (hx : 0 ≤ ⟪pairFixedPerp, x.2⟫_ℝ) :
    foldE x = x := by
  apply Prod.ext
  · rfl
  · change x.2 + (|⟪pairFixedPerp, x.2⟫_ℝ| - ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp = x.2
    rw [abs_of_nonneg hx, sub_self, zero_smul, add_zero]

lemma foldE_of_nonpos {x : PairTarget} (hx : ⟪pairFixedPerp, x.2⟫_ℝ ≤ 0) :
    foldE x = reflectFixedE x := by
  apply Prod.ext
  · rfl
  · change x.2 + (|⟪pairFixedPerp, x.2⟫_ℝ| - ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp =
      x.2 - (2 * ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp
    rw [abs_of_nonpos hx]
    module

lemma foldE_equivariant (h : PairGroup) (x : PairTarget) :
    foldE (actE' h x) = actE' h (foldE x) := by
  have hfix := actResPerp_pairFixedPerp h
  have hin : ⟪pairFixedPerp, actResPerp h x.2⟫_ℝ = ⟪pairFixedPerp, x.2⟫_ℝ := by
    conv_lhs => rw [← hfix]
    exact (actResPerp h).inner_map_map pairFixedPerp x.2
  apply Prod.ext
  · rfl
  · change actResPerp h x.2 +
        (|⟪pairFixedPerp, actResPerp h x.2⟫_ℝ| - ⟪pairFixedPerp, actResPerp h x.2⟫_ℝ) • pairFixedPerp =
      actResPerp h (x.2 + (|⟪pairFixedPerp, x.2⟫_ℝ| - ⟪pairFixedPerp, x.2⟫_ℝ) • pairFixedPerp)
    rw [(actResPerp h).map_add, (actResPerp h).map_smul, hin, hfix]

lemma foldE_inner_nonneg (x : PairTarget) :
    0 ≤ ⟪pairFixedPerp, (foldE x).2⟫_ℝ := by
  have hvv : ⟪pairFixedPerp, pairFixedPerp⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_pairFixedPerp, one_pow]
  simp only [foldE, inner_add_right, real_inner_smul_right, hvv, mul_one]
  linarith [abs_nonneg ⟪pairFixedPerp, x.2⟫_ℝ]

lemma foldE_snd_norm (x : PairTarget) : ‖(foldE x).2‖ = ‖x.2‖ := by
  rcases le_total 0 ⟪pairFixedPerp, x.2⟫_ℝ with hx | hx
  · rw [foldE_of_nonneg hx]
  · rw [foldE_of_nonpos hx]
    exact reflectPerp.norm_map x.2

def invCancelHomotopy (p : unitInterval × OnePoint PairTarget) : OnePoint PairTarget :=
  if (p.1 : ℝ) < 1 then
    p.2.elim ∞ (fun x => (((x.1, (foldE x).2 + ((p.1 : ℝ) / (1 - (p.1 : ℝ))) • pairFixedPerp) :
      PairTarget) : OnePoint PairTarget))
  else ∞

lemma invCancelHomotopy_zero (y : OnePoint PairTarget) :
    invCancelHomotopy (0, y) = y.elim ∞ (fun x => (foldE x : OnePoint PairTarget)) := by
  induction y using OnePoint.rec with
  | infty => simp [invCancelHomotopy]
  | coe x => simp [invCancelHomotopy, foldE]

lemma invCancelHomotopy_one (y : OnePoint PairTarget) :
    invCancelHomotopy (1, y) = ∞ := by
  simp [invCancelHomotopy]

lemma invCancelHomotopy_infty (t : unitInterval) :
    invCancelHomotopy (t, ∞) = ∞ := by
  by_cases ht : (t : ℝ) < 1 <;> simp [invCancelHomotopy, ht]

lemma invCancelHomotopy_equivariant (h : PairGroup) (t : unitInterval) (y : OnePoint PairTarget) :
    invCancelHomotopy (t, actOnePoint h y) = actOnePoint h (invCancelHomotopy (t, y)) := by
  by_cases ht : (t : ℝ) < 1
  · induction y using OnePoint.rec with
    | infty => simp [invCancelHomotopy, ht, actOnePoint]
    | coe x =>
      simp only [invCancelHomotopy, ht, ↓reduceIte, actOnePoint, OnePoint.map_some,
        OnePoint.elim_some, OnePoint.coe_eq_coe]
      apply Prod.ext
      · rfl
      · have hfe := congrArg Prod.snd (foldE_equivariant h x)
        have hfix := actResPerp_pairFixedPerp h
        change (foldE (actE' h x)).2 + ((t : ℝ) / (1 - (t : ℝ))) • pairFixedPerp =
          actResPerp h ((foldE x).2 + ((t : ℝ) / (1 - (t : ℝ))) • pairFixedPerp)
        rw [map_add, map_smul, hfe, hfix]
        rfl
  · simp [invCancelHomotopy, ht, actOnePoint]

lemma invCancel_snd_norm_sq_ge {t : unitInterval} (ht : (t : ℝ) < 1) (x : PairTarget) :
    ‖(foldE x).2 + ((t : ℝ) / (1 - (t : ℝ))) • pairFixedPerp‖ ^ 2 ≥
      ‖x.2‖ ^ 2 + ((t : ℝ) / (1 - (t : ℝ))) ^ 2 := by
  let c : ℝ := (t : ℝ) / (1 - (t : ℝ))
  have hc0 : 0 ≤ c := div_nonneg t.2.1 (sub_pos.mpr ht).le
  have h1 : ‖pairFixedPerp‖ = 1 := norm_pairFixedPerp
  have hin : 0 ≤ ⟪pairFixedPerp, (foldE x).2⟫_ℝ := foldE_inner_nonneg x
  have hin' : 0 ≤ ⟪(foldE x).2, pairFixedPerp⟫_ℝ := by rwa [real_inner_comm]
  rw [norm_add_sq_real, foldE_snd_norm, norm_smul, Real.norm_of_nonneg hc0, h1, mul_one,
    real_inner_smul_right]
  nlinarith

lemma invCancel_norm_ge {t : unitInterval} (ht : (t : ℝ) < 1) (x : PairTarget) :
    ‖x‖ ≤ ‖((x.1, (foldE x).2 + ((t : ℝ) / (1 - (t : ℝ))) • pairFixedPerp) : PairTarget)‖ ∧
    (t : ℝ) / (1 - (t : ℝ)) ≤
      ‖((x.1, (foldE x).2 + ((t : ℝ) / (1 - (t : ℝ))) • pairFixedPerp) : PairTarget)‖ := by
  let c : ℝ := (t : ℝ) / (1 - (t : ℝ))
  let y₂ := (foldE x).2 + c • pairFixedPerp
  have hc0 : 0 ≤ c := div_nonneg t.2.1 (sub_pos.mpr ht).le
  have hsq : ‖x.2‖ ^ 2 + c ^ 2 ≤ ‖y₂‖ ^ 2 := invCancel_snd_norm_sq_ge ht x
  have hy₂_x : ‖x.2‖ ≤ ‖y₂‖ := by nlinarith [norm_nonneg x.2, norm_nonneg y₂, sq_nonneg c]
  have hy₂_c : c ≤ ‖y₂‖ := by nlinarith [norm_nonneg x.2, norm_nonneg y₂, sq_nonneg ‖x.2‖]
  constructor
  · change max ‖x.1‖ ‖x.2‖ ≤ max ‖x.1‖ ‖y₂‖
    exact max_le_max_left ‖x.1‖ hy₂_x
  · change c ≤ max ‖x.1‖ ‖y₂‖
    exact le_max_of_le_right hy₂_c

theorem continuous_invCancelHomotopy : Continuous invCancelHomotopy := by
  apply continuous_def.mpr
  intro s hs
  by_cases hi : ∞ ∈ s
  · have hK : IsCompact ((((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)ᶜ) :=
      (OnePoint.isOpen_def.mp hs).1 hi
    have hK_closed : IsClosed ((((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)ᶜ) :=
      (OnePoint.isOpen_def.mp hs).1 hi |>.isClosed
    have hK_bdd : Bornology.IsBounded ((((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)ᶜ) :=
      hK.isBounded
    obtain ⟨R₀, hR₀⟩ := hK_bdd.subset_closedBall (0 : PairTarget)
    let R : ℝ := max R₀ 1
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hR_sub : ∀ x ∈ ((((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)ᶜ), ‖x‖ ≤ R := by
      intro x hx
      have := hR₀ hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    let tMax : ℝ := R / (R + 1)
    have htMax_pos : 0 < tMax := div_pos hRpos (by linarith)
    have htMax_lt : tMax < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    let D : Set (unitInterval × PairTarget) :=
      {q | (q.1 : ℝ) ≤ tMax ∧ ‖q.2‖ ≤ R}
    have hD_compact : IsCompact D := by
      have : ProperSpace PairTarget := FiniteDimensional.proper ℝ PairTarget
      let Isub : Set unitInterval := {t : unitInterval | (t : ℝ) ≤ tMax}
      have hIsub : IsCompact Isub :=
        isClosed_le continuous_subtype_val continuous_const |>.isCompact
      have hB : IsCompact (Metric.closedBall (0 : PairTarget) R) := isCompact_closedBall 0 R
      have hD_eq : D = Isub ×ˢ Metric.closedBall (0 : PairTarget) R := by
        ext q
        simp [D, Isub, Metric.mem_closedBall, dist_zero_right]
      rw [hD_eq]
      exact hIsub.prod hB
    let shift : unitInterval × PairTarget → PairTarget := fun q =>
      (q.2.1, (foldE q.2).2 + ((q.1 : ℝ) / (1 - (q.1 : ℝ))) • pairFixedPerp)
    have hshift_cont : ContinuousOn shift D := by
      refine (continuous_fst.comp continuous_snd).continuousOn.prodMk ?_
      have h1 : ContinuousOn (fun q : unitInterval × PairTarget => (foldE q.2).2) D :=
        (continuous_snd.comp (continuous_foldE.comp continuous_snd)).continuousOn
      have hnum : ContinuousOn (fun q : unitInterval × PairTarget => (q.1 : ℝ)) D :=
        (continuous_subtype_val.comp continuous_fst).continuousOn
      have hden : ContinuousOn (fun q : unitInterval × PairTarget => 1 - (q.1 : ℝ)) D :=
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousOn
      have hden_ne : ∀ q ∈ D, 1 - (q.1 : ℝ) ≠ 0 := fun q hq => by
        have := hq.1
        linarith
      exact h1.add ((hnum.div hden hden_ne).smul continuousOn_const)
    let C : Set (unitInterval × PairTarget) :=
      D ∩ shift ⁻¹' ((((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)ᶜ)
    have hC_closed : IsClosed C :=
      hshift_cont.preimage_isClosed_of_isClosed hD_compact.isClosed hK_closed
    have hC_compact : IsCompact C :=
      hD_compact.of_isClosed_subset hC_closed Set.inter_subset_left
    let embed : unitInterval × PairTarget → unitInterval × OnePoint PairTarget :=
      fun q => (q.1, (q.2 : OnePoint PairTarget))
    have hembed_cont : Continuous embed :=
      continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)
    have hpre_eq : (invCancelHomotopy ⁻¹' s)ᶜ = embed '' C := by
      ext ⟨t, y⟩
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_image, C, D, embed]
      constructor
      · intro hny
        have ht : (t : ℝ) < 1 := by
          by_contra hge
          apply hny
          simpa [invCancelHomotopy, hge] using hi
        induction y using OnePoint.rec with
        | infty =>
          exfalso
          apply hny
          simpa [invCancelHomotopy, ht] using hi
        | coe x =>
          have hx_not : shift (t, x) ∉ (((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s) := by
            intro hmem
            apply hny
            simpa [invCancelHomotopy, ht, shift] using hmem
          have hnorm_le := hR_sub (shift (t, x)) hx_not
          obtain ⟨hx_le, hc_le⟩ := invCancel_norm_ge ht x
          have ht_le : (t : ℝ) ≤ tMax := by
            have hden : 0 < 1 - (t : ℝ) := sub_pos.mpr ht
            have h1 : (t : ℝ) ≤ R * (1 - (t : ℝ)) := (div_le_iff₀ hden).mp (hc_le.trans hnorm_le)
            have h2 : (R + 1) * (t : ℝ) ≤ R := by linarith
            exact (le_div_iff₀' (by positivity : 0 < R + 1)).mpr h2
          exact ⟨(t, x), ⟨⟨ht_le, hx_le.trans hnorm_le⟩, hx_not⟩, rfl⟩
      · rintro ⟨⟨t', x⟩, ⟨⟨ht', _⟩, hx_not⟩, hpair⟩
        have ht_lt : (t' : ℝ) < 1 := lt_of_le_of_lt ht' htMax_lt
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        simpa [invCancelHomotopy, ht_lt, shift] using hx_not
    have hclosed_compl : IsClosed (invCancelHomotopy ⁻¹' s)ᶜ := by
      rw [hpre_eq]
      exact (hC_compact.image hembed_cont).isClosed
    exact isClosed_compl_iff.mp hclosed_compl
  · have hs_open : IsOpen (((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s) :=
      (OnePoint.isOpen_def.mp hs).2
    let U_t : Set unitInterval := {t : unitInterval | (t : ℝ) < 1}
    have hUt_open : IsOpen U_t := isOpen_lt continuous_subtype_val continuous_const
    let emb : U_t × PairTarget → unitInterval × OnePoint PairTarget :=
      fun q => (q.1.1, (q.2 : OnePoint PairTarget))
    have hemb_open : IsOpenMap emb :=
      hUt_open.isOpenEmbedding_subtypeVal.isOpenMap.prodMap OnePoint.isOpenEmbedding_coe.isOpenMap
    let shiftU : U_t × PairTarget → PairTarget := fun q =>
      (q.2.1, (foldE q.2).2 + ((q.1.1 : ℝ) / (1 - (q.1.1 : ℝ))) • pairFixedPerp)
    have hshiftU_cont : Continuous shiftU := by
      refine (continuous_fst.comp continuous_snd).prodMk ?_
      have h1 : Continuous (fun q : U_t × PairTarget => (foldE q.2).2) :=
        continuous_snd.comp (continuous_foldE.comp continuous_snd)
      have hnum : Continuous (fun q : U_t × PairTarget => (q.1.1 : ℝ)) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
      have hden : Continuous (fun q : U_t × PairTarget => 1 - (q.1.1 : ℝ)) :=
        continuous_const.sub hnum
      exact h1.add ((hnum.div hden (fun q => sub_ne_zero.mpr q.1.2.ne')).smul
        (continuous_const (y := pairFixedPerp)))
    have hpre_U : invCancelHomotopy ⁻¹' s =
        emb '' (shiftU ⁻¹' (((↑) : PairTarget → OnePoint PairTarget) ⁻¹' s)) := by
      ext ⟨t, y⟩
      constructor
      · intro hmem
        have ht : (t : ℝ) < 1 := by
          by_contra hge
          apply hi
          have : invCancelHomotopy (t, y) = ∞ := by simp [invCancelHomotopy, hge]
          rw [← this]; exact hmem
        induction y using OnePoint.rec with
        | infty =>
          exfalso; apply hi
          have : invCancelHomotopy (t, ∞) = ∞ := by simp [invCancelHomotopy, ht]
          rw [← this]; exact hmem
        | coe x =>
          refine ⟨(⟨t, ht⟩, x), ?_, rfl⟩
          simpa [shiftU, invCancelHomotopy, ht] using hmem
      · rintro ⟨⟨⟨t', ht'⟩, x⟩, hmem, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        have ht'' : (t' : ℝ) < 1 := ht'
        change (if (t' : ℝ) < 1 then
          (((x.1, (foldE x).2 + ((t' : ℝ) / (1 - (t' : ℝ))) • pairFixedPerp) :
            PairTarget) : OnePoint PairTarget) else ∞) ∈ s
        simp only [ht'', ↓reduceIte]
        exact hmem
    rw [hpre_U]
    exact hemb_open _ (hs_open.preimage hshiftU_cont)

end CancellationHomotopy

end AkopyanResearch
