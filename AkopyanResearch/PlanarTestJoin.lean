module

public import Mathlib
public import RequestProject.Surgery.Main
public import AkopyanResearch.PlanarTestGlobal

@[expose] public section

/-!
# Ball filling of `q₀`, surgery null-homotopy, and finite free-join induction

Constructs the 10-ball filling `F₀ : Rep10 → Rep10` of `q₀ : S⁹ → S⁹` with 42 affine isolated
zeros (`0` with index `+1`, 26 non-3-element caps with index `-1`, and 20 three-element caps with
index `+1`), proves `Surgery.GoodMap` with zero total index `1 - 6 - 15 + 20 = 0`, applies
`Surgery.surgery` to obtain a continuous nowhere-vanishing filling and hence a continuous
null-homotopy `q₀ ≃ const anchorS`, and runs the finite free-join induction to produce
continuous `Equiv.Perm (Fin 6)`-equivariant maps `β c : FreeJoin c → S⁹` for all `1 ≤ c`
(in particular `c = 15`).
-/

noncomputable section

open scoped BigOperators InnerProductSpace
open Metric

namespace AkopyanResearch

/-! ### Linear identification `ℝ × (Fin 9 → ℝ) ≃ₗ[ℝ] Rep10` and coordinate map `Q₀` -/

section Coordinates

def emb : (ℝ × (Fin 9 → ℝ)) ≃ₗ[ℝ] Rep10 where
  toFun p := (WithLp.equiv 2 (Fin 10 → ℝ)).symm (Surgery.toVec p)
  invFun z := (z 0, Fin.tail (WithLp.equiv 2 (Fin 10 → ℝ) z))
  left_inv p := by
    rcases p with ⟨x0, xr⟩
    ext
    · rfl
    · simp [Surgery.toVec]
  right_inv z := by
    apply PiLp.ext
    intro i
    change Fin.cons (z 0) (Fin.tail (WithLp.equiv 2 (Fin 10 → ℝ) z)) i = z i
    refine Fin.cases rfl (fun j => rfl) i
  map_add' p q := by
    apply PiLp.ext
    intro i
    change Surgery.toVec (p + q) i = Surgery.toVec p i + Surgery.toVec q i
    refine Fin.cases rfl (fun j => rfl) i
  map_smul' r p := by
    apply PiLp.ext
    intro i
    change Surgery.toVec (r • p) i = r * Surgery.toVec p i
    refine Fin.cases rfl (fun j => rfl) i

def Q0 : Rep10 →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun x := WithLp.equiv 2 (Fin 10 → ℝ) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma Q0_injective : Function.Injective Q0 := fun _ _ h =>
  PiLp.ext fun i => congrFun h i

lemma ker_Q0 : LinearMap.ker Q0 = ⊥ :=
  LinearMap.ker_eq_bot.mpr Q0_injective

lemma continuous_emb : Continuous emb :=
  emb.toLinearMap.continuous_of_finiteDimensional

lemma continuous_emb_symm : Continuous emb.symm :=
  emb.symm.toLinearMap.continuous_of_finiteDimensional

lemma norm_emb_le (h : ℝ × (Fin 9 → ℝ)) : ‖emb h‖ ≤ 4 * ‖h‖ := by
  have hsq : ‖emb h‖ ^ 2 ≤ (4 * ‖h‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    have hsum : ∑ i : Fin 10, (emb h i) ^ 2 = h.1 ^ 2 + ∑ j : Fin 9, (h.2 j) ^ 2 := by
      rw [Fin.sum_univ_succ]
      simp [emb, Surgery.toVec]
    rw [hsum]
    have h1 : h.1 ^ 2 ≤ ‖h‖ ^ 2 := by
      have hab : ‖h.1‖ ≤ ‖h‖ := le_max_left _ _
      rw [Real.norm_eq_abs] at hab
      nlinarith [norm_nonneg h, abs_nonneg h.1, sq_abs h.1]
    have h2 : ∑ j : Fin 9, (h.2 j) ^ 2 ≤ 9 * ‖h‖ ^ 2 := by
      calc ∑ j : Fin 9, (h.2 j) ^ 2
          ≤ ∑ _j : Fin 9, ‖h‖ ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hj1 : |h.2 j| ≤ ‖h.2‖ := norm_le_pi_norm h.2 j
            have hj2 : ‖h.2‖ ≤ ‖h‖ := le_max_right _ _
            have hj3 : |h.2 j| ≤ ‖h‖ := hj1.trans hj2
            nlinarith [norm_nonneg h, abs_nonneg (h.2 j), sq_abs (h.2 j)]
        _ = 9 * ‖h‖ ^ 2 := by simp
    nlinarith [norm_nonneg h]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

lemma lin_apply_basis (L : Rep10 →ₗ[ℝ] Rep10) (h : ℝ × (Fin 9 → ℝ)) :
    Surgery.lin (fun i => L (EuclideanSpace.basisFun (Fin 10) ℝ i)) h = L (emb h) := by
  rw [Surgery.lin]
  have hsum : (∑ i : Fin 10, Surgery.toVec h i • EuclideanSpace.basisFun (Fin 10) ℝ i) = emb h := by
    have hcoef : ∀ i : Fin 10,
        Surgery.toVec h i = ((EuclideanSpace.basisFun (Fin 10) ℝ).repr (emb h)).ofLp i := by
      intro i
      rw [EuclideanSpace.basisFun_repr]
      rfl
    simp_rw [hcoef]
    exact (EuclideanSpace.basisFun (Fin 10) ℝ).sum_repr (emb h)
  calc ∑ i : Fin 10, Surgery.toVec h i • L (EuclideanSpace.basisFun (Fin 10) ℝ i)
      = ∑ i : Fin 10, L (Surgery.toVec h i • EuclideanSpace.basisFun (Fin 10) ℝ i) := by
        refine Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
    _ = L (∑ i : Fin 10, Surgery.toVec h i • EuclideanSpace.basisFun (Fin 10) ℝ i) :=
        (map_sum _ _ _).symm
    _ = L (emb h) := congrArg L hsum

lemma frameMat_Q0_eq_toMatrix (L : Rep10 →ₗ[ℝ] Rep10) :
    Surgery.frameMat Q0 (fun i => L (EuclideanSpace.basisFun (Fin 10) ℝ i)) =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 10) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 10) ℝ).toBasis L := by
  ext r i
  simp [Surgery.frameMat, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr, Q0]

lemma det_frameMat_Q0_eq (L : Rep10 →ₗ[ℝ] Rep10) :
    (Surgery.frameMat Q0 (fun i => L (EuclideanSpace.basisFun (Fin 10) ℝ i))).det =
      LinearMap.det L := by
  rw [frameMat_Q0_eq_toMatrix, LinearMap.det_toMatrix]

end Coordinates

/-! ### Local affine models `LA A` around `(5 / 8) • cA A` -/

section LocalAffine

def reflB (b : Rep10) : Rep10 →ₗ[ℝ] Rep10 where
  toFun v := v - (2 * ⟪b, v⟫_ℝ) • b
  map_add' u v := by
    simp only [inner_add_right, mul_add, add_smul]
    module
  map_smul' r v := by
    simp only [real_inner_smul_right, RingHom.id_apply, smul_sub, smul_smul]
    module

lemma reflB_eq_twist (b v : Rep10) :
    PlanarTestLocal.twist b v 1 1 = reflB b v := by
  simp [PlanarTestLocal.twist, reflB]

lemma norm_reflB {b : Rep10} (hb : ‖b‖ = 1) (v : Rep10) :
    ‖reflB b v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  dsimp [reflB]
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hb, mul_one,
    inner_smul_right, real_inner_comm v b, sq_abs]
  ring

def reflCap (A : InvariantCaps.CapLabel) : Rep10 →ₗ[ℝ] Rep10 :=
  if A.val.card = 3 then reflB (bA A) else LinearMap.id

lemma norm_reflCap (A : InvariantCaps.CapLabel) (v : Rep10) :
    ‖reflCap A v‖ = ‖v‖ := by
  unfold reflCap
  split_ifs
  · exact norm_reflB (norm_bA A) v
  · rfl

lemma reflCap_eq_capPsi (A : InvariantCaps.CapLabel) {v : Rep10} {t : ℝ}
    (ht : 1 / 8 ≤ t) (hη : etaCut ‖v‖ = 1) :
    capPsi A v t = reflCap A v := by
  unfold capPsi reflCap
  split_ifs
  · rw [timeCut_eq_one ht, hη, reflB_eq_twist]
  · rfl

def LA_vec (A : InvariantCaps.CapLabel) : Rep10 →ₗ[ℝ] Rep10 where
  toFun y := (8 / 5 : ℝ) • reflCap A (y - ⟪cA A, y⟫_ℝ • cA A) - (8 * ⟪cA A, y⟫_ℝ) • cA A
  map_add' u v := by
    have h1 : (u + v) - ⟪cA A, u + v⟫_ℝ • cA A =
        (u - ⟪cA A, u⟫_ℝ • cA A) + (v - ⟪cA A, v⟫_ℝ • cA A) := by
      simp only [inner_add_right, add_smul]
      module
    rw [h1, map_add, smul_add, inner_add_right, mul_add]
    module
  map_smul' r v := by
    have h1 : (r • v) - ⟪cA A, r • v⟫_ℝ • cA A =
        r • (v - ⟪cA A, v⟫_ℝ • cA A) := by
      simp only [real_inner_smul_right, smul_sub, smul_smul]
    rw [h1, map_smul, real_inner_smul_right]
    simp only [RingHom.id_apply, smul_sub, smul_smul]
    module

def LA (A : InvariantCaps.CapLabel) (z : Rep10) : Rep10 :=
  LA_vec A (z - (5 / 8 : ℝ) • cA A)

lemma LA_eq (A : InvariantCaps.CapLabel) (z : Rep10) :
    LA A z = (8 / 5 : ℝ) • reflCap A (z - ⟪cA A, z⟫_ℝ • cA A) + (5 - 8 * ⟪cA A, z⟫_ℝ) • cA A := by
  dsimp [LA, LA_vec]
  have hc1 : ⟪cA A, cA A⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, norm_cA, one_pow]
  have hin : ⟪cA A, z - (5 / 8 : ℝ) • cA A⟫_ℝ = ⟪cA A, z⟫_ℝ - 5 / 8 := by
    rw [inner_sub_right, inner_smul_right, hc1, mul_one]
  have hperp : (z - (5 / 8 : ℝ) • cA A) - ⟪cA A, z - (5 / 8 : ℝ) • cA A⟫_ℝ • cA A =
      z - ⟪cA A, z⟫_ℝ • cA A := by
    rw [hin]; module
  rw [hperp, hin]
  module

lemma continuous_LA (A : InvariantCaps.CapLabel) : Continuous (LA A) :=
  (LA_vec A).continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)

lemma det_LA_vec_of_card_eq_three {A : InvariantCaps.CapLabel} (hA : A.val.card = 3) :
    0 < LinearMap.det (LA_vec A) := by
  have hcard : Module.finrank ℝ Rep10 = Fintype.card (Fin 10) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  let v : Fin 10 → Rep10 := fun i => if i = 0 then cA A else if i = 1 then bA A else 0
  have hv_orth : Orthonormal ℝ (({0, 1} : Set (Fin 10)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hii : i = 0 ∨ i = 1 := by simpa using hi
    have hjj : j = 0 ∨ j = 1 := by simpa using hj
    rcases hii with rfl | rfl <;> rcases hjj with rfl | rfl
    · simp [v, norm_cA]
    · simp [v, inner_cA_bA]
    · simp [v]
      rw [real_inner_comm, inner_cA_bA]
    · simp [v, norm_bA]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv_orth
  have hb0 : b 0 = cA A := by simpa [v] using hb 0 (by simp)
  have hb1 : b 1 = bA A := by simpa [v] using hb 1 (by simp)
  have horth := b.orthonormal
  have hL0 : LA_vec A (b 0) = (-8 : ℝ) • b 0 := by
    rw [hb0]
    dsimp [LA_vec]
    have hc1 : ⟪cA A, cA A⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, norm_cA, one_pow]
    rw [hc1, one_smul, sub_self, map_zero, smul_zero, zero_sub, mul_one, neg_smul]
  have hL1 : LA_vec A (b 1) = (-8 / 5 : ℝ) • b 1 := by
    rw [hb1]
    dsimp [LA_vec]
    have hcb : ⟪cA A, bA A⟫_ℝ = 0 := inner_cA_bA A
    have hbb : ⟪bA A, bA A⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, norm_bA, one_pow]
    rw [hcb, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero]
    simp only [reflCap, hA, ↓reduceIte, reflB, LinearMap.coe_mk, AddHom.coe_mk, hbb, mul_one]
    module
  have hLi : ∀ i : Fin 10, i ≠ 0 → i ≠ 1 → LA_vec A (b i) = (8 / 5 : ℝ) • b i := by
    intro i hi0 hi1
    dsimp [LA_vec]
    have hci : ⟪cA A, b i⟫_ℝ = 0 := by
      rw [← hb0]
      exact Orthonormal.inner_eq_zero horth hi0.symm
    have hbi : ⟪bA A, b i⟫_ℝ = 0 := by
      rw [← hb1]
      exact Orthonormal.inner_eq_zero horth hi1.symm
    rw [hci, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero]
    simp only [reflCap, hA, ↓reduceIte, reflB, LinearMap.coe_mk, AddHom.coe_mk, hbi, mul_zero,
      zero_smul, sub_zero]
  let d : Fin 10 → ℝ := fun i => if i = 0 then -8 else if i = 1 then -8 / 5 else 8 / 5
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis (LA_vec A) = Matrix.diagonal d := by
    ext r i
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    by_cases hi0 : i = 0
    · subst hi0
      change (b.toBasis.repr ((LA_vec A) (b 0))) r = _
      rw [hL0, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply,
        orthonormal_iff_ite.mp horth r 0]
      split_ifs with hr <;> simp [d, hr]
    · by_cases hi1 : i = 1
      · subst hi1
        change (b.toBasis.repr ((LA_vec A) (b 1))) r = _
        rw [hL1, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
          OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply,
          orthonormal_iff_ite.mp horth r 1]
        split_ifs with hr <;> simp [d, hr, eq_comm]
      · change (b.toBasis.repr ((LA_vec A) (b i))) r = _
        rw [hLi i hi0 hi1, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
          OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply,
          orthonormal_iff_ite.mp horth r i]
        split_ifs with hr <;> simp [d, hr, hi0, hi1]
  rw [← LinearMap.det_toMatrix b.toBasis (LA_vec A), hmat, Matrix.det_diagonal]
  have hprod : ∏ i : Fin 10, d i = (-8 : ℝ) * (-8 / 5) * (8 / 5) ^ 8 := by
    simp [Fin.prod_univ_succ, d]
    norm_num
  rw [hprod]
  norm_num

lemma det_LA_vec_of_card_ne_three {A : InvariantCaps.CapLabel} (hA : A.val.card ≠ 3) :
    LinearMap.det (LA_vec A) < 0 := by
  have hcard : Module.finrank ℝ Rep10 = Fintype.card (Fin 10) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  let v : Fin 10 → Rep10 := fun _ => cA A
  have hv_orth : Orthonormal ℝ (({0} : Set (Fin 10)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rcases hi with rfl; rcases hj with rfl
    simp [v, norm_cA]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv_orth
  have hb0 : b 0 = cA A := by simpa [v] using hb 0 (by simp)
  have horth := b.orthonormal
  have hL0 : LA_vec A (b 0) = (-8 : ℝ) • b 0 := by
    rw [hb0]
    dsimp [LA_vec]
    have hc1 : ⟪cA A, cA A⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, norm_cA, one_pow]
    rw [hc1, one_smul, sub_self, map_zero, smul_zero, zero_sub, mul_one, neg_smul]
  have hLi : ∀ i : Fin 10, i ≠ 0 → LA_vec A (b i) = (8 / 5 : ℝ) • b i := by
    intro i hi0
    dsimp [LA_vec]
    have hci : ⟪cA A, b i⟫_ℝ = 0 := by
      rw [← hb0]
      exact Orthonormal.inner_eq_zero horth hi0.symm
    rw [hci, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero]
    simp [reflCap, hA]
  let d : Fin 10 → ℝ := fun i => if i = 0 then -8 else 8 / 5
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis (LA_vec A) = Matrix.diagonal d := by
    ext r i
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    by_cases hi0 : i = 0
    · subst hi0
      change (b.toBasis.repr ((LA_vec A) (b 0))) r = _
      rw [hL0, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply,
        orthonormal_iff_ite.mp horth r 0]
      split_ifs with hr <;> simp [d, hr]
    · change (b.toBasis.repr ((LA_vec A) (b i))) r = _
      rw [hLi i hi0, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply,
        orthonormal_iff_ite.mp horth r i]
      split_ifs with hr <;> simp [d, hr, hi0]
  rw [← LinearMap.det_toMatrix b.toBasis (LA_vec A), hmat, Matrix.det_diagonal]
  have hprod : ∏ i : Fin 10, d i = (-8 : ℝ) * (8 / 5) ^ 9 := by
    simp [Fin.prod_univ_succ, d]
    norm_num
  rw [hprod]
  norm_num

end LocalAffine

/-! ### Global 10-ball extension `F₀ : Rep10 → Rep10` and its 42 zeros -/

section BallExtension

def eps0 : ℝ := min (capDelta0 / 64) (1 / 32)

lemma eps0_pos : 0 < eps0 := lt_min (by have := capDelta0_pos; linarith) (by norm_num)
lemma eps0_le_delta : eps0 ≤ capDelta0 / 64 := min_le_left _ _
lemma eps0_le_32 : eps0 ≤ 1 / 32 := min_le_right _ _

def blendWeight (A : InvariantCaps.CapLabel) (z : Rep10) : ℝ :=
  1 - clamp01 ((2 * ‖z - (5 / 8 : ℝ) • cA A‖ - eps0) / eps0)

lemma blendWeight_nonneg (A : InvariantCaps.CapLabel) (z : Rep10) : 0 ≤ blendWeight A z := by
  unfold blendWeight
  linarith [clamp01_le_one ((2 * ‖z - (5 / 8 : ℝ) • cA A‖ - eps0) / eps0)]

lemma blendWeight_le_one (A : InvariantCaps.CapLabel) (z : Rep10) : blendWeight A z ≤ 1 := by
  unfold blendWeight
  linarith [clamp01_nonneg ((2 * ‖z - (5 / 8 : ℝ) • cA A‖ - eps0) / eps0)]

lemma blendWeight_eq_one {A : InvariantCaps.CapLabel} {z : Rep10}
    (hz : ‖z - (5 / 8 : ℝ) • cA A‖ ≤ eps0 / 2) : blendWeight A z = 1 := by
  unfold blendWeight
  have he : 0 < eps0 := eps0_pos
  have hle : (2 * ‖z - (5 / 8 : ℝ) • cA A‖ - eps0) / eps0 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) he.le
  rw [clamp01_of_nonpos hle, sub_zero]

lemma blendWeight_eq_zero {A : InvariantCaps.CapLabel} {z : Rep10}
    (hz : eps0 ≤ ‖z - (5 / 8 : ℝ) • cA A‖) : blendWeight A z = 0 := by
  unfold blendWeight
  have he : 0 < eps0 := eps0_pos
  have hge : 1 ≤ (2 * ‖z - (5 / 8 : ℝ) • cA A‖ - eps0) / eps0 :=
    (one_le_div he).mpr (by linarith)
  rw [clamp01_of_one_le hge, sub_self]

lemma continuous_blendWeight (A : InvariantCaps.CapLabel) : Continuous (blendWeight A) := by
  unfold blendWeight
  exact continuous_const.sub (continuous_clamp01.comp
    ((((continuous_const.mul (continuous_id.sub continuous_const).norm).sub continuous_const).div_const _)))

lemma blend_balls_disjoint {A B : InvariantCaps.CapLabel} (hne : A ≠ B) {z : Rep10}
    (hzA : ‖z - (5 / 8 : ℝ) • cA A‖ < eps0) :
    eps0 ≤ ‖z - (5 / 8 : ℝ) • cA B‖ := by
  have hd : 0 < capDelta0 := capDelta0_pos
  have hsep : 5 * capDelta0 ≤ ‖cA A - cA B‖ := capDelta0_sep hne
  have he1 : eps0 ≤ capDelta0 / 64 := eps0_le_delta
  have htri : (5 / 8 : ℝ) * ‖cA A - cA B‖ ≤ ‖z - (5 / 8 : ℝ) • cA A‖ + ‖z - (5 / 8 : ℝ) • cA B‖ := by
    calc (5 / 8 : ℝ) * ‖cA A - cA B‖
        = ‖(5 / 8 : ℝ) • (cA A - cA B)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
      _ = ‖(z - (5 / 8 : ℝ) • cA B) - (z - (5 / 8 : ℝ) • cA A)‖ := by
          congr 1; module
      _ ≤ ‖z - (5 / 8 : ℝ) • cA B‖ + ‖z - (5 / 8 : ℝ) • cA A‖ := norm_sub_le _ _
      _ = ‖z - (5 / 8 : ℝ) • cA A‖ + ‖z - (5 / 8 : ℝ) • cA B‖ := add_comm _ _
  linarith

def unitOf (z : Rep10) : Metric.sphere (0 : Rep10) 1 :=
  if hz : z = 0 then anchorS
  else ⟨‖z‖⁻¹ • z, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz)),
      inv_mul_cancel₀ (norm_pos_iff.mpr hz).ne']⟩

lemma unitOf_val_of_ne_zero {z : Rep10} (hz : z ≠ 0) :
    (unitOf z : Rep10) = ‖z‖⁻¹ • z := by
  simp [unitOf, hz]

lemma continuousOn_unitOf {s : Set Rep10} (hs : ∀ z ∈ s, z ≠ 0) :
    ContinuousOn unitOf s := by
  rw [continuousOn_iff_continuous_domRestrict]
  rw [continuous_induced_rng]
  have heq : (Subtype.val ∘ s.domRestrict unitOf) =
      fun z : s => ‖z.1‖⁻¹ • z.1 := by
    funext z
    exact unitOf_val_of_ne_zero (hs z.1 z.2)
  rw [heq]
  exact ((continuous_subtype_val.norm.inv₀ fun z => norm_ne_zero_iff.mpr (hs z.1 z.2)).smul
    continuous_subtype_val)

def basePush (z : Rep10) : Rep10 :=
  spherePush (unitOf z) (2 * ‖z‖ - 1)

lemma continuousOn_basePush {s : Set Rep10} (hs : ∀ z ∈ s, z ≠ 0) :
    ContinuousOn basePush s := by
  have hpair : ContinuousOn (fun z : Rep10 => (unitOf z, 2 * ‖z‖ - 1)) s :=
    (continuousOn_unitOf hs).prodMk
      ((continuous_const.mul continuous_norm).sub continuous_const).continuousOn
  exact continuous_spherePush.comp_continuousOn hpair

def capBlend (z : Rep10) : Rep10 :=
  basePush z + ∑ A : InvariantCaps.CapLabel, blendWeight A z • (LA A z - basePush z)

lemma continuousOn_capBlend {s : Set Rep10} (hs : ∀ z ∈ s, z ≠ 0) :
    ContinuousOn capBlend s := by
  have hbase := continuousOn_basePush hs
  refine hbase.add (continuousOn_finsetSum _ fun A _ => ?_)
  exact (continuous_blendWeight A).continuousOn.smul ((continuous_LA A).continuousOn.sub hbase)

lemma capBlend_eq_base_of_outside {z : Rep10}
    (hz : ∀ A : InvariantCaps.CapLabel, eps0 ≤ ‖z - (5 / 8 : ℝ) • cA A‖) :
    capBlend z = basePush z := by
  unfold capBlend
  have hsum : ∑ A : InvariantCaps.CapLabel, blendWeight A z • (LA A z - basePush z) = 0 :=
    Finset.sum_eq_zero fun A _ => by rw [blendWeight_eq_zero (hz A), zero_smul]
  rw [hsum, add_zero]

lemma capBlend_eq_blend_in {A : InvariantCaps.CapLabel} {z : Rep10}
    (hz : ‖z - (5 / 8 : ℝ) • cA A‖ < eps0) :
    capBlend z = (1 - blendWeight A z) • basePush z + blendWeight A z • LA A z := by
  unfold capBlend
  rw [Finset.sum_eq_single A]
  · module
  · intro B _ hBA
    rw [blendWeight_eq_zero (blend_balls_disjoint hBA.symm hz), zero_smul]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma capBlend_eq_LA_inner {A : InvariantCaps.CapLabel} {z : Rep10}
    (hz : ‖z - (5 / 8 : ℝ) • cA A‖ ≤ eps0 / 2) :
    capBlend z = LA A z := by
  have hlt : ‖z - (5 / 8 : ℝ) • cA A‖ < eps0 := lt_of_le_of_lt hz (by linarith [eps0_pos])
  rw [capBlend_eq_blend_in hlt, blendWeight_eq_one hz]
  module

def radialNormalize (z : Rep10) : Rep10 :=
  let s := spherePush (unitOf z) (1 / 2)
  (4 * (1 - ‖z‖) + (4 * ‖z‖ - 3) * ‖s‖⁻¹) • s

lemma continuousOn_radialNormalize {s : Set Rep10} (hs : ∀ z ∈ s, z ≠ 0) :
    ContinuousOn radialNormalize s := by
  have hu := continuousOn_unitOf hs
  have hsp : ContinuousOn (fun z : Rep10 => spherePush (unitOf z) (1 / 2)) s :=
    continuous_spherePush.comp_continuousOn (hu.prodMk continuousOn_const)
  have hne : ∀ z ∈ s, ‖spherePush (unitOf z) (1 / 2)‖ ≠ 0 := fun z _ =>
    norm_ne_zero_iff.mpr (spherePush_half_ne_zero _)
  have hcoeff : ContinuousOn (fun z : Rep10 =>
      4 * (1 - ‖z‖) + (4 * ‖z‖ - 3) * ‖spherePush (unitOf z) (1 / 2)‖⁻¹) s :=
    (continuous_const.mul (continuous_const.sub continuous_norm)).continuousOn.add
      (((continuous_const.mul continuous_norm).sub continuous_const).continuousOn.mul
        (hsp.norm.inv₀ hne))
  exact hcoeff.smul hsp

def F0 (z : Rep10) : Rep10 :=
  if ‖z‖ ≤ 1 / 2 then (2 : ℝ) • z
  else if ‖z‖ ≤ 3 / 4 then capBlend z
  else if ‖z‖ ≤ 1 then radialNormalize z
  else (q0 (unitOf z) : Rep10)

lemma norm_sub_five_eighths_cA_ge {z : Rep10} (A : InvariantCaps.CapLabel) :
    |‖z‖ - 5 / 8| ≤ ‖z - (5 / 8 : ℝ) • cA A‖ := by
  have hnorm : ‖(5 / 8 : ℝ) • cA A‖ = 5 / 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num), norm_cA, mul_one]
  simpa [hnorm] using abs_norm_sub_norm_le z ((5 / 8 : ℝ) • cA A)

lemma F0_eq_two_smul {z : Rep10} (hz : ‖z‖ ≤ 1 / 2) : F0 z = (2 : ℝ) • z := by
  simp only [F0, hz, ↓reduceIte]

lemma F0_eq_capBlend {z : Rep10} (h1 : 1 / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 3 / 4) :
    F0 z = capBlend z := by
  dsimp [F0]
  split_ifs with h1lt
  · have hnorm : ‖z‖ = 1 / 2 := le_antisymm h1lt h1
    have hne : z ≠ 0 := by intro hz0; rw [hz0, norm_zero] at hnorm; norm_num at hnorm
    have hout : ∀ A : InvariantCaps.CapLabel, eps0 ≤ ‖z - (5 / 8 : ℝ) • cA A‖ := fun A => by
      have hab : 1 / 8 ≤ |‖z‖ - 5 / 8| := by rw [hnorm]; norm_num
      exact le_trans (eps0_le_32.trans (by norm_num)) (hab.trans (norm_sub_five_eighths_cA_ge A))
    rw [capBlend_eq_base_of_outside hout, basePush, hnorm]
    have ht0 : 2 * (1 / 2 : ℝ) - 1 = 0 := by norm_num
    rw [ht0, spherePush_zero, unitOf_val_of_ne_zero hne, hnorm]
    norm_num
  · rfl

lemma F0_eq_radialNormalize {z : Rep10} (h1 : 3 / 4 ≤ ‖z‖) (h2 : ‖z‖ ≤ 1) :
    F0 z = radialNormalize z := by
  dsimp [F0]
  split_ifs with h1lt h2lt
  · exfalso; linarith
  · have hnorm : ‖z‖ = 3 / 4 := le_antisymm h2lt h1
    have hout : ∀ A : InvariantCaps.CapLabel, eps0 ≤ ‖z - (5 / 8 : ℝ) • cA A‖ := fun A => by
      have hab : 1 / 8 ≤ |‖z‖ - 5 / 8| := by rw [hnorm]; norm_num
      exact le_trans (eps0_le_32.trans (by norm_num)) (hab.trans (norm_sub_five_eighths_cA_ge A))
    have ht : 2 * (3 / 4 : ℝ) - 1 = 1 / 2 := by norm_num
    rw [capBlend_eq_base_of_outside hout, basePush, hnorm, ht]
    dsimp [radialNormalize]
    rw [hnorm]
    norm_num
  · rfl

lemma F0_eq_q0 {z : Rep10} (h1 : 1 ≤ ‖z‖) : F0 z = (q0 (unitOf z) : Rep10) := by
  dsimp [F0]
  split_ifs with h1lt h2lt h3lt
  · exfalso; linarith
  · exfalso; linarith
  · have hnorm : ‖z‖ = 1 := le_antisymm h3lt h1
    dsimp [radialNormalize]
    rw [hnorm, q0_val]
    norm_num
  · rfl

lemma F0_of_norm_eq_one {z : Rep10} (hz : ‖z‖ = 1) :
    F0 z = (q0 ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩ : Rep10) := by
  rw [F0_eq_q0 hz.symm.le]
  have hne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  congr 2
  apply Subtype.ext
  rw [unitOf_val_of_ne_zero hne]
  change ‖z‖⁻¹ • z = z
  rw [hz, inv_one, one_smul]

lemma continuous_F0 : Continuous F0 := by
  let C1 : Set Rep10 := {z | ‖z‖ ≤ 1 / 2}
  let C2 : Set Rep10 := {z | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4}
  let C3 : Set Rep10 := {z | 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1}
  let C4 : Set Rep10 := {z | 1 ≤ ‖z‖}
  have hC1 : IsClosed C1 := isClosed_le continuous_norm continuous_const
  have hC2 : IsClosed C2 :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hC3 : IsClosed C3 :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hC4 : IsClosed C4 := isClosed_le continuous_const continuous_norm
  have hf1 : ContinuousOn F0 C1 :=
    ((continuous_const (y := (2 : ℝ))).smul continuous_id).continuousOn.congr fun z hz =>
      F0_eq_two_smul hz
  have hne2 : ∀ z ∈ C2, z ≠ 0 := fun z hz h0 => by
    have := hz.1; rw [h0, norm_zero] at this; norm_num at this
  have hne3 : ∀ z ∈ C3, z ≠ 0 := fun z hz h0 => by
    have := hz.1; rw [h0, norm_zero] at this; norm_num at this
  have hne4 : ∀ z ∈ C4, z ≠ 0 := fun z hz h0 => by
    change 1 ≤ ‖z‖ at hz
    rw [h0, norm_zero] at hz
    norm_num at hz
  have hf2 : ContinuousOn F0 C2 :=
    (continuousOn_capBlend hne2).congr fun z hz => F0_eq_capBlend hz.1 hz.2
  have hf3 : ContinuousOn F0 C3 :=
    (continuousOn_radialNormalize hne3).congr fun z hz => F0_eq_radialNormalize hz.1 hz.2
  have hf4 : ContinuousOn F0 C4 := by
    have hq : ContinuousOn (fun z : Rep10 => (q0 (unitOf z) : Rep10)) C4 :=
      (continuous_subtype_val.comp q0.continuous).comp_continuousOn (continuousOn_unitOf hne4)
    exact hq.congr fun z hz => F0_eq_q0 hz
  have hcov : (C1 ∪ C2) ∪ (C3 ∪ C4) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    rcases le_total ‖z‖ (1 / 2) with h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases le_total ‖z‖ (3 / 4) with h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · rcases le_total ‖z‖ 1 with h3 | h3
        · exact Or.inr (Or.inl ⟨h2, h3⟩)
        · exact Or.inr (Or.inr h3)
  rw [← continuousOn_univ, ← hcov]
  exact (hf1.union_of_isClosed hf2 hC1 hC2).union_of_isClosed
    (hf3.union_of_isClosed hf4 hC3 hC4) (hC1.union hC2) (hC3.union hC4)

/-! ### Exact classification of the 42 zeros of `F₀` -/

lemma capChord_gt_two_thirds_mul {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (2 / 3 : ℝ) * r < capChord r := by
  unfold capChord
  have hs : Real.sqrt (4 + r ^ 2) < 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

lemma cap_blend_eq_push_and_LA {A : InvariantCaps.CapLabel} {z : Rep10}
    (hz : ‖z - (5 / 8 : ℝ) • cA A‖ < eps0) :
    1 / 2 < ‖z‖ ∧ ‖z‖ < 3 / 4 ∧
      F0 z = (1 - blendWeight A z) • basePush z + blendWeight A z • LA A z ∧
      ∃ μ : ℝ, 0 < μ ∧
        basePush z = (5 - 8 * ‖z‖) • cA A + μ • reflCap A (z - ⟪cA A, z⟫_ℝ • cA A) := by
  have he32 : eps0 ≤ 1 / 32 := eps0_le_32
  have heδ : eps0 ≤ capDelta0 / 64 := eps0_le_delta
  have hd : 0 < capDelta0 := capDelta0_pos
  have hd10 : capDelta0 < 1 / 10 := capDelta0_lt
  have hnorm_bnd : |‖z‖ - 5 / 8| < eps0 := lt_of_le_of_lt (norm_sub_five_eighths_cA_ge A) hz
  have hzlo : 19 / 32 < ‖z‖ := by linarith [(abs_lt.mp hnorm_bnd).1]
  have hzhi : ‖z‖ < 21 / 32 := by linarith [(abs_lt.mp hnorm_bnd).2]
  have h12 : 1 / 2 < ‖z‖ := by linarith
  have h34 : ‖z‖ < 3 / 4 := by linarith
  have hne : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h12; norm_num at h12
  refine ⟨h12, h34, ?_, ?_⟩
  · rw [F0_eq_capBlend h12.le h34.le, capBlend_eq_blend_in hz]
  · set x : Metric.sphere (0 : Rep10) 1 := unitOf z
    have hxval : (x : Rep10) = ‖z‖⁻¹ • z := unitOf_val_of_ne_zero hne
    have hdist_bnd : ‖(x : Rep10) - cA A‖ < 4 * eps0 := by
      have hsub : z - ‖z‖ • cA A = (z - (5 / 8 : ℝ) • cA A) + (5 / 8 - ‖z‖) • cA A := by module
      have h1 : ‖z - ‖z‖ • cA A‖ < 2 * eps0 := by
        calc ‖z - ‖z‖ • cA A‖
            ≤ ‖z - (5 / 8 : ℝ) • cA A‖ + ‖(5 / 8 - ‖z‖) • cA A‖ := by rw [hsub]; exact norm_add_le _ _
          _ = ‖z - (5 / 8 : ℝ) • cA A‖ + |5 / 8 - ‖z‖| := by
            rw [norm_smul, Real.norm_eq_abs, norm_cA, mul_one]
          _ < 2 * eps0 := by rw [abs_sub_comm]; linarith
      calc ‖(x : Rep10) - cA A‖
          = ‖‖z‖⁻¹ • (z - ‖z‖ • cA A)‖ := by
            rw [hxval, smul_sub, smul_smul, inv_mul_cancel₀ (norm_pos_iff.mpr hne).ne', one_smul]
        _ = ‖z‖⁻¹ * ‖z - ‖z‖ • cA A‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne))]
        _ < 2 * (2 * eps0) := by
            have hinv : ‖z‖⁻¹ < 2 := inv_lt_of_inv_lt₀ (by positivity) (by linarith)
            exact mul_lt_mul' hinv.le h1 (norm_nonneg _) (by norm_num)
        _ = 4 * eps0 := by ring
    have hch6 : capDelta0 / 16 < capChord (capDelta0 / 6) := by
      have hc := capChord_gt_two_thirds_mul (r := capDelta0 / 6) (by positivity) (by linarith)
      linarith
    have hch7 : ‖(x : Rep10) - cA A‖ < capChord (capDelta0 / 6) := by linarith
    have hch_cap : ‖(x : Rep10) - cA A‖ < capChord (3 * capDelta0 / 4) :=
      lt_trans hch7 (capChord_strictMono (Set.mem_Ici.mpr (by positivity))
        (Set.mem_Ici.mpr (by positivity)) (by linarith))
    have h2 : ‖(x : Rep10) - cA A‖ < 2 :=
      lt_trans hch_cap ((capChord_lt_self (by positivity)).trans (by linarith))
    have hxnorm : ‖(x : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hv_lt : ‖stereoProj (cA A) x.1‖ < capDelta0 / 6 :=
      (norm_stereoProj_lt_iff (norm_cA A) hxnorm h2 (by positivity)).mpr hch7
    have hρ : rhoCut ‖stereoProj (cA A) x.1‖ = 1 := rhoCut_eq_one hv_lt.le
    have hη : etaCut ‖stereoProj (cA A) x.1‖ = 1 := etaCut_eq_one (by linarith)
    set t : ℝ := 2 * ‖z‖ - 1
    have ht18 : 1 / 8 ≤ t := by dsimp [t]; linarith
    have htcut : timeCut t = 1 := timeCut_eq_one ht18
    have h1p : 0 < 1 + ⟪cA A, x.1⟫_ℝ := one_add_inner_pos_of_norm_sub_lt (norm_cA A) hxnorm h2
    let μ : ℝ := 2 / ((1 + ⟪cA A, x.1⟫_ℝ) * ‖z‖)
    have hμ : 0 < μ := by positivity
    refine ⟨μ, hμ, ?_⟩
    have hsp_eq : basePush z = localCapPush A x.1 t := by
      simpa [basePush, t] using spherePush_eq_localCapPush hch_cap t
    have hv_eq : stereoProj (cA A) x.1 = μ • (z - ⟪cA A, z⟫_ℝ • cA A) := by
      have hzpos : ‖z‖ ≠ 0 := (norm_pos_iff.mpr hne).ne'
      have hx_in : ⟪cA A, x.1⟫_ℝ = ‖z‖⁻¹ * ⟪cA A, z⟫_ℝ := by rw [hxval, inner_smul_right]
      have hp' : 1 + ‖z‖⁻¹ * ⟪cA A, z⟫_ℝ ≠ 0 := by rw [← hx_in]; exact h1p.ne'
      dsimp [stereoProj, μ]
      rw [hxval, inner_smul_right, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul]
      congr 1
      · congr 1
        field_simp
      · congr 1
        field_simp
    rw [hsp_eq]
    dsimp [localCapPush]
    rw [hρ, htcut, mul_one, sub_self, zero_smul, zero_add, one_smul, mul_one]
    rw [reflCap_eq_capPsi A ht18 hη, hv_eq, map_smul]
    have htlin : 1 - 4 * t = 5 - 8 * ‖z‖ := by dsimp [t]; ring
    calc cA A + μ • reflCap A (z - ⟪cA A, z⟫_ℝ • cA A) - (4 * t) • cA A
        = (1 - 4 * t) • cA A + μ • reflCap A (z - ⟪cA A, z⟫_ℝ • cA A) := by module
      _ = (5 - 8 * ‖z‖) • cA A + μ • reflCap A (z - ⟪cA A, z⟫_ℝ • cA A) := by rw [htlin]

lemma F0_eq_zero_iff (z : Rep10) :
    F0 z = 0 ↔ z = 0 ∨ ∃ A : InvariantCaps.CapLabel, z = (5 / 8 : ℝ) • cA A := by
  constructor
  · intro hz
    rcases le_or_gt ‖z‖ (1 / 2) with h1 | h1
    · rw [F0_eq_two_smul h1] at hz
      exact Or.inl ((smul_eq_zero.mp hz).resolve_left (by norm_num))
    · have hne : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; norm_num at h1
      rcases le_or_gt ‖z‖ (3 / 4) with h2 | h2
      · rw [F0_eq_capBlend h1.le h2] at hz
        by_cases hA : ∃ A : InvariantCaps.CapLabel, ‖z - (5 / 8 : ℝ) • cA A‖ < eps0
        · obtain ⟨A, hzA⟩ := hA
          obtain ⟨_, _, hblend, μ, hμ, hbase⟩ := cap_blend_eq_push_and_LA hzA
          rw [F0_eq_capBlend h1.le h2] at hblend
          rw [hz] at hblend
          set w := blendWeight A z
          have hw0 : 0 ≤ w := blendWeight_nonneg A z
          have hw1 : w ≤ 1 := blendWeight_le_one A z
          set zperp := z - ⟪cA A, z⟫_ℝ • cA A
          have hperp : ⟪cA A, zperp⟫_ℝ = 0 := by
            dsimp [zperp]
            rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_cA, one_pow,
              mul_one, sub_self]
          have hrefl_perp : ⟪cA A, reflCap A zperp⟫_ℝ = 0 := by
            unfold reflCap
            split_ifs
            · dsimp [reflB]
              rw [inner_sub_right, inner_smul_right, inner_cA_bA, mul_zero, sub_zero, hperp]
            · exact hperp
          have hrefl_perp_symm : ⟪reflCap A zperp, cA A⟫_ℝ = 0 := by
            rw [real_inner_comm]; exact hrefl_perp
          have hcombine :
              0 = ((1 - w) * (5 - 8 * ‖z‖) + w * (5 - 8 * ⟪cA A, z⟫_ℝ)) • cA A +
                  ((1 - w) * μ + w * (8 / 5)) • reflCap A zperp := by
            calc (0 : Rep10) = (1 - w) • basePush z + w • LA A z := hblend
              _ = (1 - w) • ((5 - 8 * ‖z‖) • cA A + μ • reflCap A zperp) +
                    w • ((8 / 5 : ℝ) • reflCap A zperp + (5 - 8 * ⟪cA A, z⟫_ℝ) • cA A) := by
                  rw [hbase, LA_eq]
              _ = ((1 - w) * (5 - 8 * ‖z‖) + w * (5 - 8 * ⟪cA A, z⟫_ℝ)) • cA A +
                    ((1 - w) * μ + w * (8 / 5)) • reflCap A zperp := by module
          have hdot_refl : 0 = ((1 - w) * μ + w * (8 / 5)) * ‖reflCap A zperp‖ ^ 2 := by
            have := congrArg (fun v : Rep10 => ⟪reflCap A zperp, v⟫_ℝ) hcombine
            rw [inner_zero_right, inner_add_right, inner_smul_right, inner_smul_right,
              hrefl_perp_symm, mul_zero, zero_add, real_inner_self_eq_norm_sq] at this
            exact this
          have hcoeff_pos : 0 < (1 - w) * μ + w * (8 / 5) := by
            by_cases hw_eq : w = 1
            · rw [hw_eq]; norm_num
            · have : 0 < 1 - w := sub_pos.mpr (lt_of_le_of_ne hw1 hw_eq)
              nlinarith
          have hrefl0 : reflCap A zperp = 0 := by
            have hnsq : ‖reflCap A zperp‖ ^ 2 = 0 :=
              (mul_eq_zero.mp hdot_refl.symm).resolve_left hcoeff_pos.ne'
            exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnsq)
          have hzperp0 : zperp = 0 := by
            have hn : ‖zperp‖ = 0 := by rw [← norm_reflCap A zperp, hrefl0, norm_zero]
            exact norm_eq_zero.mp hn
          have hzs : z = ⟪cA A, z⟫_ℝ • cA A := sub_eq_zero.mp hzperp0
          have hs_pos : 0 < ⟪cA A, z⟫_ℝ := by
            have hnorm_s : ‖z‖ = |⟪cA A, z⟫_ℝ| := by
              conv_lhs => rw [hzs]
              rw [norm_smul, Real.norm_eq_abs, norm_cA, mul_one]
            have hlt_eps : |⟪cA A, z⟫_ℝ - 5 / 8| < eps0 := by
              have h1' : (⟪cA A, z⟫_ℝ - 5 / 8) • cA A = z - (5 / 8 : ℝ) • cA A := by
                conv_rhs => rw [hzs]
                module
              have h2' := hzA
              rw [← h1', norm_smul, Real.norm_eq_abs, norm_cA, mul_one] at h2'
              exact h2'
            linarith [(abs_lt.mp hlt_eps).1, eps0_le_32]
          have hznorm : ‖z‖ = ⟪cA A, z⟫_ℝ := by
            conv_lhs => rw [hzs]
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, norm_cA, mul_one]
          have hdot_c : 0 = 5 - 8 * ⟪cA A, z⟫_ℝ := by
            have := congrArg (fun v : Rep10 => ⟪cA A, v⟫_ℝ) hcombine
            rw [inner_zero_right, inner_add_right, inner_smul_right, inner_smul_right,
              real_inner_self_eq_norm_sq, norm_cA, one_pow, mul_one, hrefl_perp, mul_zero,
              add_zero, hznorm] at this
            linarith
          have hs_eq : ⟪cA A, z⟫_ℝ = 5 / 8 := by linarith
          exact Or.inr ⟨A, by rw [hzs, hs_eq]⟩
        · push Not at hA
          rw [capBlend_eq_base_of_outside hA] at hz
          have hbase0 : spherePush (unitOf z) (2 * ‖z‖ - 1) = 0 := hz
          obtain ⟨A, hxA, ht⟩ := (spherePush_eq_zero_iff (by linarith) (by linarith)).mp hbase0
          have hnorm : ‖z‖ = 5 / 8 := by linarith
          rw [unitOf_val_of_ne_zero hne, hnorm] at hxA
          have hz_eq : z = (5 / 8 : ℝ) • cA A := by
            calc z = (5 / 8 : ℝ) • ((5 / 8 : ℝ)⁻¹ • z) := by module
              _ = (5 / 8 : ℝ) • cA A := by rw [hxA]
          exact Or.inr ⟨A, hz_eq⟩
      · exfalso
        rcases le_or_gt ‖z‖ 1 with h3 | h3
        · rw [F0_eq_radialNormalize h2.le h3] at hz
          dsimp [radialNormalize] at hz
          have hsne : spherePush (unitOf z) (1 / 2) ≠ 0 := spherePush_half_ne_zero _
          have hcpos : 0 < 4 * (1 - ‖z‖) + (4 * ‖z‖ - 3) * ‖spherePush (unitOf z) (1 / 2)‖⁻¹ := by
            have hinv : 0 < ‖spherePush (unitOf z) (1 / 2)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hsne)
            have h1' : 0 ≤ 1 - ‖z‖ := sub_nonneg.mpr h3
            have h2' : 0 < 4 * ‖z‖ - 3 := by linarith
            nlinarith
          rcases smul_eq_zero.mp hz with h0 | h0
          · exact hcpos.ne' h0
          · exact hsne h0
        · rw [F0_eq_q0 h3.le] at hz
          have h1 := mem_sphere_zero_iff_norm.mp (q0 (unitOf z)).2
          rw [hz, norm_zero] at h1
          norm_num at h1
  · rintro (rfl | ⟨A, rfl⟩)
    · rw [F0_eq_two_smul (by norm_num), smul_zero]
    · have hnorm : ‖(5 / 8 : ℝ) • cA A‖ = 5 / 8 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num), norm_cA, mul_one]
      rw [F0_eq_capBlend (by rw [hnorm]; norm_num) (by rw [hnorm]; norm_num),
        capBlend_eq_LA_inner (A := A) (by rw [sub_self, norm_zero]; exact (half_pos eps0_pos).le)]
      simp [LA]

end BallExtension

/-! ### Applying `Surgery.surgery` to get a nowhere-vanishing filling and null-homotopy of `q₀` -/

section NullHomotopy

def ballPreimage : Set (ℝ × (Fin 9 → ℝ)) := emb ⁻¹' Metric.ball (0 : Rep10) 1

lemma isOpen_ballPreimage : IsOpen ballPreimage :=
  isOpen_ball.preimage continuous_emb

lemma convex_ballPreimage : Convex ℝ ballPreimage :=
  (convex_ball (0 : Rep10) 1).linear_preimage emb.toLinearMap

def F0Pull : ℝ × (Fin 9 → ℝ) → Rep10 := fun p => F0 (emb p)

lemma F0Pull_zeroSet :
    Surgery.zeros (fun _ : Unit => Q0) F0Pull () =
      insert (0 : ℝ × (Fin 9 → ℝ))
        ((fun A : InvariantCaps.CapLabel => emb.symm ((5 / 8 : ℝ) • cA A)) '' Set.univ) := by
  ext p
  simp only [Surgery.zeros, Set.mem_ofPred_eq, F0Pull, map_eq_zero_iff Q0 Q0_injective,
    F0_eq_zero_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro (hp | ⟨A, hA⟩)
    · exact Or.inl (by
        have h := congrArg emb.symm hp
        rw [emb.symm_apply_apply, map_zero] at h
        exact h)
    · exact Or.inr ⟨A, by
        have h := congrArg emb.symm hA
        rw [emb.symm_apply_apply] at h
        exact h.symm⟩
  · rintro (rfl | ⟨A, rfl⟩)
    · exact Or.inl (by simp)
    · exact Or.inr ⟨A, by simp⟩

lemma capLabel_sum_sign :
    (∑ A : InvariantCaps.CapLabel, (if A.val.card = 3 then (1 : ℤ) else -1)) = -1 := by
  let S1 : Finset InvariantCaps.CapLabel := Finset.univ.filter (fun A => A.val.card = 1)
  let S2 : Finset InvariantCaps.CapLabel := Finset.univ.filter (fun A => A.val.card = 2)
  let S3 : Finset InvariantCaps.CapLabel := Finset.univ.filter (fun A => A.val.card = 3)
  have hS1_card : S1.card = 6 := by
    have hbij : S1.card = (Finset.powersetCard 1 (Finset.univ : Finset (Fin 6))).card := by
      refine Finset.card_bij (fun A _ => A.val) ?_ ?_ ?_
      · intro A hA
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hA).2⟩
      · intro A _ B _ hAB
        exact Subtype.ext hAB
      · intro B hB
        have hBc : B.card = 1 := (Finset.mem_powersetCard.mp hB).2
        exact ⟨⟨B, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBc⟩, rfl⟩
    rw [hbij, Finset.card_powersetCard, Finset.card_fin]
    decide
  have hS2_card : S2.card = 15 := by
    have hbij : S2.card = (Finset.powersetCard 2 (Finset.univ : Finset (Fin 6))).card := by
      refine Finset.card_bij (fun A _ => A.val) ?_ ?_ ?_
      · intro A hA
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hA).2⟩
      · intro A _ B _ hAB
        exact Subtype.ext hAB
      · intro B hB
        have hBc : B.card = 2 := (Finset.mem_powersetCard.mp hB).2
        exact ⟨⟨B, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBc⟩, rfl⟩
    rw [hbij, Finset.card_powersetCard, Finset.card_fin]
    decide
  have hS3_card : S3.card = 20 := by
    have hbij : S3.card = (Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))).card := by
      refine Finset.card_bij (fun A _ => A.val) ?_ ?_ ?_
      · intro A hA
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hA).2⟩
      · intro A _ B _ hAB
        exact Subtype.ext hAB
      · intro B hB
        have hBc : B.card = 3 := (Finset.mem_powersetCard.mp hB).2
        exact ⟨⟨B, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBc⟩, rfl⟩
    rw [hbij, Finset.card_powersetCard, Finset.card_fin]
    decide
  have hpart : (Finset.univ : Finset InvariantCaps.CapLabel) = S1 ∪ (S2 ∪ S3) := by
    ext A
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, S1, S2, S3]
    have h1 := A.property.1
    have h2 := A.property.2
    omega
  have hd1 : Disjoint S1 (S2 ∪ S3) := by
    rw [Finset.disjoint_left]
    intro A h1 h23
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S1, S2, S3] at h1 h23
    omega
  have hd2 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro A h2 h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S2, S3] at h2 h3
    omega
  let f : InvariantCaps.CapLabel → ℤ := fun A => if A.val.card = 3 then 1 else -1
  calc ∑ A : InvariantCaps.CapLabel, f A
      = ∑ A ∈ S1 ∪ (S2 ∪ S3), f A := by rw [← hpart]
    _ = ∑ A ∈ S1, f A + (∑ A ∈ S2, f A + ∑ A ∈ S3, f A) := by
        rw [Finset.sum_union hd1, Finset.sum_union hd2]
    _ = ∑ _A ∈ S1, (-1 : ℤ) + (∑ _A ∈ S2, (-1 : ℤ) + ∑ _A ∈ S3, (1 : ℤ)) := by
        refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_)
        · refine Finset.sum_congr rfl fun A hA => ?_
          have hc : A.val.card = 1 := (Finset.mem_filter.mp hA).2
          simp [f, hc]
        · refine Finset.sum_congr rfl fun A hA => ?_
          have hc : A.val.card = 2 := (Finset.mem_filter.mp hA).2
          simp [f, hc]
        · refine Finset.sum_congr rfl fun A hA => ?_
          have hc : A.val.card = 3 := (Finset.mem_filter.mp hA).2
          simp [f, hc]
    _ = (S1.card : ℤ) * (-1) + ((S2.card : ℤ) * (-1) + (S3.card : ℤ) * 1) := by
        simp [Finset.sum_const]
    _ = -1 := by rw [hS1_card, hS2_card, hS3_card]; norm_num

lemma goodMap_F0Pull : Surgery.GoodMap (fun _ : Unit => Q0) ballPreimage F0Pull := by
  let hb := EuclideanSpace.basisFun (Fin 10) ℝ
  have hframe0 :
      Surgery.IsFrameAt F0Pull (0 : ℝ × (Fin 9 → ℝ))
        (fun i => ((2 : ℝ) • (LinearMap.id : Rep10 →ₗ[ℝ] Rep10)) (hb i)) := by
    refine ⟨1 / 8, by norm_num, fun h hh => ?_⟩
    have hnorm : ‖emb h‖ ≤ 1 / 2 := (norm_emb_le h).trans (by linarith)
    simp only [zero_add, F0Pull, map_zero, F0_eq_two_smul (by norm_num : ‖(0 : Rep10)‖ ≤ 1 / 2),
      smul_zero, zero_add, F0_eq_two_smul hnorm]
    dsimp only [hb]
    rw [lin_apply_basis]
    rfl
  have hdet0 :
      (Surgery.frameMat Q0 (Surgery.frameAt F0Pull (0 : ℝ × (Fin 9 → ℝ)))).det = (2 : ℝ) ^ 10 := by
    rw [Surgery.frameAt_eq hframe0]
    dsimp only [hb]
    rw [det_frameMat_Q0_eq, LinearMap.det_smul,
      finrank_euclideanSpace_fin, LinearMap.det_id, mul_one]
  have hframeA : ∀ A : InvariantCaps.CapLabel,
      Surgery.IsFrameAt F0Pull (emb.symm ((5 / 8 : ℝ) • cA A))
        (fun i => LA_vec A (hb i)) := by
    intro A
    refine ⟨eps0 / 8, div_pos eps0_pos (by norm_num), fun h hh => ?_⟩
    set z0 : Rep10 := (5 / 8 : ℝ) • cA A
    have hemb_norm : ‖emb h‖ < eps0 / 2 :=
      lt_of_le_of_lt (norm_emb_le h) (by linarith)
    have hdist_z0 : ‖z0 + emb h - z0‖ ≤ eps0 / 2 := by
      simpa [add_sub_cancel_left] using hemb_norm.le
    have hz0_norm : ‖z0‖ = 5 / 8 := by
      dsimp [z0]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num), norm_cA, mul_one]
    have hnorm_bnd : 1 / 2 ≤ ‖z0 + emb h‖ ∧ ‖z0 + emb h‖ ≤ 3 / 4 := by
      have he32 : eps0 ≤ 1 / 32 := eps0_le_32
      have htri : ‖z0‖ ≤ ‖z0 + emb h‖ + ‖emb h‖ := by
        simpa [add_neg_cancel_right] using norm_add_le (z0 + emb h) (-emb h)
      have h2 : ‖z0 + emb h‖ ≤ ‖z0‖ + ‖emb h‖ := norm_add_le _ _
      constructor <;> linarith
    have hz0_zero : F0 z0 = 0 := (F0_eq_zero_iff z0).mpr (Or.inr ⟨A, rfl⟩)
    simp only [F0Pull, map_add, emb.apply_symm_apply, hz0_zero, zero_add]
    rw [F0_eq_capBlend hnorm_bnd.1 hnorm_bnd.2, capBlend_eq_LA_inner hdist_z0]
    dsimp [hb]
    rw [lin_apply_basis]
    dsimp [LA, z0]
    congr 1
    module
  have hdetA : ∀ A : InvariantCaps.CapLabel,
      (Surgery.frameMat Q0 (Surgery.frameAt F0Pull (emb.symm ((5 / 8 : ℝ) • cA A)))).det =
        LinearMap.det (LA_vec A) := fun A => by
    rw [Surgery.frameAt_eq (hframeA A)]
    dsimp [hb]
    rw [det_frameMat_Q0_eq]
  refine ⟨continuous_F0.comp continuous_emb, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [F0Pull_zeroSet]
    exact (Set.finite_singleton _).union (Set.finite_univ.image _)
  · intro j p hp
    have hp0 : F0 (emb p) = 0 := Q0_injective (by simpa [F0Pull] using hp)
    rcases (F0_eq_zero_iff (emb p)).mp hp0 with hz0 | ⟨A, hzA⟩
    · rw [ballPreimage, Set.mem_preimage, Metric.mem_ball, dist_zero_right, hz0, norm_zero]
      norm_num
    · rw [ballPreimage, Set.mem_preimage, Metric.mem_ball, dist_zero_right, hzA,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num), norm_cA, mul_one]
      norm_num
  · intro j p hp
    have hp0 : F0 (emb p) = 0 := Q0_injective (by simpa [F0Pull] using hp)
    rcases (F0_eq_zero_iff (emb p)).mp hp0 with hz0 | ⟨A, hzA⟩
    · have hp_eq : p = 0 := by simpa using congrArg emb.symm hz0
      subst hp_eq
      refine ⟨⟨_, hframe0⟩, ?_⟩
      rw [hdet0]
      norm_num
    · have hp_eq : p = emb.symm ((5 / 8 : ℝ) • cA A) := by simpa using congrArg emb.symm hzA
      subst hp_eq
      refine ⟨⟨_, hframeA A⟩, ?_⟩
      rw [hdetA A]
      by_cases hc3 : A.val.card = 3
      · exact (det_LA_vec_of_card_eq_three hc3).ne'
      · exact (det_LA_vec_of_card_ne_three hc3).ne
  · intro j
    rw [F0Pull_zeroSet]
    have hnot0 : (0 : ℝ × (Fin 9 → ℝ)) ∉
        ((fun A : InvariantCaps.CapLabel => emb.symm ((5 / 8 : ℝ) • cA A)) '' Set.univ) := by
      rintro ⟨A, -, hA⟩
      have := congrArg (fun p => ‖emb p‖) hA
      simp only [emb.apply_symm_apply, map_zero, norm_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8), norm_cA, mul_one] at this
      norm_num at this
    have hinj : Function.Injective (fun A : InvariantCaps.CapLabel => emb.symm ((5 / 8 : ℝ) • cA A)) := by
      intro A B hAB
      have h1 := congrArg (fun p => (8 / 5 : ℝ) • emb p) hAB
      simp only [emb.apply_symm_apply, smul_smul] at h1
      norm_num at h1
      exact cA_injective h1
    rw [finsum_mem_insert _ hnot0 (Set.finite_univ.image _)]
    have hz0 : Surgery.zsign Q0 F0Pull 0 = 1 := by
      simp [Surgery.zsign, hdet0]
    have himg :
        (∑ᶠ (x : ℝ × (Fin 9 → ℝ)) (_ : x ∈
            (fun A : InvariantCaps.CapLabel => emb.symm ((5 / 8 : ℝ) • cA A)) '' Set.univ),
            Surgery.zsign Q0 F0Pull x) =
          ∑ A : InvariantCaps.CapLabel, (if A.val.card = 3 then (1 : ℤ) else -1) := by
      rw [finsum_mem_image hinj.injOn, finsum_eq_sum_of_fintype]
      refine Finset.sum_congr rfl fun A _ => ?_
      dsimp [Surgery.zsign]
      rw [hdetA A]
      split_ifs with hc3
      · have hpos := det_LA_vec_of_card_eq_three hc3
        simp [sign_pos hpos]
      · have hneg := det_LA_vec_of_card_ne_three hc3
        simp [sign_neg hneg]
    rw [hz0, himg, capLabel_sum_sign]
    ring

lemma exists_nowhere_zero_filling :
    ∃ G : Rep10 → Rep10,
      Continuous G ∧
      (∀ z : Rep10, G z ≠ 0) ∧
      (∀ z : Rep10, ‖z‖ = 1 → G z = F0 z) := by
  have hcodim : ∀ _j : Unit, Module.finrank ℝ (LinearMap.ker Q0) + 3 ≤ Module.finrank ℝ Rep10 := by
    intro _
    rw [ker_Q0, finrank_bot, zero_add, finrank_euclideanSpace_fin]
    omega
  have hrank : ∀ i j : Unit, (LinearMap.ker Q0) ≠ (LinearMap.ker Q0) →
      ∃ u ∈ LinearMap.ker Q0, ∃ w ∈ LinearMap.ker Q0,
        LinearIndependent ℝ ![Q0 u, Q0 w] := fun _ _ h => (h rfl).elim
  obtain ⟨G', hGcont, K, _, hKU, hGeq, hGnz⟩ :=
    Surgery.surgery (by norm_num : 2 ≤ 9) hcodim hrank isOpen_ballPreimage convex_ballPreimage
      goodMap_F0Pull
  refine ⟨fun z => G' (emb.symm z), hGcont.comp continuous_emb_symm, ?_, ?_⟩
  · intro z hz
    have hq0 := hGnz (emb.symm z) ()
    dsimp at hz
    exact hq0 (by rw [hz, map_zero])
  · intro z hz
    have hnotU : emb.symm z ∉ ballPreimage := by
      simp [ballPreimage, emb.apply_symm_apply, hz]
    have hnotK : emb.symm z ∉ K := fun h => hnotU (hKU h)
    have h := hGeq (emb.symm z) hnotK
    simpa [F0Pull] using h

def filledBallMap : Rep10 → Rep10 :=
  Classical.choose exists_nowhere_zero_filling

lemma continuous_filledBallMap : Continuous filledBallMap :=
  (Classical.choose_spec exists_nowhere_zero_filling).1

lemma filledBallMap_ne_zero (z : Rep10) : filledBallMap z ≠ 0 :=
  (Classical.choose_spec exists_nowhere_zero_filling).2.1 z

lemma filledBallMap_sphere {z : Rep10} (hz : ‖z‖ = 1) : filledBallMap z = F0 z :=
  (Classical.choose_spec exists_nowhere_zero_filling).2.2 z hz

def nullHomotopy_q0Fun (p : Metric.sphere (0 : Rep10) 1 × Set.Icc (0 : ℝ) 1) :
    Metric.sphere (0 : Rep10) 1 :=
  let v : Rep10 := (1 - (p.2 : ℝ)) • (p.1 : Rep10) + (p.2 : ℝ) • (anchorS : Rep10)
  let y : Rep10 := filledBallMap v
  ⟨‖y‖⁻¹ • y, by
    have hy : y ≠ 0 := filledBallMap_ne_zero v
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hy)),
      inv_mul_cancel₀ (norm_pos_iff.mpr hy).ne']⟩

lemma continuous_nullHomotopy_q0Fun : Continuous nullHomotopy_q0Fun := by
  rw [continuous_induced_rng]
  have hv : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × Set.Icc (0 : ℝ) 1 =>
      (1 - (p.2 : ℝ)) • (p.1 : Rep10) + (p.2 : ℝ) • (anchorS : Rep10)) :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul continuous_const)
  have hy : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × Set.Icc (0 : ℝ) 1 =>
      filledBallMap ((1 - (p.2 : ℝ)) • (p.1 : Rep10) + (p.2 : ℝ) • (anchorS : Rep10))) :=
    continuous_filledBallMap.comp hv
  have hval : (Subtype.val ∘ nullHomotopy_q0Fun) =
      fun p : Metric.sphere (0 : Rep10) 1 × Set.Icc (0 : ℝ) 1 =>
        ‖filledBallMap ((1 - (p.2 : ℝ)) • (p.1 : Rep10) + (p.2 : ℝ) • (anchorS : Rep10))‖⁻¹ •
          filledBallMap ((1 - (p.2 : ℝ)) • (p.1 : Rep10) + (p.2 : ℝ) • (anchorS : Rep10)) := rfl
  rw [hval]
  exact (hy.norm.inv₀ fun p => norm_ne_zero_iff.mpr (filledBallMap_ne_zero _)).smul hy

def nullHomotopy_q0 : C(Metric.sphere (0 : Rep10) 1 × Set.Icc (0 : ℝ) 1, Metric.sphere (0 : Rep10) 1) :=
  ⟨nullHomotopy_q0Fun, continuous_nullHomotopy_q0Fun⟩

lemma nullHomotopy_q0_zero (x : Metric.sphere (0 : Rep10) 1) :
    nullHomotopy_q0 (x, ⟨0, by norm_num, by norm_num⟩) = q0 x := by
  apply Subtype.ext
  change (nullHomotopy_q0Fun (x, ⟨0, _⟩) : Rep10) = (q0 x : Rep10)
  dsimp [nullHomotopy_q0Fun]
  have hx1 : ‖(x : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hv : (1 - (0 : ℝ)) • (x : Rep10) + (0 : ℝ) • (anchorS : Rep10) = (x : Rep10) := by module
  rw [hv, filledBallMap_sphere hx1, F0_of_norm_eq_one hx1]
  have hq : ‖(q0 x : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp (q0 x).2
  have hqeq : q0 ⟨x.1, mem_sphere_zero_iff_norm.mpr hx1⟩ = q0 x := by congr 1
  rw [hqeq, hq, inv_one, one_smul]

lemma nullHomotopy_q0_one (x : Metric.sphere (0 : Rep10) 1) :
    nullHomotopy_q0 (x, ⟨1, by norm_num, by norm_num⟩) = anchorS := by
  apply Subtype.ext
  change (nullHomotopy_q0Fun (x, ⟨1, _⟩) : Rep10) = (anchorS : Rep10)
  dsimp [nullHomotopy_q0Fun]
  have ha1 : ‖(anchorS : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp anchorS.2
  have hv : (1 - (1 : ℝ)) • (x : Rep10) + (1 : ℝ) • (anchorS : Rep10) = (anchorS : Rep10) := by module
  rw [hv, filledBallMap_sphere ha1, F0_of_norm_eq_one ha1]
  have hanc : (⟨anchorS.1, mem_sphere_zero_iff_norm.mpr ha1⟩ : Metric.sphere (0 : Rep10) 1) = anchorS := by
    apply Subtype.ext; rfl
  rw [hanc, q0_anchorS, ha1, inv_one, one_smul]

end NullHomotopy

/-! ### Finite free join `(Σ₆)^{*c}` and equivariant maps `β c : FreeJoin c → S⁹` -/

section FreeJoinInduction

structure JoinLeaf where
  toPerm : Equiv.Perm (Fin 6)
  deriving DecidableEq, Fintype

instance : TopologicalSpace JoinLeaf := ⊥
instance : DiscreteTopology JoinLeaf := ⟨rfl⟩
instance : CompactSpace JoinLeaf := Finite.compactSpace

def joinRel (X Y : Type*) (a b : X × Y × Set.Icc (0 : ℝ) 1) : Prop :=
  a = b ∨
  ((a.2.2 : ℝ) = 0 ∧ (b.2.2 : ℝ) = 0 ∧ a.1 = b.1) ∨
  ((a.2.2 : ℝ) = 1 ∧ (b.2.2 : ℝ) = 1 ∧ a.2.1 = b.2.1)

lemma joinRel_equivalence (X Y : Type*) : Equivalence (joinRel X Y) where
  refl _ := Or.inl rfl
  symm := by
    rintro a b (rfl | ⟨ha0, hb0, hx⟩ | ⟨ha1, hb1, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hb0, ha0, hx.symm⟩)
    · exact Or.inr (Or.inr ⟨hb1, ha1, hy.symm⟩)
  trans := by
    rintro a b c (rfl | ⟨ha0, hb0, habx⟩ | ⟨ha1, hb1, haby⟩)
        (rfl | ⟨hb0', hc0, hbcx⟩ | ⟨hb1', hc1, hbcy⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hb0', hc0, hbcx⟩)
    · exact Or.inr (Or.inr ⟨hb1', hc1, hbcy⟩)
    · exact Or.inr (Or.inl ⟨ha0, hb0, habx⟩)
    · exact Or.inr (Or.inl ⟨ha0, hc0, habx.trans hbcx⟩)
    · exfalso; linarith
    · exact Or.inr (Or.inr ⟨ha1, hb1, haby⟩)
    · exfalso; linarith
    · exact Or.inr (Or.inr ⟨ha1, hc1, haby.trans hbcy⟩)

def joinSetoid (X Y : Type*) : Setoid (X × Y × Set.Icc (0 : ℝ) 1) where
  r := joinRel X Y
  iseqv := joinRel_equivalence X Y

def TopJoin (X Y : Type*) : Type _ := Quotient (joinSetoid X Y)

instance instTopologicalSpaceTopJoin (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (TopJoin X Y) :=
  instTopologicalSpaceQuotient

instance instCompactSpaceTopJoin (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] :
    CompactSpace (TopJoin X Y) :=
  Quotient.compactSpace

def FreeJoin : ℕ → Type
  | 0 => PEmpty
  | 1 => JoinLeaf
  | c + 2 => TopJoin (FreeJoin (c + 1)) JoinLeaf

instance instTopologicalSpaceFreeJoin : (c : ℕ) → TopologicalSpace (FreeJoin c)
  | 0 => ⊥
  | 1 => inferInstanceAs (TopologicalSpace JoinLeaf)
  | c + 2 => @instTopologicalSpaceTopJoin _ _ (instTopologicalSpaceFreeJoin (c + 1)) inferInstance

instance instCompactSpaceFreeJoin : (c : ℕ) → CompactSpace (FreeJoin c)
  | 0 => inferInstanceAs (CompactSpace PEmpty)
  | 1 => inferInstanceAs (CompactSpace JoinLeaf)
  | c + 2 => @instCompactSpaceTopJoin _ _ (instTopologicalSpaceFreeJoin (c + 1)) inferInstance
      (instCompactSpaceFreeJoin (c + 1)) inferInstance

lemma nonempty_freeJoin : ∀ (c : ℕ), 1 ≤ c → Nonempty (FreeJoin c)
  | 0, hc => absurd hc (by decide)
  | 1, _ => ⟨⟨1⟩⟩
  | c + 2, _ =>
    let ⟨x⟩ := nonempty_freeJoin (c + 1) (by omega)
    ⟨Quotient.mk (joinSetoid _ _) (x, ⟨1⟩, ⟨0, by norm_num, by norm_num⟩)⟩

def joinActFun : (c : ℕ) → Equiv.Perm (Fin 6) → FreeJoin c → FreeJoin c
  | 0, _, x => PEmpty.elim x
  | 1, h, x => ⟨h * x.toPerm⟩
  | c + 2, h, q =>
    Quotient.map' (fun p => (joinActFun (c + 1) h p.1, ⟨h * p.2.1.toPerm⟩, p.2.2)) (by
      rintro ⟨x1, g1, s1⟩ ⟨x2, g2, s2⟩ (heq | ⟨hs1, hs2, hx⟩ | ⟨hs1, hs2, hg⟩)
      · cases heq; exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hs1, hs2, congrArg (joinActFun (c + 1) h) hx⟩)
      · exact Or.inr (Or.inr ⟨hs1, hs2, by
          dsimp at hg
          change (⟨h * g1.toPerm⟩ : JoinLeaf) = ⟨h * g2.toPerm⟩
          rw [hg]⟩)) q

lemma continuous_joinAct : ∀ (c : ℕ) (h : Equiv.Perm (Fin 6)), Continuous (joinActFun c h)
  | 0, _ => continuous_of_discreteTopology (α := PEmpty)
  | 1, _ => continuous_of_discreteTopology (α := JoinLeaf)
  | c + 2, h => by
    refine Continuous.quotient_lift (s := joinSetoid (FreeJoin (c + 1)) JoinLeaf) ?_ _
    refine continuous_quot_mk.comp ?_
    have ih := continuous_joinAct (c + 1) h
    have hleaf : Continuous (fun l : JoinLeaf => (⟨h * l.toPerm⟩ : JoinLeaf)) :=
      continuous_of_discreteTopology (α := JoinLeaf)
    exact (ih.comp continuous_fst).prodMk
      ((hleaf.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))

def joinAct (c : ℕ) (h : Equiv.Perm (Fin 6)) : C(FreeJoin c, FreeJoin c) :=
  ⟨joinActFun c h, continuous_joinAct c h⟩

lemma joinAct_one : ∀ (c : ℕ) (x : FreeJoin c), joinAct c 1 x = x
  | 0, x => PEmpty.elim x
  | 1, ⟨x⟩ => by
    change (⟨1 * x⟩ : JoinLeaf) = ⟨x⟩
    simp
  | c + 2, q => by
    refine Quotient.inductionOn q fun p => ?_
    change Quotient.mk (joinSetoid _ _)
      (joinAct (c + 1) 1 p.1, (⟨1 * p.2.1.toPerm⟩ : JoinLeaf), p.2.2) = Quotient.mk _ p
    rw [joinAct_one (c + 1) p.1, one_mul]

lemma joinAct_mul : ∀ (c : ℕ) (h₁ h₂ : Equiv.Perm (Fin 6)) (x : FreeJoin c),
    joinAct c (h₁ * h₂) x = joinAct c h₁ (joinAct c h₂ x)
  | 0, _, _, x => PEmpty.elim x
  | 1, h₁, h₂, ⟨x⟩ => by
    change (⟨(h₁ * h₂) * x⟩ : JoinLeaf) = ⟨h₁ * (h₂ * x)⟩
    rw [mul_assoc]
  | c + 2, h₁, h₂, q => by
    refine Quotient.inductionOn q fun p => ?_
    change Quotient.mk (joinSetoid _ _)
      (joinAct (c + 1) (h₁ * h₂) p.1, (⟨h₁ * h₂ * p.2.1.toPerm⟩ : JoinLeaf), p.2.2) =
      Quotient.mk (joinSetoid _ _)
        (joinAct (c + 1) h₁ (joinAct (c + 1) h₂ p.1),
          (⟨h₁ * (⟨h₂ * p.2.1.toPerm⟩ : JoinLeaf).toPerm⟩ : JoinLeaf), p.2.2)
    rw [joinAct_mul (c + 1) h₁ h₂ p.1, mul_assoc]

lemma permSphere_one (x : Metric.sphere (0 : Rep10) 1) : permSphere 1 x = x := by
  apply Subtype.ext
  exact perm10_one x.1

lemma permSphere_mul (g h : Equiv.Perm (Fin 6)) (x : Metric.sphere (0 : Rep10) 1) :
    permSphere (g * h) x = permSphere g (permSphere h x) := by
  apply Subtype.ext
  exact perm10_mul g h x.1

def betaPair (c : ℕ) (hc : 1 ≤ c) :
    { f : C(FreeJoin c, Metric.sphere (0 : Rep10) 1) //
      ∀ g x, f (joinAct c g x) = permSphere g (f x) } := by
  match c with
  | 0 => exact absurd hc (by decide)
  | 1 =>
    refine ⟨⟨fun (l : JoinLeaf) => permSphere l.toPerm anchorS,
      continuous_of_discreteTopology (α := JoinLeaf)⟩, fun g x => ?_⟩
    exact permSphere_mul g x.toPerm anchorS
  | c + 2 =>
    let ih := betaPair (c + 1) (by omega)
    let f0 := ih.1
    have hf0_eq : ∀ g x, f0 (joinAct (c + 1) g x) = permSphere g (f0 x) := ih.2
    let step : FreeJoin (c + 1) × JoinLeaf × Set.Icc (0 : ℝ) 1 → Metric.sphere (0 : Rep10) 1 :=
      fun p => permSphere p.2.1.toPerm (nullHomotopy_q0 (permSphere p.2.1.toPerm⁻¹ (f0 p.1), p.2.2))
    have hstep_cont : Continuous step := by
      refine continuous_iff_continuousAt.mpr fun p => ?_
      have hleaf : Continuous (fun q : FreeJoin (c + 1) × JoinLeaf × Set.Icc (0 : ℝ) 1 => q.2.1) :=
        continuous_fst.comp continuous_snd
      have harg : Continuous (fun q : FreeJoin (c + 1) × JoinLeaf × Set.Icc (0 : ℝ) 1 =>
          (permSphere p.2.1.toPerm⁻¹ (f0 q.1), q.2.2)) :=
        ((continuous_permSphere _).comp (f0.continuous.comp continuous_fst)).prodMk
          (continuous_snd.comp continuous_snd)
      have hloc : Continuous (fun q : FreeJoin (c + 1) × JoinLeaf × Set.Icc (0 : ℝ) 1 =>
          permSphere p.2.1.toPerm (nullHomotopy_q0 (permSphere p.2.1.toPerm⁻¹ (f0 q.1), q.2.2))) :=
        (continuous_permSphere _).comp (nullHomotopy_q0.continuous.comp harg)
      have hopen : IsOpen {q : FreeJoin (c + 1) × JoinLeaf × Set.Icc (0 : ℝ) 1 | q.2.1 = p.2.1} :=
        (isOpen_discrete {p.2.1}).preimage hleaf
      have heq : Set.EqOn step (fun q =>
          permSphere p.2.1.toPerm (nullHomotopy_q0 (permSphere p.2.1.toPerm⁻¹ (f0 q.1), q.2.2)))
          {q | q.2.1 = p.2.1} := fun q hq => by
        have hq' : q.2.1 = p.2.1 := hq
        simp [step, hq']
      exact (hloc.continuousOn.congr heq).continuousAt (hopen.mem_nhds rfl)
    have hstep_rel : ∀ a b, joinSetoid (FreeJoin (c + 1)) JoinLeaf a b → step a = step b := by
      rintro ⟨y1, g1, s1⟩ ⟨y2, g2, s2⟩ (heq | ⟨hs1, hs2, hy⟩ | ⟨hs1, hs2, hg⟩)
      · cases heq; rfl
      · have hs1' : s1 = ⟨0, by norm_num, by norm_num⟩ := Subtype.ext hs1
        have hs2' : s2 = ⟨0, by norm_num, by norm_num⟩ := Subtype.ext hs2
        subst hy; subst hs1'; subst hs2'
        simp only [step]
        rw [nullHomotopy_q0_zero, nullHomotopy_q0_zero, q0_equivariant, q0_equivariant,
          ← permSphere_mul, ← permSphere_mul, mul_inv_cancel, mul_inv_cancel, permSphere_one]
      · have hs1' : s1 = ⟨1, by norm_num, by norm_num⟩ := Subtype.ext hs1
        have hs2' : s2 = ⟨1, by norm_num, by norm_num⟩ := Subtype.ext hs2
        subst hg; subst hs1'; subst hs2'
        simp only [step]
        rw [nullHomotopy_q0_one, nullHomotopy_q0_one]
    refine ⟨⟨Quotient.lift step hstep_rel, Continuous.quotient_lift hstep_cont hstep_rel⟩, ?_⟩
    intro h q
    refine Quotient.inductionOn q fun p => ?_
    rcases p with ⟨y, g, s⟩
    change step (joinAct (c + 1) h y, ⟨h * g.toPerm⟩, s) = permSphere h (step (y, g, s))
    dsimp [step]
    rw [hf0_eq h y, mul_inv_rev, permSphere_mul g.toPerm⁻¹ h⁻¹ _, ← permSphere_mul h⁻¹ h,
      inv_mul_cancel, permSphere_one, permSphere_mul h g.toPerm]

def beta (c : ℕ) (hc : 1 ≤ c) : C(FreeJoin c, Metric.sphere (0 : Rep10) 1) :=
  (betaPair c hc).1

lemma beta_equivariant (c : ℕ) (hc : 1 ≤ c) (g : Equiv.Perm (Fin 6)) (x : FreeJoin c) :
    beta c hc (joinAct c g x) = permSphere g (beta c hc x) :=
  (betaPair c hc).2 g x

def beta15 : C(FreeJoin 15, Metric.sphere (0 : Rep10) 1) :=
  beta 15 (by decide)

lemma beta15_equivariant (g : Equiv.Perm (Fin 6)) (x : FreeJoin 15) :
    beta15 (joinAct 15 g x) = permSphere g (beta15 x) :=
  beta_equivariant 15 (by decide) g x

end FreeJoinInduction

end AkopyanResearch
