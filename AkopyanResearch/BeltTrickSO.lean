module

public import AkopyanResearch.QuaternionBelt
public import AkopyanResearch.FrameTransport
public import AkopyanResearch.CoxeterTriangulation

@[expose] public section

/-!
# The belt trick in `SO(n)` (`n ≥ 3`) via `QuaternionBelt`, `FrameTransport`, and codimension-2 reductions

1. Based loop space `BasedLoop n` in `SO n`, pointwise product `loopMul`, and the
   Eckmann–Hilton equivalence `loopConcat_homotopic_loopMul : γ₁.trans γ₂ ~ loopMul γ₁ γ₂`.
2. Block embedding `embedSO n : SO n →* SO (n + 1)` and smooth section extraction `extractSO`
   on matrices whose first column equals `e0 n`.
3. Loop reduction `exists_basedLoop_reduction_SO` (`2 ≤ n`): piecewise-chordal ramp approximation,
   omitted unit vector `v₀` via `exists_unit_notMem_biUnion_proper_subspaces`, stereographic
   contraction on `S^n`, and globally continuous strip-wise lift via `FrameTransport`.
4. Belt trick in `SO 3` via `QuaternionBelt.rotationHomotopy` and induction to every `SO n`
   (`3 ≤ n`), specializing to `basedLoop_double_nullHomotopic_SO13`.
-/

noncomputable section

open scoped BigOperators InnerProductSpace Classical unitInterval
open Metric Set

namespace AkopyanResearch

/-! ### 1. Based loops in `SO(n)` and Eckmann–Hilton -/

section LoopAlgebra

abbrev SO (n : ℕ) := Matrix.specialOrthogonalGroup (Fin n) ℝ

abbrev BasedLoop (n : ℕ) := Path (1 : SO n) 1

def BasedLoopHomotopic {n : ℕ} (γ₁ γ₂ : BasedLoop n) : Prop :=
  Path.Homotopic γ₁ γ₂

lemma continuous_SO_entry (n : ℕ) (i j : Fin n) : Continuous (fun A : SO n => A.1 i j) := by
  have hval : Continuous (fun A : SO n => (A.1 : Fin n → Fin n → ℝ)) := continuous_subtype_val
  exact (continuous_apply j).comp ((continuous_apply i).comp hval)

lemma continuous_mul_SO (n : ℕ) : Continuous (fun p : SO n × SO n => p.1 * p.2) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_fst).matrix_mul
    (continuous_subtype_val.comp continuous_snd)

def loopMul {n : ℕ} (γ₁ γ₂ : BasedLoop n) : BasedLoop n where
  toFun t := γ₁ t * γ₂ t
  continuous_toFun := (continuous_mul_SO n).comp (γ₁.continuous.prodMk γ₂.continuous)
  source' := by simp
  target' := by simp

@[simp] lemma loopMul_apply {n : ℕ} (γ₁ γ₂ : BasedLoop n) (t : I) :
    loopMul γ₁ γ₂ t = γ₁ t * γ₂ t := rfl

theorem basedLoopHomotopic_loopMul {n : ℕ} {γ₁ γ₂ δ₁ δ₂ : BasedLoop n}
    (h₁ : BasedLoopHomotopic γ₁ δ₁) (h₂ : BasedLoopHomotopic γ₂ δ₂) :
    BasedLoopHomotopic (loopMul γ₁ γ₂) (loopMul δ₁ δ₂) := by
  obtain ⟨H₁⟩ := h₁
  obtain ⟨H₂⟩ := h₂
  refine ⟨{
    toFun := fun p => H₁ p * H₂ p
    continuous_toFun := (continuous_mul_SO n).comp (H₁.continuous.prodMk H₂.continuous)
    map_zero_left := fun t => by simp [H₁.apply_zero t, H₂.apply_zero t]
    map_one_left := fun t => by simp [H₁.apply_one t, H₂.apply_one t]
    prop' := fun s t ht => by
      rcases ht with rfl | rfl
      · have a1 : H₁ (s, 0) = 1 := (H₁.prop' s 0 (by simp)).trans γ₁.source
        have a2 : H₂ (s, 0) = 1 := (H₂.prop' s 0 (by simp)).trans γ₂.source
        simp [a1, a2]
      · have a1 : H₁ (s, 1) = 1 := (H₁.prop' s 1 (by simp)).trans γ₁.target
        have a2 : H₂ (s, 1) = 1 := (H₂.prop' s 1 (by simp)).trans γ₂.target
        simp [a1, a2]
  }⟩

theorem loopConcat_eq_loopMul_refl {n : ℕ} (γ₁ γ₂ : BasedLoop n) :
    γ₁.trans γ₂ = loopMul (γ₁.trans (Path.refl 1)) ((Path.refl 1).trans γ₂) := by
  ext t
  simp only [loopMul_apply, Path.trans_apply]
  split_ifs <;> simp

theorem loopConcat_homotopic_loopMul {n : ℕ} (γ₁ γ₂ : BasedLoop n) :
    BasedLoopHomotopic (γ₁.trans γ₂) (loopMul γ₁ γ₂) := by
  rw [loopConcat_eq_loopMul_refl]
  exact basedLoopHomotopic_loopMul (Path.Homotopic.trans_refl γ₁) (Path.Homotopic.refl_trans γ₂)

end LoopAlgebra

/-! ### 2. Block embedding `embedSO` and section `extractSO` -/

section BlockEmbedding

def embedSOMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

@[simp] lemma embedSOMatrix_zero_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    embedSOMatrix n A 0 0 = 1 := rfl

@[simp] lemma embedSOMatrix_zero_succ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    embedSOMatrix n A 0 j.succ = 0 := rfl

@[simp] lemma embedSOMatrix_succ_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    embedSOMatrix n A i.succ 0 = 0 := rfl

@[simp] lemma embedSOMatrix_succ_succ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    embedSOMatrix n A i.succ j.succ = A i j := rfl

lemma embedSOMatrix_one (n : ℕ) : embedSOMatrix n 1 = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [Matrix.one_apply]
    | succ j => simp [Matrix.one_apply, Fin.ext_iff]
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [Matrix.one_apply, Fin.ext_iff]
    | succ j => simp [Matrix.one_apply]

lemma embedSOMatrix_mul (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    embedSOMatrix n (A * B) = embedSOMatrix n A * embedSOMatrix n B := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
    cases j using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma embedSOMatrix_transpose (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    embedSOMatrix n A.transpose = (embedSOMatrix n A).transpose := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> rfl

lemma det_embedSOMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (embedSOMatrix n A).det = A.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hsub : (embedSOMatrix n A).submatrix (0 : Fin (n + 1)).succAbove Fin.succ = A := by
    ext i j
    simp [Matrix.submatrix, Fin.succAbove_zero]
  have htail : ∑ x : Fin n, (-1 : ℝ) ^ (x.succ : ℕ) * embedSOMatrix n A x.succ 0 *
      ((embedSOMatrix n A).submatrix x.succ.succAbove Fin.succ).det = 0 :=
    Finset.sum_eq_zero fun x _ => by simp
  rw [htail, add_zero, hsub]
  simp

def embedSO (n : ℕ) : SO n →* SO (n + 1) where
  toFun A := ⟨embedSOMatrix n A.1, by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · have hAAT : A.1 ∈ Matrix.orthogonalGroup (Fin n) ℝ := A.2.1
      rw [Matrix.mem_orthogonalGroup_iff] at hAAT
      rw [← embedSOMatrix_transpose, ← embedSOMatrix_mul, hAAT, embedSOMatrix_one]
    · have hAdet : A.1.det = 1 := A.2.2
      change (embedSOMatrix n A.1).det = 1
      rw [det_embedSOMatrix, hAdet]⟩
  map_one' := by ext i j; simp [embedSOMatrix_one]
  map_mul' A B := by ext i j; simp [embedSOMatrix_mul]

lemma continuous_embedSO (n : ℕ) : Continuous (embedSO n) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  cases i using Fin.cases <;> cases j using Fin.cases
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · rename_i i' j'
    exact continuous_SO_entry n i' j'

def mapLoop (n : ℕ) (δ : BasedLoop n) : BasedLoop (n + 1) :=
  (δ.map (continuous_embedSO n)).cast (embedSO n).map_one.symm (embedSO n).map_one.symm

def e0 (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.single 0 1

def col0 {n : ℕ} (A : SO (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => A.1 i 0)

lemma norm_e0 (n : ℕ) : ‖e0 n‖ = 1 := by
  rw [e0, EuclideanSpace.norm_eq]
  simp [EuclideanSpace.single, PiLp.single_apply]

lemma norm_col0 {n : ℕ} (A : SO (n + 1)) : ‖col0 A‖ = 1 := by
  have hAT : A.1 ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ := A.2.1
  rw [Matrix.mem_orthogonalGroup_iff'] at hAT
  have h00 : ∑ i : Fin (n + 1), (A.1 i 0) ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M 0 0) hAT
    simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using h
  rw [EuclideanSpace.norm_eq]
  simp [col0, Real.norm_eq_abs, h00]

lemma col0_one (n : ℕ) : col0 (1 : SO (n + 1)) = e0 n := by
  ext i
  cases i using Fin.cases <;> simp [col0, e0, EuclideanSpace.single, Matrix.one_apply]

lemma continuous_col0 (n : ℕ) : Continuous (col0 (n := n)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp (continuous_pi fun i => ?_)
  exact continuous_SO_entry (n + 1) i 0

lemma extractSO_row0_eq_zero {n : ℕ} (A : SO (n + 1)) (hA : col0 A = e0 n) (j : Fin n) :
    A.1 0 j.succ = 0 := by
  have hA0 : A.1 0 0 = 1 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v 0) hA
    simpa [col0, e0, EuclideanSpace.single, PiLp.single_apply] using h
  have hAAT : A.1 ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ := A.2.1
  rw [Matrix.mem_orthogonalGroup_iff] at hAAT
  have h00 := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M 0 0) hAAT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, Fin.sum_univ_succ,
    hA0, mul_one] at h00
  have hsum : ∑ k : Fin n, (A.1 0 k.succ) ^ 2 = 0 := by
    have : ∑ k : Fin n, A.1 0 k.succ * A.1 0 k.succ = 0 := by linarith
    simpa [sq] using this
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (A.1 0 k.succ))).mp
    hsum j (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp hzero

def extractSO {n : ℕ} (A : SO (n + 1)) (hA : col0 A = e0 n) : SO n :=
  ⟨A.1.submatrix Fin.succ Fin.succ, by
    have hA0 : A.1 0 0 = 1 := by
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v 0) hA
      simpa [col0, e0, EuclideanSpace.single, PiLp.single_apply] using h
    have hAcol : ∀ i : Fin n, A.1 i.succ 0 = 0 := fun i => by
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v i.succ) hA
      simpa [col0, e0, EuclideanSpace.single, PiLp.single_apply] using h
    have hAAT : A.1 ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ := A.2.1
    rw [Matrix.mem_orthogonalGroup_iff] at hAAT
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i k
      have hik := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M i.succ k.succ) hAAT
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hAcol, zero_mul,
        zero_add, Matrix.one_apply, Fin.succ_inj] at hik
      simpa [Matrix.mul_apply, Matrix.submatrix, Matrix.one_apply] using hik
    · have hAdet : A.1.det = 1 := A.2.2
      have hdet := Matrix.det_succ_column_zero A.1
      rw [Fin.sum_univ_succ, hA0, hAdet] at hdet
      have htail : ∑ x : Fin n, (-1 : ℝ) ^ (x.succ : ℕ) * A.1 x.succ 0 *
          (A.1.submatrix x.succ.succAbove Fin.succ).det = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [hAcol x]
      rw [htail, add_zero] at hdet
      have hsub : A.1.submatrix (0 : Fin (n + 1)).succAbove Fin.succ =
          A.1.submatrix Fin.succ Fin.succ := by
        ext i j
        simp [Matrix.submatrix, Fin.succAbove_zero]
      simp only [Fin.val_zero, pow_zero, one_mul, hsub] at hdet
      exact hdet.symm⟩

lemma embedSO_extractSO {n : ℕ} (A : SO (n + 1)) (hA : col0 A = e0 n) :
    embedSO n (extractSO A hA) = A := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v 0) hA
      simpa [embedSO, col0, e0, EuclideanSpace.single, PiLp.single_apply] using h.symm
    | succ j =>
      simpa [embedSO] using (extractSO_row0_eq_zero A hA j).symm
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v i.succ) hA
      simpa [embedSO, col0, e0, EuclideanSpace.single, PiLp.single_apply] using h.symm
    | succ j =>
      rfl

lemma continuous_extractSO {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : X → SO (n + 1)) (hf : Continuous f) (hcol : ∀ x, col0 (f x) = e0 n) :
    Continuous (fun x => extractSO (f x) (hcol x)) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  exact (continuous_SO_entry (n + 1) i.succ j.succ).comp hf

end BlockEmbedding

/-! ### 3. Loop reduction `SO(n + 1) → SO(n)` for `2 ≤ n` -/

section LoopReduction

private def transportMatrix {n : ℕ} (u v : EuclideanSpace ℝ (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => FrameTransport.transport u v (EuclideanSpace.single j 1) i

private lemma transportMatrix_eq_toMatrix {n : ℕ} (u v : EuclideanSpace ℝ (Fin (n + 1))) :
    transportMatrix u v =
      LinearMap.toMatrix
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
        (FrameTransport.transport u v).toLinearMap := by
  ext i j
  simp [transportMatrix, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr]

private lemma transportMatrix_self {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    transportMatrix u u = 1 := by
  ext i j
  simp [transportMatrix, FrameTransport.transport_self, EuclideanSpace.single, PiLp.single_apply,
    Matrix.one_apply]

private lemma transportMatrix_mem_SO {n : ℕ} {u v : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : u ≠ 0) (huv : u + v ≠ 0) :
    transportMatrix u v ∈ SO (n + 1) := by
  let T := FrameTransport.transport u v
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    have hinner :
        ⟪T (EuclideanSpace.single i 1), T (EuclideanSpace.single j 1)⟫_ℝ =
          ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫_ℝ :=
      T.inner_map_map _ _
    have hlhs :
        ⟪T (EuclideanSpace.single i 1), T (EuclideanSpace.single j 1)⟫_ℝ =
          ((transportMatrix u v).transpose * transportMatrix u v) i j := by
      rw [PiLp.inner_apply]
      simp [T, Matrix.mul_apply, Matrix.transpose_apply, transportMatrix, mul_comm]
    have hrhs :
        ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫_ℝ =
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j := by
      have hi : EuclideanSpace.single i (1 : ℝ) = EuclideanSpace.basisFun (Fin (n + 1)) ℝ i :=
        (EuclideanSpace.basisFun_apply (Fin (n + 1)) ℝ i).symm
      have hj : EuclideanSpace.single j (1 : ℝ) = EuclideanSpace.basisFun (Fin (n + 1)) ℝ j :=
        (EuclideanSpace.basisFun_apply (Fin (n + 1)) ℝ j).symm
      rw [hi, hj]
      by_cases hij : i = j
      · subst hij
        rw [real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).orthonormal.1 i]
        simp [Matrix.one_apply]
      · rw [(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).orthonormal.2 hij]
        simp [Matrix.one_apply, hij]
    exact hlhs.symm.trans (hinner.trans hrhs)
  · rw [transportMatrix_eq_toMatrix, LinearMap.det_toMatrix]
    exact FrameTransport.det_transport hu huv

private lemma euclidean_sum_apply {ι : Type*} [DecidableEq ι] {κ : Type*}
    (s : Finset κ) (f : κ → EuclideanSpace ℝ ι) (i : ι) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma transportMatrix_mul_col0 {n : ℕ} (u v : EuclideanSpace ℝ (Fin (n + 1)))
    (A : SO (n + 1)) (hM : transportMatrix u v * A.1 ∈ SO (n + 1)) :
    col0 ⟨transportMatrix u v * A.1, hM⟩ = FrameTransport.transport u v (col0 A) := by
  ext i
  have hcol : col0 A = ∑ j : Fin (n + 1), (A.1 j 0) • EuclideanSpace.single j (1 : ℝ) := by
    ext k
    rw [euclidean_sum_apply]
    simp [col0, EuclideanSpace.single, PiLp.single_apply]
  rw [hcol, map_sum]
  simp_rw [map_smul]
  rw [euclidean_sum_apply]
  simp only [col0, Matrix.mul_apply, transportMatrix, Matrix.of_apply, PiLp.smul_apply,
    smul_eq_mul, mul_comm]

private lemma continuous_transportMatrix_comp {n : ℕ} {X : Type*} [TopologicalSpace X]
    {f g : X → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, f x ≠ 0) (hfg : ∀ x, f x + g x ≠ 0) :
    Continuous (fun x => transportMatrix (f x) (g x)) := by
  refine continuous_matrix fun i j => continuous_iff_continuousAt.mpr fun x => ?_
  have ht := FrameTransport.continuousAt_transport (u := f x) (v := g x)
    (x := EuclideanSpace.single j (1 : ℝ)) (hf0 x) (hfg x)
  have harg : Continuous (fun y : X => (f y, g y, EuclideanSpace.single j (1 : ℝ))) :=
    hf.prodMk (hg.prodMk continuous_const)
  have heval : ContinuousAt (fun p : EuclideanSpace ℝ (Fin (n + 1)) => p i)
      (FrameTransport.transport (f x) (g x) (EuclideanSpace.single j 1)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).continuousAt
  have hcomp : ContinuousAt (fun y : X => FrameTransport.transport (f y) (g y) (EuclideanSpace.single j 1)) x :=
    ContinuousAt.comp (f := fun y : X => (f y, g y, EuclideanSpace.single j (1 : ℝ))) ht harg.continuousAt
  exact ContinuousAt.comp (f := fun y : X => FrameTransport.transport (f y) (g y) (EuclideanSpace.single j 1))
    heval hcomp

private lemma add_ne_zero_of_sphere_dist_lt_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hlt : ‖u - v‖ < 2) :
    u + v ≠ 0 := by
  intro h0
  have hvu : v = -u := eq_neg_of_add_eq_zero_right h0
  rw [hvu, sub_neg_eq_add, ← two_smul ℝ u, norm_smul, Real.norm_of_nonneg zero_le_two, hu] at hlt
  linarith

private lemma convex_lt_one {a b s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : a < 1) (hb : b < 1) :
    (1 - s) * a + s * b < 1 := by
  rcases eq_or_lt_of_le hs0 with rfl | hs_pos
  · simpa using ha
  · have h1 : (1 - s) * a ≤ 1 - s := by
      nlinarith
    have h2 : s * b < s := by
      nlinarith
    linarith

private lemma neg_norm_sub_eq_norm_sub {E : Type*} [NormedAddCommGroup E] {x u : E}
    (hu : ‖u‖ = 1) (hlt : ‖x - u‖ < 1) : x ≠ 0 := by
  intro h0
  subst h0
  simp [hu] at hlt

private lemma st_formula_properties {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v₀ : E} (hv₀ : ‖v₀‖ = 1) :
    let st := fun x : E => (1 - ⟪v₀, x⟫_ℝ)⁻¹ • (x - ⟪v₀, x⟫_ℝ • v₀)
    let stInv := fun y : E => (‖y‖ ^ 2 + 1)⁻¹ • ((2 : ℝ) • y + (‖y‖ ^ 2 - 1) • v₀)
    (∀ x, ⟪v₀, st x⟫_ℝ = 0) ∧
    (∀ {x : E}, ‖x‖ = 1 → x ≠ v₀ → 0 < 1 - ⟪v₀, x⟫_ℝ) ∧
    (∀ {y : E}, ⟪v₀, y⟫_ℝ = 0 → ‖stInv y‖ = 1) ∧
    (∀ {x : E}, ‖x‖ = 1 → x ≠ v₀ → stInv (st x) = x) := by
  intro st stInv
  have hvv : ⟪v₀, v₀⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₀, one_pow]
  have hst_inner : ∀ x, ⟪v₀, st x⟫_ℝ = 0 := fun x => by
    dsimp [st]
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, hvv, mul_one,
      sub_self, mul_zero]
  have hpos : ∀ {x : E}, ‖x‖ = 1 → x ≠ v₀ → 0 < 1 - ⟪v₀, x⟫_ℝ := by
    intro x hx hne
    have hnorm : 0 < ‖x - v₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have hexp : ‖x - v₀‖ ^ 2 = 2 - 2 * ⟪v₀, x⟫_ℝ := by
      rw [norm_sub_sq_real, hx, hv₀, real_inner_comm]
      ring
    linarith
  have hnormInv : ∀ {y : E}, ⟪v₀, y⟫_ℝ = 0 → ‖stInv y‖ = 1 := by
    intro y hy
    have hdenom : 0 < ‖y‖ ^ 2 + 1 := by positivity
    have hnum_sq : ‖(2 : ℝ) • y + (‖y‖ ^ 2 - 1) • v₀‖ ^ 2 = (‖y‖ ^ 2 + 1) ^ 2 := by
      rw [norm_add_sq_real, norm_smul, Real.norm_of_nonneg zero_le_two, norm_smul, Real.norm_eq_abs,
        hv₀, mul_one, sq_abs, real_inner_smul_left, real_inner_smul_right, real_inner_comm v₀ y, hy]
      ring
    have hnum : ‖(2 : ℝ) • y + (‖y‖ ^ 2 - 1) • v₀‖ = ‖y‖ ^ 2 + 1 := by
      rw [← Real.sqrt_sq (norm_nonneg _), hnum_sq, Real.sqrt_sq hdenom.le]
    rw [show stInv y = (‖y‖ ^ 2 + 1)⁻¹ • ((2 : ℝ) • y + (‖y‖ ^ 2 - 1) • v₀) from rfl,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hdenom.le), hnum, inv_mul_cancel₀ hdenom.ne']
  have hcomp : ∀ {x : E}, ‖x‖ = 1 → x ≠ v₀ → stInv (st x) = x := by
    intro x hx hne
    set c : ℝ := ⟪v₀, x⟫_ℝ
    have hc : 0 < 1 - c := hpos hx hne
    have hcx : ⟪x, v₀⟫_ℝ = c := real_inner_comm v₀ x
    have hu_sq : ‖x - c • v₀‖ ^ 2 = 1 - c ^ 2 := by
      rw [norm_sub_sq_real, hx, norm_smul, Real.norm_eq_abs, hv₀, mul_one, sq_abs,
        real_inner_smul_right, hcx]
      ring
    have hst_sq : ‖st x‖ ^ 2 = (1 + c) / (1 - c) := by
      rw [show st x = (1 - c)⁻¹ • (x - c • v₀) from rfl, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), mul_pow, hu_sq]
      field_simp [hc.ne']
      ring
    have hden_ne : ‖st x‖ ^ 2 + 1 ≠ 0 := by positivity
    have hcoeff1 : (‖st x‖ ^ 2 + 1)⁻¹ * (2 * (1 - c)⁻¹) = 1 := by
      rw [hst_sq]; field_simp [hc.ne']; ring
    have hcoeff2 : (‖st x‖ ^ 2 + 1)⁻¹ * (2 * (1 - c)⁻¹ * (-c) + (‖st x‖ ^ 2 - 1)) = 0 := by
      rw [hst_sq]; field_simp [hc.ne']; ring
    calc
      stInv (st x)
        = (‖st x‖ ^ 2 + 1)⁻¹ • ((2 : ℝ) • ((1 - c)⁻¹ • (x - c • v₀)) + (‖st x‖ ^ 2 - 1) • v₀) := rfl
      _ = ((‖st x‖ ^ 2 + 1)⁻¹ * (2 * (1 - c)⁻¹)) • x +
            ((‖st x‖ ^ 2 + 1)⁻¹ * (2 * (1 - c)⁻¹ * (-c) + (‖st x‖ ^ 2 - 1))) • v₀ := by
          module
      _ = x := by rw [hcoeff1, hcoeff2, one_smul, zero_smul, add_zero]
  exact ⟨hst_inner, hpos, hnormInv, hcomp⟩

private lemma exists_sphere_nullHomotopy {n : ℕ} (hn : 2 ≤ n)
    (p : Path (⟨e0 n, mem_sphere_zero_iff_norm.mpr (norm_e0 n)⟩ :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      ⟨e0 n, mem_sphere_zero_iff_norm.mpr (norm_e0 n)⟩) :
    Path.Homotopic p
      (Path.refl (⟨e0 n, mem_sphere_zero_iff_norm.mpr (norm_e0 n)⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let S := Metric.sphere (0 : E) 1
  let s₀ : S := ⟨e0 n, mem_sphere_zero_iff_norm.mpr (norm_e0 n)⟩
  let pFun : I → E := fun t => (p t).1
  have hpFun_cont : Continuous pFun := continuous_subtype_val.comp p.continuous
  have hpFun_uc : UniformContinuous pFun := CompactSpace.uniformContinuous_of_continuous hpFun_cont
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hpFun_uc 1 zero_lt_one
  obtain ⟨mN, hmN⟩ := exists_nat_one_div_lt hδ0
  let N : ℕ := mN + 1
  have hNpos : 0 < N := Nat.succ_pos mN
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have h1divN : (1 : ℝ) / N < δ := by simpa [N] using hmN
  let pt : ℕ → E := fun k => pFun (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N))
  have hpt0 : pt 0 = e0 n := by
    have h0 : Set.projIcc 0 1 zero_le_one ((0 : ℝ) / N) = 0 := Subtype.ext (by simp)
    change pFun (Set.projIcc 0 1 zero_le_one (((0 : ℕ) : ℝ) / N)) = e0 n
    rw [Nat.cast_zero, h0]
    exact congrArg Subtype.val p.source
  have hptN : pt N = e0 n := by
    have h1 : Set.projIcc 0 1 zero_le_one ((N : ℝ) / N) = 1 :=
      Subtype.ext (by rw [div_self hNposR.ne']; simp)
    change pFun (Set.projIcc 0 1 zero_le_one ((N : ℝ) / N)) = e0 n
    rw [h1]
    exact congrArg Subtype.val p.target
  have hpt_norm : ∀ k, ‖pt k‖ = 1 := fun k => mem_sphere_zero_iff_norm.mp (p _).2
  let qReal : ℝ → E := fun t =>
    pt 0 + ∑ k : Fin N, max 0 (min 1 ((N : ℝ) * t - (k.1 : ℝ))) • (pt (k.1 + 1) - pt k.1)
  have hqReal_cont : Continuous qReal := by
    dsimp only [qReal]
    fun_prop
  have hqReal0 : qReal 0 = e0 n := by
    have hsum0 : ∑ k : Fin N, max 0 (min 1 ((N : ℝ) * 0 - (k.1 : ℝ))) •
        (pt (k.1 + 1) - pt k.1) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hneg : (N : ℝ) * 0 - (k.1 : ℝ) ≤ 0 := by simp
      have hmin : min 1 ((N : ℝ) * 0 - (k.1 : ℝ)) ≤ 0 := min_le_of_right_le hneg
      rw [max_eq_left hmin, zero_smul]
    simp [qReal, hsum0, hpt0]
  have hqReal1 : qReal 1 = e0 n := by
    have hsum1 : ∑ k : Fin N, max 0 (min 1 ((N : ℝ) * 1 - (k.1 : ℝ))) •
        (pt (k.1 + 1) - pt k.1) = pt N - pt 0 := by
      have hterm : ∀ k : Fin N,
          max 0 (min 1 ((N : ℝ) * 1 - (k.1 : ℝ))) • (pt (k.1 + 1) - pt k.1) =
            pt (k.1 + 1) - pt k.1 := fun k => by
        have hge : 1 ≤ (N : ℝ) * 1 - (k.1 : ℝ) := by
          have hk : (k.1 + 1 : ℕ) ≤ N := k.2
          have hk' : (k.1 : ℝ) + 1 ≤ N := by exact_mod_cast hk
          linarith
        rw [min_eq_left hge, max_eq_right zero_le_one, one_smul]
      simp_rw [hterm]
      rw [Fin.sum_univ_eq_sum_range (fun k => pt (k + 1) - pt k) N, Finset.sum_range_sub pt N]
    dsimp only [qReal]
    rw [hsum1, add_sub_cancel, hptN]
  have hqReal_bin : ∀ (m : Fin N) (t : ℝ),
      (m.1 : ℝ) / N ≤ t → t ≤ (m.1 + 1 : ℝ) / N →
        qReal t = (1 - ((N : ℝ) * t - m.1)) • pt m.1 + ((N : ℝ) * t - m.1) • pt (m.1 + 1) := by
    intro m t ht0 ht1
    let g : ℕ → E := fun k => max 0 (min 1 ((N : ℝ) * t - (k : ℝ))) • (pt (k + 1) - pt k)
    have hsplit : ∑ k : Fin N, g k =
        (∑ k ∈ Finset.range m.1, g k) + g m.1 + ∑ k ∈ Finset.Ico (m.1 + 1) N, g k := by
      rw [Fin.sum_univ_eq_sum_range g N]
      have hmle : m.1 ≤ N := m.2.le
      rw [← Finset.sum_range_add_sum_Ico g hmle, Finset.sum_eq_sum_Ico_succ_bot m.2]
      abel
    have hlow : ∑ k ∈ Finset.range m.1, g k = pt m.1 - pt 0 := by
      have hterm : ∀ k ∈ Finset.range m.1, g k = pt (k + 1) - pt k := by
        intro k hk
        have hkm : k + 1 ≤ m.1 := Finset.mem_range.mp hk
        have hkmR : (k : ℝ) + 1 ≤ m.1 := by exact_mod_cast hkm
        have hge : 1 ≤ (N : ℝ) * t - k := by
          have : (m.1 : ℝ) ≤ (N : ℝ) * t := (div_le_iff₀' hNposR).mp ht0
          linarith
        simp [g, min_eq_left hge]
      rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub pt m.1]
    have hhigh : ∑ k ∈ Finset.Ico (m.1 + 1) N, g k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hmk : m.1 + 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hmkR : (m.1 : ℝ) + 1 ≤ k := by exact_mod_cast hmk
      have hle : (N : ℝ) * t - k ≤ 0 := by
        have : (N : ℝ) * t ≤ m.1 + 1 := (le_div_iff₀' hNposR).mp ht1
        linarith
      have hmin : min 1 ((N : ℝ) * t - k) ≤ 0 := min_le_of_right_le hle
      simp [g, max_eq_left hmin]
    have hmid : g m.1 = ((N : ℝ) * t - m.1) • (pt (m.1 + 1) - pt m.1) := by
      have h0 : 0 ≤ (N : ℝ) * t - m.1 := sub_nonneg.mpr ((div_le_iff₀' hNposR).mp ht0)
      have h1 : (N : ℝ) * t - m.1 ≤ 1 := by
        have : (N : ℝ) * t ≤ m.1 + 1 := (le_div_iff₀' hNposR).mp ht1
        linarith
      simp [g, min_eq_right h1, max_eq_right h0]
    dsimp only [qReal]
    change pt 0 + ∑ k : Fin N, g k = _
    rw [hsplit, hlow, hhigh, add_zero, hmid]
    module
  have hex_bin : ∀ t : I, ∃ m : Fin N, (m.1 : ℝ) / N ≤ t ∧ (t : ℝ) ≤ (m.1 + 1 : ℝ) / N := by
    intro t
    by_cases ht1 : (t : ℝ) = 1
    · refine ⟨⟨N - 1, Nat.sub_lt hNpos zero_lt_one⟩, ?_, ?_⟩
      · rw [ht1, div_le_one hNposR]
        exact_mod_cast Nat.sub_le N 1
      · rw [ht1, le_div_iff₀' hNposR]
        change (N : ℝ) * 1 ≤ ((N - 1 : ℕ) : ℝ) + 1
        have hNnat : N = (N - 1) + 1 := (Nat.sub_add_cancel hNpos).symm
        have hNR : (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hNnat
        linarith
    · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
      have hNt_nonneg : 0 ≤ (N : ℝ) * t := mul_nonneg hNposR.le t.2.1
      have hNt_lt : (N : ℝ) * t < N := by nlinarith
      let mnat := Nat.floor ((N : ℝ) * t)
      have hm_lt : mnat < N := (Nat.floor_lt hNt_nonneg).mpr hNt_lt
      refine ⟨⟨mnat, hm_lt⟩, ?_, ?_⟩
      · exact (div_le_iff₀' hNposR).mpr (Nat.floor_le hNt_nonneg)
      · exact (le_div_iff₀' hNposR).mpr (Nat.lt_floor_add_one ((N : ℝ) * t)).le
  have hbin_dist : ∀ (m : Fin N) (t : I),
      (m.1 : ℝ) / N ≤ t → (t : ℝ) ≤ (m.1 + 1 : ℝ) / N →
        ‖pFun t - pt m.1‖ < 1 ∧ ‖pt (m.1 + 1) - pt m.1‖ < 1 := by
    intro m t ht0 ht1
    have hm_mem : (m.1 : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (Nat.cast_nonneg _) hNposR.le, (div_le_one hNposR).mpr ?_⟩
      exact_mod_cast m.2.le
    have hm1_mem : ((m.1 + 1 : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (Nat.cast_nonneg _) hNposR.le, (div_le_one hNposR).mpr ?_⟩
      exact_mod_cast m.2
    let tm : I := ⟨(m.1 : ℝ) / N, hm_mem⟩
    let tm1 : I := ⟨((m.1 + 1 : ℕ) : ℝ) / N, hm1_mem⟩
    have hptm : pt m.1 = pFun tm := by
      simp [pt, tm, Set.projIcc_of_mem zero_le_one hm_mem]
    have hptm1 : pt (m.1 + 1) = pFun tm1 := by
      have hc : (((m.1 + 1 : ℕ) : ℝ) / N) = ((m.1 : ℝ) + 1) / N := by push_cast; rfl
      simp [pt, tm1, ← hc, Set.projIcc_of_mem zero_le_one hm1_mem]
    have hd1 : dist t tm < δ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      have hsub : |(t : ℝ) - (m.1 : ℝ) / N| ≤ 1 / N := by
        rw [abs_of_nonneg (sub_nonneg.mpr ht0)]
        have : ((m.1 : ℝ) + 1) / N - (m.1 : ℝ) / N = 1 / N := by ring
        linarith
      exact lt_of_le_of_lt hsub h1divN
    have hd2 : dist tm1 tm < δ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      have hsub : |(((m.1 + 1 : ℕ) : ℝ) / N) - (m.1 : ℝ) / N| = 1 / N := by
        have hc : (((m.1 + 1 : ℕ) : ℝ) / N) - (m.1 : ℝ) / N = 1 / N := by push_cast; ring
        rw [hc, abs_of_nonneg (div_nonneg zero_le_one hNposR.le)]
      exact hsub ▸ h1divN
    exact ⟨by rw [hptm]; exact hδ hd1, by rw [hptm1, hptm]; exact hδ hd2⟩
  have hchord_lt_one : ∀ s t : I, ∃ m : Fin N,
      (m.1 : ℝ) / N ≤ t ∧ (t : ℝ) ≤ (m.1 + 1 : ℝ) / N ∧
      ‖((1 - (s : ℝ)) • pFun t + (s : ℝ) • qReal t) - pt m.1‖ < 1 := by
    intro s t
    obtain ⟨m, ht0, ht1⟩ := hex_bin t
    refine ⟨m, ht0, ht1, ?_⟩
    obtain ⟨hp_lt, hpt_lt⟩ := hbin_dist m t ht0 ht1
    set α : ℝ := (N : ℝ) * t - m.1
    have hα0 : 0 ≤ α := sub_nonneg.mpr ((div_le_iff₀' hNposR).mp ht0)
    have hα1 : α ≤ 1 := by
      have : (N : ℝ) * t ≤ m.1 + 1 := (le_div_iff₀' hNposR).mp ht1
      linarith [show α = (N : ℝ) * t - m.1 from rfl]
    have hq_diff : ‖qReal t - pt m.1‖ < 1 := by
      rw [hqReal_bin m t ht0 ht1]
      have hsub : (1 - α) • pt m.1 + α • pt (m.1 + 1) - pt m.1 = α • (pt (m.1 + 1) - pt m.1) := by
        module
      rw [hsub, norm_smul, Real.norm_of_nonneg hα0]
      calc α * ‖pt (m.1 + 1) - pt m.1‖
          ≤ 1 * ‖pt (m.1 + 1) - pt m.1‖ := mul_le_mul_of_nonneg_right hα1 (norm_nonneg _)
        _ = ‖pt (m.1 + 1) - pt m.1‖ := one_mul _
        _ < 1 := hpt_lt
    have hsplit : ((1 - (s : ℝ)) • pFun t + (s : ℝ) • qReal t) - pt m.1 =
        (1 - (s : ℝ)) • (pFun t - pt m.1) + (s : ℝ) • (qReal t - pt m.1) := by
      module
    rw [hsplit]
    calc ‖(1 - (s : ℝ)) • (pFun t - pt m.1) + (s : ℝ) • (qReal t - pt m.1)‖
        ≤ ‖(1 - (s : ℝ)) • (pFun t - pt m.1)‖ + ‖(s : ℝ) • (qReal t - pt m.1)‖ := norm_add_le _ _
      _ = (1 - (s : ℝ)) * ‖pFun t - pt m.1‖ + (s : ℝ) * ‖qReal t - pt m.1‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr s.2.2),
            Real.norm_of_nonneg s.2.1]
      _ < 1 := convex_lt_one s.2.1 s.2.2 hp_lt hq_diff
  have hchord_ne : ∀ s t : I, (1 - (s : ℝ)) • pFun t + (s : ℝ) • qReal t ≠ 0 := by
    intro s t
    obtain ⟨m, _, _, hlt⟩ := hchord_lt_one s t
    exact neg_norm_sub_eq_norm_sub (hpt_norm m.1) hlt
  have hqReal_ne : ∀ t : I, qReal t ≠ 0 := by
    intro t
    have h := hchord_ne 1 t
    simpa using h
  let qBarFun : I → S := fun t => ⟨‖qReal t‖⁻¹ • qReal t, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hqReal_ne t))]⟩
  let qBar : Path s₀ s₀ :=
    { toFun := qBarFun
      continuous_toFun := Continuous.subtype_mk
        ((Continuous.inv₀ (hqReal_cont.comp continuous_subtype_val).norm
          (fun t => norm_ne_zero_iff.mpr (hqReal_ne t))).smul
          (hqReal_cont.comp continuous_subtype_val)) _
      source' := by
        apply Subtype.ext
        change ‖qReal 0‖⁻¹ • qReal 0 = e0 n
        rw [hqReal0, norm_e0, inv_one, one_smul]
      target' := by
        apply Subtype.ext
        change ‖qReal 1‖⁻¹ • qReal 1 = e0 n
        rw [hqReal1, norm_e0, inv_one, one_smul] }
  let H1Fun : I × I → S := fun ⟨s, t⟩ =>
    let v := (1 - (s : ℝ)) • pFun t + (s : ℝ) • qReal t
    ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hchord_ne s t))]⟩
  have H1_cont : Continuous H1Fun := by
    let vFun : I × I → E := fun q => (1 - (q.1 : ℝ)) • pFun q.2 + (q.1 : ℝ) • qReal q.2
    have hvFun_cont : Continuous vFun := by
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (hpFun_cont.comp continuous_snd)
      · exact (continuous_subtype_val.comp continuous_fst).smul
          (hqReal_cont.comp (continuous_subtype_val.comp continuous_snd))
    refine Continuous.subtype_mk ?_ _
    exact (Continuous.inv₀ hvFun_cont.norm (fun q => norm_ne_zero_iff.mpr (hchord_ne q.1 q.2))).smul
      hvFun_cont
  have H1 : p.Homotopy qBar :=
    { toFun := H1Fun
      continuous_toFun := H1_cont
      map_zero_left := fun t => by
        apply Subtype.ext
        have hn1 : ‖pFun t‖ = 1 := mem_sphere_zero_iff_norm.mp (p t).2
        simp [H1Fun, hn1, pFun]
      map_one_left := fun t => by apply Subtype.ext; simp [H1Fun, qBar, qBarFun]
      prop' := fun s t ht => by
        rcases ht with rfl | rfl
        · apply Subtype.ext
          have hp0 : pFun 0 = e0 n := congrArg Subtype.val p.source
          have hv : (1 - (s : ℝ)) • pFun 0 + (s : ℝ) • qReal 0 = e0 n := by
            rw [hp0, hqReal0]; module
          change ‖(1 - (s : ℝ)) • pFun 0 + (s : ℝ) • qReal 0‖⁻¹ •
            ((1 - (s : ℝ)) • pFun 0 + (s : ℝ) • qReal 0) = pFun 0
          rw [hv, norm_e0, inv_one, one_smul, hp0]
        · apply Subtype.ext
          have hp1 : pFun 1 = e0 n := congrArg Subtype.val p.target
          have hv : (1 - (s : ℝ)) • pFun 1 + (s : ℝ) • qReal 1 = e0 n := by
            rw [hp1, hqReal1]; module
          change ‖(1 - (s : ℝ)) • pFun 1 + (s : ℝ) • qReal 1‖⁻¹ •
            ((1 - (s : ℝ)) • pFun 1 + (s : ℝ) • qReal 1) = pFun 1
          rw [hv, norm_e0, inv_one, one_smul, hp1] }
  -- Step 3b: omit `v₀` and stereographically contract `qBar` to `Path.refl s₀`
  let badW : Fin (N + 1) → Submodule ℝ E := fun k =>
    if hk : k.1 < N then Submodule.span ℝ ({pt k.1, pt (k.1 + 1)} : Set E) else ℝ ∙ e0 n
  have hE_dim : Module.finrank ℝ E = n + 1 := finrank_euclideanSpace_fin
  have hbad_proper : ∀ k ∈ (Finset.univ : Finset (Fin (N + 1))), badW k ≠ ⊤ := by
    intro k _ htop
    by_cases hk : k.1 < N
    · have h1 : badW k = Submodule.span ℝ ({pt k.1, pt (k.1 + 1)} : Set E) := by simp [badW, hk]
      have hcard := finrank_span_le_card (R := ℝ) ({pt k.1, pt (k.1 + 1)} : Set E)
      have htwo : ({pt k.1, pt (k.1 + 1)} : Set E).toFinset.card ≤ 2 := by
        simpa using Finset.card_le_two (a := pt k.1) (b := pt (k.1 + 1))
      rw [← h1, htop, finrank_top, hE_dim] at hcard
      omega
    · have h1 : badW k = ℝ ∙ e0 n := by simp [badW, hk]
      have hle : Module.finrank ℝ ↥(ℝ ∙ e0 n) ≤ 1 := by
        rw [finrank_span_singleton (by
          intro h0; have := norm_e0 n; rw [h0, norm_zero] at this; linarith)]
      rw [← h1, htop, finrank_top, hE_dim] at hle
      omega
  obtain ⟨v₀, hv₀_avoid⟩ := exists_unit_notMem_biUnion_proper_subspaces
    (by rw [hE_dim]; omega) Finset.univ badW hbad_proper
  have hv₀_norm : ‖v₀.1‖ = 1 := mem_sphere_zero_iff_norm.mp v₀.2
  have hv₀_e0 : e0 n ≠ v₀.1 := by
    intro heq
    apply hv₀_avoid ⟨N, Nat.lt_succ_self N⟩ (Finset.mem_univ _)
    simp only [badW, lt_irrefl, ↓reduceDIte]
    rw [← heq]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hv₀_qBar : ∀ t : I, (qBar t).1 ≠ v₀.1 := by
    intro t heq
    obtain ⟨m, ht0, ht1⟩ := hex_bin t
    let m' : Fin (N + 1) := ⟨m.1, Nat.lt_succ_of_lt m.2⟩
    apply hv₀_avoid m' (Finset.mem_univ _)
    have hm_lt : m'.1 < N := m.2
    simp only [badW, m', hm_lt, ↓reduceDIte]
    rw [← heq]
    refine Submodule.smul_mem _ _ ?_
    change qReal t ∈ Submodule.span ℝ ({pt m.1, pt (m.1 + 1)} : Set E)
    rw [hqReal_bin m t ht0 ht1]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  let st : E → E := fun x => (1 - ⟪v₀.1, x⟫_ℝ)⁻¹ • (x - ⟪v₀.1, x⟫_ℝ • v₀.1)
  let stInv : E → E := fun y => (‖y‖ ^ 2 + 1)⁻¹ • ((2 : ℝ) • y + (‖y‖ ^ 2 - 1) • v₀.1)
  obtain ⟨_hst_inner, hpos_st, hnormInv, hcomp_st⟩ := st_formula_properties hv₀_norm
  let Y : I × I → E := fun q => (1 - (q.1 : ℝ)) • st (qBar q.2).1 + (q.1 : ℝ) • st (e0 n)
  have hvv₀ : ⟪v₀.1, v₀.1⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₀_norm, one_pow]
  have hY_inner : ∀ q : I × I, ⟪v₀.1, Y q⟫_ℝ = 0 := fun q => by
    simp only [Y, st, inner_add_right, real_inner_smul_right, inner_sub_right, hvv₀, mul_one,
      sub_self, mul_zero, add_zero]
  have hst_qBar_cont : Continuous (fun t : I => st (qBar t).1) := by
    have hinner : Continuous (fun t : I => ⟪v₀.1, (qBar t).1⟫_ℝ) :=
      Continuous.inner (continuous_const (y := v₀.1)) (continuous_subtype_val.comp qBar.continuous)
    have hden : Continuous (fun t : I => (1 - ⟪v₀.1, (qBar t).1⟫_ℝ)⁻¹) :=
      Continuous.inv₀ (continuous_const.sub hinner)
        (fun t => (hpos_st (mem_sphere_zero_iff_norm.mp (qBar t).2) (hv₀_qBar t)).ne')
    have hnum : Continuous (fun t : I => (qBar t).1 - ⟪v₀.1, (qBar t).1⟫_ℝ • v₀.1) :=
      (continuous_subtype_val.comp qBar.continuous).sub (hinner.smul (continuous_const (y := v₀.1)))
    exact hden.smul hnum
  have hY_cont : Continuous Y := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (hst_qBar_cont.comp continuous_snd)
    · exact (continuous_subtype_val.comp continuous_fst).smul continuous_const
  have hstInv_cont : Continuous stInv := by
    have h1 : Continuous (fun y : E => (‖y‖ ^ 2 + 1)⁻¹) :=
      Continuous.inv₀ ((continuous_norm.pow 2).add continuous_const) (fun y => by positivity)
    have h2 : Continuous (fun y : E => (2 : ℝ) • y + (‖y‖ ^ 2 - 1) • v₀.1) :=
      (continuous_const_smul (2 : ℝ)).add (((continuous_norm.pow 2).sub continuous_const).smul continuous_const)
    exact h1.smul h2
  let H2 : qBar.Homotopy (Path.refl s₀) :=
    { toFun := fun q => ⟨stInv (Y q), mem_sphere_zero_iff_norm.mpr (hnormInv (hY_inner q))⟩
      continuous_toFun := Continuous.subtype_mk (hstInv_cont.comp hY_cont) _
      map_zero_left := fun t => by
        apply Subtype.ext
        have hY0 : Y (0, t) = st (qBar t).1 := by simp [Y]
        change stInv (Y (0, t)) = (qBar t).1
        rw [hY0]
        exact hcomp_st (mem_sphere_zero_iff_norm.mp (qBar t).2) (hv₀_qBar t)
      map_one_left := fun t => by
        apply Subtype.ext
        have hY1 : Y (1, t) = st (e0 n) := by simp [Y]
        change stInv (Y (1, t)) = s₀.1
        rw [hY1]
        exact hcomp_st (norm_e0 n) hv₀_e0
      prop' := fun s t ht => by
        rcases ht with rfl | rfl
        · apply Subtype.ext
          have hqb0 : (qBar 0).1 = e0 n := by simp [qBar.source, s₀]
          have hYs : Y (s, 0) = st (e0 n) := by
            simp only [Y, hqb0]
            module
          change stInv (Y (s, 0)) = (qBar 0).1
          rw [hYs, hqb0]
          exact hcomp_st (norm_e0 n) hv₀_e0
        · apply Subtype.ext
          have hqb1 : (qBar 1).1 = e0 n := by simp [qBar.target, s₀]
          have hYs : Y (s, 1) = st (e0 n) := by
            simp only [Y, hqb1]
            module
          change stInv (Y (s, 1)) = (qBar 1).1
          rw [hYs, hqb1]
          exact hcomp_st (norm_e0 n) hv₀_e0 }
  exact ⟨H1.trans H2⟩

private def liftProdStep {n : ℕ}
    (G : I × I → EuclideanSpace ℝ (Fin (n + 1))) (τ : ℕ → I → I)
    (γ : BasedLoop (n + 1))
    (hG_ne0 : ∀ q : I × I, G q ≠ 0)
    (hG_step_sum : ∀ k (s t : I), G (τ k s, t) + G (τ (k + 1) s, t) ≠ 0) :
    ℕ → I × I → SO (n + 1)
  | 0, q => γ q.2
  | k + 1, q =>
    ⟨transportMatrix (G (τ k q.1, q.2)) (G (τ (k + 1) q.1, q.2)),
      transportMatrix_mem_SO (hG_ne0 _) (hG_step_sum k q.1 q.2)⟩ *
      liftProdStep G τ γ hG_ne0 hG_step_sum k q

theorem exists_basedLoop_reduction_SO (n : ℕ) (hn : 2 ≤ n) (γ : BasedLoop (n + 1)) :
    ∃ δ : BasedLoop n, BasedLoopHomotopic γ (mapLoop n δ) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let S := Metric.sphere (0 : E) 1
  let s₀ : S := ⟨e0 n, mem_sphere_zero_iff_norm.mpr (norm_e0 n)⟩
  let p : Path s₀ s₀ :=
    { toFun := fun t => ⟨col0 (γ t), mem_sphere_zero_iff_norm.mpr (norm_col0 (γ t))⟩
      continuous_toFun := Continuous.subtype_mk ((continuous_col0 n).comp γ.continuous) _
      source' := by ext; simp [s₀, γ.source, col0_one]
      target' := by ext; simp [s₀, γ.target, col0_one] }
  obtain ⟨G⟩ := exists_sphere_nullHomotopy hn p
  have hG_uc : UniformContinuous (fun q : I × I => (G q).1) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_subtype_val.comp G.continuous)
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.uniformContinuous_iff.mp hG_uc 2 zero_lt_two
  obtain ⟨mM, hmM⟩ := exists_nat_one_div_lt hδ₂_pos
  let M : ℕ := mM + 1
  have hMpos : 0 < M := Nat.succ_pos mM
  have hMposR : (0 : ℝ) < M := Nat.cast_pos.mpr hMpos
  have h1divM : (1 : ℝ) / M < δ₂ := by simpa [M] using hmM
  let τ : ℕ → I → I := fun k s =>
    ⟨min (s : ℝ) (min 1 ((k : ℝ) / M)), by
      constructor
      · exact le_min s.2.1 (le_min zero_le_one (div_nonneg (Nat.cast_nonneg k) hMposR.le))
      · exact min_le_of_left_le s.2.2⟩
  have hτ_cont : ∀ k, Continuous (τ k) := fun k =>
    Continuous.subtype_mk ((continuous_subtype_val).min continuous_const) _
  have hτ_zero : ∀ k, τ k 0 = 0 := fun k => by
    ext
    have h0 : (0 : ℝ) ≤ min 1 ((k : ℝ) / M) :=
      le_min zero_le_one (div_nonneg (Nat.cast_nonneg k) hMposR.le)
    simp [τ, min_eq_left h0]
  have hτ0 : ∀ s, τ 0 s = 0 := fun s => by
    ext
    simp [τ, min_eq_right s.2.1]
  have hτM : ∀ s, τ M s = s := fun s => by
    ext
    simp [τ, hMposR.ne', min_eq_left s.2.2]
  have hτ_step : ∀ k (s : I), dist (τ k s) (τ (k + 1) s) < δ₂ := by
    intro k s
    rw [Subtype.dist_eq, Real.dist_eq]
    have hk : (k : ℝ) / M ≤ ((k + 1 : ℕ) : ℝ) / M := by
      gcongr; simp
    have hmin_le : min (s : ℝ) (min 1 ((k : ℝ) / M)) ≤ min (s : ℝ) (min 1 (((k + 1 : ℕ) : ℝ) / M)) :=
      min_le_min_left _ (min_le_min_left _ hk)
    have hdiff_le : min (s : ℝ) (min 1 (((k + 1 : ℕ) : ℝ) / M)) - min (s : ℝ) (min 1 ((k : ℝ) / M)) ≤
        1 / M := by
      have hinc : min 1 (((k + 1 : ℕ) : ℝ) / M) - min 1 ((k : ℝ) / M) ≤ 1 / M := by
        have hstep : (((k + 1 : ℕ) : ℝ) / M) - (k : ℝ) / M = 1 / M := by push_cast; ring
        rcases le_total 1 (((k + 1 : ℕ) : ℝ) / M) with h1 | h1 <;>
          rcases le_total 1 ((k : ℝ) / M) with h2 | h2
        · rw [min_eq_left h1, min_eq_left h2, sub_self]
          exact div_nonneg zero_le_one hMposR.le
        · rw [min_eq_left h1, min_eq_right h2]
          linarith
        · exfalso; linarith [hstep, div_pos zero_lt_one hMposR]
        · rw [min_eq_right h1, min_eq_right h2, hstep]
      have hmin_inc : min 1 ((k : ℝ) / M) ≤ min 1 (((k + 1 : ℕ) : ℝ) / M) :=
        min_le_min_left 1 hk
      rcases le_total (s : ℝ) (min 1 ((k : ℝ) / M)) with hs1 | hs1 <;>
        rcases le_total (s : ℝ) (min 1 (((k + 1 : ℕ) : ℝ) / M)) with hs2 | hs2
      · rw [min_eq_left hs1, min_eq_left hs2, sub_self]
        exact div_nonneg zero_le_one hMposR.le
      · rw [min_eq_left hs1, min_eq_right hs2]
        linarith [hmin_inc, div_nonneg zero_le_one hMposR.le]
      · rw [min_eq_right hs1, min_eq_left hs2]
        linarith [hmin_inc]
      · rw [min_eq_right hs1, min_eq_right hs2]
        exact hinc
    have habs : |(τ k s : ℝ) - (τ (k + 1) s : ℝ)| ≤ 1 / M := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hmin_le)]
      exact hdiff_le
    exact lt_of_le_of_lt habs h1divM
  have hG_ne0 : ∀ q : I × I, (G q).1 ≠ 0 := fun q h0 => by
    have := mem_sphere_zero_iff_norm.mp (G q).2
    rw [h0, norm_zero] at this
    linarith
  have hG_step_sum : ∀ k (s t : I), (G (τ k s, t)).1 + (G (τ (k + 1) s, t)).1 ≠ 0 := by
    intro k s t
    have hd : dist (τ k s, t) (τ (k + 1) s, t) < δ₂ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hτ_step k s
    exact add_ne_zero_of_sphere_dist_lt_two
      (mem_sphere_zero_iff_norm.mp (G (τ k s, t)).2)
      (mem_sphere_zero_iff_norm.mp (G (τ (k + 1) s, t)).2)
      (hδ₂ hd)
  let liftProd := liftProdStep (fun q => (G q).1) τ γ hG_ne0 hG_step_sum
  have hcont_lift : ∀ k, Continuous (liftProd k) := by
    intro k
    induction k with
    | zero => exact γ.continuous.comp continuous_snd
    | succ k ih =>
      refine (continuous_mul_SO (n + 1)).comp (Continuous.prodMk ?_ ih)
      refine Continuous.subtype_mk ?_ _
      exact continuous_transportMatrix_comp
        (continuous_subtype_val.comp (G.continuous.comp ((hτ_cont k).prodMap continuous_id)))
        (continuous_subtype_val.comp (G.continuous.comp ((hτ_cont (k + 1)).prodMap continuous_id)))
        (fun q => hG_ne0 _) (fun q => hG_step_sum k q.1 q.2)
  have hzero_lift : ∀ k t, liftProd k (0, t) = γ t := by
    intro k t
    induction k with
    | zero => rfl
    | succ k ih =>
      change ⟨transportMatrix (G (τ k 0, t)).1 (G (τ (k + 1) 0, t)).1, _⟩ * liftProd k (0, t) = γ t
      have hT : (⟨transportMatrix (G (τ k 0, t)).1 (G (τ (k + 1) 0, t)).1,
          transportMatrix_mem_SO (hG_ne0 _) (hG_step_sum k 0 t)⟩ : SO (n + 1)) = 1 := by
        ext i j
        simp [hτ_zero k, hτ_zero (k + 1), transportMatrix_self]
      rw [hT, one_mul, ih]
  have hend_lift : ∀ k s, liftProd k (s, 0) = 1 ∧ liftProd k (s, 1) = 1 := by
    intro k s
    induction k with
    | zero => exact ⟨γ.source, γ.target⟩
    | succ k ih =>
      constructor
      · have h0a : (G (τ k s, 0)).1 = e0 n := by
          have := (G.prop' (τ k s) 0 (by simp)).trans p.source
          exact congrArg Subtype.val this
        have h0b : (G (τ (k + 1) s, 0)).1 = e0 n := by
          have := (G.prop' (τ (k + 1) s) 0 (by simp)).trans p.source
          exact congrArg Subtype.val this
        have hT : (⟨transportMatrix (G (τ k s, 0)).1 (G (τ (k + 1) s, 0)).1,
            transportMatrix_mem_SO (hG_ne0 _) (hG_step_sum k s 0)⟩ : SO (n + 1)) = 1 := by
          ext i j
          simp [h0a, h0b, transportMatrix_self]
        change _ * liftProd k (s, 0) = 1
        rw [hT, one_mul, ih.1]
      · have h1a : (G (τ k s, 1)).1 = e0 n := by
          have := (G.prop' (τ k s) 1 (by simp)).trans p.target
          exact congrArg Subtype.val this
        have h1b : (G (τ (k + 1) s, 1)).1 = e0 n := by
          have := (G.prop' (τ (k + 1) s) 1 (by simp)).trans p.target
          exact congrArg Subtype.val this
        have hT : (⟨transportMatrix (G (τ k s, 1)).1 (G (τ (k + 1) s, 1)).1,
            transportMatrix_mem_SO (hG_ne0 _) (hG_step_sum k s 1)⟩ : SO (n + 1)) = 1 := by
          ext i j
          simp [h1a, h1b, transportMatrix_self]
        change _ * liftProd k (s, 1) = 1
        rw [hT, one_mul, ih.2]
  have hcol_lift : ∀ k q, col0 (liftProd k q) = (G (τ k q.1, q.2)).1 := by
    intro k q
    induction k with
    | zero =>
      rw [hτ0 q.1]
      have hG0 := G.apply_zero q.2
      exact (congrArg (fun x : S => x.1) hG0).symm
    | succ k ih =>
      change col0 (⟨transportMatrix (G (τ k q.1, q.2)).1 (G (τ (k + 1) q.1, q.2)).1,
        transportMatrix_mem_SO (hG_ne0 _) (hG_step_sum k q.1 q.2)⟩ * liftProd k q) =
          (G (τ (k + 1) q.1, q.2)).1
      let u := (G (τ k q.1, q.2)).1
      let v := (G (τ (k + 1) q.1, q.2)).1
      have hmul : transportMatrix u v * (liftProd k q).1 ∈ SO (n + 1) :=
        Submonoid.mul_mem _ (transportMatrix_mem_SO (hG_ne0 _) (hG_step_sum k q.1 q.2))
          (liftProd k q).2
      have hcol := transportMatrix_mul_col0 u v (liftProd k q) hmul
      change col0 ⟨transportMatrix u v * (liftProd k q).1, hmul⟩ = v
      rw [hcol, ih]
      exact FrameTransport.transport_vector
        ((mem_sphere_zero_iff_norm.mp (G (τ k q.1, q.2)).2).trans
          (mem_sphere_zero_iff_norm.mp (G (τ (k + 1) q.1, q.2)).2).symm)
  have hcol_one : ∀ t, col0 (liftProd M (1, t)) = e0 n := fun t => by
    rw [hcol_lift M (1, t), hτM 1]
    exact congrArg (fun x : S => x.1) (G.apply_one t)
  let fEnd : I → SO (n + 1) := fun t => liftProd M (1, t)
  have hfEnd_cont : Continuous fEnd :=
    (hcont_lift M).comp (continuous_const.prodMk continuous_id)
  have hinj_embed : Function.Injective (embedSO n) := fun a b h => by
    ext i j
    exact congrArg (fun M : SO (n + 1) => M.1 i.succ j.succ) h
  let δ : BasedLoop n :=
    { toFun := fun t => extractSO (fEnd t) (hcol_one t)
      continuous_toFun := continuous_extractSO fEnd hfEnd_cont hcol_one
      source' := by
        apply hinj_embed
        rw [embedSO_extractSO, (embedSO n).map_one]
        exact (hend_lift M 1).1
      target' := by
        apply hinj_embed
        rw [embedSO_extractSO, (embedSO n).map_one]
        exact (hend_lift M 1).2 }
  refine ⟨δ, ⟨{
    toFun := liftProd M
    continuous_toFun := hcont_lift M
    map_zero_left := fun t => hzero_lift M t
    map_one_left := fun t => by
      change liftProd M (1, t) = mapLoop n δ t
      change liftProd M (1, t) = embedSO n (δ t)
      exact (embedSO_extractSO (fEnd t) (hcol_one t)).symm
    prop' := fun s t ht => by
      rcases ht with rfl | rfl
      · exact (hend_lift M s).1.trans γ.source.symm
      · exact (hend_lift M s).2.trans γ.target.symm
  }⟩⟩

end LoopReduction

/-! ### 4. The belt trick in `SO(3)` and stabilization to `SO(n)` (`3 ≤ n`) -/

section BeltTrick

def so2ToCircle : SO 2 →* Circle where
  toFun A := ⟨⟨A.1 0 0, A.1 1 0⟩, by
    have hM := A.2
    have hmat : A.1 = !![A.1 0 0, A.1 0 1; A.1 1 0, A.1 1 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hmat, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff] at hM
    rcases hM with ⟨_, h01, hsq⟩
    change (⟨A.1 0 0, A.1 1 0⟩ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, Complex.norm_def, Complex.normSq_mk]
    have hsq' : A.1 0 0 * A.1 0 0 + A.1 1 0 * A.1 1 0 = 1 := by
      rw [h01, neg_sq] at hsq
      simpa [sq] using hsq
    simp [hsq']⟩
  map_one' := by
    apply Subtype.ext
    apply Complex.ext <;> simp [Matrix.one_apply]
  map_mul' A B := by
    have hA := A.2
    have hmatA : A.1 = !![A.1 0 0, A.1 0 1; A.1 1 0, A.1 1 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hmatA, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff] at hA
    rcases hA with ⟨hA_diag, hA_off, _⟩
    apply Circle.ext
    change (⟨(A * B).1 0 0, (A * B).1 1 0⟩ : ℂ) =
      (⟨A.1 0 0, A.1 1 0⟩ : ℂ) * (⟨B.1 0 0, B.1 1 0⟩ : ℂ)
    apply Complex.ext
    · simp only [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
        Complex.mul_re, hA_off]
      ring
    · simp only [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
        Complex.mul_im, ← hA_diag]
      ring

@[simp] lemma so2ToCircle_re (A : SO 2) : ((so2ToCircle A : Circle) : ℂ).re = A.1 0 0 := rfl
@[simp] lemma so2ToCircle_im (A : SO 2) : ((so2ToCircle A : Circle) : ℂ).im = A.1 1 0 := rfl

def circleToSO2 : Circle →* SO 2 where
  toFun z := ⟨!![z.1.re, -z.1.im; z.1.im, z.1.re], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    have hns : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, sq] using Circle.normSq_coe z
    refine ⟨rfl, rfl, ?_⟩
    nlinarith [sq z.1.im]⟩
  map_one' := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  map_mul' z w := by
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Circle.coe_mul, Complex.mul_re,
        Complex.mul_im] <;> ring

lemma circleToSO2_so2ToCircle (A : SO 2) : circleToSO2 (so2ToCircle A) = A := by
  have hA := A.2
  have hmatA : A.1 = !![A.1 0 0, A.1 0 1; A.1 1 0, A.1 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hmatA, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff] at hA
  rcases hA with ⟨hdiag, hoff, _⟩
  apply Subtype.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [circleToSO2, so2ToCircle_re, so2ToCircle_im, hdiag, hoff]

lemma embedSO2_circleToSO2_sq (z : Circle) :
    (embedSO 2 (circleToSO2 (z ^ 2))).1 = QuaternionBelt.rotationHomotopy 0 z.1 := by
  have hz : Complex.normSq z.1 = 1 := Circle.normSq_coe z
  rw [QuaternionBelt.rotationHomotopy_zero hz]
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      fin_cases j <;> rfl
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      fin_cases i <;> rfl
    | succ j =>
      change (circleToSO2 (z ^ 2)).1 i j = _
      fin_cases i <;> fin_cases j <;>
        simp [circleToSO2, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

lemma continuous_so2ToCircle : Continuous so2ToCircle := by
  refine Continuous.subtype_mk ?_ _
  have heq : (fun A : SO 2 => ((so2ToCircle A : Circle) : ℂ)) =
      fun A => (A.1 0 0 : ℂ) + (A.1 1 0 : ℂ) * Complex.I := by
    funext A
    apply Complex.ext <;> simp [so2ToCircle_re, so2ToCircle_im]
  change Continuous (fun A : SO 2 => ((so2ToCircle A : Circle) : ℂ))
  rw [heq]
  exact (Complex.continuous_ofReal.comp (continuous_SO_entry 2 0 0)).add
    ((Complex.continuous_ofReal.comp (continuous_SO_entry 2 1 0)).mul continuous_const)

theorem basedLoop_double_nullHomotopic_SO3 (γ : BasedLoop 3) :
    BasedLoopHomotopic (γ.trans γ) (Path.refl 1) := by
  obtain ⟨δ, hδ⟩ := exists_basedLoop_reduction_SO 2 le_rfl γ
  let δ3 : BasedLoop 3 := mapLoop 2 δ
  have hcon : BasedLoopHomotopic (γ.trans γ) (loopMul δ3 δ3) :=
    (loopConcat_homotopic_loopMul γ γ).trans (basedLoopHomotopic_loopMul hδ hδ)
  let H : Path.Homotopy (loopMul δ3 δ3) (Path.refl 1) :=
    { toFun := fun q => ⟨QuaternionBelt.rotationHomotopy q.1.1 (so2ToCircle (δ q.2)).1,
        QuaternionBelt.rotationHomotopy_mem q.1.2.1 q.1.2.2
          (Circle.normSq_coe (so2ToCircle (δ q.2)))⟩
      continuous_toFun := by
        have harg : Continuous (fun q : I × I => (q.1.1, (so2ToCircle (δ q.2)).1)) :=
          (continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp (continuous_so2ToCircle.comp (δ.continuous.comp continuous_snd)))
        exact Continuous.subtype_mk (QuaternionBelt.continuous_rotationHomotopy.comp harg) _
      map_zero_left := fun t => by
        apply Subtype.ext
        have hloop : (loopMul δ3 δ3 t).1 =
            (embedSO 2 (circleToSO2 ((so2ToCircle (δ t)) ^ 2))).1 := by
          have h1 : δ t * δ t = circleToSO2 ((so2ToCircle (δ t)) ^ 2) := by
            rw [map_pow, circleToSO2_so2ToCircle, pow_two]
          change (embedSO 2 (δ t) * embedSO 2 (δ t)).1 = _
          rw [← (embedSO 2).map_mul, h1]
        change QuaternionBelt.rotationHomotopy 0 (so2ToCircle (δ t)).1 = (loopMul δ3 δ3 t).1
        rw [hloop, embedSO2_circleToSO2_sq]
      map_one_left := fun t => by
        apply Subtype.ext
        simp [QuaternionBelt.rotationHomotopy_one]
      prop' := fun s t ht => by
        rcases ht with rfl | rfl
        · apply Subtype.ext
          change QuaternionBelt.rotationHomotopy s.1 (so2ToCircle (δ 0)).1 = (loopMul δ3 δ3 0).1
          rw [δ.source, (so2ToCircle).map_one, (loopMul δ3 δ3).source]
          exact QuaternionBelt.rotationHomotopy_base s.2.1 s.2.2
        · apply Subtype.ext
          change QuaternionBelt.rotationHomotopy s.1 (so2ToCircle (δ 1)).1 = (loopMul δ3 δ3 1).1
          rw [δ.target, (so2ToCircle).map_one, (loopMul δ3 δ3).target]
          exact QuaternionBelt.rotationHomotopy_base s.2.1 s.2.2 }
  exact hcon.trans ⟨H⟩

theorem basedLoop_double_nullHomotopic_SO (n : ℕ) (hn : 3 ≤ n) (γ : BasedLoop n) :
    BasedLoopHomotopic (γ.trans γ) (Path.refl 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact basedLoop_double_nullHomotopic_SO3 γ
  | succ k hk ih =>
    obtain ⟨δ, hδ⟩ := exists_basedLoop_reduction_SO k (by omega) γ
    have hred : BasedLoopHomotopic (γ.trans γ) (mapLoop k (δ.trans δ)) := by
      have h1 : BasedLoopHomotopic (γ.trans γ) ((mapLoop k δ).trans (mapLoop k δ)) :=
        Path.Homotopic.hcomp hδ hδ
      have h2 : (mapLoop k δ).trans (mapLoop k δ) = mapLoop k (δ.trans δ) := by
        ext t
        simp [mapLoop, Path.trans_apply]
        all_goals try rfl
      exact h2 ▸ h1
    have ih' := Path.Homotopic.map (ih δ) ⟨embedSO k, continuous_embedSO k⟩
    have hmap : ((Path.refl (1 : SO k)).map (continuous_embedSO k)).cast
        (embedSO k).map_one.symm (embedSO k).map_one.symm = Path.refl (1 : SO (k + 1)) := by
      ext t
      simp [(embedSO k).map_one]
    have hred2 : BasedLoopHomotopic (mapLoop k (δ.trans δ)) (Path.refl 1) := by
      rw [← hmap]
      exact Path.Homotopic.pathCast ih' (embedSO k).map_one.symm (embedSO k).map_one.symm
    exact hred.trans hred2

theorem basedLoop_double_nullHomotopic_SO13 (γ : BasedLoop 13) :
    BasedLoopHomotopic (γ.trans γ) (Path.refl 1) :=
  basedLoop_double_nullHomotopic_SO 13 (by norm_num) γ

end BeltTrick

end AkopyanResearch
