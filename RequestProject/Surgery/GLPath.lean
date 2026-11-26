module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# Paths of invertible matrices

Two real square matrices whose determinants have the same (nonzero) sign can be joined by a path
of invertible matrices (`Surgery.joinedIn_gl_of_det_mul_pos`).

The proof uses the decomposition of a matrix into transvections and a diagonal matrix
(`Matrix.diagonal_transvection_induction_of_det_ne_zero`).
-/

open Matrix Pointwise

namespace Surgery

variable {k : ℕ}

/-- Invertible matrices. -/
def glSet (k : ℕ) : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := {M | M.det ≠ 0}

lemma glSet_mul_subset : glSet k * glSet k ⊆ glSet k := by
  rintro _ ⟨A, hA, B, hB, rfl⟩
  simp only [glSet, Set.mem_setOf_eq, det_mul] at hA hB ⊢
  exact mul_ne_zero hA hB

/-- The diagonal matrix `diag(-1, 1, …, 1)`. -/
noncomputable def negBase (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  diagonal (Function.update 1 0 (-1))

lemma det_update_one_neg (i : Fin (k + 1)) :
    (diagonal (Function.update (1 : Fin (k + 1) → ℝ) i (-1))).det = -1 := by
  rw [det_diagonal, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  rw [Finset.prod_eq_one]
  · ring
  · intro j hj
    rw [Finset.mem_erase] at hj
    simp [Function.update_of_ne hj.1]

lemma det_negBase : (negBase k).det = -1 := det_update_one_neg 0

lemma negBase_mul_self : negBase k * negBase k = 1 := by
  rw [negBase, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · simp [Function.update_of_ne hi]

/-- The base point of the component of `M`. -/
noncomputable def base (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  if 0 < M.det then 1 else negBase k

lemma base_mul {A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    base A * base B = base (A * B) := by
  unfold base
  rw [det_mul]
  rcases hA.lt_or_gt with hA | hA <;> rcases hB.lt_or_gt with hB | hB
  · simp [not_lt.2 hA.le, not_lt.2 hB.le, mul_pos_of_neg_of_neg hA hB, negBase_mul_self]
  · simp [not_lt.2 hA.le, hB, not_lt.2 (mul_neg_of_neg_of_pos hA hB).le]
  · simp [hA, not_lt.2 hB.le, not_lt.2 (mul_neg_of_pos_of_neg hA hB).le]
  · simp [hA, hB, mul_pos hA hB]

/-- The property proved by induction. -/
def Good (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Prop := JoinedIn (glSet k) M (base M)

lemma good_mul {A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (gA : Good A) (gB : Good B) : Good (A * B) := by
  unfold Good
  rw [← base_mul hA hB]
  exact (JoinedIn.mul gA gB).mono glSet_mul_subset

lemma good_one : Good (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := by
  have : base (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) = 1 := by simp [base]
  rw [Good, this]
  exact JoinedIn.refl (by simp [glSet])

lemma joinedIn_transvection (t : TransvectionStruct (Fin (k + 1)) ℝ) :
    JoinedIn (glSet k) t.toMatrix 1 := by
  refine JoinedIn.ofLine (f := fun s : ℝ => transvection t.i t.j ((1 - s) * t.c)) ?_ ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    unfold transvection
    refine continuous_const.add (continuous_pi fun a => continuous_pi fun b => ?_)
    simp only [Matrix.single_apply]
    split_ifs <;> fun_prop
  · simp [TransvectionStruct.toMatrix]
  · simp
  · rintro _ ⟨s, _, rfl⟩
    simp [glSet, det_transvection_of_ne _ _ t.hij]

lemma good_transvection (t : TransvectionStruct (Fin (k + 1)) ℝ) : Good t.toMatrix := by
  have h1 : base t.toMatrix = 1 := by
    simp [base, TransvectionStruct.det]
  rw [Good, h1]
  exact joinedIn_transvection t

/-- The matrix `-1` on the coordinates `0, i` and `1` elsewhere is a product of transvections. -/
lemma rot_sq_eq {i : Fin (k + 1)} (hi : i ≠ 0) :
    (transvection 0 i (1 : ℝ) * transvection i 0 (-1) * transvection 0 i 1) *
      (transvection 0 i (1 : ℝ) * transvection i 0 (-1) * transvection 0 i 1) =
      diagonal (Function.update (Function.update 1 0 (-1)) i (-1)) := by
  ext a b
  rw [show (transvection 0 i (1 : ℝ) * transvection i 0 (-1) * transvection 0 i 1) *
      (transvection 0 i (1 : ℝ) * transvection i 0 (-1) * transvection 0 i 1) =
      transvection 0 i (1 : ℝ) * (transvection i 0 (-1) * (transvection 0 i 1 *
      (transvection 0 i (1 : ℝ) * (transvection i 0 (-1) * transvection 0 i 1)))) by
    simp only [Matrix.mul_assoc]]
  have hi' : (0 : Fin (k + 1)) ≠ i := Ne.symm hi
  by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> by_cases hai : a = i <;> by_cases hbi : b = i
  all_goals first
    | (exfalso; exact hi (hai.symm.trans ha0))
    | (exfalso; exact hi (hbi.symm.trans hb0))
    | skip
  all_goals (try subst ha0); (try subst hb0); (try subst hai); (try subst hbi)
  all_goals simp only [transvection_mul_apply_same, transvection_mul_apply_of_ne,
    mul_transvection_apply_same, mul_transvection_apply_of_ne, ne_eq, not_false_eq_true, *]
  all_goals simp [transvection, Matrix.one_apply, single_apply, diagonal_apply, Function.update_apply,
    eq_comm, *]
  all_goals first
    | (intro h; subst h; simp_all)
    | (split_ifs <;> simp_all)

lemma good_of_det_one_transvections {i : Fin (k + 1)} (hi : i ≠ 0) :
    Good (diagonal (Function.update (Function.update (1 : Fin (k + 1) → ℝ) 0 (-1)) i (-1))) := by
  rw [← rot_sq_eq hi]
  have h1 : Good (transvection 0 i (1 : ℝ)) := good_transvection ⟨0, i, Ne.symm hi, 1⟩
  have h2 : Good (transvection i 0 (-1 : ℝ)) := good_transvection ⟨i, 0, hi, -1⟩
  have d1 : (transvection 0 i (1 : ℝ)).det ≠ 0 := by
    rw [det_transvection_of_ne _ _ (Ne.symm hi)]; exact one_ne_zero
  have d2 : (transvection i 0 (-1 : ℝ)).det ≠ 0 := by
    rw [det_transvection_of_ne _ _ hi]; exact one_ne_zero
  have d12 : (transvection 0 i (1 : ℝ) * transvection i 0 (-1)).det ≠ 0 := by
    rw [det_mul]; exact mul_ne_zero d1 d2
  have g3 := good_mul d12 d1 (good_mul d1 d2 h1 h2) h1
  have d3 : (transvection 0 i (1 : ℝ) * transvection i 0 (-1) * transvection 0 i 1).det ≠ 0 := by
    rw [det_mul]; exact mul_ne_zero d12 d1
  exact good_mul d3 d3 g3 g3

lemma good_single_neg (i : Fin (k + 1)) :
    Good (diagonal (Function.update (1 : Fin (k + 1) → ℝ) i (-1))) := by
  have hdetN : (negBase k).det ≠ 0 := by rw [det_negBase]; norm_num
  have hgN : Good (negBase k) := by
    have : base (negBase k) = negBase k := by simp [base, det_negBase]
    rw [Good, this]
    exact JoinedIn.refl hdetN
  by_cases hi : i = 0
  · subst hi
    exact hgN
  · have hdecomp : diagonal (Function.update (1 : Fin (k + 1) → ℝ) i (-1)) =
        negBase k * diagonal (Function.update (Function.update 1 0 (-1)) i (-1)) := by
      rw [negBase, diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases ha : a = i
      · subst ha; simp [Function.update_of_ne hi]
      · by_cases ha0 : a = 0
        · subst ha0; simp [Function.update_of_ne ha]
        · simp [Function.update_of_ne ha, Function.update_of_ne ha0]
    have hdetD : (diagonal (Function.update (Function.update (1 : Fin (k + 1) → ℝ) 0 (-1)) i
        (-1))).det ≠ 0 := by
      rw [← rot_sq_eq hi]
      have d1 := det_transvection_of_ne (0 : Fin (k + 1)) i (Ne.symm hi) (1 : ℝ)
      have d2 := det_transvection_of_ne i (0 : Fin (k + 1)) hi (-1 : ℝ)
      simp [det_mul, d1, d2]
    rw [hdecomp]
    exact good_mul hdetN hdetD hgN (good_of_det_one_transvections hi)

lemma good_diagonal_sign (ε : Fin (k + 1) → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    Good (diagonal ε) := by
  classical
  have key : ∀ S : Finset (Fin (k + 1)),
      Good (diagonal (fun j => if j ∈ S then ε j else 1)) ∧
        (diagonal (fun j => if j ∈ S then ε j else (1 : ℝ))).det ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false]
      rw [show (diagonal fun _ : Fin (k + 1) => (1 : ℝ)) = 1 from diagonal_one]
      exact ⟨good_one, by simp⟩
    | insert a S ha ih =>
      have hsplit : diagonal (fun j => if j ∈ insert a S then ε j else (1 : ℝ)) =
          diagonal (Function.update (1 : Fin (k + 1) → ℝ) a (ε a)) *
            diagonal (fun j => if j ∈ S then ε j else 1) := by
        rw [diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = a
        · subst hj; simp [ha]
        · simp [Function.update_of_ne hj, hj]
      have hfac : Good (diagonal (Function.update (1 : Fin (k + 1) → ℝ) a (ε a))) ∧
          (diagonal (Function.update (1 : Fin (k + 1) → ℝ) a (ε a))).det ≠ 0 := by
        rcases hε a with h | h
        · rw [h]
          rw [show Function.update (1 : Fin (k + 1) → ℝ) a 1 = fun _ => 1 from
            Function.update_eq_self_iff.2 rfl, diagonal_one]
          exact ⟨good_one, by simp⟩
        · rw [h]
          refine ⟨good_single_neg a, ?_⟩
          rw [det_update_one_neg]; norm_num
      rw [hsplit]
      refine ⟨good_mul hfac.2 ih.2 hfac.1 ih.1, ?_⟩
      rw [det_mul]; exact mul_ne_zero hfac.2 ih.2
  have := (key Finset.univ).1
  simpa using this

lemma prod_pos_iff_of_sign {S : Finset (Fin (k + 1))} (D ε : Fin (k + 1) → ℝ)
    (hDi : ∀ i, D i ≠ 0) (hε : ∀ i, ε i = if 0 < D i then 1 else -1) :
    (0 < ∏ i ∈ S, D i ↔ 0 < ∏ i ∈ S, ε i) ∧ (∏ i ∈ S, D i ≠ 0) ∧ (∏ i ∈ S, ε i ≠ 0) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨h1, h2, h3⟩ := ih
    have hεa : ε a ≠ 0 := by rw [hε a]; split_ifs <;> norm_num
    refine ⟨?_, mul_ne_zero (hDi a) h2, mul_ne_zero hεa h3⟩
    rw [hε a]
    rcases (hDi a).lt_or_gt with h | h
    · simp only [not_lt.2 h.le, if_false, neg_one_mul, neg_pos]
      constructor
      · intro hp
        rcases h2.lt_or_gt with h6 | h6
        · rcases h3.lt_or_gt with h7 | h7
          · exact h7
          · exact absurd (h1.2 h7) (not_lt.2 h6.le)
        · nlinarith
      · intro hp
        rcases h2.lt_or_gt with h6 | h6
        · nlinarith
        · exact absurd (h1.1 h6) (not_lt.2 hp.le)
    · simp only [h, if_true, one_mul]
      rw [mul_pos_iff_of_pos_left h]
      exact h1

lemma good_diagonal (D : Fin (k + 1) → ℝ) (hD : (diagonal D).det ≠ 0) : Good (diagonal D) := by
  have hDi : ∀ i, D i ≠ 0 := by
    intro i h
    apply hD
    rw [det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  set ε : Fin (k + 1) → ℝ := fun i => if 0 < D i then 1 else -1 with hεdef
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
    simp only [ε]; split_ifs <;> simp
  -- straight line from `D` to `ε`
  have hline : JoinedIn (glSet k) (diagonal D) (diagonal ε) := by
    refine JoinedIn.ofLine (f := fun s : ℝ => diagonal (fun i => (1 - s) * D i + s * ε i))
      ?_ ?_ ?_ ?_
    · refine Continuous.continuousOn ?_
      exact Continuous.matrix_diagonal (by fun_prop)
    · simp
    · simp
    · rintro _ ⟨s, hs, rfl⟩
      simp only [glSet, Set.mem_setOf_eq, det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simp only [ε]
      rcases (hDi i).lt_or_gt with h | h
      · simp only [not_lt.2 h.le, if_false]
        obtain ⟨hs0, hs1⟩ := hs
        have : (1 - s) * D i + s * -1 < 0 := by
          rcases eq_or_lt_of_le hs1 with h1 | h1
          · subst h1; norm_num
          · nlinarith
        exact this.ne
      · simp only [h, if_true]
        obtain ⟨hs0, hs1⟩ := hs
        have : 0 < (1 - s) * D i + s * 1 := by
          rcases eq_or_lt_of_le hs1 with h1 | h1
          · subst h1; norm_num
          · nlinarith
        exact this.ne'
  have hsign : base (diagonal D) = base (diagonal ε) := by
    unfold base
    rw [det_diagonal, det_diagonal]
    have hiff := (prod_pos_iff_of_sign (S := Finset.univ) D ε hDi (fun i => rfl)).1
    by_cases hp : 0 < ∏ i, D i
    · rw [if_pos hp, if_pos (hiff.1 hp)]
    · rw [if_neg hp, if_neg (fun h => hp (hiff.2 h))]
  unfold Good
  rw [hsign]
  exact hline.trans (good_diagonal_sign ε hε)

theorem good_of_det_ne_zero (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hM : M.det ≠ 0) :
    Good M :=
  diagonal_transvection_induction_of_det_ne_zero Good M hM good_diagonal good_transvection
    fun _ _ hA hB gA gB => good_mul hA hB gA gB

/-- **Paths of invertible matrices.** Two matrices whose determinants have the same sign are
joined by a path of invertible matrices. -/
theorem joinedIn_gl_of_det_mul_pos {A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (h : 0 < A.det * B.det) : JoinedIn (glSet k) A B := by
  have hA : A.det ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h
  have hB : B.det ≠ 0 := by intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  have hbase : base A = base B := by
    unfold base
    rcases hA.lt_or_gt with h1 | h1 <;> rcases hB.lt_or_gt with h2 | h2
    · simp [not_lt.2 h1.le, not_lt.2 h2.le]
    · exact absurd h (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg h1.le h2.le))
    · exact absurd h (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos h1.le h2.le))
    · simp [h1, h2]
  have gA := good_of_det_ne_zero A hA
  have gB := good_of_det_ne_zero B hB
  unfold Good at gA gB
  rw [hbase] at gA
  exact gA.trans gB.symm

end Surgery
