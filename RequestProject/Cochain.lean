module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The alternating identity for oriented simplex indices (Lemma 5, algebraic form)

For `n + 1` points `w` of `ℝ^n`, `simplexIndex w ∈ {-1, 0, 1}` is the sign of the affine
determinant of the points if the origin has strictly positive barycentric coordinates with
respect to them, and `0` otherwise (the local degree at the origin of the affine simplex).

`alternating_simplexIndex`: for `n + 2` points `z` of `ℝ^n`, any `n` of which are linearly
independent and some `n + 1` of which are affinely independent,
`∑ k, (-1)^k * simplexIndex (z ∘ k.succAbove) = 0`.

The proof is elementary linear algebra: the barycentric solutions form a segment on the
kernel line of the `(n+1) × (n+2)` system, whose two endpoints carry opposite signs.
-/

open Matrix

namespace Tverberg6R

/-- The integer sign of a real number. -/
noncomputable def rsign (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

lemma rsign_neg_one_pow_mul (k : ℕ) (x : ℝ) : (-1 : ℤ) ^ k * rsign x = rsign ((-1) ^ k * x) := by
  rcases neg_one_pow_eq_or ℝ k with h | h
  · have h' : (-1 : ℤ) ^ k = 1 := by exact_mod_cast h
    rw [h, h', one_mul, one_mul]
  · have h' : (-1 : ℤ) ^ k = -1 := by exact_mod_cast h
    rw [h, h']
    unfold rsign
    rcases lt_trichotomy x 0 with hx | hx | hx
    · simp [hx, hx.not_gt, neg_pos.2 hx]
    · simp [hx]
    · simp [hx, (neg_neg_iff_pos).2 hx, (neg_pos.not).2 (not_lt.2 hx.le)]

/-- The affine matrix of `n + 1` points of `ℝ^n`: columns `(1, w s)`. -/
def affMat {n : ℕ} (w : Fin (n + 1) → Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun r s => (Fin.cons 1 (w s) : Fin (n + 1) → ℝ) r

open Classical in
/-- Oriented local index of the affine simplex spanned by `w` at the origin. -/
noncomputable def simplexIndex {n : ℕ} (w : Fin (n + 1) → Fin n → ℝ) : ℤ :=
  if ∃ y : Fin (n + 1) → ℝ, (∀ s, 0 < y s) ∧ affMat w *ᵥ y = Pi.single 0 1 then
    rsign (affMat w).det
  else 0

section Identity

variable {n : ℕ} (z : Fin (n + 2) → Fin n → ℝ)

/-- The full `(n+1) × (n+2)` system. -/
def fullMat : Matrix (Fin (n + 1)) (Fin (n + 2)) ℝ :=
  Matrix.of fun r k => (Fin.cons 1 (z k) : Fin (n + 1) → ℝ) r

lemma fullMat_submatrix (k : Fin (n + 2)) :
    (fullMat z).submatrix id k.succAbove = affMat (z ∘ k.succAbove) := rfl

/-- The cofactor vector spanning the kernel. -/
noncomputable def kerVec (k : Fin (n + 2)) : ℝ :=
  (-1) ^ (k : ℕ) * (affMat (z ∘ k.succAbove)).det

lemma fullMat_mulVec_kerVec : fullMat z *ᵥ kerVec z = 0 := by
  funext r
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    Matrix.of (Fin.cons (fun k => fullMat z r k) (fun i k => fullMat z i k))
  have hA : A.det = 0 := by
    apply Matrix.det_zero_of_row_eq (i := 0) (j := r.succ) (Fin.succ_ne_zero r).symm
    funext k; simp [A]
  rw [Matrix.det_succ_row_zero] at hA
  simp only [mulVec, dotProduct, kerVec, Pi.zero_apply]
  rw [← hA]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : A.submatrix Fin.succ k.succAbove = affMat (z ∘ k.succAbove) := by
    ext i j; simp [A, fullMat, affMat]
  rw [this]
  simp [A]
  ring

lemma mulVec_split (v : Fin (n + 2) → ℝ) (a : Fin (n + 2)) :
    fullMat z *ᵥ v = affMat (z ∘ a.succAbove) *ᵥ (v ∘ a.succAbove) +
      v a • (fun r => fullMat z r a) := by
  funext r
  simp only [mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succAbove _ a]
  simp [affMat, fullMat]
  ring

/-- The kernel is spanned by `kerVec` as soon as one maximal minor is nonzero. -/
lemma ker_eq_smul {a : Fin (n + 2)} (ha : (affMat (z ∘ a.succAbove)).det ≠ 0)
    {w : Fin (n + 2) → ℝ} (hw : fullMat z *ᵥ w = 0) :
    w = (w a / kerVec z a) • kerVec z := by
  have hκ : kerVec z a ≠ 0 := by
    unfold kerVec
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ha
  set w' := w - (w a / kerVec z a) • kerVec z with hw'
  have hw'a : w' a = 0 := by
    simp [hw', hκ]
  have hGw' : fullMat z *ᵥ w' = 0 := by
    rw [hw', Matrix.mulVec_sub, Matrix.mulVec_smul, fullMat_mulVec_kerVec, hw]; simp
  rw [mulVec_split z w' a, hw'a, zero_smul, add_zero] at hGw'
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero ha hGw'
  have : w' = 0 := by
    funext k
    rcases Fin.eq_self_or_eq_succAbove a k with rfl | ⟨j, rfl⟩
    · exact hw'a
    · exact congrFun h0 j
  rw [hw'] at this
  exact sub_eq_zero.1 this

/-- Barycentric feasibility of the `k`-th facet. -/
def Feasible (k : Fin (n + 2)) : Prop :=
  ∃ x : Fin (n + 2) → ℝ, fullMat z *ᵥ x = Pi.single 0 1 ∧ (∀ j, 0 ≤ x j) ∧ x k = 0

lemma fullMat_row_zero (x : Fin (n + 2) → ℝ) : (fullMat z *ᵥ x) 0 = ∑ k, x k := by
  simp [mulVec, dotProduct, fullMat]

lemma fullMat_row_succ (x : Fin (n + 2) → ℝ) (r : Fin n) :
    (fullMat z *ᵥ x) r.succ = (∑ k, x k • z k) r := by
  simp [mulVec, dotProduct, fullMat, Finset.sum_apply, mul_comm]

variable {z}

/-- Hypothesis: any `n` of the points are linearly independent. -/
def NIndep (z : Fin (n + 2) → Fin n → ℝ) : Prop :=
  ∀ x : Fin (n + 2) → ℝ, ∑ k, x k • z k = 0 → ∀ a b, a ≠ b → x a = 0 → x b = 0 → x = 0

lemma two_zero_false (hz : NIndep z) {x : Fin (n + 2) → ℝ}
    (hx : fullMat z *ᵥ x = Pi.single 0 1) {a b : Fin (n + 2)} (hab : a ≠ b)
    (ha : x a = 0) (hb : x b = 0) : False := by
  have hsum : ∑ k, x k • z k = 0 := by
    funext r
    have := congrFun hx r.succ
    rw [fullMat_row_succ] at this
    simpa [Pi.single_apply, Fin.succ_ne_zero] using this
  have h0 := hz x hsum a b hab ha hb
  have := congrFun hx 0
  rw [fullMat_row_zero, h0] at this
  simp at this

lemma sum_kerVec : ∑ k, kerVec z k = 0 := by
  have := congrFun (fullMat_mulVec_kerVec z) 0
  rwa [fullMat_row_zero] at this

/-- Moving along a kernel direction until a coordinate vanishes. -/
lemma ray_hits {x d : Fin (n + 2) → ℝ} (hx : ∀ j, 0 ≤ x j) (hd : d ≠ 0) (hds : ∑ k, d k = 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ j, d j < 0 ∧ (∀ k, 0 ≤ x k + t * d k) ∧ x j + t * d j = 0 := by
  classical
  have hneg : ∃ j, d j < 0 := by
    by_contra h
    push_neg at h
    apply hd
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).1 hds k (Finset.mem_univ _)
    simpa using this
  set J := Finset.univ.filter fun j => d j < 0
  have hJ : J.Nonempty := by
    obtain ⟨j, hj⟩ := hneg; exact ⟨j, by simp [J, hj]⟩
  obtain ⟨j, hjJ, hjmin⟩ := J.exists_min_image (fun j => x j / (-d j)) hJ
  have hdj : d j < 0 := by simpa [J] using hjJ
  refine ⟨x j / (-d j), div_nonneg (hx j) (by linarith), j, hdj, fun k => ?_, ?_⟩
  · by_cases hk : d k < 0
    · have := hjmin k (by simp [J, hk])
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · push_neg at hk
      have : 0 ≤ x j / (-d j) := div_nonneg (hx j) (by linarith)
      nlinarith [hx k]
  · have hne : d j ≠ 0 := hdj.ne
    field_simp
    ring

lemma kerVec_ne_zero_of_det {a : Fin (n + 2)} (ha : (affMat (z ∘ a.succAbove)).det ≠ 0) :
    kerVec z ≠ 0 := by
  intro h
  have := congrFun h a
  simp only [kerVec, Pi.zero_apply] at this
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ha this

lemma kerVec_ne_zero_of_feasible (hz : NIndep z) {a : Fin (n + 2)}
    (ha : (affMat (z ∘ a.succAbove)).det ≠ 0) {k : Fin (n + 2)} (hk : Feasible z k) :
    kerVec z k ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hx0, hxk⟩ := hk
  obtain ⟨t, -, j, hj, hpos, hzero⟩ := ray_hits hx0 (kerVec_ne_zero_of_det ha) sum_kerVec
  have hjk : j ≠ k := by rintro rfl; rw [h0] at hj; exact lt_irrefl _ hj
  have hy : fullMat z *ᵥ (x + t • kerVec z) = Pi.single 0 1 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, fullMat_mulVec_kerVec, hx]; simp
  exact two_zero_false hz hy hjk (by simpa using hzero) (by simp [hxk, h0])

/-- From a feasible facet, the kernel ray reaches a feasible facet of the opposite sign. -/
lemma feasible_partner {a : Fin (n + 2)}
    (ha : (affMat (z ∘ a.succAbove)).det ≠ 0) (ε : ℝ) (hε : ε ≠ 0) {k : Fin (n + 2)}
    (hk : Feasible z k) : ∃ j, Feasible z j ∧ ε * kerVec z j < 0 := by
  obtain ⟨x, hx, hx0, -⟩ := hk
  have hd : ε • kerVec z ≠ 0 := smul_ne_zero hε (kerVec_ne_zero_of_det ha)
  have hds : ∑ k, (ε • kerVec z) k = 0 := by
    simp [← Finset.mul_sum, sum_kerVec]
  obtain ⟨t, -, j, hj, hpos, hzero⟩ := ray_hits hx0 hd hds
  refine ⟨j, ⟨x + t • (ε • kerVec z), ?_, fun k => by simpa using hpos k,
    by simpa using hzero⟩, by simpa using hj⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, fullMat_mulVec_kerVec, hx]
  simp

/-- Two feasible facets cannot have kernel coordinates of the same sign. -/
lemma feasible_unique (hz : NIndep z) {a : Fin (n + 2)}
    (ha : (affMat (z ∘ a.succAbove)).det ≠ 0) (ε : ℝ) {k k' : Fin (n + 2)}
    (hk : Feasible z k) (hk' : Feasible z k') (hεk : 0 < ε * kerVec z k)
    (hεk' : 0 < ε * kerVec z k') : k = k' := by
  by_contra hne
  obtain ⟨x, hx, hx0, hxk⟩ := hk
  obtain ⟨x', hx', hx0', hxk'⟩ := hk'
  have hw : fullMat z *ᵥ (x' - x) = 0 := by
    rw [Matrix.mulVec_sub, hx, hx', sub_self]
  obtain ⟨s, hdiff⟩ : ∃ s : ℝ, x' - x = s • kerVec z := ⟨_, ker_eq_smul z ha hw⟩
  have e1 : x' k = x k + s * kerVec z k := by
    have := congrFun hdiff k; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have e2 : x' k' = x k' + s * kerVec z k' := by
    have := congrFun hdiff k'; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  rw [hxk] at e1
  rw [hxk'] at e2
  -- `s * κ_k ≥ 0` and `s * κ_k' ≤ 0` with `κ_k, κ_k'` of the same sign force `s = 0`
  have h1 : 0 ≤ s * kerVec z k := by linarith [hx0' k]
  have h2 : s * kerVec z k' ≤ 0 := by linarith [hx0 k']
  have hs : s * kerVec z k' = 0 := by
    have hεne : ε ≠ 0 := by rintro rfl; simp at hεk
    have key : 0 ≤ (s * kerVec z k) * (ε * kerVec z k') := by positivity
    have key2 : (s * kerVec z k') * (ε * kerVec z k) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h2 hεk.le
    have : (s * kerVec z k) * (ε * kerVec z k') = (s * kerVec z k') * (ε * kerVec z k) := by ring
    rcases lt_or_eq_of_le h2 with h | h
    · exfalso
      have : (s * kerVec z k') * (ε * kerVec z k) < 0 := mul_neg_of_neg_of_pos h hεk
      linarith
    · exact h
  have hxk'0 : x k' = 0 := by linarith
  exact two_zero_false hz hx hne hxk hxk'0

open Classical in
lemma simplexIndex_eq (hz : NIndep z) (k : Fin (n + 2)) :
    simplexIndex (z ∘ k.succAbove) =
      if Feasible z k then rsign (affMat (z ∘ k.succAbove)).det else 0 := by
  classical
  unfold simplexIndex
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy0, hy⟩
    refine ⟨Fin.insertNth k 0 y, ?_, fun j => ?_, by simp⟩
    · rw [mulVec_split z _ k]
      simp only [Fin.insertNth_apply_same, zero_smul, add_zero]
      convert hy using 2
      funext j; simp
    · rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
      · simp
      · simp [(hy0 i).le]
  · rintro ⟨x, hx, hx0, hxk⟩
    refine ⟨x ∘ k.succAbove, fun s => ?_, ?_⟩
    · rcases lt_or_eq_of_le (hx0 (k.succAbove s)) with h | h
      · exact h
      · exact (two_zero_false hz hx (Fin.succAbove_ne k s).symm hxk h.symm).elim
    · rw [← hx, mulVec_split z x k, hxk, zero_smul, add_zero]

/-- **Lemma 5 (algebraic form).** The alternating sum of the oriented indices of the facets of
`n + 2` points in general position vanishes. -/
theorem alternating_simplexIndex (hz : NIndep z) {a : Fin (n + 2)}
    (ha : (affMat (z ∘ a.succAbove)).det ≠ 0) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) * simplexIndex (z ∘ k.succAbove) = 0 := by
  classical
  have hterm : ∀ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) * simplexIndex (z ∘ k.succAbove) =
      (if Feasible z k ∧ 0 < kerVec z k then 1 else 0) -
        (if Feasible z k ∧ kerVec z k < 0 then 1 else 0) := by
    intro k
    rw [simplexIndex_eq hz]
    by_cases hf : Feasible z k
    · rw [if_pos hf, rsign_neg_one_pow_mul]
      have hne := kerVec_ne_zero_of_feasible hz ha hf
      unfold kerVec at hne ⊢
      rcases lt_or_gt_of_ne hne with h | h
      · simp [rsign, h, h.not_gt, hf]
      · simp [rsign, h, h.not_gt, hf]
    · simp [hf]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib,
    Finset.sum_boole, Finset.sum_boole, sub_eq_zero]
  congr 1
  set Fp := Finset.univ.filter fun k => Feasible z k ∧ 0 < kerVec z k
  set Fn := Finset.univ.filter fun k => Feasible z k ∧ kerVec z k < 0
  have hp1 : Fp.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk k' hk'
    simp only [Fp, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact feasible_unique hz ha 1 hk.1 hk'.1 (by simpa using hk.2) (by simpa using hk'.2)
  have hn1 : Fn.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk k' hk'
    simp only [Fn, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact feasible_unique hz ha (-1) hk.1 hk'.1 (by linarith [hk.2]) (by linarith [hk'.2])
  have hpn : Fp.Nonempty ↔ Fn.Nonempty := by
    constructor
    · rintro ⟨k, hk⟩
      simp only [Fp, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨j, hj, hj'⟩ := feasible_partner ha 1 one_ne_zero hk.1
      exact ⟨j, by simp [Fn, hj, by simpa using hj']⟩
    · rintro ⟨k, hk⟩
      simp only [Fn, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨j, hj, hj'⟩ := feasible_partner ha (-1) (by norm_num) hk.1
      exact ⟨j, by simp [Fp, hj, (show 0 < kerVec z j by linarith [hj'])]⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp1 with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn1 with h' | h'
  · rw [h, h']
  · exfalso
    have : Fn.Nonempty := Finset.card_pos.1 (by omega)
    have := Finset.card_pos.2 (hpn.2 this); omega
  · exfalso
    have : Fp.Nonempty := Finset.card_pos.1 (by omega)
    have := Finset.card_pos.2 (hpn.1 this); omega
  · rw [h, h']

end Identity

end Tverberg6R
