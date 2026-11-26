module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import RequestProject.Reduction

@[expose] public section

/-!
# A chart of the mass simplex

`toBary : ℝ × ℝ⁴ → ℝ⁶` is the affine chart `y ↦ (y₀, y₁, …, y₄, 1 - ∑ yᵢ)` of the hyperplane
`∑ xᵢ = 1`; `Uo` is the preimage of the open simplex and `ret` a retraction of `ℝ × ℝ⁴` onto the
preimage of the closed simplex.
-/

open Set

namespace Tverberg6R

/-- The chart. -/
def toBary (y : ℝ × (Fin 4 → ℝ)) : Fin 6 → ℝ :=
  Fin.cons y.1 (Fin.snoc y.2 (1 - y.1 - ∑ j, y.2 j))

/-- Inverse chart. -/
def fromBary (x : Fin 6 → ℝ) : ℝ × (Fin 4 → ℝ) := (x 0, fun i => x i.castSucc.succ)

/-- Linear part of the chart. -/
def toBaryLin (y : ℝ × (Fin 4 → ℝ)) : Fin 6 → ℝ :=
  Fin.cons y.1 (Fin.snoc y.2 (- y.1 - ∑ j, y.2 j))

@[simp] lemma cons_snoc_five (a : ℝ) (v : Fin 4 → ℝ) (l : ℝ) :
    (Fin.cons a (Fin.snoc v l) : Fin 6 → ℝ) 5 = l := rfl

lemma toBary_zero (y : ℝ × (Fin 4 → ℝ)) : toBary y 0 = y.1 := rfl

lemma toBary_succ_castSucc (y : ℝ × (Fin 4 → ℝ)) (i : Fin 4) :
    toBary y i.castSucc.succ = y.2 i := by
  simp [toBary]

lemma toBary_five (y : ℝ × (Fin 4 → ℝ)) : toBary y 5 = 1 - y.1 - ∑ j, y.2 j := by
  simp only [toBary]
  rfl

lemma sum_toBary (y : ℝ × (Fin 4 → ℝ)) : ∑ i, toBary y i = 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [toBary, Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last]
  ring

lemma fromBary_toBary (y : ℝ × (Fin 4 → ℝ)) : fromBary (toBary y) = y := by
  ext
  · rfl
  · simp [fromBary, toBary_succ_castSucc]

lemma toBary_fromBary {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) : toBary (fromBary x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · rw [show (Fin.last 4).succ = (5 : Fin 6) from rfl, toBary_five]
      simp only [fromBary]
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hx
      have : x (Fin.last 4).succ = x 5 := rfl
      linarith
    · rw [toBary_succ_castSucc]; rfl

lemma toBary_add (y v : ℝ × (Fin 4 → ℝ)) : toBary (y + v) = toBary y + toBaryLin v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [toBary, toBaryLin]
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [toBary, toBaryLin, Fin.cons_succ, Fin.snoc_last, Pi.add_apply,
        Prod.fst_add, Prod.snd_add, Finset.sum_add_distrib]
      ring
    · simp [toBary, toBaryLin]

/-- `toBaryLin` as a linear map. -/
def toBaryL : (ℝ × (Fin 4 → ℝ)) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := toBaryLin
  map_add' y v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [toBaryLin]
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · simp only [toBaryLin, Fin.cons_succ, Fin.snoc_last, Pi.add_apply,
          Prod.fst_add, Prod.snd_add, Finset.sum_add_distrib]
        ring
      · simp [toBaryLin]
  map_smul' c y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [toBaryLin]
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · simp only [toBaryLin, Fin.cons_succ, Fin.snoc_last, Pi.smul_apply, smul_eq_mul,
          Prod.smul_fst, Prod.smul_snd, ← Finset.mul_sum]
        simp only [RingHom.id_apply, ← Finset.mul_sum]; ring
      · simp [toBaryLin]

lemma continuous_toBary : Continuous toBary := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [toBary, Fin.cons_succ, Fin.snoc_last]
      fun_prop
    · simp only [toBary, Fin.cons_succ, Fin.snoc_castSucc]
      fun_prop

lemma toBary_affine (y y' : ℝ × (Fin 4 → ℝ)) (a b : ℝ) (hab : a + b = 1) :
    toBary (a • y + b • y') = a • toBary y + b • toBary y' := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [toBary]
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [toBary, Fin.cons_succ, Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      linear_combination -hab
    · simp [toBary]

/-- The open simplex in the chart. -/
def Uo : Set (ℝ × (Fin 4 → ℝ)) := {y | ∀ i, 0 < toBary y i}

lemma isOpen_Uo : IsOpen Uo := by
  have : Uo = ⋂ i, {y | 0 < toBary y i} := by ext y; simp [Uo]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const ((continuous_apply i).comp continuous_toBary)

lemma convex_Uo : Convex ℝ Uo := by
  intro y hy y' hy' a b ha hb hab i
  rw [toBary_affine y y' a b hab]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha | ha
  · nlinarith [hy i, hy' i]
  · subst ha; simp at hab; subst hab; simpa using hy' i

/-- Positive part. -/
noncomputable def posPart' (y : ℝ × (Fin 4 → ℝ)) : ℝ × (Fin 4 → ℝ) :=
  (max y.1 0, fun j => max (y.2 j) 0)

/-- The retraction onto the closed simplex. -/
noncomputable def ret (y : ℝ × (Fin 4 → ℝ)) : ℝ × (Fin 4 → ℝ) :=
  (1 / max 1 ((posPart' y).1 + ∑ j, (posPart' y).2 j)) • posPart' y

lemma continuous_ret : Continuous ret := by
  unfold ret posPart'
  have h_scalar :
      Continuous (fun y : ℝ × (Fin 4 → ℝ) => 1 / max 1 (max y.1 0 + ∑ j, max (y.2 j) 0)) :=
    Continuous.div continuous_const (by fun_prop) (fun y => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')
  have h_vec : Continuous (fun y : ℝ × (Fin 4 → ℝ) => (max y.1 0, fun j => max (y.2 j) 0)) := by
    fun_prop
  exact h_scalar.smul h_vec

lemma sum_ret (y : ℝ × (Fin 4 → ℝ)) :
    (ret y).1 + ∑ j, (ret y).2 j = ((posPart' y).1 + ∑ j, (posPart' y).2 j) /
      max 1 ((posPart' y).1 + ∑ j, (posPart' y).2 j) := by
  simp only [ret, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma toBary_ret_mem (y : ℝ × (Fin 4 → ℝ)) : toBary (ret y) ∈ massSimplex := by
  set s := (posPart' y).1 + ∑ j, (posPart' y).2 j with hs
  have hM : 0 < max 1 s := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : 0 ≤ (posPart' y).1 := le_max_right _ _
  have h2 : ∀ j, 0 ≤ (posPart' y).2 j := fun j => le_max_right _ _
  refine ⟨fun i => ?_, sum_toBary _⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [toBary_zero, ret, Prod.smul_fst, smul_eq_mul]
    exact mul_nonneg (by positivity) h1
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · rw [show (Fin.last 4).succ = (5 : Fin 6) from rfl, toBary_five]
      have h := sum_ret y
      rw [← hs] at h
      have : s / max 1 s ≤ 1 := (div_le_one hM).2 (le_max_right _ _)
      linarith
    · rw [toBary_succ_castSucc]
      simp only [ret, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (h2 l)

lemma ret_eq_self {y : ℝ × (Fin 4 → ℝ)} (hy : ∀ i, 0 ≤ toBary y i) : ret y = y := by
  have h1 : 0 ≤ y.1 := hy 0
  have h2 : ∀ j, 0 ≤ y.2 j := fun j => by have := hy j.castSucc.succ; rwa [toBary_succ_castSucc] at this
  have h5 := hy 5
  rw [toBary_five] at h5
  have hp : posPart' y = y := by
    ext
    · exact max_eq_left h1
    · exact max_eq_left (h2 _)
  unfold ret
  rw [hp, max_eq_left (by linarith), div_one, one_smul]

lemma exists_toBary_ret_eq_zero {y : ℝ × (Fin 4 → ℝ)} (hy : y ∉ Uo) :
    ∃ i, toBary (ret y) i = 0 := by
  simp only [Uo, mem_setOf_eq, not_forall, not_lt] at hy
  obtain ⟨i, hi⟩ := hy
  set s := (posPart' y).1 + ∑ j, (posPart' y).2 j with hs
  by_cases h1 : y.1 ≤ 0
  · refine ⟨0, ?_⟩
    simp [toBary_zero, ret, posPart', max_eq_right h1]
  by_cases h2 : ∃ j, y.2 j ≤ 0
  · obtain ⟨j, hj⟩ := h2
    refine ⟨j.castSucc.succ, ?_⟩
    rw [toBary_succ_castSucc]
    simp [ret, posPart', max_eq_right hj]
  push_neg at h1 h2
  -- the last coordinate is nonpositive, so `s ≥ 1`
  have hi' : toBary y 5 ≤ 0 := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [toBary_zero] at hi; linarith
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
      · rw [toBary_succ_castSucc] at hi; linarith [h2 l]
      · exact hi
  rw [toBary_five] at hi'
  have hp : posPart' y = y := by
    ext
    · exact max_eq_left h1.le
    · exact max_eq_left (h2 _).le
  have hs1 : 1 ≤ s := by rw [hs, hp]; linarith
  refine ⟨5, ?_⟩
  rw [toBary_five]
  have h := sum_ret y
  rw [← hs, max_eq_right hs1, div_self (by linarith)] at h
  linarith

end Tverberg6R
