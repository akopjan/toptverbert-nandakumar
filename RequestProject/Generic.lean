module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import RequestProject.Reduction

@[expose] public section

/-!
# Generic initial data (Step A)

For a choice `q : Fin 6 → Fin 6 → ℝ` of 36 reals, the additive height table
`H⁰(λ) w = ∑ i, λ i * q i (w i)` has, along an ordered matching `m`, the normal vectors
`vvec q m i = ℓ_m (w ↦ q i (w i)) ∈ ℝ^5`.  We prove that some `q` is *generic* for all
matchings simultaneously:

* any five of the six vectors `vvec q m i` are linearly independent (`det5 ≠ 0`);
* every anchor vector `uvec P` (`P` a nonempty proper subset of `Fin 6`) together with any
  four of the `vvec q m i` is linearly independent (`detA ≠ 0`);
* the six vectors `vvec q m i` are affinely independent (`detAff ≠ 0`).

The proof is the polynomial specialization argument: every determinant is a polynomial in the
36 variables, it is nonzero because a suitable specialization evaluates to `±1` or `±6`, and a
nonzero polynomial (here: the product of all of them) does not vanish identically on `ℝ^36`.
-/

open Matrix MvPolynomial

namespace Tverberg6R

/-- Normal coordinates of a table along an ordered six-tuple of words. -/
def ell (m : Fin 6 → Word) (T : Table) : Fin 5 → ℝ :=
  fun r => T (m r.castSucc) - T (m 5)

/-- The color-`i` part of the additive table. -/
def colorTable (q : Fin 6 → Fin 6 → ℝ) (i : Fin 6) : Table := fun w => q i (w i)

/-- The normal vector of color `i` along `m`. -/
def vvec (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (i : Fin 6) : Fin 5 → ℝ :=
  ell m (colorTable q i)

/-- The (matching-independent) normal vector of a two-level anchor with row set `P`. -/
def uvec (P : Finset (Fin 6)) : Fin 5 → ℝ :=
  fun r => 6 * ((if r.castSucc ∈ P then 1 else 0) - (if (5 : Fin 6) ∈ P then 1 else 0))

/-- Determinant of five color vectors. -/
noncomputable def det5 (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (c : Fin 5 → Fin 6) : ℝ :=
  (Matrix.of fun r s => vvec q m (c s) r).det

/-- Determinant of an anchor vector and four color vectors. -/
noncomputable def detA (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (P : Finset (Fin 6))
    (c : Fin 4 → Fin 6) : ℝ :=
  (Matrix.of fun r s => (Fin.cons (uvec P) (fun t => vvec q m (c t)) : Fin 5 → Fin 5 → ℝ) s r).det

/-- The affine determinant of the six color vectors. -/
noncomputable def detAff (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) : ℝ :=
  (Matrix.of fun r s => (Fin.cons 1 (vvec q m s) : Fin 6 → ℝ) r).det

/-- Genericity of the initial data, for all matchings simultaneously. -/
structure IsGeneric (q : Fin 6 → Fin 6 → ℝ) : Prop where
  five : ∀ m, IsMatching m → ∀ c : Fin 5 → Fin 6, Function.Injective c → det5 q m c ≠ 0
  anchor : ∀ m, IsMatching m → ∀ P : Finset (Fin 6), P.Nonempty → P ≠ Finset.univ →
    ∀ c : Fin 4 → Fin 6, Function.Injective c → detA q m P c ≠ 0
  affine : ∀ m, IsMatching m → detAff q m ≠ 0

lemma uvec_exists_ne {P : Finset (Fin 6)} (h1 : P.Nonempty) (h2 : P ≠ Finset.univ) :
    ∃ r, uvec P r ≠ 0 := by
  by_cases h5 : (5 : Fin 6) ∈ P
  · obtain ⟨a, ha⟩ : ∃ a, a ∉ P := by
      by_contra h; push_neg at h; exact h2 (Finset.eq_univ_iff_forall.2 h)
    have ha5 : a ≠ Fin.last 5 := fun h => ha (by subst h; exact h5)
    refine ⟨a.castPred ha5, ?_⟩
    simp [uvec, ha, h5]
  · obtain ⟨a, ha⟩ := h1
    have ha5 : a ≠ Fin.last 5 := fun h => h5 (by subst h; exact ha)
    refine ⟨a.castPred ha5, ?_⟩
    simp [uvec, ha, h5]

/-! ### Polynomial versions -/

/-- Variables: `(color, label)`. -/
abbrev Var := Fin 6 × Fin 6

/-- The point of `ℝ^36` as a function of two arguments. -/
def qOf (x : Var → ℝ) : Fin 6 → Fin 6 → ℝ := fun i a => x (i, a)

noncomputable def vpoly (m : Fin 6 → Word) (i : Fin 6) : Fin 5 → MvPolynomial Var ℝ :=
  fun r => X (i, m r.castSucc i) - X (i, m 5 i)

lemma eval_vpoly (x : Var → ℝ) (m : Fin 6 → Word) (i : Fin 6) (r : Fin 5) :
    eval x (vpoly m i r) = vvec (qOf x) m i r := by
  simp [vpoly, vvec, ell, colorTable, qOf]

noncomputable def det5poly (m : Fin 6 → Word) (c : Fin 5 → Fin 6) : MvPolynomial Var ℝ :=
  (Matrix.of fun r s => vpoly m (c s) r).det

noncomputable def detApoly (m : Fin 6 → Word) (P : Finset (Fin 6)) (c : Fin 4 → Fin 6) :
    MvPolynomial Var ℝ :=
  (Matrix.of fun r s => (Fin.cons (fun r => C (uvec P r)) (fun t => vpoly m (c t)) :
    Fin 5 → Fin 5 → MvPolynomial Var ℝ) s r).det

noncomputable def detAffpoly (m : Fin 6 → Word) : MvPolynomial Var ℝ :=
  (Matrix.of fun r s => (Fin.cons 1 (vpoly m s) : Fin 6 → MvPolynomial Var ℝ) r).det

lemma eval_det5poly (x : Var → ℝ) (m : Fin 6 → Word) (c : Fin 5 → Fin 6) :
    eval x (det5poly m c) = det5 (qOf x) m c := by
  rw [det5poly, RingHom.map_det]
  congr 1
  ext r s
  simp [eval_vpoly]

lemma eval_detApoly (x : Var → ℝ) (m : Fin 6 → Word) (P : Finset (Fin 6)) (c : Fin 4 → Fin 6) :
    eval x (detApoly m P c) = detA (qOf x) m P c := by
  rw [detApoly, RingHom.map_det]
  congr 1
  ext r s
  refine Fin.cases ?_ (fun t => ?_) s <;> simp [eval_vpoly]

lemma eval_detAffpoly (x : Var → ℝ) (m : Fin 6 → Word) :
    eval x (detAffpoly m) = detAff (qOf x) m := by
  rw [detAffpoly, RingHom.map_det]
  congr 1
  ext r s
  refine Fin.cases ?_ (fun t => ?_) r <;> simp [eval_vpoly]

/-! ### Specialization -/

/-- A point of `ℝ^36` at which the color vectors along `m` are prescribed vectors `y i`. -/
noncomputable def specPt (m : Fin 6 → Word) (y : Fin 6 → Fin 5 → ℝ) : Var → ℝ :=
  fun p => ∑ r : Fin 5, if p.2 = m r.castSucc p.1 then y p.1 r else 0

lemma vvec_specPt {m : Fin 6 → Word} (hm : IsMatching m) (y : Fin 6 → Fin 5 → ℝ) (i : Fin 6) :
    vvec (qOf (specPt m y)) m i = y i := by
  funext r'
  simp only [vvec, ell, colorTable, qOf, specPt]
  have h1 : ∀ r : Fin 5, (m r'.castSucc i = m r.castSucc i) ↔ r' = r :=
    fun r => ⟨fun h => Fin.castSucc_injective _ (hm i h), fun h => h ▸ rfl⟩
  have h2 : ∀ r : Fin 5, ¬ (m 5 i = m r.castSucc i) :=
    fun r h => (Fin.castSucc_lt_last r).ne' (hm i h)
  simp [h1, h2]

lemma det5poly_ne_zero {m : Fin 6 → Word} (hm : IsMatching m) {c : Fin 5 → Fin 6}
    (hc : Function.Injective c) : det5poly m c ≠ 0 := by
  intro h
  let y : Fin 6 → Fin 5 → ℝ := fun i r => if c r = i then 1 else 0
  have := congrArg (eval (specPt m y)) h
  rw [eval_det5poly, map_zero] at this
  have hI : (Matrix.of fun r s => vvec (qOf (specPt m y)) m (c s) r) = 1 := by
    ext r s
    simp [vvec_specPt hm, y, Matrix.one_apply, hc.eq_iff]
  rw [det5, hI, Matrix.det_one] at this
  exact one_ne_zero this

lemma detApoly_ne_zero {m : Fin 6 → Word} (hm : IsMatching m) {P : Finset (Fin 6)}
    (h1 : P.Nonempty) (h2 : P ≠ Finset.univ) {c : Fin 4 → Fin 6}
    (hc : Function.Injective c) : detApoly m P c ≠ 0 := by
  intro h
  obtain ⟨r₀, hr₀⟩ := uvec_exists_ne h1 h2
  let y : Fin 6 → Fin 5 → ℝ := fun i r => if ∃ t, c t = i ∧ r = r₀.succAbove t then 1 else 0
  have hy : ∀ t r, y (c t) r = if r = r₀.succAbove t then 1 else 0 := by
    intro t r
    simp only [y, hc.eq_iff]
    congr 1
    apply propext
    constructor
    · rintro ⟨t', rfl, h⟩; exact h
    · intro h; exact ⟨t, rfl, h⟩
  have := congrArg (eval (specPt m y)) h
  rw [eval_detApoly, map_zero, detA, Matrix.det_succ_row (n := 4) _ r₀, Fin.sum_univ_succ] at this
  have hrest : ∀ t : Fin 4, (Matrix.of fun r s => (Fin.cons (uvec P)
      (fun t => vvec (qOf (specPt m y)) m (c t)) : Fin 5 → Fin 5 → ℝ) s r) r₀ t.succ = 0 := by
    intro t
    simp [vvec_specPt hm, hy, (Fin.succAbove_ne r₀ t).symm]
  simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at this
  have hsub : (Matrix.of fun r s => (Fin.cons (uvec P)
      (fun t => vvec (qOf (specPt m y)) m (c t)) : Fin 5 → Fin 5 → ℝ) s r).submatrix
      r₀.succAbove (Fin.succAbove 0) = 1 := by
    ext r t
    simp [vvec_specPt hm, hy, Matrix.one_apply]
  rw [hsub, Matrix.det_one] at this
  simp at this
  exact hr₀ this

lemma detAffpoly_ne_zero {m : Fin 6 → Word} (hm : IsMatching m) : detAffpoly m ≠ 0 := by
  intro h
  let y : Fin 6 → Fin 5 → ℝ := fun i r => if i = r.castSucc then 1 else 0
  have := congrArg (eval (specPt m y)) h
  rw [eval_detAffpoly, map_zero, detAff, Matrix.det_succ_column _ (Fin.last 5),
    Fin.sum_univ_succ] at this
  have hrest : ∀ i : Fin 5, (Matrix.of fun r s => (Fin.cons 1
      (vvec (qOf (specPt m y)) m s) : Fin 6 → ℝ) r) i.succ (Fin.last 5) = 0 := by
    intro i
    have : (5 : Fin 6) ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
    simp [vvec_specPt hm, y, this]
  simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.succAbove_last] at this
  have hsub : (Matrix.of fun r s => (Fin.cons 1
      (vvec (qOf (specPt m y)) m s) : Fin 6 → ℝ) r).submatrix
      (Fin.succAbove 0) Fin.castSucc = 1 := by
    ext r t
    simp [vvec_specPt hm, y, Matrix.one_apply, eq_comm]
  rw [hsub, Matrix.det_one] at this
  norm_num at this

/-! ### Existence of generic data -/

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **Lemma 2 (genericity).** Some choice of the 36 initial reals is generic for every
matching simultaneously. -/
theorem exists_generic : ∃ q, IsGeneric q := by
  let S1 : Finset ((Fin 6 → Word) × (Fin 5 → Fin 6)) :=
    Finset.univ.filter (fun p => IsMatching p.1 ∧ Function.Injective p.2)
  let S2 : Finset ((Fin 6 → Word) × Finset (Fin 6) × (Fin 4 → Fin 6)) :=
    Finset.univ.filter (fun p => IsMatching p.1 ∧ p.2.1.Nonempty ∧ p.2.1 ≠ Finset.univ ∧
      Function.Injective p.2.2)
  let S3 : Finset (Fin 6 → Word) := Finset.univ.filter IsMatching
  let F : MvPolynomial Var ℝ := (∏ p ∈ S1, det5poly p.1 p.2) *
    (∏ p ∈ S2, detApoly p.1 p.2.1 p.2.2) * ∏ m ∈ S3, detAffpoly m
  have hF : F ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      simp only [S1, Finset.mem_filter] at hp
      exact det5poly_ne_zero hp.2.1 hp.2.2
    · refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      simp only [S2, Finset.mem_filter] at hp
      exact detApoly_ne_zero hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    · refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      simp only [S3, Finset.mem_filter] at hp
      exact detAffpoly_ne_zero hp.2
  obtain ⟨x, hx⟩ : ∃ x, eval x F ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF (MvPolynomial.funext fun x => by simp [hcon x])
  simp only [F, map_mul, map_prod] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := (mul_ne_zero_iff.1 hx).imp_left mul_ne_zero_iff.1
  refine ⟨qOf x, ⟨?_, ?_, ?_⟩⟩
  · intro m hm c hc
    have := (Finset.prod_ne_zero_iff.1 h1) (m, c) (by simp [S1, hm, hc])
    rwa [eval_det5poly] at this
  · intro m hm P hP1 hP2 c hc
    have := (Finset.prod_ne_zero_iff.1 h2) (m, P, c) (by simp [S2, hm, hP1, hP2, hc])
    rwa [eval_detApoly] at this
  · intro m hm
    have := (Finset.prod_ne_zero_iff.1 h3) m (by simp [S3, hm])
    rwa [eval_detAffpoly] at this

end Tverberg6R
