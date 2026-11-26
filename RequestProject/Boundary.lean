module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import RequestProject.Generic

@[expose] public section

/-!
# The additive table `H⁰` and the anchors (Corollary 3 and Lemma 4)

* `H0 q` is continuous and boundary compatible;
* for generic `q`, `H0 q` is safe on the boundary of the mass simplex;
* the two-level anchors `anchorTable j₀ A` have matching-independent normal vectors
  `uvec P`, and every convex combination of an anchor with `H0 q λ`, where `λ` has at least
  two vanishing masses, is safe.
-/

open Matrix

namespace Tverberg6R

/-- The additive table `H⁰(λ) w = ∑ i, λ i * q i (w i)`. -/
noncomputable def H0 (q : Fin 6 → Fin 6 → ℝ) (l : Fin 6 → ℝ) : Table :=
  fun w => ∑ i, l i * q i (w i)

lemma continuous_H0 (q : Fin 6 → Fin 6 → ℝ) : Continuous (H0 q) :=
  continuous_pi fun w => by unfold H0; fun_prop

lemma compatible_H0 (q : Fin 6 → Fin 6 → ℝ) : Compatible (H0 q) := by
  intro l _ i hi u v huv
  simp only [H0]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp [hi]
  · rw [huv j hj]

lemma ell_H0 (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (l : Fin 6 → ℝ) :
    ell m (H0 q l) = ∑ i, l i • vvec q m i := by
  funext r
  simp [ell, H0, vvec, colorTable, ← Finset.sum_sub_distrib, mul_sub]

/-- A table whose normal vector along `m` is nonzero is not constant along `m`. -/
lemma exists_ne_of_ell_ne {m : Fin 6 → Word} {T : Table} (h : ell m T ≠ 0) :
    ∃ j, T (m j) ≠ T (m 0) := by
  by_contra hc
  push_neg at hc
  apply h
  funext r
  simp [ell, hc]

/-- Columns with nonzero determinant are linearly independent. -/
lemma coeff_eq_zero_of_det_ne_zero {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hd : (Matrix.of fun r s => w s r).det ≠ 0) (a : Fin n → ℝ)
    (h : ∑ s, a s • w s = 0) : a = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero hd
  funext r
  have := congrFun h r
  simpa [mulVec, dotProduct, mul_comm] using this

/-- **Corollary 3.** For generic data, `H⁰` is safe on the boundary of the mass simplex. -/
theorem ell_H0_ne_zero_of_boundary {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q)
    {l : Fin 6 → ℝ} (hl : l ∈ massSimplex) {k : Fin 6} (hk : l k = 0)
    {m : Fin 6 → Word} (hm : IsMatching m) : ell m (H0 q l) ≠ 0 := by
  intro h0
  rw [ell_H0, Fin.sum_univ_succAbove _ k, hk, zero_smul, zero_add] at h0
  have hz := coeff_eq_zero_of_det_ne_zero (fun s => vvec q m (k.succAbove s))
    (hq.five m hm _ (Fin.succAbove_right_injective)) (fun s => l (k.succAbove s)) h0
  have hsum := hl.2
  rw [Fin.sum_univ_succAbove _ k, hk] at hsum
  simp [show ∀ s, l (k.succAbove s) = 0 from fun s => congrFun hz s] at hsum

/-! ### Anchors -/

/-- The two-level anchor table attached to the color `j₀` and the label set `A`. -/
def anchorTable (j₀ : Fin 6) (A : Finset (Fin 6)) : Table :=
  fun w => 6 * (if w j₀ ∈ A then 1 else 0) - A.card

/-- The rows of a matching whose `j₀`-label lies in `A`. -/
def rowSet (m : Fin 6 → Word) (j₀ : Fin 6) (A : Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ.filter fun r => m r j₀ ∈ A

lemma ell_anchorTable (m : Fin 6 → Word) (j₀ : Fin 6) (A : Finset (Fin 6)) :
    ell m (anchorTable j₀ A) = uvec (rowSet m j₀ A) := by
  funext r
  simp only [ell, anchorTable, uvec, rowSet, Finset.mem_filter, Finset.mem_univ, true_and]
  ring

lemma card_rowSet {m : Fin 6 → Word} (hm : IsMatching m) (j₀ : Fin 6) (A : Finset (Fin 6)) :
    (rowSet m j₀ A).card = A.card := by
  have hbij : Function.Bijective (fun r => m r j₀) :=
    (Finite.injective_iff_bijective).mp (hm j₀)
  let e := Equiv.ofBijective _ hbij
  have : rowSet m j₀ A = A.map e.symm.toEmbedding := by
    ext r
    simp only [rowSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_symm]
    rfl
  rw [this, Finset.card_map]

/-- **Lemma 4 (anchor cones are safe).** A combination `a • anchor + H⁰(λ)` with
`a + ∑ λ = 1`, where `λ` has two vanishing masses, has nonzero normal vector along every
matching (in particular every convex combination of an anchor with such an `H⁰(λ)` is safe). -/
theorem ell_anchor_H0_ne_zero {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q)
    {m : Fin 6 → Word} (hm : IsMatching m) (j₀ : Fin 6) {A : Finset (Fin 6)}
    (hA1 : 1 ≤ A.card) (hA5 : A.card ≤ 5) {a : ℝ} {l : Fin 6 → ℝ}
    (hsum : a + ∑ i, l i = 1) {k₁ k₂ : Fin 6} (hk : k₁ ≠ k₂)
    (h₁ : l k₁ = 0) (h₂ : l k₂ = 0) :
    ell m (fun w => a * anchorTable j₀ A w + H0 q l w) ≠ 0 := by
  classical
  set S : Finset (Fin 6) := Finset.univ \ {k₁, k₂} with hS
  have hScard : S.card = 4 := by
    rw [hS, Finset.card_univ_diff, Finset.card_pair hk]; simp
  let c : Fin 4 → Fin 6 := S.orderEmbOfFin hScard
  have hc : Function.Injective c := (S.orderEmbOfFin hScard).injective
  set P := rowSet m j₀ A
  have hP1 : P.Nonempty := by
    rw [← Finset.card_pos, card_rowSet hm]; omega
  have hP2 : P ≠ Finset.univ := by
    intro h
    have := card_rowSet hm j₀ A
    rw [show rowSet m j₀ A = Finset.univ from h] at this
    simp at this
    omega
  have hSmap : S = Finset.univ.map (S.orderEmbOfFin hScard).toEmbedding := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · intro hi
      have : i ∈ Set.range (S.orderEmbOfFin hScard) := by
        rw [Finset.range_orderEmbOfFin]; exact hi
      exact this
    · rintro ⟨t, rfl⟩
      exact Finset.orderEmbOfFin_mem _ _ _
  have hsplit : ∀ {β : Type} [AddCommMonoid β] (f : Fin 6 → β), (∀ i, i ∉ S → f i = 0) →
      ∑ i, f i = ∑ t, f (c t) := by
    intro β _ f hf
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hf i hi)]
    conv_lhs => rw [hSmap]
    rw [Finset.sum_map]
    rfl
  have hzero : ∀ i, i ∉ S → l i = 0 := by
    intro i hi
    simp only [hS, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_not] at hi
    rcases hi with rfl | rfl <;> assumption
  intro h0
  have hell : ell m (fun w => a * anchorTable j₀ A w + H0 q l w) =
      a • uvec P + ∑ i, l i • vvec q m i := by
    rw [← ell_anchorTable, ← ell_H0]
    funext r
    simp only [ell, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hell, hsplit (fun i => l i • vvec q m i)
    (fun i hi => by simp [hzero i hi])] at h0
  have hz := coeff_eq_zero_of_det_ne_zero
    (Fin.cons (uvec P) (fun t => vvec q m (c t)) : Fin 5 → Fin 5 → ℝ)
    (hq.anchor m hm P hP1 hP2 c hc) (Fin.cons a (fun t => l (c t)))
    (by rw [Fin.sum_univ_succ]; simpa using h0)
  have ha0 : a = 0 := by simpa using congrFun hz 0
  have hl0 : ∀ t, l (c t) = 0 := fun t => by simpa using congrFun hz t.succ
  rw [hsplit l hzero] at hsum
  simp [ha0, hl0] at hsum

end Tverberg6R
