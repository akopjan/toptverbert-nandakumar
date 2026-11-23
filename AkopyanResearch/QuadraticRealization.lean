module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
# Elementary analytic infrastructure for quadratic height tables

This file does not assert existence of a safe height table. It supplies a continuous
retraction to a standard simplex and a continuous quadratic realization map.
All safety assumptions, when used, are explicit hypotheses.
-/

noncomputable section

namespace AkopyanResearch

set_option linter.unusedSectionVars false

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The standard simplex, in the coordinate convention used by the project. -/
def coordinateSimplex (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

def positiveMass (z : I → ℝ) : ℝ := ∑ i, max (z i) 0

/-- Retraction onto the simplex, with all missing mass placed at `i₀`. -/
def simplexRetraction (i₀ : I) (z : I → ℝ) (i : I) : ℝ :=
  max (z i) 0 / max 1 (positiveMass z) +
    if i = i₀ then 1 - positiveMass z / max 1 (positiveMass z) else 0

theorem positiveMass_nonneg (z : I → ℝ) : 0 ≤ positiveMass z := by
  exact Finset.sum_nonneg (fun i _ => le_max_right (z i) 0)

theorem simplexRetraction_den_pos (z : I → ℝ) :
    0 < max 1 (positiveMass z) :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem simplexRetraction_mem (i₀ : I) (z : I → ℝ) :
    simplexRetraction i₀ z ∈ coordinateSimplex I := by
  have hd := simplexRetraction_den_pos z
  have hs : positiveMass z / max 1 (positiveMass z) ≤ 1 :=
    (div_le_one hd).2 (le_max_right _ _)
  constructor
  · intro i
    unfold simplexRetraction
    apply add_nonneg (div_nonneg (le_max_right _ _) hd.le)
    split_ifs <;> linarith
  · simp only [simplexRetraction, Finset.sum_add_distrib]
    rw [← Finset.sum_div]
    simp only [positiveMass, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

theorem simplexRetraction_eq_self (i₀ : I) {z : I → ℝ}
    (hz : z ∈ coordinateSimplex I) : simplexRetraction i₀ z = z := by
  have hp : positiveMass z = 1 := by
    simpa only [positiveMass, max_eq_left (hz.1 _)] using hz.2
  funext i
  simp [simplexRetraction, hp, max_eq_left (hz.1 i)]

theorem continuous_positiveMass : Continuous (positiveMass (I := I)) := by
  unfold positiveMass
  fun_prop

theorem continuous_simplexRetraction (i₀ : I) : Continuous (simplexRetraction i₀) := by
  apply continuous_pi
  intro i
  have hd : ∀ z : I → ℝ, max 1 (positiveMass z) ≠ 0 :=
    fun z => ne_of_gt (simplexRetraction_den_pos z)
  unfold simplexRetraction
  have hden : Continuous (fun z : I → ℝ => max 1 (positiveMass z)) :=
    continuous_const.max continuous_positiveMass
  have hquot : Continuous (fun z : I → ℝ => positiveMass z / max 1 (positiveMass z)) :=
    continuous_positiveMass.div hden hd
  have hcoord : Continuous (fun z : I → ℝ => max (z i) 0 / max 1 (positiveMass z)) :=
    ((continuous_apply i).max continuous_const).div hden hd
  split_ifs <;> fun_prop

/-- A continuous map to the simplex subtype, usable to extend coefficients globally. -/
def simplexRetractionMap (i₀ : I) : C(I → ℝ, coordinateSimplex I) where
  toFun z := ⟨simplexRetraction i₀ z, simplexRetraction_mem i₀ z⟩
  continuous_toFun := (continuous_simplexRetraction i₀).subtype_mk _

section Quadratic

variable {C L K : Type*} [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] [Fintype K]

def colorMass (x : C → L → ℝ) (i : C) : ℝ := ∑ a, x i a

theorem continuous_colorMass : Continuous (colorMass (C := C) (L := L)) := by
  unfold colorMass
  fun_prop

/-- A point supported at one vertex of every active color. -/
def pureColorPoint (massVec : C → ℝ) (w : C → L) (i : C) (a : L) : ℝ :=
  if a = w i then massVec i else 0

@[simp] theorem colorMass_pureColorPoint (massVec : C → ℝ) (w : C → L) :
    colorMass (pureColorPoint massVec w) = massVec := by
  funext i
  simp [colorMass, pureColorPoint]

/-- Linear and two-color coefficients. An arbitrary finite relation selects the color pairs. -/
def quadraticHeight (pairs : Finset (C × C))
    (A : (C → ℝ) → C → L → K → ℝ)
    (B : (C → ℝ) → C → C → L → L → K → ℝ)
    (x : C → L → ℝ) (t : K) : ℝ :=
  (∑ i, ∑ a, x i a * A (colorMass x) i a t) +
    ∑ ij ∈ pairs, ∑ a, ∑ b,
      x ij.1 a * x ij.2 b * B (colorMass x) ij.1 ij.2 a b t

/-- Evaluation on a word, with the mass factors explicit. -/
def quadraticTable (pairs : Finset (C × C))
    (A : (C → ℝ) → C → L → K → ℝ)
    (B : (C → ℝ) → C → C → L → L → K → ℝ)
    (massVec : C → ℝ) (w : C → L) (t : K) : ℝ :=
  (∑ i, massVec i * A massVec i (w i) t) +
    ∑ ij ∈ pairs, massVec ij.1 * massVec ij.2 * B massVec ij.1 ij.2 (w ij.1) (w ij.2) t

theorem continuous_quadraticHeight (pairs : Finset (C × C))
    (A : (C → ℝ) → C → L → K → ℝ)
    (B : (C → ℝ) → C → C → L → L → K → ℝ)
    (hA : ∀ i a t, Continuous (fun massVec => A massVec i a t))
    (hB : ∀ i j a b t, Continuous (fun massVec => B massVec i j a b t)) :
    Continuous (quadraticHeight pairs A B) := by
  have hcoord (i : C) (a : L) : Continuous (fun x : C → L → ℝ => x i a) := by
    fun_prop
  apply continuous_pi
  intro t
  unfold quadraticHeight
  apply Continuous.add
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro a _
    exact (hcoord i a).mul
      ((hA i a t).comp continuous_colorMass)
  · apply continuous_finsetSum
    intro ij _
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro b _
    exact ((hcoord ij.1 a).mul (hcoord ij.2 b)).mul
      ((hB ij.1 ij.2 a b t).comp continuous_colorMass)

theorem quadraticHeight_pureColorPoint (pairs : Finset (C × C))
    (A : (C → ℝ) → C → L → K → ℝ)
    (B : (C → ℝ) → C → C → L → L → K → ℝ)
    (massVec : C → ℝ) (w : C → L) :
    quadraticHeight pairs A B (pureColorPoint massVec w) = quadraticTable pairs A B massVec w := by
  funext t
  simp [quadraticHeight, quadraticTable, pureColorPoint, mul_ite, ite_mul,
    Finset.sum_ite_eq']

/-- Equal row masses and disjoint nonnegative supports force a permutation matrix,
scaled by the common mass. The statement includes mass zero. -/
theorem equal_mass_disjoint_matrix [Nonempty L] (y : L → L → ℝ) (m : ℝ)
    (hnonneg : ∀ j a, 0 ≤ y j a)
    (hrow : ∀ j, ∑ a, y j a = m)
    (hdisj : ∀ j l, j ≠ l → ∀ a, y j a = 0 ∨ y l a = 0) :
    ∃ σ : Equiv.Perm L, ∀ j a, y j a = if a = σ j then m else 0 := by
  classical
  by_cases hm : m = 0
  · refine ⟨Equiv.refl L, ?_⟩
    intro j a
    have hzero : ∑ b, y j b = 0 := by simpa [hm] using hrow j
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg j b)).mp hzero
    have hya := hz a (Finset.mem_univ a)
    simp [hya, hm]
  · have hmnonneg : 0 ≤ m := by
      obtain ⟨j⟩ := ‹Nonempty L›
      rw [← hrow j]
      exact Finset.sum_nonneg (fun a _ => hnonneg j a)
    have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hm)
    have hex (j : L) : ∃ a, 0 < y j a := by
      have hs : 0 < ∑ a, y j a := by rw [hrow j]; exact hmpos
      obtain ⟨a, _, ha⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun a _ => hnonneg j a)).mp hs
      exact ⟨a, ha⟩
    let f : L → L := fun j => Classical.choose (hex j)
    have hf (j : L) : 0 < y j (f j) := Classical.choose_spec (hex j)
    have hinj : Function.Injective f := by
      intro j l hfl
      by_contra hjl
      rcases hdisj j l hjl (f j) with hj | hl
      · exact (ne_of_gt (hf j)) hj
      · have hz : y l (f l) = 0 := by simpa [hfl] using hl
        exact (ne_of_gt (hf l)) hz
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
    have hoff (j a : L) (ha : a ≠ f j) : y j a = 0 := by
      obtain ⟨l, hl⟩ := hsurj a
      have hjl : j ≠ l := by
        intro h
        apply ha
        simpa [← h] using hl.symm
      rcases hdisj j l hjl a with h | h
      · exact h
      · have hz : y l (f l) = 0 := by simpa [hl] using h
        exact False.elim ((ne_of_gt (hf l)) hz)
    have hon (j : L) : y j (f j) = m := by
      rw [← hrow j]
      symm
      exact Finset.sum_eq_single (f j) (fun a _ ha => hoff j a ha) (by simp)
    refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
    intro j a
    change y j a = if a = f j then m else 0
    split_ifs with ha
    · simpa [ha] using hon j
    · exact hoff j a ha

/-- The combinatorial step used to realize a safe table, without expanding its words. -/
theorem equal_masses_disjoint_are_pure [Nonempty L]
    (x : L → C → L → ℝ) (massVec : C → ℝ)
    (hnonneg : ∀ j i a, 0 ≤ x j i a)
    (hmass : ∀ j, colorMass (x j) = massVec)
    (hdisj : ∀ j l, j ≠ l → ∀ i a, x j i a = 0 ∨ x l i a = 0) :
    ∃ σ : C → Equiv.Perm L,
      ∀ j, x j = pureColorPoint massVec (fun i => σ i j) := by
  classical
  have hex (i : C) := equal_mass_disjoint_matrix (fun j a => x j i a) (massVec i)
    (fun j a => hnonneg j i a)
    (fun j => congrFun (hmass j) i)
    (fun j l hjl a => hdisj j l hjl i a)
  let σ : C → Equiv.Perm L := fun i => Classical.choose (hex i)
  refine ⟨σ, ?_⟩
  intro j
  funext i a
  exact Classical.choose_spec (hex i) j a

/-- Safety for the small quadratic formula. It is an explicit hypothesis, not an axiom. -/
def QuadraticSafe (j₀ : L) (pairs : Finset (C × C))
    (A : (C → ℝ) → C → L → K → ℝ)
    (B : (C → ℝ) → C → C → L → L → K → ℝ) : Prop :=
  ∀ massVec ∈ coordinateSimplex C, ∀ σ : C → Equiv.Perm L,
    ∃ j, quadraticTable pairs A B massVec (fun i => σ i j) ≠
      quadraticTable pairs A B massVec (fun i => σ i j₀)

/-- A safe quadratic certificate rules out a common height at a common mass. -/
theorem quadraticHeight_no_common_value [Nonempty L] (j₀ : L)
    (pairs : Finset (C × C))
    (A : (C → ℝ) → C → L → K → ℝ)
    (B : (C → ℝ) → C → C → L → L → K → ℝ)
    (hsafe : QuadraticSafe j₀ pairs A B)
    (x : L → C → L → ℝ) (massVec : C → ℝ)
    (hmassVec : massVec ∈ coordinateSimplex C)
    (hnonneg : ∀ j i a, 0 ≤ x j i a)
    (hmass : ∀ j, colorMass (x j) = massVec)
    (hdisj : ∀ j l, j ≠ l → ∀ i a, x j i a = 0 ∨ x l i a = 0) :
    ∃ j, quadraticHeight pairs A B (x j) ≠ quadraticHeight pairs A B (x j₀) := by
  obtain ⟨σ, hσ⟩ := equal_masses_disjoint_are_pure x massVec hnonneg hmass hdisj
  obtain ⟨j, hj⟩ := hsafe massVec hmassVec σ
  refine ⟨j, ?_⟩
  simpa only [hσ, quadraticHeight_pureColorPoint] using hj

end Quadratic

section TargetNinety

abbrev LinearCoefficients := (Fin 15 → ℝ) → Fin 15 → Fin 6 → Fin 2 → ℝ
abbrev PairCoefficients :=
  (Fin 15 → ℝ) → Fin 15 → Fin 15 → Fin 6 → Fin 6 → Fin 2 → ℝ

/-- The canonical identification of ninety vertices with fifteen colors of six vertices. -/
def splitNinety (x : Fin 90 → ℝ) (i : Fin 15) (a : Fin 6) : ℝ :=
  x (finProdFinEquiv (i, a))

theorem continuous_splitNinety : Continuous splitNinety := by
  unfold splitNinety
  fun_prop

theorem sum_colorMass_splitNinety (x : Fin 90 → ℝ) :
    ∑ i, colorMass (splitNinety x) i = ∑ v, x v := by
  simp only [colorMass, splitNinety]
  calc
    _ = ∑ p : Fin 15 × Fin 6, x (finProdFinEquiv p) :=
      (Fintype.sum_prod_type (fun p : Fin 15 × Fin 6 => x (finProdFinEquiv p))).symm
    _ = _ := Equiv.sum_comp (finProdFinEquiv : Fin 15 × Fin 6 ≃ Fin 90) x

theorem colorMass_splitNinety_mem {x : Fin 90 → ℝ}
    (hx : x ∈ coordinateSimplex (Fin 90)) :
    colorMass (splitNinety x) ∈ coordinateSimplex (Fin 15) := by
  constructor
  · intro i
    exact Finset.sum_nonneg (fun a _ => hx.1 _)
  · rw [sum_colorMass_splitNinety, hx.2]

/-- The final formula has fourteen mass coordinates and two height coordinates. -/
def quadraticMapNinety (pairs : Finset (Fin 15 × Fin 15))
    (A : LinearCoefficients) (B : PairCoefficients) (x : Fin 90 → ℝ) : Fin 16 → ℝ :=
  fun v => Fin.addCases (m := 14) (n := 2) (motive := fun _ => ℝ)
    (fun i : Fin 14 => colorMass (splitNinety x) i.castSucc)
    (quadraticHeight pairs A B (splitNinety x)) v

theorem continuous_quadraticMapNinety (pairs : Finset (Fin 15 × Fin 15))
    (A : LinearCoefficients) (B : PairCoefficients)
    (hA : ∀ i a t, Continuous (fun massVec => A massVec i a t))
    (hB : ∀ i j a b t, Continuous (fun massVec => B massVec i j a b t)) :
    Continuous (quadraticMapNinety pairs A B) := by
  apply continuous_pi
  intro v
  refine Fin.addCases (m := 14) (n := 2) (fun i => ?_) (fun t => ?_) v
  · simp only [quadraticMapNinety, Fin.addCases_left]
    exact (continuous_apply i.castSucc).comp
      (continuous_colorMass.comp continuous_splitNinety)
  · simp only [quadraticMapNinety, Fin.addCases_right]
    exact (continuous_apply t).comp
      ((continuous_quadraticHeight pairs A B hA hB).comp continuous_splitNinety)

/-- This is exactly the support-disjointness condition in the question. -/
def SixDisjointSupports (x : Fin 6 → Fin 90 → ℝ) : Prop :=
  ∀ j l, j ≠ l → ∀ v, x j v = 0 ∨ x l v = 0

/-- The complete analytic reduction, conditional only on a safe quadratic certificate.

The hypothesis `hsafe` is the unsolved existence input. This theorem does not construct it.
-/
theorem quadraticMapNinety_isAlmostSix
    (pairs : Finset (Fin 15 × Fin 15)) (A : LinearCoefficients) (B : PairCoefficients)
    (hA : ∀ i a t, Continuous (fun massVec => A massVec i a t))
    (hB : ∀ i j a b t, Continuous (fun massVec => B massVec i j a b t))
    (hsafe : QuadraticSafe (0 : Fin 6) pairs A B) :
    Continuous (quadraticMapNinety pairs A B) ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ j, x j ∈ coordinateSimplex (Fin 90)) → SixDisjointSupports x →
        ∃ j, quadraticMapNinety pairs A B (x j) ≠ quadraticMapNinety pairs A B (x 0) := by
  refine ⟨continuous_quadraticMapNinety pairs A B hA hB, ?_⟩
  intro x hx hdisj
  by_contra h
  have heq : ∀ j, quadraticMapNinety pairs A B (x j) =
      quadraticMapNinety pairs A B (x 0) := by
    intro j
    by_contra hj
    exact h ⟨j, hj⟩
  have hprefix (j : Fin 6) (i : Fin 14) :
      colorMass (splitNinety (x j)) i.castSucc =
        colorMass (splitNinety (x 0)) i.castSucc := by
    have hh := congrFun (heq j) (Fin.castAdd 2 i)
    simpa only [quadraticMapNinety, Fin.addCases_left] using hh
  have hmass (j : Fin 6) : colorMass (splitNinety (x j)) =
      colorMass (splitNinety (x 0)) := by
    funext i
    refine Fin.lastCases ?_ (fun a => hprefix j a) i
    have hj := (colorMass_splitNinety_mem (hx j)).2
    have hzero := (colorMass_splitNinety_mem (hx 0)).2
    rw [Fin.sum_univ_castSucc] at hj hzero
    have hp : (∑ a : Fin 14, colorMass (splitNinety (x j)) a.castSucc) =
        ∑ a : Fin 14, colorMass (splitNinety (x 0)) a.castSucc := by
      exact Finset.sum_congr rfl (fun a _ => hprefix j a)
    linarith
  obtain ⟨j, hj⟩ := quadraticHeight_no_common_value (0 : Fin 6) pairs A B hsafe
    (fun j => splitNinety (x j)) (colorMass (splitNinety (x 0)))
    (colorMass_splitNinety_mem (hx 0))
    (fun j i a => (hx j).1 _) hmass
    (fun j l hjl i a => hdisj j l hjl _)
  apply hj
  funext t
  have hh := congrFun (heq j) (Fin.natAdd 14 t)
  simpa only [quadraticMapNinety, Fin.addCases_right] using hh

end TargetNinety

section SimplexCoefficients

abbrev MassSimplex := coordinateSimplex (Fin 15)
abbrev SimplexLinearCoefficients := MassSimplex → Fin 15 → Fin 6 → Fin 2 → ℝ
abbrev SimplexPairCoefficients :=
  MassSimplex → Fin 15 → Fin 15 → Fin 6 → Fin 6 → Fin 2 → ℝ

def extendLinearCoefficients (A : SimplexLinearCoefficients) : LinearCoefficients :=
  fun massVec => A (simplexRetractionMap (0 : Fin 15) massVec)

def extendPairCoefficients (B : SimplexPairCoefficients) : PairCoefficients :=
  fun massVec => B (simplexRetractionMap (0 : Fin 15) massVec)

/-- The certificate may be given only on the compact mass simplex. -/
def simplexCertificateTable (pairs : Finset (Fin 15 × Fin 15))
    (A : SimplexLinearCoefficients) (B : SimplexPairCoefficients)
    (massVec : MassSimplex) (w : Fin 15 → Fin 6) (t : Fin 2) : ℝ :=
  (∑ i, massVec.val i * A massVec i (w i) t) +
    ∑ ij ∈ pairs, massVec.val ij.1 * massVec.val ij.2 *
      B massVec ij.1 ij.2 (w ij.1) (w ij.2) t

theorem quadraticTable_extended (pairs : Finset (Fin 15 × Fin 15))
    (A : SimplexLinearCoefficients) (B : SimplexPairCoefficients)
    (massVec : MassSimplex) (w : Fin 15 → Fin 6) :
    quadraticTable pairs (extendLinearCoefficients A) (extendPairCoefficients B)
      massVec.val w = simplexCertificateTable pairs A B massVec w := by
  have hfix : simplexRetractionMap (0 : Fin 15) massVec.val = massVec := by
    apply Subtype.ext
    exact simplexRetraction_eq_self (0 : Fin 15) massVec.property
  funext t
  simp only [quadraticTable, simplexCertificateTable, extendLinearCoefficients,
    extendPairCoefficients, hfix]

/-- A continuous safe certificate on the mass simplex suffices for the exact
ambient map required in the question. The safety certificate remains an
explicit hypothesis; this file does not prove its existence. -/
theorem exists_almostSix_of_simplex_quadratic_certificate
    (pairs : Finset (Fin 15 × Fin 15))
    (A : SimplexLinearCoefficients) (B : SimplexPairCoefficients)
    (hA : ∀ i a t, Continuous (fun massVec => A massVec i a t))
    (hB : ∀ i j a b t, Continuous (fun massVec => B massVec i j a b t))
    (hsafe : ∀ massVec : MassSimplex, ∀ σ : Fin 15 → Equiv.Perm (Fin 6),
      ∃ j, simplexCertificateTable pairs A B massVec (fun i => σ i j) ≠
        simplexCertificateTable pairs A B massVec (fun i => σ i 0)) :
    ∃ g : (Fin 90 → ℝ) → (Fin 16 → ℝ), Continuous g ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ j, x j ∈ coordinateSimplex (Fin 90)) → SixDisjointSupports x →
        ∃ j, g (x j) ≠ g (x 0) := by
  have hA' : ∀ i a t,
      Continuous (fun massVec => extendLinearCoefficients A massVec i a t) := by
    intro i a t
    exact (hA i a t).comp (simplexRetractionMap (0 : Fin 15)).continuous
  have hB' : ∀ i j a b t,
      Continuous (fun massVec => extendPairCoefficients B massVec i j a b t) := by
    intro i j a b t
    exact (hB i j a b t).comp (simplexRetractionMap (0 : Fin 15)).continuous
  have hs : QuadraticSafe (0 : Fin 6) pairs
      (extendLinearCoefficients A) (extendPairCoefficients B) := by
    intro massVec hmassVec σ
    obtain ⟨j, hj⟩ := hsafe ⟨massVec, hmassVec⟩ σ
    refine ⟨j, ?_⟩
    simpa only [quadraticTable_extended pairs A B ⟨massVec, hmassVec⟩] using hj
  exact ⟨quadraticMapNinety pairs (extendLinearCoefficients A) (extendPairCoefficients B),
    quadraticMapNinety_isAlmostSix pairs _ _ hA' hB' hs⟩

end SimplexCoefficients

end AkopyanResearch
