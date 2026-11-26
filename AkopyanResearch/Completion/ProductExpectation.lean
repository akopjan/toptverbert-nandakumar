module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

/-!
# Finite product expectations and active coordinates

The weights are real and normalized in each coordinate; nonnegativity is not
needed for these algebraic identities. A function depending only on a specified
set of active coordinates has the same expectation for any two weight systems
that agree there. If the active weights are point masses, the expectation is
the corresponding evaluation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AkopyanResearch.ProductExpectation

variable {C L : Type*} [Fintype C] [Fintype L] [DecidableEq C]

/-- The expectation of a function on words under a product of finite weights. -/
def expectation (u : C → L → ℝ) (H : (C → L) → ℝ) : ℝ :=
  ∑ w : C → L, (∏ c : C, u c (w c)) * H w

/-- A function on words depends only on coordinates satisfying `p`. -/
def DependsOn {V : Type*} (p : C → Prop) (H : (C → L) → V) : Prop :=
  ∀ w w', (∀ c, p c → w c = w' c) → H w = H w'

/-- The total mass of a normalized product of finite weights is one. -/
theorem sum_product_weights (u : C → L → ℝ)
    (hu : ∀ c, ∑ l : L, u c l = 1) :
    (∑ w : C → L, ∏ c : C, u c (w c)) = 1 := by
  rw [← Fintype.prod_sum]
  simp_rw [hu]
  simp

theorem expectation_const (u : C → L → ℝ)
    (hu : ∀ c, ∑ l : L, u c l = 1) (a : ℝ) :
    expectation u (fun _ => a) = a := by
  unfold expectation
  rw [← Finset.sum_mul, sum_product_weights u hu, one_mul]

omit [Fintype L] in
/-- Replacing one inactive coordinate at a time is sufficient for full
dependence only on the active coordinates. -/
theorem dependsOn_of_update_invariant {V : Type*} (p : C → Prop)
    (H : (C → L) → V)
    (hupdate : ∀ c, ¬p c → ∀ w l, H (Function.update w c l) = H w) :
    DependsOn p H := by
  classical
  have aux (t : Finset C) :
      ∀ w w' : C → L, (∀ c, c ∉ t → w c = w' c) →
        (∀ c, p c → w c = w' c) → H w = H w' := by
    induction t using Finset.induction with
    | empty =>
      intro w w' hout _
      have hw : w = w' := by
        funext c
        exact hout c (by simp)
      rw [hw]
    | @insert c t hct ih =>
      intro w w' hout hactive
      let w₁ : C → L := Function.update w c (w' c)
      have hval : H w₁ = H w := by
        by_cases hc : p c
        · have heq := hactive c hc
          simp [w₁, ← heq]
        · exact hupdate c hc w (w' c)
      calc
        H w = H w₁ := hval.symm
        _ = H w' := by
          apply ih w₁ w'
          · intro j hj
            by_cases hjc : j = c
            · subst j
              simp [w₁]
            · have ho := hout j (by simp [hjc, hj])
              simpa [w₁, hjc] using ho
          · intro j hj
            by_cases hjc : j = c
            · subst j
              simp [w₁]
            · simpa [w₁, hjc] using hactive j hj
  intro w w' hactive
  exact aux Finset.univ w w' (by simp) hactive

/-- Summing out all inactive coordinates leaves the expectation over the
active coordinates alone. The arbitrary background word is used only outside
the active set, where the value of `H` does not depend on it. -/
theorem expectation_restrict (u : C → L → ℝ)
    (hu : ∀ c, ∑ l : L, u c l = 1) (p : C → Prop) [DecidablePred p]
    (H : (C → L) → ℝ) (hH : DependsOn p H) (w₀ : C → L) :
    expectation u H =
      ∑ a : {c : C // p c} → L,
        (∏ c : {c : C // p c}, u c (a c)) *
          H (fun c => if hc : p c then a ⟨c, hc⟩ else w₀ c) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : C => L)
  let merge (a : {c : C // p c} → L) (b : {c : C // ¬p c} → L) : C → L :=
    fun c => if hc : p c then a ⟨c, hc⟩ else b ⟨c, hc⟩
  have hsplit (a : {c : C // p c} → L) (b : {c : C // ¬p c} → L) :
      (∏ c : C, u c (merge a b c)) =
        (∏ c : {c : C // p c}, u c (a c)) *
          ∏ c : {c : C // ¬p c}, u c (b c) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype p (fun c => u c (merge a b c))]
    congr 1
    · apply Finset.prod_congr rfl
      intro c _
      simp only [merge, dite_eq_left c.property]
    · apply Finset.prod_congr rfl
      intro c _
      simp only [merge, dite_eq_right c.property]
  have hvalue (a : {c : C // p c} → L) (b : {c : C // ¬p c} → L) :
      H (merge a b) = H (merge a (fun c => w₀ c)) := by
    apply hH
    intro c hc
    simp [merge, hc]
  have hmass :
      (∑ b : {c : C // ¬p c} → L,
        ∏ c : {c : C // ¬p c}, u c (b c)) = 1 :=
    sum_product_weights (fun c : {c : C // ¬p c} => u c) (fun c => hu c)
  unfold expectation
  calc
    (∑ w : C → L, (∏ c : C, u c (w c)) * H w) =
        ∑ ab : ({c : C // p c} → L) × ({c : C // ¬p c} → L),
          (∏ c : C, u c (e.symm ab c)) * H (e.symm ab) :=
      (Equiv.sum_comp e.symm (fun w : C → L => (∏ c : C, u c (w c)) * H w)).symm
    _ = ∑ a : {c : C // p c} → L,
        (∏ c : {c : C // p c}, u c (a c)) *
          H (fun c => if hc : p c then a ⟨c, hc⟩ else w₀ c) := by
      rw [Fintype.sum_prod_type]
      change (∑ a : {c : C // p c} → L,
        ∑ b : {c : C // ¬p c} → L,
          (∏ c : C, u c (merge a b c)) * H (merge a b)) = _
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [hsplit, hvalue]
      calc
        (∑ b : {c : C // ¬p c} → L,
          ((∏ c : {c : C // p c}, u c (a c)) *
            ∏ c : {c : C // ¬p c}, u c (b c)) *
              H (merge a (fun c => w₀ c))) =
            ((∏ c : {c : C // p c}, u c (a c)) *
              H (merge a (fun c => w₀ c))) *
                ∑ b : {c : C // ¬p c} → L,
                  ∏ c : {c : C // ¬p c}, u c (b c) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ac_rfl
        _ = _ := by rw [hmass, mul_one]

/-- Normalized weights outside the active set do not affect the expectation. -/
theorem expectation_congr_of_dependsOn (u v : C → L → ℝ)
    (hu : ∀ c, ∑ l : L, u c l = 1) (hv : ∀ c, ∑ l : L, v c l = 1)
    (p : C → Prop) (H : (C → L) → ℝ) (hH : DependsOn p H)
    (huv : ∀ c, p c → u c = v c) : expectation u H = expectation v H := by
  classical
  rcases isEmpty_or_nonempty (C → L) with hempty | hnonempty
  · simp [expectation]
  · let w₀ : C → L := Classical.choice hnonempty
    rw [expectation_restrict u hu p H hH w₀, expectation_restrict v hv p H hH w₀]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    exact congrFun (huv c c.property) (a c)

/-- Point-mass weights on all active coordinates make the expectation an
evaluation. The weights on inactive coordinates may be any normalized weights. -/
theorem expectation_eq_of_dirac_on [DecidableEq L] (u : C → L → ℝ)
    (hu : ∀ c, ∑ l : L, u c l = 1) (p : C → Prop)
    (H : (C → L) → ℝ) (hH : DependsOn p H) (w₀ : C → L)
    (hdirac : ∀ c, p c → ∀ l, u c l = if l = w₀ c then 1 else 0) :
    expectation u H = H w₀ := by
  unfold expectation
  calc
    (∑ w : C → L, (∏ c : C, u c (w c)) * H w) =
        ∑ w : C → L, (∏ c : C, u c (w c)) * H w₀ := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : (∏ c : C, u c (w c)) = 0
      · simp [hw]
      · congr 1
        apply hH
        intro c hc
        have hentry : u c (w c) ≠ 0 := by
          intro hz
          exact hw (Finset.prod_eq_zero (Finset.mem_univ c) hz)
        rw [hdirac c hc] at hentry
        by_contra hne
        simp [hne] at hentry
    _ = (∑ w : C → L, ∏ c : C, u c (w c)) * H w₀ := by
      rw [Finset.sum_mul]
    _ = H w₀ := by rw [sum_product_weights u hu, one_mul]

end AkopyanResearch.ProductExpectation


end
