module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.SplitIfs

/-!
# Retraction onto the codimension-two skeleton of a simplex

On the boundary, subtract the second-smallest barycentric coordinate,
truncate at zero, and normalize the sum. The denominator vanishes
precisely at the barycentres of the facets. The resulting continuous
map fixes every point with two zero coordinates.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.deprecated false
noncomputable section

namespace AkopyanResearch.SimplexSkeletonRetraction

open scoped Topology
open Finset

variable (n : ℕ)

abbrev Index := Fin (n + 2)
abbrev Simplex := stdSimplex ℝ (Index n)

def Pairs := {ij : Index n × Index n // ij.1 ≠ ij.2}

instance : Fintype (Pairs n) := inferInstanceAs (Fintype {ij : Index n × Index n // _})
instance : Nonempty (Pairs n) := ⟨⟨(0, 1), by simp⟩⟩

def skeleton : Set (Simplex n) := {p | ∃ i j, i ≠ j ∧ p.val i = 0 ∧ p.val j = 0}
def boundary : Set (Simplex n) := {p | ∃ i, p.val i = 0}

def second (p : Simplex n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ij : Pairs n =>
    max (p.val ij.val.1) (p.val ij.val.2))

theorem second_nonneg (p : Simplex n) : 0 ≤ second n p := by
  apply Finset.le_inf'
  intro ij _
  exact (p.property.1 ij.val.1).trans (le_max_left _ _)

theorem second_le (p : Simplex n) (i j : Index n) (hij : i ≠ j) :
    second n p ≤ max (p.val i) (p.val j) :=
  Finset.inf'_le _ (Finset.mem_univ (⟨(i, j), hij⟩ : Pairs n))

theorem second_attained (p : Simplex n) :
    ∃ i j : Index n, i ≠ j ∧ second n p = max (p.val i) (p.val j) := by
  obtain ⟨ij, _, hij⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun ij : Pairs n => max (p.val ij.val.1) (p.val ij.val.2))
  exact ⟨ij.val.1, ij.val.2, ij.property, hij⟩

@[fun_prop]
theorem continuous_second : Continuous (second n) := by
  apply Continuous.finset_inf'_apply
  intro ij _
  exact ((continuous_apply ij.val.1).comp continuous_subtype_val).max
    ((continuous_apply ij.val.2).comp continuous_subtype_val)

def weight (p : Simplex n) (i : Index n) : ℝ := max (p.val i - second n p) 0
def mass (p : Simplex n) : ℝ := ∑ i, weight n p i

theorem weight_nonneg (p : Simplex n) (i : Index n) : 0 ≤ weight n p i :=
  le_max_right _ _

@[fun_prop]
theorem continuous_weight (i : Index n) : Continuous (fun p : Simplex n => weight n p i) := by
  exact (((continuous_apply i).comp continuous_subtype_val).sub
    (continuous_second n)).max continuous_const

@[fun_prop]
theorem continuous_mass : Continuous (mass n) :=
  continuous_finsetSum _ (fun i _ => continuous_weight n i)

theorem mass_nonneg (p : Simplex n) : 0 ≤ mass n p :=
  Finset.sum_nonneg fun i _ => weight_nonneg n p i

/-- The barycentre of the facet opposite `k`. -/
def faceCenter (k : Index n) : Simplex n :=
  ⟨fun i => if i = k then 0 else (n + 1 : ℝ)⁻¹, by
    constructor
    · intro i
      dsimp only
      split_ifs <;> positivity
    · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      simp only [ite_true, add_zero]
      have h : ∀ i ∈ Finset.univ.erase k,
          (if i = k then (0 : ℝ) else (n + 1 : ℝ)⁻¹) = (n + 1 : ℝ)⁻¹ := by
        intro i hi
        exact if_neg (Finset.mem_erase.mp hi).1
      rw [Finset.sum_congr rfl h, Finset.sum_const]
      simp [nsmul_eq_mul]
      field_simp⟩

@[simp]
theorem faceCenter_same (k : Index n) : (faceCenter n k).val k = 0 := by
  simp [faceCenter]

@[simp]
theorem faceCenter_other (k i : Index n) (hi : i ≠ k) :
    (faceCenter n k).val i = (n + 1 : ℝ)⁻¹ := by
  simp [faceCenter, hi]

def puncturedBoundary : Set (Simplex n) :=
  {p | p ∈ boundary n ∧ ∀ k, p ≠ faceCenter n k}

theorem mass_pos (p : puncturedBoundary n) : 0 < mass n p.val := by
  apply lt_of_le_of_ne (mass_nonneg n p.val)
  intro hz
  have hw (i : Index n) : weight n p.val i = 0 := by
    have hi := Finset.single_le_sum (fun j _ => weight_nonneg n p.val j)
      (Finset.mem_univ i)
    apply le_antisymm _ (weight_nonneg n p.val i)
    change weight n p.val i ≤ mass n p.val at hi
    rwa [← hz] at hi
  obtain ⟨k, hk⟩ := p.property.1
  have he (i : Index n) (hi : i ≠ k) : p.val.val i = second n p.val := by
    have hupper : p.val.val i ≤ second n p.val := by
      have h := le_max_left (p.val.val i - second n p.val) 0
      change p.val.val i - second n p.val ≤ weight n p.val i at h
      rw [hw i] at h
      linarith
    have hlower := second_le n p.val k i hi.symm
    rw [hk, max_eq_right (p.val.property.1 i)] at hlower
    exact le_antisymm hupper hlower
  have hsum : (n + 1 : ℝ) * second n p.val = 1 := by
    have hs := p.val.property.2
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hk, add_zero] at hs
    have h : ∀ i ∈ Finset.univ.erase k, p.val.val i = second n p.val := by
      intro i hi
      exact he i (Finset.mem_erase.mp hi).1
    rw [Finset.sum_congr rfl h, Finset.sum_const] at hs
    simpa [nsmul_eq_mul] using hs
  have hv : second n p.val = (n + 1 : ℝ)⁻¹ := by
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [hsum, mul_inv_cancel₀ hn]
  apply p.property.2 k
  apply Subtype.ext
  funext i
  by_cases hi : i = k
  · subst i
    simpa using hk
  · rw [faceCenter_other n k i hi, he i hi, hv]

/-- The normalized truncated coordinates. -/
def retract (p : puncturedBoundary n) : skeleton n :=
  ⟨⟨fun i => weight n p.val i / mass n p.val, by
      constructor
      · intro i
        exact div_nonneg (weight_nonneg n p.val i) (mass_nonneg n p.val)
      · rw [← Finset.sum_div]
        exact div_self (ne_of_gt (mass_pos n p))⟩, by
    obtain ⟨i, j, hij, he⟩ := second_attained n p.val
    refine ⟨i, j, hij, ?_, ?_⟩
    · have hle : p.val.val i ≤ second n p.val := by rw [he]; exact le_max_left _ _
      simp [weight, max_eq_right (sub_nonpos.mpr hle)]
    · have hle : p.val.val j ≤ second n p.val := by rw [he]; exact le_max_right _ _
      simp [weight, max_eq_right (sub_nonpos.mpr hle)]⟩

@[fun_prop]
theorem continuous_retract : Continuous (retract n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply ((continuous_weight n i).comp continuous_subtype_val).div
    ((continuous_mass n).comp continuous_subtype_val)
  exact fun p => ne_of_gt (mass_pos n p)

theorem second_eq_zero (p : skeleton n) : second n p.val = 0 := by
  obtain ⟨i, j, hij, hi, hj⟩ := p.property
  apply le_antisymm _ (second_nonneg n p.val)
  simpa [hi, hj] using second_le n p.val i j hij

/-- The skeleton contains no deleted facet barycentre. -/
def inclusion (p : skeleton n) : puncturedBoundary n :=
  ⟨p.val, by
    obtain ⟨i, j, hij, hi, hj⟩ := p.property
    refine ⟨⟨i, hi⟩, ?_⟩
    intro k hk
    have hzero : (n + 1 : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    by_cases hik : i = k
    · have hjk : j ≠ k := by intro he; exact hij (hik.trans he.symm)
      have := congrArg (fun q : Simplex n => q.val j) hk
      rw [hj, faceCenter_other n k j hjk] at this
      exact hzero this.symm
    · have := congrArg (fun q : Simplex n => q.val i) hk
      rw [hi, faceCenter_other n k i hik] at this
      exact hzero this.symm⟩

@[fun_prop]
theorem continuous_inclusion : Continuous (inclusion n) :=
  continuous_subtype_val.subtype_mk _

theorem retract_inclusion (p : skeleton n) : retract n (inclusion n p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  have hw (i : Index n) : weight n p.val i = p.val.val i := by
    rw [weight, second_eq_zero, sub_zero, max_eq_left (p.val.property.1 i)]
  have hm : mass n p.val = 1 := by
    unfold mass
    simpa only [hw] using p.val.property.2
  funext i
  change weight n p.val i / mass n p.val = p.val.val i
  rw [hw, hm, div_one]

def retractionMap : C(puncturedBoundary n, skeleton n) :=
  ⟨retract n, continuous_retract n⟩

def inclusionMap : C(skeleton n, puncturedBoundary n) :=
  ⟨inclusion n, continuous_inclusion n⟩

theorem retraction_identity : (retractionMap n).comp (inclusionMap n) =
    ContinuousMap.id (skeleton n) := by
  apply ContinuousMap.ext
  intro p
  exact retract_inclusion n p

end AkopyanResearch.SimplexSkeletonRetraction
