module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Extracted from Submission/Model/SphereConnected.lean, section Boundary,
at upstream commit c66523531ff172d7f41913d94e56921e790a1b47.
-/
public import Submission.Approximation.Simplex

@[expose] public section
open scoped unitInterval Topology Topology.Homotopy
namespace Submission

section Boundary

variable {n N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A grid vertex contributing at a boundary point of the cube is itself a boundary point. -/
theorem gridVertex_mem_boundary_of_gridCoeff_pos (hN : 1 ≤ N) {v : Fin n → ℕ} {y : I^ Fin n}
    {j : Fin n} (hj : y j = 0 ∨ y j = 1) (hv : v ∈ activeVerts N y) :
    gridVertex N v ∈ Cube.boundary (Fin n) := by
  obtain ⟨hvmem, hvpos⟩ := mem_activeVerts.mp hv
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have habs := abs_lt.mp (abs_sub_lt_one_of_gridCoeff_pos hvpos j)
  have hcoe := coe_gridVertex hN hvmem j
  refine ⟨j, ?_⟩
  rcases hj with h0 | h1
  · left
    have hyj : ((y j : ℝ)) = 0 := congrArg Subtype.val h0
    rw [hyj, mul_zero] at habs
    have hlt : (v j : ℝ) < 1 := by linarith [habs.1]
    have : v j = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hlt)
    refine Subtype.ext ?_
    rw [hcoe, this]
    simp
  · right
    have hyj : ((y j : ℝ)) = 1 := congrArg Subtype.val h1
    rw [hyj, mul_one] at habs
    have hlt : (v j : ℝ) < (N : ℝ) + 1 := by linarith [habs.1]
    have hgt : (N : ℝ) - 1 < (v j : ℝ) := by linarith [habs.2]
    have h1' : v j < N + 1 := by exact_mod_cast hlt
    have h2' : N ≤ v j := by
      by_contra hc
      have : (v j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_le hc)
      linarith
    have hvN : v j = N := by omega
    refine Subtype.ext ?_
    rw [hcoe, hvN, div_self (ne_of_gt hN')]
    simp

/-- The piecewise-affine approximation of a map which is constant on the boundary of the cube is
constant on the boundary, with the same value.  This is what makes the approximation homotopy a
homotopy *relative to the cube boundary*. -/
theorem cubeGridAffineApprox_eq_of_mem_boundary (hN : 1 ≤ N) (g : C(I^ Fin n, V)) {b : V}
    (hg : ∀ z ∈ Cube.boundary (Fin n), g z = b) {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) : cubeGridAffineApprox n N g y = b := by
  obtain ⟨j, hj⟩ := hy
  have hval : ∀ v ∈ activeVerts N y, g (gridVertex N v) = b := fun v hv =>
    hg _ (gridVertex_mem_boundary_of_gridCoeff_pos hN hj hv)
  rw [cubeGridAffineApprox_eq_sum_activeVerts,
    Finset.sum_congr rfl (fun v hv => by rw [hval v hv]), ← Finset.sum_smul,
    sum_gridCoeff_activeVerts hN, one_smul]

end Boundary

end Submission
