module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
Noncommutative algebra for a colored-join chain filler.

In the geometric application `R` is an endomorphism ring of the augmented
total chain module, `d` is the differential, and `s i` inserts the chosen
vertex of color `i`. This file proves the operator identity only; the signed
simplex formula for each insertion and the active-color support statement
are separate combinatorial hypotheses of the application.
-/

namespace ChainTelescoping

variable {R : Type*} [Ring R]

def defect (d s : R) : R := 1 - d * s - s * d

lemma defect_identity (d s : R) : d * s + s * d = 1 - defect d s := by
  unfold defect
  noncomm_ring

lemma defect_commutes {d : R} (hdd : d * d = 0) (s : R) :
    d * defect d s = defect d s * d := by
  have h : d * defect d s - defect d s * d = -(d * d) * s + s * (d * d) := by
    unfold defect
    noncomm_ring
  rw [hdd, neg_zero, zero_mul, mul_zero, add_zero] at h
  exact sub_eq_zero.mp h

def partialProduct (d : R) (s : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => partialProduct d s n * defect d (s n)

def filler (d : R) (s : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => filler d s n + partialProduct d s n * s n

lemma prefix_commutes {d : R} (hdd : d * d = 0) (s : ℕ → R) (n : ℕ) :
    d * partialProduct d s n = partialProduct d s n * d := by
  induction n with
  | zero => simp [partialProduct]
  | succ n ih =>
      calc
        d * partialProduct d s (n + 1) = (d * partialProduct d s n) * defect d (s n) := by
          simp [partialProduct, mul_assoc]
        _ = (partialProduct d s n * d) * defect d (s n) := by rw [ih]
        _ = partialProduct d s n * (defect d (s n) * d) := by
          rw [mul_assoc, defect_commutes hdd]
        _ = partialProduct d s (n + 1) * d := by simp [partialProduct, mul_assoc]

lemma homotopy_step (d k p s q : R)
    (hcomm : d * p = p * d)
    (hk : d * k + k * d = 1 - p)
    (hs : d * s + s * d = 1 - q) :
    d * (k + p * s) + (k + p * s) * d = 1 - p * q := by
  calc
    d * (k + p * s) + (k + p * s) * d =
        (d * k + k * d) + p * (d * s + s * d) := by
      rw [mul_add, add_mul, ← mul_assoc d p s, hcomm]
      noncomm_ring
    _ = (1 - p) + p * (1 - q) := by rw [hk, hs]
    _ = 1 - p * q := by noncomm_ring

theorem filler_identity {d : R} (hdd : d * d = 0) (s : ℕ → R) (n : ℕ) :
    d * filler d s n + filler d s n * d = 1 - partialProduct d s n := by
  induction n with
  | zero => simp [filler, partialProduct]
  | succ n ih =>
      exact homotopy_step d (filler d s n) (partialProduct d s n) (s n)
        (defect d (s n)) (prefix_commutes hdd s n) ih (defect_identity d (s n))

theorem filler_contracts_when_prefix_zero {d : R} (hdd : d * d = 0)
    (s : ℕ → R) (n : ℕ) (hprefix : partialProduct d s n = 0) :
    d * filler d s n + filler d s n * d = 1 := by
  simpa [hprefix] using filler_identity hdd s n

/-- The useful graded application is pointwise: the product need only
annihilate the chosen cycle, not the entire total chain module. -/
theorem fills_cycle {M : Type*} [AddCommGroup M]
    {d : Module.End ℤ M} (hdd : d * d = 0)
    (s : ℕ → Module.End ℤ M) (n : ℕ) (x : M)
    (hcycle : d x = 0) (hproduct : (partialProduct d s n) x = 0) :
    d ((filler d s n) x) = x := by
  have h := congrArg (fun f : Module.End ℤ M => f x) (filler_identity hdd s n)
  simpa [hcycle, hproduct] using h

end ChainTelescoping
