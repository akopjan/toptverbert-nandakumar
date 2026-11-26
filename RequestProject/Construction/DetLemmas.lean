module

public import Mathlib.LinearAlgebra.Matrix.Block
public import RequestProject.Cochain

@[expose] public section

/-!
# Determinant identities for local signs

`det_frame_eq`: if `y` (with `∑ y = 1`) solves `∑ yₛ zₛ = 0` and the columns `D i` have zero
sum, then the `5 × 5` matrix `∑ₛ D i s • zₛ` has determinant `-det(affMat z) * det [D | y]`.
-/

open Matrix

namespace Tverberg6R

@[simp] lemma snoc_six_five {α : Type*} (D : Fin 5 → α) (y : α) :
    (Fin.snoc D y : Fin 6 → α) 5 = y := Fin.snoc_last (α := fun _ => α) y D

@[simp] lemma castSucc_ne_five (i : Fin 5) : i.castSucc ≠ (5 : Fin 6) :=
  (Fin.castSucc_lt_last i).ne

@[simp] lemma five_ne_castSucc (i : Fin 5) : (5 : Fin 6) ≠ i.castSucc :=
  (Fin.castSucc_lt_last i).ne'

/-- The `6 × 6` matrix with columns `D 0, …, D 4, y`. -/
def snocMat (D : Fin 5 → Fin 6 → ℝ) (y : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun s j => (Fin.snoc D y : Fin 6 → Fin 6 → ℝ) j s

lemma det_frame_eq (z : Fin 6 → Fin 5 → ℝ) (D : Fin 5 → Fin 6 → ℝ) (y : Fin 6 → ℝ)
    (hD : ∀ i, ∑ s, D i s = 0) (hy1 : ∑ s, y s = 1) (hy0 : ∑ s, y s • z s = 0) :
    (Matrix.of fun r i => ∑ s, D i s * z s r).det =
      - (affMat z).det * (snocMat D y).det := by
  set N := affMat z * snocMat D y with hN
  have hdetN : N.det = (affMat z).det * (snocMat D y).det := Matrix.det_mul _ _
  have hlast : ∀ i, N i (Fin.last 5) = (Pi.single 0 1 : Fin 6 → ℝ) i := by
    intro i
    refine Fin.cases ?_ (fun r => ?_) i
    · simp [hN, affMat, snocMat, Matrix.mul_apply, hy1]
    · have := congrFun hy0 r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp [hN, affMat, snocMat, Matrix.mul_apply]
      simpa [mul_comm] using this
  have hsub : N.submatrix Fin.succ Fin.castSucc = Matrix.of fun r i => ∑ s, D i s * z s r := by
    ext r i
    simp [hN, affMat, snocMat, Matrix.mul_apply, mul_comm]
  have hexp := Matrix.det_succ_column N (Fin.last 5)
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => by rw [hlast]; simp)] at hexp
  rw [hlast] at hexp
  simp only [Fin.val_zero, Fin.val_last, Pi.single_eq_same, Fin.succAbove_zero,
    Fin.succAbove_last, mul_one, add_zero] at hexp
  rw [hsub] at hexp
  norm_num at hexp
  linarith

/-- Adding a combination of the first five columns to the last one. -/
lemma det_snocMat_add (D : Fin 5 → Fin 6 → ℝ) (y : Fin 6 → ℝ) (c : Fin 5 → ℝ) :
    (snocMat D (y + ∑ i, c i • D i)).det = (snocMat D y).det := by
  have h : snocMat D (y + ∑ i, c i • D i) = snocMat D y *
      (1 + Matrix.of fun a b => if b = Fin.last 5 then (Fin.snoc c 0 : Fin 6 → ℝ) a else 0) := by
    ext s j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have e : ∑ x : Fin 6, (Fin.snoc D y : Fin 6 → Fin 6 → ℝ) x s *
          (Fin.snoc c 0 : Fin 6 → ℝ) x = ∑ i, c i * D i s := by
        rw [Fin.sum_univ_castSucc]; simp [mul_comm]
      simp [snocMat, Matrix.mul_apply, e]
    · simp [snocMat, Matrix.mul_apply, Fin.snoc_castSucc, (Fin.castSucc_lt_last i).ne]
  rw [h, Matrix.det_mul]
  have hU : (1 + Matrix.of fun a b => if b = Fin.last 5 then
      (Fin.snoc c 0 : Fin 6 → ℝ) a else (0 : ℝ)).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      refine Fin.lastCases ?_ (fun l => ?_) i
      · simp
      · simp [(Fin.castSucc_lt_last l).ne]
    · intro a b hab
      have hb : b ≠ Fin.last 5 := fun h => by
        subst h; exact absurd hab (not_lt.2 (Fin.le_last a))
      have hb' : b ≠ 5 := hb
      have hab' : a ≠ b := ne_of_gt (by simpa using hab)
      simp [Matrix.one_apply, hb', hab']
  rw [hU, mul_one]

end Tverberg6R
