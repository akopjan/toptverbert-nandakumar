module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic


@[expose] public section

/-!
An explicit based contraction of the complex unit circle inside the unit
quaternions, together with the quaternion double-angle rotation formula.

This file checks the algebra and continuity of the belt-trick formula.
It does not assert a Pontryagin--Thom theorem, a framed-bordism classification,
or the null-homotopy of an arbitrary map from S¹⁴ to S¹³.
-/

open scoped Quaternion

namespace QuaternionBelt

def j : ℍ := ⟨0, 0, 1, 0⟩

noncomputable def q (s : ℝ) (z : ℂ) : ℍ :=
  Real.sqrt (1 - s ^ 2) • (z : ℍ) + s • j

noncomputable def contraction (s : ℝ) (z : ℂ) : ℍ :=
  star (q s 1) * q s z

lemma q_normSq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {z : ℂ} (hz : Complex.normSq z = 1) :
    Quaternion.normSq (q s z) = 1 := by
  have hnonneg : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hsqrt := Real.sq_sqrt hnonneg
  have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hz
  calc
    Quaternion.normSq (q s z) =
        Real.sqrt (1 - s ^ 2) ^ 2 * (z.re ^ 2 + z.im ^ 2) + s ^ 2 := by
      simp [q, j, Quaternion.normSq_def']
      ring
    _ = 1 := by rw [hsqrt, hz']; ring

lemma contraction_normSq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {z : ℂ} (hz : Complex.normSq z = 1) :
    Quaternion.normSq (contraction s z) = 1 := by
  simp only [contraction, map_mul, Quaternion.normSq_star]
  rw [q_normSq hs0 hs1 (by norm_num : Complex.normSq (1 : ℂ) = 1),
    q_normSq hs0 hs1 hz, one_mul]

lemma contraction_norm {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {z : ℂ} (hz : Complex.normSq z = 1) : ‖contraction s z‖ = 1 := by
  have h := contraction_normSq hs0 hs1 hz
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg (contraction s z)]

lemma contraction_zero (z : ℂ) : contraction 0 z = (z : ℍ) := by
  ext <;> simp [contraction, q, j]

lemma contraction_one (z : ℂ) : contraction 1 z = 1 := by
  ext <;> simp [contraction, q, j]

lemma contraction_base {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    contraction s 1 = 1 := by
  rw [contraction, Quaternion.star_mul_self,
    q_normSq hs0 hs1 (by norm_num : Complex.normSq (1 : ℂ) = 1)]
  simp

lemma continuous_q : Continuous (fun p : ℝ × ℂ => q p.1 p.2) := by
  have hcoe : Continuous (fun z : ℂ => (z : ℍ)) :=
    Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional
  unfold q
  exact ((by fun_prop : Continuous (fun p : ℝ × ℂ => Real.sqrt (1 - p.1 ^ 2))).smul
    (hcoe.comp continuous_snd)).add (continuous_fst.smul continuous_const)

lemma continuous_contraction : Continuous (fun p : ℝ × ℂ => contraction p.1 p.2) := by
  have hanchor : Continuous (fun p : ℝ × ℂ => q p.1 1) :=
    continuous_q.comp (continuous_fst.prodMk continuous_const)
  exact hanchor.star.mul continuous_q

def imaginary (x y z : ℝ) : ℍ := ⟨0, x, y, z⟩

lemma complex_conjugation_formula (a b x y z : ℝ) :
    (⟨a, b, 0, 0⟩ : ℍ) * imaginary x y z * star (⟨a, b, 0, 0⟩ : ℍ) =
      imaginary ((a ^ 2 + b ^ 2) * x)
        ((a ^ 2 - b ^ 2) * y - 2 * a * b * z)
        (2 * a * b * y + (a ^ 2 - b ^ 2) * z) := by
  ext <;> simp [imaginary] <;> ring

lemma complex_unit_conjugation_formula {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (x y z : ℝ) :
    (⟨a, b, 0, 0⟩ : ℍ) * imaginary x y z * star (⟨a, b, 0, 0⟩ : ℍ) =
      imaginary x ((a ^ 2 - b ^ 2) * y - 2 * a * b * z)
        (2 * a * b * y + (a ^ 2 - b ^ 2) * z) := by
  simpa [hab] using complex_conjugation_formula a b x y z

def rotation (u : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![u.re ^ 2 + u.imI ^ 2 - u.imJ ^ 2 - u.imK ^ 2,
      2 * (u.imI * u.imJ - u.re * u.imK),
      2 * (u.imI * u.imK + u.re * u.imJ);
    2 * (u.imI * u.imJ + u.re * u.imK),
      u.re ^ 2 - u.imI ^ 2 + u.imJ ^ 2 - u.imK ^ 2,
      2 * (u.imJ * u.imK - u.re * u.imI);
    2 * (u.imI * u.imK - u.re * u.imJ),
      2 * (u.imJ * u.imK + u.re * u.imI),
      u.re ^ 2 - u.imI ^ 2 - u.imJ ^ 2 + u.imK ^ 2]

lemma rotation_transpose_mul (u : ℍ) :
    Matrix.transpose (rotation u) * rotation u = Quaternion.normSq u ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_three, Quaternion.normSq_def'] <;> ring

lemma det_rotation (u : ℍ) : (rotation u).det = Quaternion.normSq u ^ 3 := by
  simp [rotation, Matrix.det_fin_three, Quaternion.normSq_def']
  ring

lemma rotation_mem_specialOrthogonalGroup {u : ℍ} (hu : Quaternion.normSq u = 1) :
    rotation u ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  constructor
  · simpa [hu] using rotation_transpose_mul u
  · simp [det_rotation, hu]

lemma continuous_rotation : Continuous rotation := by
  have h0 := Quaternion.continuous_re
  have h1 := Quaternion.continuous_imI
  have h2 := Quaternion.continuous_imJ
  have h3 := Quaternion.continuous_imK
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotation, Matrix.of_apply] <;> fun_prop

@[simp] lemma rotation_one : rotation (1 : ℍ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

noncomputable def rotationHomotopy (s : ℝ) (z : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rotation (contraction s z)

lemma continuous_rotationHomotopy :
    Continuous (fun p : ℝ × ℂ => rotationHomotopy p.1 p.2) :=
  continuous_rotation.comp continuous_contraction

lemma rotationHomotopy_mem {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {z : ℂ} (hz : Complex.normSq z = 1) :
    rotationHomotopy s z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  rotation_mem_specialOrthogonalGroup (contraction_normSq hs0 hs1 hz)

@[simp] lemma rotationHomotopy_one (z : ℂ) : rotationHomotopy 1 z = 1 := by
  simp [rotationHomotopy, contraction_one]

lemma rotationHomotopy_base {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    rotationHomotopy s 1 = 1 := by
  simp [rotationHomotopy, contraction_base hs0 hs1]

lemma rotationHomotopy_zero {z : ℂ} (hz : Complex.normSq z = 1) :
    rotationHomotopy 0 z =
      !![1, 0, 0;
        0, z.re ^ 2 - z.im ^ 2, -(2 * z.re * z.im);
        0, 2 * z.re * z.im, z.re ^ 2 - z.im ^ 2] := by
  have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationHomotopy, contraction_zero, rotation, hz'] <;> ring

end QuaternionBelt
