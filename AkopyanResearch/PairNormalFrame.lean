module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
Euclidean normal-frame calculation for the pair anti-diagonal.

The geometric application takes `U = ℝ⁸`, `W = ℝ⁶`, with unit vectors
`f : U` and `w : W`. The forward map exchanges the line `ℝ f` in `U`
with the missing radial line `ℝ w` in the orthogonal space `wᗮ`.
No tubular-neighborhood, degree, or obstruction theorem is asserted here.
-/

open scoped InnerProductSpace

namespace PairNormalFrame

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

noncomputable def forward (f : U) (w : W) (x : U) (z : W) : W × U :=
  (z + ⟪f, x⟫_ℝ • w, x - ⟪f, x⟫_ℝ • f)

noncomputable def backward (f : U) (w : W) (y : W) (u : U) : U × W :=
  (u + ⟪w, y⟫_ℝ • f, y - ⟪w, y⟫_ℝ • w)

lemma forward_perpendicular {f : U} (hf : ‖f‖ = 1) (w : W) (x : U) (z : W) :
    ⟪f, (forward f w x z).2⟫_ℝ = 0 := by
  simp [forward, inner_sub_right, inner_smul_right, hf]

lemma backward_perpendicular (f : U) {w : W} (hw : ‖w‖ = 1) (y : W) (u : U) :
    ⟪w, (backward f w y u).2⟫_ℝ = 0 := by
  simp [backward, inner_sub_right, inner_smul_right, hw]

lemma backward_forward {f : U} {w z : W} (hw : ‖w‖ = 1)
    (hz : ⟪w, z⟫_ℝ = 0) (x : U) :
    backward f w (forward f w x z).1 (forward f w x z).2 = (x, z) := by
  simp [forward, backward, inner_add_right, inner_smul_right, hw, hz]

lemma forward_backward {f u : U} {w : W} (hf : ‖f‖ = 1)
    (hu : ⟪f, u⟫_ℝ = 0) (y : W) :
    forward f w (backward f w y u).1 (backward f w y u).2 = (y, u) := by
  simp [forward, backward, inner_add_right, inner_smul_right, hf, hu]

lemma forward_norm_sq {f : U} {w z : W}
    (hf : ‖f‖ = 1) (hw : ‖w‖ = 1) (hz : ⟪w, z⟫_ℝ = 0) (x : U) :
    ‖(forward f w x z).1‖ ^ 2 + ‖(forward f w x z).2‖ ^ 2 =
      ‖x‖ ^ 2 + ‖z‖ ^ 2 := by
  have hzw : ⟪z, w⟫_ℝ = 0 := by simpa [real_inner_comm] using hz
  simp [forward, norm_add_sq_real, norm_sub_sq_real, norm_smul,
    Real.norm_eq_abs, inner_smul_right, real_inner_comm x f, hzw, hf, hw]
  ring

lemma continuous_forward (f : U) :
    Continuous (fun p : (W × U) × W => forward f p.1.1 p.1.2 p.2) := by
  unfold forward
  fun_prop

lemma continuous_backward (f : U) :
    Continuous (fun p : (W × W) × U => backward f p.1.1 p.1.2 p.2) := by
  unfold backward
  fun_prop

section Naturality

variable {U' W' : Type*}
  [NormedAddCommGroup U'] [InnerProductSpace ℝ U']
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W']

/-- The two exchanged lines may both change by the same sign. -/
lemma forward_natural (A : U →ₗ[ℝ] U') (B : W →ₗ[ℝ] W')
    (f : U) (f' : U') (w : W) (w' : W') (σ : ℝ)
    (hf : A f = σ • f') (hw : B w = σ • w')
    (hinner : ∀ x, ⟪f', A x⟫_ℝ = σ * ⟪f, x⟫_ℝ)
    (x : U) (z : W) :
    forward f' w' (A x) (B z) =
      (B (forward f w x z).1, A (forward f w x z).2) := by
  simp only [forward, hinner, map_add, map_sub, map_smul, hf, hw, smul_smul]
  rw [mul_comm σ]

end Naturality

end PairNormalFrame
