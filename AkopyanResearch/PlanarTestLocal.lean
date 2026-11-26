module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity


@[expose] public section

/-!
Local zero calculation for an equivariant planar test.
This file does not assert existence of the requested almost-six-embedding.
-/

open scoped InnerProductSpace ContDiff
open Metric

namespace PlanarTestLocal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def capChart (c v : E) : E := stereoInvFunAux (-c) v

lemma capChart_zero (c : E) : capChart c 0 = c := by
  simp [capChart, stereoInvFunAux]

lemma hasFDerivAt_capChart (c : E) :
    HasFDerivAt (capChart c) (ContinuousLinearMap.id ℝ E) 0 := by
  exact hasFDerivAt_stereoInvFunAux (-c)

lemma contDiff_capChart (c : E) {n : ℕ∞ω} : ContDiff ℝ n (capChart c) := by
  exact contDiff_stereoInvFunAux

lemma norm_capChart {c v : E} (hc : ‖c‖ = 1) (hv : ⟪c, v⟫_ℝ = 0) :
    ‖capChart c v‖ = 1 := by
  have hv' : v ∈ (ℝ ∙ (-c))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simpa using hv
  have h := stereoInvFunAux_mem (v := -c) (by simpa using hc) hv'
  simpa [capChart, mem_sphere_zero_iff_norm] using h

lemma capChart_eq_center_iff {c v : E} (hc : ‖c‖ = 1)
    (hv : ⟪c, v⟫_ℝ = 0) : capChart c v = c ↔ v = 0 := by
  constructor
  · intro h
    have hd : ‖v‖ ^ 2 + 4 ≠ 0 := by positivity
    have hi := congrArg (fun x : E => ⟪c, x⟫_ℝ) h
    simp only [capChart, stereoInvFunAux, inner_smul_right, inner_add_right,
      inner_neg_right, hv, real_inner_self_eq_norm_sq, hc] at hi
    have hn : ‖v‖ = 0 := by
      field_simp at hi
      nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hn
  · rintro rfl
    exact capChart_zero c

noncomputable def twist (b v : E) (a η : ℝ) : E :=
  v - (2 * a * η * ⟪b, v⟫_ℝ) • b

lemma inner_twist {b c v : E} (hcb : ⟪c, b⟫_ℝ = 0)
    (hcv : ⟪c, v⟫_ℝ = 0) (a η : ℝ) :
    ⟪c, twist b v a η⟫_ℝ = 0 := by
  simp [twist, inner_sub_right, inner_smul_right, hcb, hcv]

lemma twist_one_eq_zero_iff {b v : E} (hb : ‖b‖ = 1) :
    twist b v 1 1 = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hi := congrArg (fun x : E => ⟪b, x⟫_ℝ) h
    simp only [twist, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      hb, inner_zero_right] at hi
    have hbi : ⟪b, v⟫_ℝ = 0 := by nlinarith
    simpa [twist, hbi] using h
  · rintro rfl
    simp [twist]

lemma twist_one_eq_reflection [FiniteDimensional ℝ E] {b v : E}
    (hb : ‖b‖ = 1) : twist b v 1 1 = (ℝ ∙ b)ᗮ.reflection v := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [twist, hb, two_smul, two_mul, add_smul]

lemma det_reflection_unit [FiniteDimensional ℝ E] {b : E} (hb : ‖b‖ = 1) :
    LinearMap.det ((ℝ ∙ b)ᗮ.reflection.toLinearMap) = -1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hb0]
  norm_num

noncomputable def capPush (c b v : E) (t a η ρ : ℝ) : E :=
  capChart c (twist b v a η) - (4 * t * ρ) • c

noncomputable def plainCapPush (c v : E) (t ρ : ℝ) : E :=
  capChart c v - (4 * t * ρ) • c

lemma plainCapPush_eq_zero_iff {c v : E} {t ρ : ℝ}
    (hc : ‖c‖ = 1) (hcv : ⟪c, v⟫_ℝ = 0)
    (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hρzero : v = 0 → ρ = 1) :
    plainCapPush c v t ρ = 0 ↔ v = 0 ∧ t = 1 / 4 := by
  constructor
  · intro hz
    have he : capChart c v = (4 * t * ρ) • c := sub_eq_zero.mp hz
    have hn := congrArg norm he
    rw [norm_capChart hc hcv, norm_smul, Real.norm_eq_abs, hc, mul_one,
      abs_of_nonneg (by positivity : 0 ≤ 4 * t * ρ)] at hn
    have he' : capChart c v = c := by simpa [← hn] using he
    have hv0 := (capChart_eq_center_iff hc hcv).mp he'
    refine ⟨hv0, ?_⟩
    rw [hρzero hv0] at hn
    nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [plainCapPush, capChart_zero, hρzero rfl]

lemma capPush_eq_zero_iff {c b v : E} {t a η ρ : ℝ}
    (hc : ‖c‖ = 1) (hb : ‖b‖ = 1)
    (hcb : ⟪c, b⟫_ℝ = 0) (hcv : ⟪c, v⟫_ℝ = 0)
    (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ha : 1 / 4 ≤ t → a = 1) (hη : 0 < ρ → η = 1)
    (hρzero : v = 0 → ρ = 1) :
    capPush c b v t a η ρ = 0 ↔ v = 0 ∧ t = 1 / 4 := by
  constructor
  · intro hz
    have he : capChart c (twist b v a η) = (4 * t * ρ) • c :=
      sub_eq_zero.mp hz
    have hn := congrArg norm he
    rw [norm_capChart hc (inner_twist hcb hcv a η), norm_smul,
      Real.norm_eq_abs, hc, mul_one, abs_of_nonneg (by positivity : 0 ≤ 4 * t * ρ)] at hn
    have htq : 1 / 4 ≤ t := by nlinarith
    have hρp : 0 < ρ := by nlinarith
    have he' : capChart c (twist b v 1 1) = c := by
      simpa [ha htq, hη hρp, ← hn] using he
    have hv0 : v = 0 :=
      (twist_one_eq_zero_iff hb).mp
        ((capChart_eq_center_iff hc (inner_twist hcb hcv 1 1)).mp he')
    refine ⟨hv0, ?_⟩
    rw [hρzero hv0] at hn
    nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [capPush, twist, capChart_zero, hρzero rfl]

end PlanarTestLocal
