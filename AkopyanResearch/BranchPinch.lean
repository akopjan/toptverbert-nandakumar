module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic


@[expose] public section

/-!
The based radial ball-collapse homotopy on a one-point compactified real
normed space. All parameters lie in [0,1]. No degree classification is used.
-/

open Set Topology
open scoped OnePoint

namespace BranchPinch

abbrev Time := Set.Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

def shrink (t : Time) (z : E) : E := (1 + (t : ℝ) * ‖z‖)⁻¹ • z

def expand (t : Time) (y : E) : E := (1 - (t : ℝ) * ‖y‖)⁻¹ • y

def radial (t : Time) (p : OnePoint E) : OnePoint E :=
  p.elim ∞ (fun y => if (t : ℝ) * ‖y‖ < 1 then OnePoint.some (expand t y) else ∞)

omit [NormedSpace ℝ E] in
lemma shrink_den_pos (t : Time) (z : E) : 0 < 1 + (t : ℝ) * ‖z‖ := by
  have := t.property.1
  positivity

lemma norm_shrink (t : Time) (z : E) :
    ‖shrink t z‖ = ‖z‖ / (1 + (t : ℝ) * ‖z‖) := by
  simp only [shrink, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (shrink_den_pos t z), div_eq_mul_inv]
  exact mul_comm _ _

lemma shrink_inside (t : Time) (z : E) : (t : ℝ) * ‖shrink t z‖ < 1 := by
  rw [norm_shrink, ← mul_div_assoc]
  apply (div_lt_iff₀ (shrink_den_pos t z)).mpr
  linarith

lemma expand_shrink (t : Time) (z : E) : expand t (shrink t z) = z := by
  rw [expand, norm_shrink, shrink, smul_smul]
  have hp := shrink_den_pos t z
  have he : 1 - (t : ℝ) * (‖z‖ / (1 + (t : ℝ) * ‖z‖)) =
      (1 + (t : ℝ) * ‖z‖)⁻¹ := by
    field_simp
    ring
  rw [he, inv_inv, mul_inv_cancel₀ (ne_of_gt hp), one_smul]

lemma norm_expand (t : Time) (y : E) (hy : (t : ℝ) * ‖y‖ < 1) :
    ‖expand t y‖ = ‖y‖ / (1 - (t : ℝ) * ‖y‖) := by
  have hp : 0 < 1 - (t : ℝ) * ‖y‖ := by linarith
  simp only [expand, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp, div_eq_mul_inv]
  exact mul_comm _ _

lemma shrink_expand (t : Time) (y : E) (hy : (t : ℝ) * ‖y‖ < 1) :
    shrink t (expand t y) = y := by
  rw [shrink, norm_expand t y hy, expand, smul_smul]
  have hp : 0 < 1 - (t : ℝ) * ‖y‖ := by linarith
  have he : 1 + (t : ℝ) * (‖y‖ / (1 - (t : ℝ) * ‖y‖)) =
      (1 - (t : ℝ) * ‖y‖)⁻¹ := by
    field_simp
    ring
  rw [he, inv_inv, mul_inv_cancel₀ (ne_of_gt hp), one_smul]

@[simp] lemma radial_infty (t : Time) : radial (E := E) t ∞ = ∞ := rfl

@[simp] lemma radial_shrink (t : Time) (z : E) :
    radial t (OnePoint.some (shrink t z)) = (z : OnePoint E) := by
  simp [radial, shrink_inside, expand_shrink]

lemma radial_eq_coe_iff (t : Time) (p : OnePoint E) (z : E) :
    radial t p = (z : OnePoint E) ↔ p = OnePoint.some (shrink t z) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe y =>
    by_cases hy : (t : ℝ) * ‖y‖ < 1
    · simp only [radial, OnePoint.elim_some, ite_eq_left hy, OnePoint.coe_eq_coe]
      constructor
      · intro h
        rw [← h, shrink_expand t y hy]
      · rintro rfl
        exact expand_shrink t z
    · simp only [radial, OnePoint.elim_some, ite_eq_right hy, OnePoint.infty_ne_coe,
        false_iff, OnePoint.coe_eq_coe]
      intro h
      apply hy
      rw [h]
      exact shrink_inside t z

lemma continuous_shrink : Continuous (fun p : Time × E => shrink p.1 p.2) := by
  apply Continuous.smul
  · apply Continuous.inv₀
    · exact continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul
        continuous_snd.norm)
    · intro p
      exact ne_of_gt (shrink_den_pos p.1 p.2)
  · exact continuous_snd

omit [NormedSpace ℝ E] in
lemma isOpen_inside : IsOpen {p : Time × E | (p.1 : ℝ) * ‖p.2‖ < 1} :=
  isOpen_lt ((continuous_subtype_val.comp continuous_fst).mul continuous_snd.norm)
    continuous_const

lemma continuousOn_expand :
    ContinuousOn (fun p : Time × E => expand p.1 p.2)
      {p : Time × E | (p.1 : ℝ) * ‖p.2‖ < 1} := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.smul
  · apply ContinuousAt.inv₀
    · exact continuousAt_const.sub
        ((continuous_subtype_val.comp continuous_fst).continuousAt.mul continuous_snd.norm.continuousAt)
    · have : (p.1 : ℝ) * ‖p.2‖ < 1 := hp
      linarith
  · exact continuousAt_snd


lemma preimage_finite_set (s : Set E) :
    (fun p : Time × OnePoint E => radial p.1 p.2) ⁻¹' (((↑) : E → OnePoint E) '' s) =
      (fun q : Time × E => (q.1, OnePoint.some (shrink q.1 q.2))) '' (Set.univ ×ˢ s) := by
  ext p
  constructor
  · rintro ⟨z, hz, heq⟩
    have hp := (radial_eq_coe_iff p.1 p.2 z).mp heq.symm
    refine ⟨(p.1, z), ⟨Set.mem_univ _, hz⟩, ?_⟩
    exact Prod.ext rfl hp.symm
  · rintro ⟨⟨t, z⟩, ⟨_, hz⟩, rfl⟩
    exact ⟨z, hz, (radial_shrink t z).symm⟩

lemma isCompact_preimage_finite_set {s : Set E} (hs : IsCompact s) :
    IsCompact ((fun p : Time × OnePoint E => radial p.1 p.2) ⁻¹'
      (((↑) : E → OnePoint E) '' s)) := by
  rw [preimage_finite_set]
  exact (isCompact_univ.prod hs).image
    (continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_shrink))

lemma isOpen_preimage_of_not_infty {s : Set (OnePoint E)}
    (hs : IsOpen s) (hinf : ∞ ∉ s) :
    IsOpen ((fun p : Time × OnePoint E => radial p.1 p.2) ⁻¹' s) := by
  let A : Set (Time × E) := {p | (p.1 : ℝ) * ‖p.2‖ < 1}
  let B : Set (Time × E) := A ∩
    (fun p : Time × E => expand p.1 p.2) ⁻¹' (((↑) : E → OnePoint E) ⁻¹' s)
  have hB : IsOpen B := continuousOn_expand.isOpen_inter_preimage isOpen_inside
    (hs.preimage OnePoint.continuous_coe)
  have heq : (fun p : Time × OnePoint E => radial p.1 p.2) ⁻¹' s =
      (fun q : Time × E => (q.1, (q.2 : OnePoint E))) '' B := by
    ext p
    constructor
    · intro hp
      rcases p with ⟨t, y⟩
      induction y using OnePoint.rec with
      | infty => exact False.elim (hinf hp)
      | coe y =>
        have hy : (t : ℝ) * ‖y‖ < 1 := by
          by_contra h
          exact hinf (by simpa [radial, h] using hp)
        refine ⟨(t, y), ⟨hy, ?_⟩, rfl⟩
        simpa [radial, hy] using hp
    · rintro ⟨⟨t, y⟩, ⟨hy, hv⟩, rfl⟩
      have hy' : (t : ℝ) * ‖y‖ < 1 := hy
      simpa [radial, hy'] using hv
  rw [heq]
  exact (IsOpenMap.id.prodMap OnePoint.isOpenMap_coe) _ hB

/-- Joint continuity includes both the boundary of the collapsing ball and
infinity, uniformly in the homotopy parameter. Compact inverse images are
parametrized by the explicit continuous inverse `shrink`. -/
lemma continuous_radial [ProperSpace E] :
    Continuous (fun p : Time × OnePoint E => radial p.1 p.2) := by
  apply continuous_def.mpr
  intro s hs
  by_cases hinf : (∞ : OnePoint E) ∈ s
  · let K : Set E := (((↑) : E → OnePoint E) ⁻¹' s)ᶜ
    have hK : IsCompact K := (OnePoint.isOpen_def.mp hs).1 hinf
    have hcompl : sᶜ = ((↑) : E → OnePoint E) '' K := by
      ext p
      induction p using OnePoint.rec with
      | infty => simp [hinf]
      | coe y => simp [K]
    have hc : IsClosed ((fun p : Time × OnePoint E => radial p.1 p.2) ⁻¹' sᶜ) := by
      rw [hcompl]
      exact (isCompact_preimage_finite_set hK).isClosed
    simpa only [Set.preimage_compl, isClosed_compl_iff] using hc
  · exact isOpen_preimage_of_not_infty hs hinf

lemma radial_equivariant (e : E ≃ₗᵢ[ℝ] E) (t : Time) (p : OnePoint E) :
    radial t (p.map e) = (radial t p).map e := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe y =>
    simp only [OnePoint.map_some, radial, OnePoint.elim_some, e.norm_map]
    split_ifs <;> simp [expand, e.norm_map]

@[simp] lemma radial_zero (p : OnePoint E) : radial ⟨0, by norm_num⟩ p = p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe y => simp [radial, expand]

@[simp] lemma radial_one (y : E) :
    radial ⟨1, by norm_num⟩ (y : OnePoint E) =
      if ‖y‖ < 1 then (((1 - ‖y‖)⁻¹ • y : E) : OnePoint E) else ∞ := by
  simp [radial, expand]

/-- The positive radial collapse of the open unit ball. -/
def collapse [ProperSpace E] : C(OnePoint E, OnePoint E) where
  toFun := radial ⟨1, by norm_num⟩
  continuous_toFun := continuous_radial.comp (continuous_const.prodMk continuous_id)

/-- A based homotopy from the identity to the ball collapse. -/
def radialHomotopy [ProperSpace E] :
    ContinuousMap.Homotopy (ContinuousMap.id (OnePoint E)) collapse where
  toFun p := radial p.1 p.2
  continuous_toFun := continuous_radial
  map_zero_left p := radial_zero p
  map_one_left _ := rfl

@[simp] lemma radialHomotopy_fixed [ProperSpace E] (t : Time) :
    radialHomotopy (E := E) (t, ∞) = ∞ := rfl

end
end BranchPinch
