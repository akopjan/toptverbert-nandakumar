module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# An explicit trivial normal tube after deleting a closed exceptional set

For a linear subspace `L` in a finite-dimensional Euclidean space and a closed
exceptional set `Z`, the surviving locus `L \ Z` has a product normal tube
contained in `E \ Z`. Its radius is half the distance to `Z`. The homeomorphism
identifies the actual zero section and the actual punctured normal fibers.
This is the geometric input for excision with trivial normal bundles.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearTube

open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable (L : Submodule ℝ E) (Z : Set E)

def coordinates : E ≃L[ℝ] (L × Lᗮ) :=
  (L.prodEquivOfIsCompl Lᗮ L.isCompl_orthogonal).symm.toContinuousLinearEquiv

theorem coordinates_symm_apply (p : L × Lᗮ) :
    (coordinates L).symm p = (p.1 : E) + (p.2 : E) := rfl

theorem coordinates_coe (a : L) : coordinates L a.val = (a, 0) :=
  L.prodEquivOfIsCompl_symm_apply_left Lᗮ L.isCompl_orthogonal a

theorem distance_base (x : E) :
    dist (coordinates L x).1.val x = ‖(coordinates L x).2‖ := by
  have he : x = (coordinates L x).1.val + (coordinates L x).2.val :=
    ((coordinates L).symm_apply_apply x).symm.trans
      (coordinates_symm_apply L (coordinates L x))
  calc
    dist (coordinates L x).1.val x =
        dist (coordinates L x).1.val ((coordinates L x).1.val + (coordinates L x).2.val) :=
      congrArg (dist (coordinates L x).1.val) he
    _ = ‖(coordinates L x).2‖ := by simp [dist_eq_norm]

theorem normal_zero_iff (x : E) : (coordinates L x).2 = 0 ↔ x ∈ L :=
  L.prodEquivOfIsCompl_symm_apply_snd_eq_zero Lᗮ L.isCompl_orthogonal

abbrev Base := {a : L // (a : E) ∉ Z}
abbrev NormalBall := Metric.ball (0 : Lᗮ) 1

def radius (a : L) : ℝ := infDist (a : E) Z / 2

omit [FiniteDimensional ℝ E] in
theorem continuous_radius : Continuous (radius L Z) :=
  ((continuous_infDist_pt Z).comp continuous_subtype_val).div_const 2

omit [FiniteDimensional ℝ E] in
theorem radius_pos (hZ : IsClosed Z) (hne : Z.Nonempty) (a : Base L Z) :
    0 < radius L Z a.val :=
  div_pos ((hZ.notMem_iff_infDist_pos hne).mp a.property) (by norm_num)

def Tube : Set E := {x | (coordinates L x).1.val ∉ Z ∧
  ‖(coordinates L x).2‖ < radius L Z (coordinates L x).1}

theorem isOpen_tube (hZ : IsClosed Z) : IsOpen (Tube L Z) := by
  unfold Tube
  rw [Set.ofPred_and]
  apply IsOpen.inter
  · exact hZ.isOpen_compl.preimage (continuous_subtype_val.comp
      (continuous_fst.comp (coordinates L).continuous))
  · exact isOpen_lt
      ((continuous_snd.comp (coordinates L).continuous).norm)
      ((continuous_radius L Z).comp (continuous_fst.comp (coordinates L).continuous))

theorem tube_disjoint_exceptional (x : E) (hx : x ∈ Tube L Z) : x ∉ Z := by
  apply notMem_of_dist_lt_infDist (x := (coordinates L x).1.val)
  rw [distance_base]
  exact hx.2.trans_le (by unfold radius; have := infDist_nonneg (x := (coordinates L x).1.val) (s := Z); linarith)

/-- Normal tubes are disjoint if each radius also measures the distance
to the other subspace. This supplies disjoint neighborhoods for the surviving
critical pair strata. -/
theorem disjoint_tubes (M : Submodule ℝ E) (Z' : Set E)
    (hM : (M : Set E) ⊆ Z) (hL : (L : Set E) ⊆ Z') :
    Disjoint (Tube L Z) (Tube M Z') := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  let a : E := (coordinates L x).1.val
  let b : E := (coordinates M x).1.val
  have ha : 2 * dist a x < dist a b := by
    have hdist : infDist a Z ≤ dist a b := infDist_le_dist_of_mem (hM (coordinates M x).1.property)
    have hnorm := hx.2
    change ‖(coordinates L x).2‖ < infDist a Z / 2 at hnorm
    dsimp only [a]
    rw [distance_base]
    linarith
  have hb : 2 * dist b x < dist b a := by
    have hdist : infDist b Z' ≤ dist b a := infDist_le_dist_of_mem (hL (coordinates L x).1.property)
    have hnorm := hy.2
    change ‖(coordinates M x).2‖ < infDist b Z' / 2 at hnorm
    dsimp only [b]
    rw [distance_base]
    linarith
  have htri := dist_triangle a x b
  rw [dist_comm x b] at htri
  rw [dist_comm b a] at hb
  linarith

theorem base_mem_tube (hZ : IsClosed Z) (hne : Z.Nonempty) (a : Base L Z) :
    a.val.val ∈ Tube L Z := by
  change (coordinates L a.val.val).1.val ∉ Z ∧
    ‖(coordinates L a.val.val).2‖ < radius L Z (coordinates L a.val.val).1
  rw [coordinates_coe]
  exact ⟨a.property, by simpa only [norm_zero] using radius_pos L Z hZ hne a⟩

variable (hZ : IsClosed Z) (hne : Z.Nonempty)

def toTube (p : Base L Z × NormalBall L) : Tube L Z :=
  ⟨(coordinates L).symm (p.1.val, radius L Z p.1.val • p.2.val), by
    change ((coordinates L) ((coordinates L).symm _)).1.val ∉ Z ∧
      ‖((coordinates L) ((coordinates L).symm _)).2‖ <
        radius L Z ((coordinates L) ((coordinates L).symm _)).1
    rw [(coordinates L).apply_symm_apply]
    refine ⟨p.1.property, ?_⟩
    have hr := radius_pos L Z hZ hne p.1
    have hp : ‖p.2.val‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using p.2.property
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hp hr⟩

def fromTube (x : Tube L Z) : Base L Z × NormalBall L :=
  (⟨(coordinates L x.val).1, x.property.1⟩,
    ⟨(radius L Z (coordinates L x.val).1)⁻¹ • (coordinates L x.val).2, by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (radius_pos L Z hZ hne
          ⟨(coordinates L x.val).1, x.property.1⟩))]
      exact (inv_mul_lt_one₀ (radius_pos L Z hZ hne
        ⟨(coordinates L x.val).1, x.property.1⟩)).mpr x.property.2⟩)

theorem fromTube_toTube (p : Base L Z × NormalBall L) :
    fromTube L Z hZ hne (toTube L Z hZ hne p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst ((coordinates L).apply_symm_apply _)
  · apply Subtype.ext
    change (radius L Z ((coordinates L) ((coordinates L).symm _)).1)⁻¹ •
      ((coordinates L) ((coordinates L).symm _)).2 = p.2.val
    rw [(coordinates L).apply_symm_apply, smul_smul,
      inv_mul_cancel₀ (radius_pos L Z hZ hne p.1).ne', one_smul]

theorem toTube_fromTube (x : Tube L Z) :
    toTube L Z hZ hne (fromTube L Z hZ hne x) = x := by
  apply Subtype.ext
  change (coordinates L).symm
    ((coordinates L x.val).1,
      radius L Z (coordinates L x.val).1 •
        ((radius L Z (coordinates L x.val).1)⁻¹ • (coordinates L x.val).2)) = x.val
  rw [smul_smul, mul_inv_cancel₀
    (radius_pos L Z hZ hne ⟨(coordinates L x.val).1, x.property.1⟩).ne', one_smul]
  exact (coordinates L).symm_apply_apply x.val

theorem continuous_toTube : Continuous (toTube L Z hZ hne) := by
  apply Continuous.subtype_mk
  apply (coordinates L).symm.continuous.comp
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    (((continuous_radius L Z).comp (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd))

theorem continuous_fromTube : Continuous (fromTube L Z hZ hne) := by
  have hc : Continuous (fun x : Tube L Z => coordinates L x.val) :=
    (coordinates L).continuous.comp continuous_subtype_val
  have hr : Continuous (fun x : Tube L Z => radius L Z (coordinates L x.val).1) :=
    (continuous_radius L Z).comp (continuous_fst.comp hc)
  have hn : Continuous (fun x : Tube L Z =>
      (radius L Z (coordinates L x.val).1)⁻¹ • (coordinates L x.val).2) :=
    (hr.inv₀ (fun x => (radius_pos L Z hZ hne
      ⟨(coordinates L x.val).1, x.property.1⟩).ne')).smul (continuous_snd.comp hc)
  exact ((continuous_fst.comp hc).subtype_mk _).prodMk
    (hn.subtype_mk _)

/-- A product trivialization of the actual open tube, not merely a
dimension count or a bundle-class assumption. -/
def homeomorph : (Base L Z × NormalBall L) ≃ₜ Tube L Z where
  toFun := toTube L Z hZ hne
  invFun := fromTube L Z hZ hne
  left_inv := fromTube_toTube L Z hZ hne
  right_inv := toTube_fromTube L Z hZ hne
  continuous_toFun := continuous_toTube L Z hZ hne
  continuous_invFun := continuous_fromTube L Z hZ hne

theorem homeomorph_apply (p : Base L Z × NormalBall L) :
    (homeomorph L Z hZ hne p).val = p.1.val.val + radius L Z p.1.val • p.2.val.val := rfl

theorem homeomorph_zero_section (a : Base L Z) :
    (homeomorph L Z hZ hne (a, ⟨0, by simp⟩)).val = a.val.val := by
  rw [homeomorph_apply]
  simp

theorem homeomorph_mem_submodule_iff (p : Base L Z × NormalBall L) :
    (homeomorph L Z hZ hne p).val ∈ L ↔ p.2.val = 0 := by
  rw [← normal_zero_iff L]
  change ((coordinates L) ((coordinates L).symm _)).2 = 0 ↔ _
  rw [(coordinates L).apply_symm_apply]
  exact smul_eq_zero.trans (or_iff_right (radius_pos L Z hZ hne p.1).ne')

/-- The same tube trivialization restricts to the complements of the
actual zero sections. -/
def puncturedHomeomorph :
    {p : Base L Z × NormalBall L // p.2.val ≠ 0} ≃ₜ
      {x : Tube L Z // x.val ∉ L} :=
  (homeomorph L Z hZ hne).subtype
    (fun p => (not_congr (homeomorph_mem_submodule_iff L Z hZ hne p)).symm)

abbrev Time := Set.Icc (0 : ℝ) 1

def contraction (p : Time × Tube L Z) : Tube L Z :=
  ⟨(coordinates L).symm
      ((coordinates L p.2.val).1, (1 - p.1.val) • (coordinates L p.2.val).2), by
    change ((coordinates L) ((coordinates L).symm _)).1.val ∉ Z ∧
      ‖((coordinates L) ((coordinates L).symm _)).2‖ <
        radius L Z ((coordinates L) ((coordinates L).symm _)).1
    rw [(coordinates L).apply_symm_apply]
    refine ⟨p.2.property.1, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [p.1.property.2])]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [p.1.property.1])).trans_lt
      p.2.property.2⟩

theorem continuous_contraction : Continuous (contraction L Z) := by
  apply Continuous.subtype_mk
  apply (coordinates L).symm.continuous.comp
  have hc : Continuous (fun p : Time × Tube L Z => coordinates L p.2.val) := by fun_prop
  exact (continuous_fst.comp hc).prodMk
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_snd.comp hc))

theorem contraction_start (x : Tube L Z) : contraction L Z (0, x) = x := by
  apply Subtype.ext
  change (coordinates L).symm
    ((coordinates L x.val).1, (1 - (0 : ℝ)) • (coordinates L x.val).2) = x.val
  rw [sub_zero, one_smul]
  exact (coordinates L).symm_apply_apply x.val

theorem contraction_finish (x : Tube L Z) :
    (contraction L Z (1, x)).val = (coordinates L x.val).1.val := by
  change (coordinates L).symm
    ((coordinates L x.val).1, (1 - (1 : ℝ)) • (coordinates L x.val).2) = _
  rw [sub_self, zero_smul, coordinates_symm_apply]
  simp

theorem contraction_fixed (x : Tube L Z) (hx : x.val ∈ L) (t : Time) :
    contraction L Z (t, x) = x := by
  have hn := (normal_zero_iff L x.val).mpr hx
  apply Subtype.ext
  change (coordinates L).symm
    ((coordinates L x.val).1, (1 - t.val) • (coordinates L x.val).2) = x.val
  rw [hn, smul_zero, ← hn]
  exact (coordinates L).symm_apply_apply x.val

end AkopyanResearch.LinearTube
