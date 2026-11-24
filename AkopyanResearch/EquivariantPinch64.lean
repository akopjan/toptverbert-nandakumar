module

public import AkopyanResearch.RowSylowGeometry
public import AkopyanResearch.BranchPinch

@[expose] public section

/-!
# `P_row`-equivariant stereographic pinch maps `branchCollapse` and `pinch64`

1. Orthogonal complement `E9 := (ℝ ∙ anchor10)ᗮ` with restricted `P_row` linear isometry
   action `permE9` fixing the `S¹`-tangent unit vector `cA0_E9`.
2. Explicit `P_row`-equivariant stereographic homeomorphism
   `stereoAnchor : Metric.sphere (0 : Rep10) 1 ≃ₜ OnePoint E9` sending `anchorS ↦ ∞`.
3. Conjugation of `BranchPinch.collapse` along `stereoAnchor` (`branchCollapse`) and
   across `64` disjoint invariant balls centered at `(i : ℕ) • cA0_E9` (`pinch64`),
   together with its restriction `pinch64RestrictedP_row` and based null-homotopy
   `nullHomotopy_pinch64_q0_P_row`.
-/

noncomputable section

open scoped BigOperators InnerProductSpace Classical OnePoint
open Metric Set Filter Topology

namespace AkopyanResearch

/-! ### 1. Orthogonal complement `E9` of `anchor10` and restricted `P_row` action -/

section OrthogonalComplement

abbrev E9 : Type := ↥((ℝ ∙ anchor10)ᗮ)

lemma perm10_mem_E9 (g : P_row) {v : Rep10} (hv : v ∈ (ℝ ∙ anchor10)ᗮ) :
    perm10 g.1 v ∈ (ℝ ∙ anchor10)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv ⊢
  rw [← perm10_anchor10_of_mem_P_row g.2, perm10_inner, hv]

def permE9 (g : P_row) : E9 ≃ₗᵢ[ℝ] E9 where
  toFun v := ⟨perm10 g.1 v.1, perm10_mem_E9 g v.2⟩
  invFun v := ⟨perm10 g⁻¹.1 v.1, perm10_mem_E9 g⁻¹ v.2⟩
  left_inv v := by
    apply Subtype.ext
    change perm10 g⁻¹.1 (perm10 g.1 v.1) = v.1
    rw [Subgroup.coe_inv, ← perm10_mul, inv_mul_cancel, perm10_one]
  right_inv v := by
    apply Subtype.ext
    change perm10 g.1 (perm10 g⁻¹.1 v.1) = v.1
    rw [Subgroup.coe_inv, ← perm10_mul, mul_inv_cancel, perm10_one]
  map_add' u v := Subtype.ext (map_add (perm10 g.1) u.1 v.1)
  map_smul' r u := Subtype.ext (map_smul (perm10 g.1) r u.1)
  norm_map' v := (perm10 g.1).norm_map v.1

def cA0_E9 : E9 :=
  ⟨cA0, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr inner_anchor10_cA0⟩

lemma norm_cA0_E9 : ‖cA0_E9‖ = 1 := norm_cA0

lemma permE9_cA0_E9 (g : P_row) : permE9 g cA0_E9 = cA0_E9 := by
  apply Subtype.ext
  exact cA0_mem_fixedSubspace_of_le_P_row le_rfl g.1 g.2

attribute [irreducible] cA0_E9

end OrthogonalComplement

/-! ### 2. Stereographic homeomorphism `S⁹ ≃ₜ OnePoint E9` centered at `-anchor10` -/

section StereographicHomeo

lemma norm_neg_anchor10 : ‖-anchor10‖ = 1 := by
  rw [norm_neg, norm_anchor10]

lemma stereoProj_neg_anchor10_mem_E9 (x : Rep10) :
    stereoProj (-anchor10) x ∈ (ℝ ∙ anchor10)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have h := inner_stereoProj norm_neg_anchor10 x
  simpa only [inner_neg_left, neg_eq_zero] using h

lemma inner_anchor10_capChart_neg (v : E9) :
    ⟪anchor10, PlanarTestLocal.capChart (-anchor10) v.1⟫_ℝ =
      (‖v.1‖ ^ 2 - 4) / (‖v.1‖ ^ 2 + 4) := by
  have hv : ⟪anchor10, v.1⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.2
  rw [capChart_eq, inner_add_right, inner_smul_right, inner_smul_right, inner_neg_right,
    real_inner_self_eq_norm_sq, norm_anchor10, hv]
  have hden : (0 : ℝ) < ‖v.1‖ ^ 2 + 4 := by positivity
  field_simp
  ring

lemma norm_capChart_neg_anchor10 (v : E9) :
    ‖PlanarTestLocal.capChart (-anchor10) v.1‖ = 1 := by
  have hv : ⟪v.1, anchor10⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.2
  have hsq : ‖PlanarTestLocal.capChart (-anchor10) v.1‖ ^ 2 = 1 := by
    rw [capChart_eq, norm_add_sq_real, norm_smul, norm_smul, norm_neg, norm_anchor10, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, inner_smul_left, inner_smul_right, inner_neg_right, hv]
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_pow, sq_abs]
    have hden : (‖v.1‖ ^ 2 + 4 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  nlinarith [norm_nonneg (PlanarTestLocal.capChart (-anchor10) v.1)]

lemma capChart_neg_anchor10_ne_anchor10 (v : E9) :
    PlanarTestLocal.capChart (-anchor10) v.1 ≠ anchor10 := by
  intro heq
  have h := congrArg (inner ℝ anchor10) heq
  rw [inner_anchor10_capChart_neg, real_inner_self_eq_norm_sq, norm_anchor10, one_pow] at h
  have hden : (‖v.1‖ ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  rw [div_eq_one_iff_eq hden] at h
  linarith

lemma stereoProj_capChart_neg_anchor10 (v : E9) :
    stereoProj (-anchor10) (PlanarTestLocal.capChart (-anchor10) v.1) = v.1 := by
  have hv : ⟪anchor10, v.1⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.2
  have hden : (‖v.1‖ ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  have hinner : ⟪-anchor10, PlanarTestLocal.capChart (-anchor10) v.1⟫_ℝ =
      (4 - ‖v.1‖ ^ 2) / (‖v.1‖ ^ 2 + 4) := by
    rw [inner_neg_left, inner_anchor10_capChart_neg]
    ring
  rw [stereoProj, hinner]
  have h1p : 1 + (4 - ‖v.1‖ ^ 2) / (‖v.1‖ ^ 2 + 4) = 8 / (‖v.1‖ ^ 2 + 4) := by
    field_simp; ring
  rw [h1p, capChart_eq]
  have hvec : (4 / (‖v.1‖ ^ 2 + 4)) • v.1 +
      ((4 - ‖v.1‖ ^ 2) / (‖v.1‖ ^ 2 + 4)) • (-anchor10) -
      ((4 - ‖v.1‖ ^ 2) / (‖v.1‖ ^ 2 + 4)) • (-anchor10) =
      (4 / (‖v.1‖ ^ 2 + 4)) • v.1 := by module
  rw [hvec, smul_smul]
  have hc : 2 / (8 / (‖v.1‖ ^ 2 + 4)) * (4 / (‖v.1‖ ^ 2 + 4)) = 1 := by
    field_simp
    ring
  rw [hc, one_smul]

lemma norm_sq_capChart_neg_anchor10_sub (v : E9) :
    ‖PlanarTestLocal.capChart (-anchor10) v.1 - anchor10‖ ^ 2 =
      16 / (‖v.1‖ ^ 2 + 4) := by
  rw [norm_sub_sq_eq norm_anchor10 (norm_capChart_neg_anchor10 v), inner_anchor10_capChart_neg]
  have hden : (‖v.1‖ ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

def fromOnePointFun (p : OnePoint E9) : Metric.sphere (0 : Rep10) 1 :=
  p.elim anchorS fun v =>
    ⟨PlanarTestLocal.capChart (-anchor10) v.1,
      mem_sphere_zero_iff_norm.mpr (norm_capChart_neg_anchor10 v)⟩

def toOnePointFun (x : Metric.sphere (0 : Rep10) 1) : OnePoint E9 :=
  if x = anchorS then ∞
  else OnePoint.some ⟨stereoProj (-anchor10) x.1, stereoProj_neg_anchor10_mem_E9 x.1⟩

lemma fromOnePoint_toOnePoint (x : Metric.sphere (0 : Rep10) 1) :
    fromOnePointFun (toOnePointFun x) = x := by
  by_cases hx : x = anchorS
  · simp [toOnePointFun, fromOnePointFun, hx]
  · simp only [toOnePointFun, if_neg hx, fromOnePointFun, OnePoint.elim_some]
    apply Subtype.ext
    have hxn : x.1 ≠ anchor10 := fun h => hx (Subtype.ext h)
    have hx_norm : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hdist : ‖x.1 - (-anchor10)‖ < 2 := by
      have hpos : 0 < ‖x.1 - anchor10‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxn))
      have hpar : ‖x.1 - anchor10‖ ^ 2 + ‖x.1 - (-anchor10)‖ ^ 2 = 4 := by
        rw [sub_neg_eq_add, norm_sub_sq_real, norm_add_sq_real, hx_norm, norm_anchor10]
        ring
      have hlt : ‖x.1 - (-anchor10)‖ ^ 2 < 4 := by linarith
      nlinarith [norm_nonneg (x.1 - (-anchor10))]
    exact capChart_stereoProj norm_neg_anchor10 hx_norm hdist

lemma toOnePoint_fromOnePoint (p : OnePoint E9) :
    toOnePointFun (fromOnePointFun p) = p := by
  induction p using OnePoint.rec with
  | infty => simp [fromOnePointFun, toOnePointFun]
  | coe v =>
    have hne : fromOnePointFun (v : OnePoint E9) ≠ anchorS := by
      intro h
      exact capChart_neg_anchor10_ne_anchor10 v (congrArg Subtype.val h)
    dsimp only [fromOnePointFun, OnePoint.elim_some, toOnePointFun]
    rw [if_neg (by simpa [fromOnePointFun] using hne)]
    congr 1
    exact Subtype.ext (stereoProj_capChart_neg_anchor10 v)

lemma continuous_fromOnePointFun : Continuous fromOnePointFun := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · rw [hasBasis_coclosedCompact.tendsto_iff Metric.nhds_basis_ball]
    intro ε hε
    let R : ℝ := max (4 / ε) 1
    refine ⟨Metric.closedBall (0 : E9) R, ⟨isClosed_closedBall, isCompact_closedBall 0 R⟩, ?_⟩
    intro v hv
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hv
    have hR : 4 / ε ≤ R := le_max_left _ _
    have hlt : 4 / ε < ‖v.1‖ := lt_of_le_of_lt hR hv
    have hsq : 16 / ε ^ 2 < ‖v.1‖ ^ 2 + 4 := by
      have hpos : 0 ≤ 4 / ε := by positivity
      have h1 : (4 / ε) ^ 2 < ‖v.1‖ ^ 2 := by nlinarith
      linarith [show (4 / ε) ^ 2 = 16 / ε ^ 2 by ring]
    have hd_sq : dist ((fromOnePointFun ∘ (↑)) v) anchorS ^ 2 < ε ^ 2 := by
      change dist (fromOnePointFun (v : OnePoint E9)) anchorS ^ 2 < ε ^ 2
      rw [Subtype.dist_eq, dist_eq_norm]
      change ‖PlanarTestLocal.capChart (-anchor10) v.1 - anchor10‖ ^ 2 < ε ^ 2
      rw [norm_sq_capChart_neg_anchor10_sub v, div_lt_iff₀ (by positivity : (0 : ℝ) < ‖v.1‖ ^ 2 + 4)]
      have h16 := (div_lt_iff₀ (pow_pos hε 2)).mp hsq
      rw [mul_comm] at h16
      exact h16
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hd_sq
  · rw [continuous_induced_rng]
    change Continuous (fun v : E9 => (fromOnePointFun (v : OnePoint E9) : Rep10))
    have hfun : (fun v : E9 => (fromOnePointFun (v : OnePoint E9) : Rep10)) =
        fun v => (4 / (‖v.1‖ ^ 2 + 4)) • v.1 + ((4 - ‖v.1‖ ^ 2) / (‖v.1‖ ^ 2 + 4)) • (-anchor10) := by
      funext v
      exact capChart_eq (-anchor10) v.1
    rw [hfun]
    have hv1 : Continuous (fun v : E9 => v.1) := continuous_subtype_val
    have hnsq : Continuous (fun v : E9 => ‖v.1‖ ^ 2) := (hv1.norm).pow 2
    have hden : Continuous (fun v : E9 => ‖v.1‖ ^ 2 + 4) := hnsq.add continuous_const
    have hden_ne : ∀ v : E9, ‖v.1‖ ^ 2 + 4 ≠ 0 := fun v => by positivity
    exact ((continuous_const.div hden hden_ne).smul hv1).add
      (((continuous_const.sub hnsq).div hden hden_ne).smul continuous_const)

def fromOnePointHomeo : OnePoint E9 ≃ₜ Metric.sphere (0 : Rep10) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := {
      toFun := fromOnePointFun
      invFun := toOnePointFun
      left_inv := toOnePoint_fromOnePoint
      right_inv := fromOnePoint_toOnePoint })
    continuous_fromOnePointFun

def stereoAnchor : Metric.sphere (0 : Rep10) 1 ≃ₜ OnePoint E9 :=
  fromOnePointHomeo.symm

@[simp] lemma stereoAnchor_anchorS : stereoAnchor anchorS = ∞ := by
  change toOnePointFun anchorS = ∞
  simp [toOnePointFun]

@[simp] lemma stereoAnchor_symm_infty : stereoAnchor.symm ∞ = anchorS := rfl

lemma fromOnePointHomeo_map (g : P_row) (p : OnePoint E9) :
    fromOnePointHomeo (p.map (permE9 g)) = permSphere g.1 (fromOnePointHomeo p) := by
  induction p using OnePoint.rec with
  | infty =>
    simp only [OnePoint.map_infty]
    exact (permSphere_anchorS_of_mem_P_row g.2).symm
  | coe v =>
    apply Subtype.ext
    change PlanarTestLocal.capChart (-anchor10) (perm10 g.1 v.1) =
      perm10 g.1 (PlanarTestLocal.capChart (-anchor10) v.1)
    rw [perm10_capChart, map_neg, perm10_anchor10_of_mem_P_row g.2]

lemma stereoAnchor_permSphere (g : P_row) (x : Metric.sphere (0 : Rep10) 1) :
    stereoAnchor (permSphere g.1 x) = (stereoAnchor x).map (permE9 g) := by
  apply fromOnePointHomeo.injective
  rw [fromOnePointHomeo_map]
  change fromOnePointHomeo (fromOnePointHomeo.symm (permSphere g.1 x)) =
    permSphere g.1 (fromOnePointHomeo (fromOnePointHomeo.symm x))
  simp

end StereographicHomeo

/-! ### 3. Conjugated branch collapse and `P_row`-equivariant 64-ball pinch `pinch64` -/

section BranchAndPinch64

def homeoToCont {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous⟩

@[simp] lemma homeoToCont_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (x : α) : homeoToCont e x = e x := rfl

def branchCollapse : C(Metric.sphere (0 : Rep10) 1, Metric.sphere (0 : Rep10) 1) :=
  (homeoToCont stereoAnchor.symm).comp
    ((BranchPinch.collapse (E := E9)).comp (homeoToCont stereoAnchor))

def branchCollapseHomotopy :
    ContinuousMap.HomotopyRel (ContinuousMap.id (Metric.sphere (0 : Rep10) 1)) branchCollapse
      {anchorS} where
  toFun p := stereoAnchor.symm (BranchPinch.radial p.1 (stereoAnchor p.2))
  continuous_toFun := stereoAnchor.symm.continuous.comp
    (BranchPinch.continuous_radial.comp (continuous_fst.prodMk (stereoAnchor.continuous.comp continuous_snd)))
  map_zero_left x := by
    change stereoAnchor.symm (BranchPinch.radial ⟨0, by norm_num⟩ (stereoAnchor x)) = x
    rw [BranchPinch.radial_zero]
    simp
  map_one_left x := rfl
  prop' t x hx := by
    rw [Set.mem_singleton_iff.mp hx]
    change stereoAnchor.symm (BranchPinch.radial t (stereoAnchor anchorS)) = anchorS
    rw [stereoAnchor_anchorS, BranchPinch.radial_infty, stereoAnchor_symm_infty]

lemma branchCollapseHomotopy_equivariant (g : P_row) (t : unitInterval)
    (x : Metric.sphere (0 : Rep10) 1) :
    branchCollapseHomotopy (t, permSphere g.1 x) = permSphere g.1 (branchCollapseHomotopy (t, x)) := by
  change stereoAnchor.symm (BranchPinch.radial t (stereoAnchor (permSphere g.1 x))) =
    permSphere g.1 (stereoAnchor.symm (BranchPinch.radial t (stereoAnchor x)))
  rw [stereoAnchor_permSphere, BranchPinch.radial_equivariant (permE9 g)]
  exact fromOnePointHomeo_map g _

def pinchCenter (i : Fin 64) : E9 := (i.1 : ℝ) • cA0_E9

def pinchRadius : ℝ := 1 / 4

lemma permE9_pinchCenter (g : P_row) (i : Fin 64) :
    permE9 g (pinchCenter i) = pinchCenter i := by
  simp [pinchCenter, map_smul, permE9_cA0_E9]

lemma dist_pinchCenter_ge_one {i j : Fin 64} (hij : i ≠ j) :
    1 ≤ ‖pinchCenter i - pinchCenter j‖ := by
  have hsub : pinchCenter i - pinchCenter j = ((i.1 : ℝ) - (j.1 : ℝ)) • cA0_E9 := by
    simp only [pinchCenter, sub_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, norm_cA0_E9, mul_one]
  have hne : (i.1 : ℤ) ≠ (j.1 : ℤ) := by
    intro h
    exact hij (Fin.ext (by omega))
  have habs : (1 : ℤ) ≤ |(i.1 : ℤ) - (j.1 : ℤ)| := by
    rcases le_total (i.1 : ℤ) (j.1 : ℤ) with hle | hle
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  exact_mod_cast habs

attribute [irreducible] pinchCenter

lemma pinch_balls_disjoint {i j : Fin 64} (hij : i ≠ j) {y : E9}
    (hi : ‖y - pinchCenter i‖ ≤ pinchRadius) :
    pinchRadius < ‖y - pinchCenter j‖ := by
  have h1 : 1 ≤ ‖(pinchCenter i : Rep10) - (pinchCenter j : Rep10)‖ :=
    dist_pinchCenter_ge_one hij
  have htri : ‖(pinchCenter i : Rep10) - (pinchCenter j : Rep10)‖ ≤
      ‖(y : Rep10) - (pinchCenter i : Rep10)‖ + ‖(y : Rep10) - (pinchCenter j : Rep10)‖ := by
    calc
      ‖(pinchCenter i : Rep10) - (pinchCenter j : Rep10)‖ =
          ‖((y : Rep10) - (pinchCenter j : Rep10)) - ((y : Rep10) - (pinchCenter i : Rep10))‖ := by
        congr 1; abel
      _ ≤ ‖(y : Rep10) - (pinchCenter j : Rep10)‖ + ‖(y : Rep10) - (pinchCenter i : Rep10)‖ :=
        norm_sub_le _ _
      _ = ‖(y : Rep10) - (pinchCenter i : Rep10)‖ + ‖(y : Rep10) - (pinchCenter j : Rep10)‖ :=
        add_comm _ _
  have hi' : ‖(y : Rep10) - (pinchCenter i : Rep10)‖ ≤ 1 / 4 := hi
  change 1 / 4 < ‖(y : Rep10) - (pinchCenter j : Rep10)‖
  linarith

def ballAffine (i : Fin 64) : E9 ≃ₜ E9 where
  toFun y := (4 : ℝ) • (y - pinchCenter i)
  invFun u := pinchCenter i + (1 / 4 : ℝ) • u
  left_inv y := by simp [smul_smul]
  right_inv u := by simp [smul_smul]
  continuous_toFun := (continuous_const : Continuous (fun _ : E9 => (4 : ℝ))).smul
    (continuous_id.sub continuous_const)
  continuous_invFun := continuous_const.add
    ((continuous_const : Continuous (fun _ : E9 => (1 / 4 : ℝ))).smul continuous_id)

def ballPinch (i : Fin 64) : C(OnePoint E9, OnePoint E9) :=
  ((homeoToCont (Homeomorph.onePointCongr (ballAffine i)).symm).comp
    (BranchPinch.collapse (E := E9))).comp
    (homeoToCont (Homeomorph.onePointCongr (ballAffine i)))

@[simp] lemma ballPinch_infty (i : Fin 64) : ballPinch i ∞ = ∞ := by
  simp [ballPinch, BranchPinch.collapse]

lemma ballPinch_outside (i : Fin 64) {y : E9} (hy : pinchRadius ≤ ‖y - pinchCenter i‖) :
    ballPinch i (y : OnePoint E9) = ∞ := by
  simp only [ballPinch, ContinuousMap.comp_apply, homeoToCont_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, BranchPinch.collapse,
    ContinuousMap.coe_mk, BranchPinch.radial_one]
  have hnorm : 1 ≤ ‖ballAffine i y‖ := by
    have hy' : 1 / 4 ≤ ‖(y : Rep10) - (pinchCenter i : Rep10)‖ := hy
    change 1 ≤ ‖((4 : ℝ) • (y - pinchCenter i) : E9)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have heq : ‖y - pinchCenter i‖ = ‖(y : Rep10) - (pinchCenter i : Rep10)‖ := rfl
    linarith
  rw [if_neg (not_lt.mpr hnorm)]
  rfl

lemma ballPinch_equivariant (g : P_row) (i : Fin 64) (p : OnePoint E9) :
    ballPinch i (p.map (permE9 g)) = (ballPinch i p).map (permE9 g) := by
  have haff : ∀ y : E9, ballAffine i (permE9 g y) = permE9 g (ballAffine i y) := fun y => by
    simp only [ballAffine, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, map_smul, map_sub,
      permE9_pinchCenter]
  induction p using OnePoint.rec with
  | infty => simp
  | coe y =>
    simp only [ballPinch, ContinuousMap.comp_apply, homeoToCont_apply,
      Homeomorph.onePointCongr_apply, Homeomorph.onePointCongr_symm_apply,
      OnePoint.map_some, haff]
    have hrad := BranchPinch.radial_equivariant (permE9 g)
      ⟨1, by norm_num⟩ (ballAffine i y : OnePoint E9)
    change (Homeomorph.onePointCongr (ballAffine i)).symm
        (BranchPinch.radial ⟨1, by norm_num⟩ ((ballAffine i y : OnePoint E9).map (permE9 g))) =
      OnePoint.map (permE9 g)
        ((Homeomorph.onePointCongr (ballAffine i)).symm
          (BranchPinch.radial ⟨1, by norm_num⟩ (ballAffine i y : OnePoint E9)))
    rw [hrad]
    generalize BranchPinch.radial ⟨1, by norm_num⟩ (ballAffine i y : OnePoint E9) = q
    induction q using OnePoint.rec with
    | infty => rfl
    | coe u =>
      simp only [Homeomorph.onePointCongr_symm_apply, OnePoint.map_some,
        Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk, ballAffine,
        map_add, map_smul, permE9_pinchCenter]

def pinch64E9Fun (p : OnePoint E9) : OnePoint E9 :=
  p.elim ∞ fun y =>
    if h : ∃ i : Fin 64, ‖y - pinchCenter i‖ < pinchRadius then
      ballPinch h.choose (y : OnePoint E9)
    else ∞

@[simp] lemma pinch64E9Fun_infty : pinch64E9Fun ∞ = ∞ := rfl

lemma pinch64E9Fun_on_closedBall (i : Fin 64) {y : E9} (hy : ‖y - pinchCenter i‖ ≤ pinchRadius) :
    pinch64E9Fun (y : OnePoint E9) = ballPinch i (y : OnePoint E9) := by
  dsimp only [pinch64E9Fun, OnePoint.elim_some]
  by_cases h : ∃ j : Fin 64, ‖y - pinchCenter j‖ < pinchRadius
  · rw [dif_pos h]
    have hEq : h.choose = i := by
      by_contra hne
      exact not_lt_of_gt (pinch_balls_disjoint (Ne.symm hne) hy) h.choose_spec
    exact congrArg (fun k => ballPinch k (y : OnePoint E9)) hEq
  · rw [dif_neg h]
    push Not at h
    exact (ballPinch_outside i (h i)).symm

lemma pinch64E9Fun_outside {y : E9} (hy : ∀ i : Fin 64, pinchRadius ≤ ‖y - pinchCenter i‖) :
    pinch64E9Fun (y : OnePoint E9) = ∞ := by
  dsimp only [pinch64E9Fun, OnePoint.elim_some]
  rw [dif_neg (by push Not; exact hy)]

lemma pinch64E9Fun_equivariant (g : P_row) (p : OnePoint E9) :
    pinch64E9Fun (p.map (permE9 g)) = (pinch64E9Fun p).map (permE9 g) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe y =>
    simp only [OnePoint.map_some]
    by_cases h : ∃ i : Fin 64, ‖y - pinchCenter i‖ < pinchRadius
    · obtain ⟨i, hi⟩ := h
      have hgi : ‖permE9 g y - pinchCenter i‖ ≤ pinchRadius := by
        rw [← permE9_pinchCenter g i, ← map_sub, (permE9 g).norm_map]
        exact hi.le
      rw [pinch64E9Fun_on_closedBall i hgi, pinch64E9Fun_on_closedBall i hi.le]
      exact ballPinch_equivariant g i (y : OnePoint E9)
    · push Not at h
      have hgy : ∀ i : Fin 64, pinchRadius ≤ ‖permE9 g y - pinchCenter i‖ := fun i => by
        rw [← permE9_pinchCenter g i, ← map_sub, (permE9 g).norm_map]
        exact h i
      rw [pinch64E9Fun_outside hgy, pinch64E9Fun_outside h, OnePoint.map_infty]

lemma continuous_pinch64E9Fun : Continuous pinch64E9Fun := by
  let K : Fin 64 → Set (OnePoint E9) := fun i =>
    ((↑) : E9 → OnePoint E9) '' Metric.closedBall (pinchCenter i) pinchRadius
  let U : Fin 64 → Set (OnePoint E9) := fun i =>
    ((↑) : E9 → OnePoint E9) '' Metric.ball (pinchCenter i) pinchRadius
  let Kout : Set (OnePoint E9) := (⋃ i : Fin 64, U i)ᶜ
  have hK_closed : ∀ i : Fin 64, IsClosed (K i) := fun i =>
    OnePoint.isClosed_image_coe.mpr ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩
  have hKout_closed : IsClosed Kout := by
    rw [isClosed_compl_iff]
    exact isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  have hK_cont : ∀ i : Fin 64, ContinuousOn pinch64E9Fun (K i) := fun i => by
    refine (ballPinch i).continuous.continuousOn.congr ?_
    rintro p ⟨y, hy, rfl⟩
    exact pinch64E9Fun_on_closedBall i (Metric.mem_closedBall.mp hy)
  have hKout_cont : ContinuousOn pinch64E9Fun Kout := by
    refine (continuous_const (y := (∞ : OnePoint E9))).continuousOn.congr ?_
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact pinch64E9Fun_infty
    | coe y =>
      refine pinch64E9Fun_outside fun i => ?_
      by_contra hlt
      exact hp (Set.mem_iUnion.mpr ⟨i, ⟨y, Metric.mem_ball.mpr (not_le.mp hlt), rfl⟩⟩)
  have hUnion : ∀ s : Finset (Fin 64),
      IsClosed (⋃ i ∈ s, K i) ∧ ContinuousOn pinch64E9Fun (⋃ i ∈ s, K i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have heq : (⋃ j ∈ insert i s, K j) = K i ∪ ⋃ j ∈ s, K j := by
        simp [Finset.set_biUnion_insert]
      rw [heq]
      exact ⟨(hK_closed i).union ih.1,
        (hK_cont i).union_of_isClosed ih.2 (hK_closed i) ih.1⟩
  have hcov : Kout ∪ (⋃ i ∈ (Finset.univ : Finset (Fin 64)), K i) = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true, Set.mem_union]
    by_cases hp : p ∈ ⋃ i : Fin 64, U i
    · right
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_biUnion (Finset.mem_univ i) ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
    · left
      exact hp
  rw [← continuousOn_univ, ← hcov]
  exact hKout_cont.union_of_isClosed (hUnion Finset.univ).2 hKout_closed (hUnion Finset.univ).1

attribute [irreducible] pinch64E9Fun

def pinch64E9 : C(OnePoint E9, OnePoint E9) :=
  ⟨pinch64E9Fun, continuous_pinch64E9Fun⟩

def pinch64 : C(Metric.sphere (0 : Rep10) 1, Metric.sphere (0 : Rep10) 1) :=
  (homeoToCont stereoAnchor.symm).comp (pinch64E9.comp (homeoToCont stereoAnchor))

lemma pinch64_anchorS : pinch64 anchorS = anchorS := by
  change stereoAnchor.symm (pinch64E9Fun (stereoAnchor anchorS)) = anchorS
  rw [stereoAnchor_anchorS, pinch64E9Fun_infty, stereoAnchor_symm_infty]

lemma pinch64_equivariant (g : P_row) (x : Metric.sphere (0 : Rep10) 1) :
    pinch64 (permSphere g.1 x) = permSphere g.1 (pinch64 x) := by
  change stereoAnchor.symm (pinch64E9Fun (stereoAnchor (permSphere g.1 x))) =
    permSphere g.1 (stereoAnchor.symm (pinch64E9Fun (stereoAnchor x)))
  rw [stereoAnchor_permSphere, pinch64E9Fun_equivariant]
  exact fromOnePointHomeo_map g _

lemma pinch64_fixed_mem (x : FixedP_row) :
    (pinch64 x.1 : Rep10) ∈ fixedSubspace P_row := by
  intro g hg
  have hfg : permSphere g x.1 = x.1 := Subtype.ext (x.2 g hg)
  have heq := pinch64_equivariant ⟨g, hg⟩ x.1
  rw [hfg] at heq
  exact congrArg Subtype.val heq.symm

def pinch64RestrictedP_row : C(FixedP_row, FixedP_row) where
  toFun x := ⟨pinch64 x.1, pinch64_fixed_mem x⟩
  continuous_toFun :=
    (pinch64.continuous.comp continuous_subtype_val).subtype_mk _

lemma pinch64RestrictedP_row_anchorS :
    pinch64RestrictedP_row anchorS_P_row = anchorS_P_row :=
  Subtype.ext pinch64_anchorS

theorem nullHomotopy_pinch64_q0_P_row :
    Nonempty (ContinuousMap.HomotopyRel
      (pinch64RestrictedP_row.comp q0RestrictedP_row)
      (ContinuousMap.const FixedP_row anchorS_P_row)
      {anchorS_P_row}) := by
  obtain ⟨H⟩ := nullHomotopy_q0_P_row
  refine ⟨(H.compContinuousMap pinch64RestrictedP_row).cast rfl ?_⟩
  ext1 x
  exact pinch64RestrictedP_row_anchorS

end BranchAndPinch64

end AkopyanResearch
