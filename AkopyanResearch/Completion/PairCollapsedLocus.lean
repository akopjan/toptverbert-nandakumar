module

public import AkopyanResearch.PairCollapse
public import AkopyanResearch.Completion.PairDeformation

/-!
# Strong deformation of the actual collapsed locus

The complement of the original pair chart strongly deformation retracts onto
its subspace of equal common components. The larger common vector gives a
continuous choice on this locus; private vectors are shortened and the straight
homotopy is normalized. The zero-common cases, continuity, both endpoints and
pointwise fixing are proved. No comparison-connectivity statement is assumed
or concluded.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairCollapsedLocus

open PairCollapse PairDeformation

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The actual closed locus collapsed by the pair chart. -/
abbrev Locus := {x : PairSpace U V W // x ∉ chartDomain}

abbrev privateA (x : Locus (U := U) (V := V) (W := W)) : V := x.val.1.val.1
abbrev privateB (x : Locus (U := U) (V := V) (W := W)) : U := x.val.2.val.1
abbrev commonA (x : Locus (U := U) (V := V) (W := W)) : W := x.val.1.val.2
abbrev commonB (x : Locus (U := U) (V := V) (W := W)) : W := x.val.2.val.2

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem relation (x : Locus (U := U) (V := V) (W := W)) :
    ‖commonB x‖ • commonA x = ‖commonA x‖ • commonB x :=
  not_not.mp x.property

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem common_eq_of_norm_eq (x : Locus (U := U) (V := V) (W := W))
    (he : ‖commonB x‖ = ‖commonA x‖) : commonA x = commonB x := by
  by_cases h : ‖commonA x‖ = 0
  · exact (norm_eq_zero.mp h).trans (norm_eq_zero.mp (he.trans h)).symm
  · have hh := congrArg (fun w : W => ‖commonA x‖⁻¹ • w) (relation x)
    simpa only [he, smul_smul, inv_mul_cancel₀ h, one_smul] using hh

def common (x : Locus (U := U) (V := V) (W := W)) : W :=
  if ‖commonB x‖ ≤ ‖commonA x‖ then commonA x else commonB x

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem continuous_common : Continuous (common (U := U) (V := V) (W := W)) := by
  apply continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact common_eq_of_norm_eq

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem norm_common (x : Locus (U := U) (V := V) (W := W)) :
    ‖common x‖ = max ‖commonA x‖ ‖commonB x‖ := by
  by_cases h : ‖commonB x‖ ≤ ‖commonA x‖
  · simp [common, h]
  · simp [common, h, max_eq_right (le_of_not_ge h)]

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem first_scaled (x : Locus (U := U) (V := V) (W := W)) :
    ‖common x‖ • commonA x = ‖commonA x‖ • common x := by
  by_cases h : ‖commonB x‖ ≤ ‖commonA x‖
  · simp [common, h]
  · simpa only [common, ite_eq_right h] using relation x

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem second_scaled (x : Locus (U := U) (V := V) (W := W)) :
    ‖common x‖ • commonB x = ‖commonB x‖ • common x := by
  by_cases h : ‖commonB x‖ ≤ ‖commonA x‖
  · simpa only [common, ite_eq_left h] using (relation x).symm
  · simp [common, h]

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem common_zero (x : Locus (U := U) (V := V) (W := W))
    (h : common x = 0) : commonA x = 0 ∧ commonB x = 0 := by
  have hm : max ‖commonA x‖ ‖commonB x‖ = 0 := by rw [← norm_common, h, norm_zero]
  exact ⟨norm_eq_zero.mp (le_antisymm (hm ▸ le_max_left _ _) (norm_nonneg _)),
    norm_eq_zero.mp (le_antisymm (hm ▸ le_max_right _ _) (norm_nonneg _))⟩

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem first_as_common (x : Locus (U := U) (V := V) (W := W)) :
    commonA x = (‖commonA x‖ / ‖common x‖) • common x := by
  by_cases h : common x = 0
  · simp [h, (common_zero x h).1]
  · have hh := congrArg (fun w : W => ‖common x‖⁻¹ • w) (first_scaled x)
    simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h), one_smul,
      div_eq_mul_inv, mul_comm] using hh

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem second_as_common (x : Locus (U := U) (V := V) (W := W)) :
    commonB x = (‖commonB x‖ / ‖common x‖) • common x := by
  by_cases h : common x = 0
  · simp [h, (common_zero x h).2]
  · have hh := congrArg (fun w : W => ‖common x‖⁻¹ • w) (second_scaled x)
    simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h), one_smul,
      div_eq_mul_inv, mul_comm] using hh

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem private_norm_le (x : Locus (U := U) (V := V) (W := W))
    (h : ‖commonB x‖ ≤ ‖commonA x‖) : ‖privateA x‖ ≤ ‖privateB x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  linarith [x.val.1.property, x.val.2.property]

theorem endpoint_unit (x : Locus (U := U) (V := V) (W := W)) :
    ‖shorten (privateA x) (privateB x)‖ ^ 2 + ‖common x‖ ^ 2 = 1 ∧
    ‖shorten (privateB x) (privateA x)‖ ^ 2 + ‖common x‖ ^ 2 = 1 := by
  rw [norm_shorten, norm_shorten, min_comm ‖privateB x‖]
  suffices h : (min ‖privateA x‖ ‖privateB x‖) ^ 2 + ‖common x‖ ^ 2 = 1 from ⟨h,h⟩
  by_cases h : ‖commonB x‖ ≤ ‖commonA x‖
  · simpa only [min_eq_left (private_norm_le x h), common, ite_eq_left h] using x.val.1.property
  · have hn : ‖privateB x‖ ≤ ‖privateA x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (le_of_not_ge h)
      linarith [x.val.1.property, x.val.2.property]
    simpa only [min_eq_right hn, common, ite_eq_right h] using x.val.2.property

abbrev Balanced := {x : Locus (U := U) (V := V) (W := W) // commonA x = commonB x}

def inclusion (x : Balanced (U := U) (V := V) (W := W)) : Locus (U := U) (V := V) (W := W) := x.val

def retraction (x : Locus (U := U) (V := V) (W := W)) : Balanced (U := U) (V := V) (W := W) :=
  ⟨⟨(⟨(shorten (privateA x) (privateB x), common x), (endpoint_unit x).1⟩,
    ⟨(shorten (privateB x) (privateA x), common x), (endpoint_unit x).2⟩), by
      change ¬ (‖common x‖ • common x ≠ ‖common x‖ • common x)
      simp⟩, rfl⟩

theorem continuous_retraction : Continuous (retraction (U := U) (V := V) (W := W)) := by
  have ha : Continuous (privateA (U := U) (V := V) (W := W)) := by fun_prop
  have hb : Continuous (privateB (U := U) (V := V) (W := W)) := by fun_prop
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_shorten.comp (ha.prodMk hb)).prodMk continuous_common
  · apply Continuous.subtype_mk
    exact (continuous_shorten.comp (hb.prodMk ha)).prodMk continuous_common

theorem retraction_inclusion (x : Balanced (U := U) (V := V) (W := W)) :
    retraction (inclusion x) = x := by
  have he := x.property
  have hn : ‖privateA x.val‖ = ‖privateB x.val‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h1 := x.val.val.1.property
    have h2 := x.val.val.2.property
    change ‖privateA x.val‖^2 + ‖commonA x.val‖^2 = 1 at h1
    change ‖privateB x.val‖^2 + ‖commonB x.val‖^2 = 1 at h2
    rw [he] at h1
    linarith
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · change (shorten (privateA x.val) (privateB x.val), common x.val) = _
    rw [shorten_eq_left _ _ hn.le]
    simp only [common, he, le_refl, ite_true]
    exact Prod.ext rfl he.symm
  · change (shorten (privateB x.val) (privateA x.val), common x.val) = _
    rw [shorten_eq_left _ _ hn.symm.le]
    simp only [common, he, le_refl, ite_true]

section Normalize
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev NonzeroPair := {p : F × W // p.1 ≠ 0 ∨ p.2 ≠ 0}

def radius (p : F × W) : ℝ := Real.sqrt (‖p.1‖^2 + ‖p.2‖^2)

omit [InnerProductSpace ℝ W] [NormedSpace ℝ F] in
theorem radius_pos (p : NonzeroPair (F := F) (W := W)) : 0 < radius p.val := by
  apply Real.sqrt_pos.mpr
  rcases p.property with h | h
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr h) 2) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.mpr h) 2)

def normalize (p : NonzeroPair (F := F) (W := W)) : FullUnit F W :=
  ⟨((radius p.val)⁻¹ • p.val.1, (radius p.val)⁻¹ • p.val.2), by
    have hr := radius_pos p
    have hs : radius p.val ^ 2 = ‖p.val.1‖^2 + ‖p.val.2‖^2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc
      _ = (radius p.val)⁻¹^2 * (‖p.val.1‖^2 + ‖p.val.2‖^2) := by ring
      _ = (radius p.val)⁻¹^2 * radius p.val^2 := by rw [hs]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]⟩

theorem continuous_normalize : Continuous (normalize (F := F) (W := W)) := by
  have hr : Continuous (fun p : NonzeroPair (F := F) (W := W) => (radius p.val)⁻¹) := by
    apply Continuous.inv₀ _ (fun p => (radius_pos p).ne')
    unfold radius
    fun_prop
  exact ((hr.smul (by fun_prop)).prodMk (hr.smul (by fun_prop))).subtype_mk _

theorem normalize_unit (p : NonzeroPair (F := F) (W := W))
    (h : ‖p.val.1‖^2 + ‖p.val.2‖^2 = 1) : (normalize p).val = p.val := by
  have hr : radius p.val = 1 := by rw [radius, h, Real.sqrt_one]
  simp [normalize, hr]

end Normalize

def rawFirst (p : Time × Locus (U := U) (V := V) (W := W)) : V × W :=
  (1-p.1.val) • p.2.val.1.val + p.1.val • (retraction p.2).val.val.1.val

def rawSecond (p : Time × Locus (U := U) (V := V) (W := W)) : U × W :=
  (1-p.1.val) • p.2.val.2.val + p.1.val • (retraction p.2).val.val.2.val

def coeff (t : Time) (r R : ℝ) : ℝ := (1-t.val)*(r/R)+t.val

theorem coeff_nonneg (t : Time) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    0 ≤ coeff t r R :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg hr hR)) t.property.1

theorem rawFirst_common (p : Time × Locus (U := U) (V := V) (W := W)) :
    (rawFirst p).2 = coeff p.1 ‖commonA p.2‖ ‖common p.2‖ • common p.2 := by
  change (1-p.1.val) • commonA p.2 + p.1.val • common p.2 = _
  conv_lhs => rw [first_as_common p.2, smul_smul, ← add_smul]
  rfl

theorem rawSecond_common (p : Time × Locus (U := U) (V := V) (W := W)) :
    (rawSecond p).2 = coeff p.1 ‖commonB p.2‖ ‖common p.2‖ • common p.2 := by
  change (1-p.1.val) • commonB p.2 + p.1.val • common p.2 = _
  conv_lhs => rw [second_as_common p.2, smul_smul, ← add_smul]
  rfl

theorem raw_nonzero (p : Time × Locus (U := U) (V := V) (W := W)) :
    ((rawFirst p).1 ≠ 0 ∨ (rawFirst p).2 ≠ 0) ∧
    ((rawSecond p).1 ≠ 0 ∨ (rawSecond p).2 ≠ 0) := by
  by_cases ht : p.1.val = 0
  · simp only [rawFirst, rawSecond, ht, sub_zero, one_smul, zero_smul, add_zero]
    constructor
    · by_contra h
      push Not at h
      have hh := p.2.val.1.property
      simp [h.1, h.2] at hh
    · by_contra h
      push Not at h
      have hh := p.2.val.2.property
      simp [h.1, h.2] at hh
  · by_cases hc : common p.2 = 0
    · have hz := common_zero p.2 hc
      let b : Balanced (U := U) (V := V) (W := W) := ⟨p.2, hz.1.trans hz.2.symm⟩
      have he : (retraction p.2).val = p.2 := congrArg Subtype.val (retraction_inclusion b)
      have hF : rawFirst p = p.2.val.1.val := by
        simp only [rawFirst, he, ← add_smul, sub_add_cancel, one_smul]
      have hS : rawSecond p = p.2.val.2.val := by
        simp only [rawSecond, he, ← add_smul, sub_add_cancel, one_smul]
      rw [hF, hS]
      constructor
      · by_contra h
        push Not at h
        have hh := p.2.val.1.property
        simp [h.1, h.2] at hh
      · by_contra h
        push Not at h
        have hh := p.2.val.2.property
        simp [h.1, h.2] at hh
    · have htp : 0 < p.1.val := lt_of_le_of_ne p.1.property.1 (Ne.symm ht)
      have hp (r : ℝ) (hr : 0 ≤ r) : 0 < coeff p.1 r ‖common p.2‖ :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr p.1.property.2) (div_nonneg hr (norm_nonneg _))) htp
      constructor <;> right
      · rw [rawFirst_common]
        exact smul_ne_zero (hp _ (norm_nonneg _)).ne' hc
      · rw [rawSecond_common]
        exact smul_ne_zero (hp _ (norm_nonneg _)).ne' hc

def firstNonzero (p : Time × Locus (U := U) (V := V) (W := W)) : NonzeroPair (F := V) (W := W) :=
  ⟨rawFirst p, (raw_nonzero p).1⟩
def secondNonzero (p : Time × Locus (U := U) (V := V) (W := W)) : NonzeroPair (F := U) (W := W) :=
  ⟨rawSecond p, (raw_nonzero p).2⟩

def deformation (p : Time × Locus (U := U) (V := V) (W := W)) : Locus (U := U) (V := V) (W := W) :=
  ⟨(normalize (firstNonzero p), normalize (secondNonzero p)), by
    change ¬ (‖(normalize (secondNonzero p)).val.2‖ • (normalize (firstNonzero p)).val.2 ≠
      ‖(normalize (firstNonzero p)).val.2‖ • (normalize (secondNonzero p)).val.2)
    apply not_not.mpr
    change ‖(radius (rawSecond p))⁻¹ • (rawSecond p).2‖ •
        ((radius (rawFirst p))⁻¹ • (rawFirst p).2) =
      ‖(radius (rawFirst p))⁻¹ • (rawFirst p).2‖ •
        ((radius (rawSecond p))⁻¹ • (rawSecond p).2)
    rw [rawFirst_common, rawSecond_common]
    have ha : 0 ≤ (radius (rawFirst p))⁻¹ * coeff p.1 ‖commonA p.2‖ ‖common p.2‖ :=
      mul_nonneg (inv_nonneg.mpr (radius_pos (firstNonzero p)).le)
        (coeff_nonneg p.1 (norm_nonneg _) (norm_nonneg _))
    have hb : 0 ≤ (radius (rawSecond p))⁻¹ * coeff p.1 ‖commonB p.2‖ ‖common p.2‖ :=
      mul_nonneg (inv_nonneg.mpr (radius_pos (secondNonzero p)).le)
        (coeff_nonneg p.1 (norm_nonneg _) (norm_nonneg _))
    simp only [smul_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    congr 1
    ring⟩

theorem continuous_deformation : Continuous (deformation (U := U) (V := V) (W := W)) := by
  have ht : Continuous (fun p : Time × Locus (U := U) (V := V) (W := W) => p.1.val) := by fun_prop
  have hr := continuous_retraction (U := U) (V := V) (W := W)
  have hr0 : Continuous (fun p : Time × Locus (U := U) (V := V) (W := W) =>
      (retraction p.2).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp (hr.comp continuous_snd))
  have hF : Continuous (firstNonzero (U := U) (V := V) (W := W)) := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub ht).smul (by fun_prop)).add
      (ht.smul (continuous_subtype_val.comp hr0.fst))
  have hS : Continuous (secondNonzero (U := U) (V := V) (W := W)) := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub ht).smul (by fun_prop)).add
      (ht.smul (continuous_subtype_val.comp hr0.snd))
  exact ((continuous_normalize.comp hF).prodMk (continuous_normalize.comp hS)).subtype_mk _

theorem deformation_start (x : Locus (U := U) (V := V) (W := W)) :
    deformation (⟨0, by simp⟩, x) = x := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (normalize_unit _ (by simpa [firstNonzero, rawFirst] using x.val.1.property)).trans
      (by simp [firstNonzero, rawFirst])
  · exact (normalize_unit _ (by simpa [secondNonzero, rawSecond] using x.val.2.property)).trans
      (by simp [secondNonzero, rawSecond])

theorem deformation_end (x : Locus (U := U) (V := V) (W := W)) :
    deformation (⟨1, by simp⟩, x) = inclusion (retraction x) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (normalize_unit _ (by simpa [firstNonzero, rawFirst] using (retraction x).val.val.1.property)).trans
      (by simp [firstNonzero, rawFirst, inclusion])
  · exact (normalize_unit _ (by simpa [secondNonzero, rawSecond] using (retraction x).val.val.2.property)).trans
      (by simp [secondNonzero, rawSecond, inclusion])

theorem deformation_fixes (t : Time) (x : Balanced (U := U) (V := V) (W := W)) :
    deformation (t, inclusion x) = inclusion x := by
  have he : (retraction (inclusion x)).val = x.val := congrArg Subtype.val (retraction_inclusion x)
  change (retraction x.val).val = x.val at he
  have hF : rawFirst (t, inclusion x) = x.val.val.1.val := by
    simp only [rawFirst, inclusion, he, ← add_smul, sub_add_cancel, one_smul]
  have hS : rawSecond (t, inclusion x) = x.val.val.2.val := by
    simp only [rawSecond, inclusion, he, ← add_smul, sub_add_cancel, one_smul]
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (normalize_unit _ (by simpa only [firstNonzero, hF] using x.val.val.1.property)).trans hF
  · exact (normalize_unit _ (by simpa only [secondNonzero, hS] using x.val.val.2.property)).trans hS

/-- The actual complement of `PairCollapse.chartDomain` strongly retracts onto
the locus where the two common components are equal. -/
theorem strong_deformation_retraction :
    Continuous (inclusion (U := U) (V := V) (W := W)) ∧
    Continuous (retraction (U := U) (V := V) (W := W)) ∧
    (∀ x : Balanced (U := U) (V := V) (W := W), retraction (inclusion x) = x) ∧
    Continuous (deformation (U := U) (V := V) (W := W)) ∧
    (∀ x : Locus (U := U) (V := V) (W := W), deformation (⟨0, by simp⟩, x) = x) ∧
    (∀ x : Locus (U := U) (V := V) (W := W), deformation (⟨1, by simp⟩, x) = inclusion (retraction x)) ∧
    (∀ (t : Time) (x : Balanced (U := U) (V := V) (W := W)), deformation (t, inclusion x) = inclusion x) :=
  ⟨continuous_subtype_val, continuous_retraction, retraction_inclusion,
    continuous_deformation, deformation_start, deformation_end, deformation_fixes⟩


end AkopyanResearch.PairCollapsedLocus
