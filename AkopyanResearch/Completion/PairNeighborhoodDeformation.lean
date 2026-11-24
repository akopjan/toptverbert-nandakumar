module

public import AkopyanResearch.Completion.PairCommonAlignment

/-!
# An explicit neighborhood deformation onto the actual collapsed locus

Remove the antipodal pure-common locus from the product of the two unit
spheres. Continuous weighted alignment of the common components, followed
by normalization, strongly deforms this open neighborhood onto the original
closed chart complement. No triangulation or cofibration theorem is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairNeighborhoodDeformation

open PairCollapse PairCommonAlignment PairDeformation

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def badAntipodal : Set (PairSpace U V W) :=
  {x | x.1.val.1 = 0 ∧ x.2.val.1 = 0 ∧ x.1.val.2 + x.2.val.2 = 0}

abbrev Neighborhood := {x : PairSpace U V W // x ∉ badAntipodal}
abbrev Locus := PairCollapsedLocus.Locus (U := U) (V := V) (W := W)

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] [InnerProductSpace ℝ W] in
theorem isClosed_badAntipodal : IsClosed (badAntipodal (U := U) (V := V) (W := W)) := by
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const))

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] [InnerProductSpace ℝ W] in
theorem isOpen_neighborhood : IsOpen (badAntipodal (U := U) (V := V) (W := W))ᶜ :=
  isClosed_badAntipodal.isOpen_compl

omit [InnerProductSpace ℝ W] in
theorem common_norm_le_one {F : Type*} [NormedAddCommGroup F]
    (x : FullUnit F W) : ‖x.val.2‖ ≤ 1 := by
  nlinarith [x.property, sq_nonneg ‖x.val.1‖, norm_nonneg x.val.2]

omit [InnerProductSpace ℝ W] in
theorem common_norm_eq_one {F : Type*} [NormedAddCommGroup F]
    (x : FullUnit F W) (hx : x.val.1 = 0) : ‖x.val.2‖ = 1 := by
  have he := x.property
  rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at he
  nlinarith [norm_nonneg x.val.2]

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem locus_not_bad (x : Locus (U := U) (V := V) (W := W)) : x.val ∉ badAntipodal := by
  rintro ⟨ha, hb, hsum⟩
  have hza := common_norm_eq_one x.val.1 ha
  have hzb := common_norm_eq_one x.val.2 hb
  have he : x.val.1.val.2 = x.val.2.val.2 := by
    have h := PairCollapsedLocus.relation x
    change ‖x.val.2.val.2‖ • x.val.1.val.2 = ‖x.val.1.val.2‖ • x.val.2.val.2 at h
    simpa only [hza, hzb, one_smul] using h
  have hn := congrArg norm hsum
  rw [← he, ← two_smul ℝ x.val.1.val.2, norm_smul, hza, norm_zero] at hn
  norm_num at hn

def inclusion (x : Locus (U := U) (V := V) (W := W)) :
    Neighborhood (U := U) (V := V) (W := W) := ⟨x.val, locus_not_bad x⟩

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem continuous_inclusion : Continuous (inclusion (U := U) (V := V) (W := W)) :=
  continuous_subtype_val.subtype_mk _

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem first_interpolation_safe (t : Time) (a : FullUnit V W) (b : FullUnit U W)
    (hbad : ¬ (a.val.1 = 0 ∧ b.val.1 = 0 ∧ a.val.2 + b.val.2 = 0)) :
    a.val.1 ≠ 0 ∨ interpolate t a.val.2 b.val.2 ≠ 0 := by
  by_cases ha : a.val.1 = 0
  · right
    have hza := common_norm_eq_one a ha
    have hsum : a.val.2 + b.val.2 ≠ 0 := by
      intro hzero
      have he : b.val.2 = -a.val.2 := eq_neg_of_add_eq_zero_right hzero
      have hzb : ‖b.val.2‖ = 1 := by rw [he, norm_neg, hza]
      have hnb : ‖b.val.1‖ = 0 := by
        have hb := b.property
        rw [hzb] at hb
        nlinarith [norm_nonneg b.val.1]
      exact hbad ⟨ha, norm_eq_zero.mp hnb, hzero⟩
    exact interpolate_ne_zero_of_unit t _ _ hza (common_norm_le_one b) hsum
  · exact Or.inl ha

def rawFirst (p : Time × Neighborhood (U := U) (V := V) (W := W)) : V × W :=
  (p.2.val.1.val.1, interpolate p.1 p.2.val.1.val.2 p.2.val.2.val.2)

def rawSecond (p : Time × Neighborhood (U := U) (V := V) (W := W)) : U × W :=
  (p.2.val.2.val.1, interpolate p.1 p.2.val.2.val.2 p.2.val.1.val.2)

def firstTest (p : Time × Neighborhood (U := U) (V := V) (W := W)) :
    PairCollapsedLocus.NonzeroPair (F := V) (W := W) :=
  ⟨rawFirst p, first_interpolation_safe p.1 p.2.val.1 p.2.val.2 p.2.property⟩

def secondTest (p : Time × Neighborhood (U := U) (V := V) (W := W)) :
    PairCollapsedLocus.NonzeroPair (F := U) (W := W) :=
  ⟨rawSecond p, first_interpolation_safe p.1 p.2.val.2 p.2.val.1 (by
    rintro ⟨hb, ha, hs⟩
    exact p.2.property ⟨ha, hb, by rwa [add_comm]⟩)⟩

def deformationRaw (p : Time × Neighborhood (U := U) (V := V) (W := W)) : PairSpace U V W :=
  (PairCollapsedLocus.normalize (firstTest p), PairCollapsedLocus.normalize (secondTest p))

theorem continuous_deformationRaw :
    Continuous (deformationRaw (U := U) (V := V) (W := W)) := by
  have h₁ : Continuous (firstTest (U := U) (V := V) (W := W)) := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    exact continuous_interpolate.comp (continuous_fst.prodMk
      ((by fun_prop : Continuous (fun p : Time × Neighborhood (U := U) (V := V) (W := W) =>
        p.2.val.1.val.2)).prodMk (by fun_prop)))
  have h₂ : Continuous (secondTest (U := U) (V := V) (W := W)) := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    exact continuous_interpolate.comp (continuous_fst.prodMk
      ((by fun_prop : Continuous (fun p : Time × Neighborhood (U := U) (V := V) (W := W) =>
        p.2.val.2.val.2)).prodMk (by fun_prop)))
  exact (PairCollapsedLocus.continuous_normalize.comp h₁).prodMk
    (PairCollapsedLocus.continuous_normalize.comp h₂)

theorem deformationRaw_not_bad (p : Time × Neighborhood (U := U) (V := V) (W := W)) :
    deformationRaw p ∉ badAntipodal := by
  rintro ⟨ha, hb, hsum⟩
  have hra := PairCollapsedLocus.radius_pos (firstTest p)
  have hrb := PairCollapsedLocus.radius_pos (secondTest p)
  have hpa : p.2.val.1.val.1 = 0 := by
    change (PairCollapsedLocus.radius (rawFirst p))⁻¹ • p.2.val.1.val.1 = 0 at ha
    exact (smul_eq_zero.mp ha).resolve_left (inv_ne_zero hra.ne')
  have hpb : p.2.val.2.val.1 = 0 := by
    change (PairCollapsedLocus.radius (rawSecond p))⁻¹ • p.2.val.2.val.1 = 0 at hb
    exact (smul_eq_zero.mp hb).resolve_left (inv_ne_zero hrb.ne')
  have hza := common_norm_eq_one p.2.val.1 hpa
  have hzb := common_norm_eq_one p.2.val.2 hpb
  have he : PairCollapsedLocus.radius (rawFirst p) = PairCollapsedLocus.radius (rawSecond p) := by
    unfold PairCollapsedLocus.radius rawFirst rawSecond
    rw [hpa, hpb, norm_zero, norm_zero,
      norm_interpolate_eq_of_unit p.1 _ _ hza hzb]
  change (PairCollapsedLocus.radius (rawFirst p))⁻¹ •
      interpolate p.1 p.2.val.1.val.2 p.2.val.2.val.2 +
    (PairCollapsedLocus.radius (rawSecond p))⁻¹ •
      interpolate p.1 p.2.val.2.val.2 p.2.val.1.val.2 = 0 at hsum
  rw [← he, ← smul_add, interpolate_add_swap] at hsum
  exact p.2.property ⟨hpa, hpb, (smul_eq_zero.mp hsum).resolve_left (inv_ne_zero hra.ne')⟩

def deformation (p : Time × Neighborhood (U := U) (V := V) (W := W)) :
    Neighborhood (U := U) (V := V) (W := W) := ⟨deformationRaw p, deformationRaw_not_bad p⟩

theorem continuous_deformation :
    Continuous (deformation (U := U) (V := V) (W := W)) :=
  continuous_deformationRaw.subtype_mk _

theorem deformationRaw_end_mem_locus (x : Neighborhood (U := U) (V := V) (W := W)) :
    deformationRaw (⟨1, by simp⟩, x) ∉ chartDomain := by
  let p : Time × Neighborhood (U := U) (V := V) (W := W) := (⟨1, by simp⟩, x)
  let z := x.val.1.val.2
  let w := x.val.2.val.2
  let r := (PairCollapsedLocus.radius (rawFirst p))⁻¹ * (‖z‖ / (‖z‖ + ‖w‖))
  let s := (PairCollapsedLocus.radius (rawSecond p))⁻¹ * (‖w‖ / (‖z‖ + ‖w‖))
  have hr : 0 ≤ r := mul_nonneg
    (inv_nonneg.mpr (PairCollapsedLocus.radius_pos (firstTest p)).le)
    (div_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hs : 0 ≤ s := mul_nonneg
    (inv_nonneg.mpr (PairCollapsedLocus.radius_pos (secondTest p)).le)
    (div_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  apply not_not.mpr
  change ‖(PairCollapsedLocus.radius (rawSecond p))⁻¹ • interpolate p.1 w z‖ •
      ((PairCollapsedLocus.radius (rawFirst p))⁻¹ • interpolate p.1 z w) =
    ‖(PairCollapsedLocus.radius (rawFirst p))⁻¹ • interpolate p.1 z w‖ •
      ((PairCollapsedLocus.radius (rawSecond p))⁻¹ • interpolate p.1 w z)
  simpa only [interpolate, p, sub_self, zero_smul, one_smul, one_mul, zero_add,
    align, add_comm w z, add_comm ‖w‖ ‖z‖, smul_smul, r, s] using
    nonneg_smul_relation r s hr hs (z + w)

def retraction (x : Neighborhood (U := U) (V := V) (W := W)) :
    Locus (U := U) (V := V) (W := W) :=
  ⟨deformationRaw (⟨1, by simp⟩, x), deformationRaw_end_mem_locus x⟩

theorem continuous_retraction : Continuous (retraction (U := U) (V := V) (W := W)) :=
  (continuous_deformationRaw.comp (continuous_const.prodMk continuous_id)).subtype_mk _

theorem deformation_start (x : Neighborhood (U := U) (V := V) (W := W)) :
    deformation (⟨0, by simp⟩, x) = x := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (PairCollapsedLocus.normalize_unit _ (by
      simpa [firstTest, rawFirst, interpolate] using x.val.1.property)).trans
      (by simp [firstTest, rawFirst, interpolate])
  · exact (PairCollapsedLocus.normalize_unit _ (by
      simpa [secondTest, rawSecond, interpolate] using x.val.2.property)).trans
      (by simp [secondTest, rawSecond, interpolate])

theorem deformation_end (x : Neighborhood (U := U) (V := V) (W := W)) :
    deformation (⟨1, by simp⟩, x) = inclusion (retraction x) := by
  apply Subtype.ext
  rfl

theorem deformationRaw_fixes (t : Time) (x : Locus (U := U) (V := V) (W := W)) :
    deformationRaw (t, inclusion x) = x.val := by
  have hr := PairCollapsedLocus.relation x
  change ‖x.val.2.val.2‖ • x.val.1.val.2 = ‖x.val.1.val.2‖ • x.val.2.val.2 at hr
  have h₁ : rawFirst (t, inclusion x) = x.val.1.val := by
    apply Prod.ext
    · rfl
    · exact interpolate_fixes t _ _ hr
  have h₂ : rawSecond (t, inclusion x) = x.val.2.val := by
    apply Prod.ext
    · rfl
    · exact interpolate_fixes t _ _ hr.symm
  apply Prod.ext <;> apply Subtype.ext
  · exact (PairCollapsedLocus.normalize_unit _ (by
      simpa only [firstTest, h₁] using x.val.1.property)).trans h₁
  · exact (PairCollapsedLocus.normalize_unit _ (by
      simpa only [secondTest, h₂] using x.val.2.property)).trans h₂

theorem deformation_fixes (t : Time) (x : Locus (U := U) (V := V) (W := W)) :
    deformation (t, inclusion x) = inclusion x :=
  Subtype.ext (deformationRaw_fixes t x)

theorem retraction_inclusion (x : Locus (U := U) (V := V) (W := W)) :
    retraction (inclusion x) = x :=
  Subtype.ext (deformationRaw_fixes ⟨1, by simp⟩ x)

/-- Every displayed map is continuous, both endpoints are exact, and the
actual closed chart complement is fixed throughout the homotopy. -/
theorem strong_neighborhood_deformation :
    IsOpen (badAntipodal (U := U) (V := V) (W := W))ᶜ ∧
    Continuous (inclusion (U := U) (V := V) (W := W)) ∧
    Continuous (retraction (U := U) (V := V) (W := W)) ∧
    (∀ x : Locus (U := U) (V := V) (W := W), retraction (inclusion x) = x) ∧
    Continuous (deformation (U := U) (V := V) (W := W)) ∧
    (∀ x : Neighborhood (U := U) (V := V) (W := W), deformation (⟨0, by simp⟩, x) = x) ∧
    (∀ x : Neighborhood (U := U) (V := V) (W := W),
      deformation (⟨1, by simp⟩, x) = inclusion (retraction x)) ∧
    (∀ (t : Time) (x : Locus (U := U) (V := V) (W := W)),
      deformation (t, inclusion x) = inclusion x) :=
  ⟨isOpen_neighborhood, continuous_inclusion, continuous_retraction,
    retraction_inclusion, continuous_deformation, deformation_start,
    deformation_end, deformation_fixes⟩

end AkopyanResearch.PairNeighborhoodDeformation
