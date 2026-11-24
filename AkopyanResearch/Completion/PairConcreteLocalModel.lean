module

public import AkopyanResearch.Completion.PairNormalModel
public import AkopyanResearch.Completion.PairBalancedJoin

/-!
# The original pair tests in the explicit local model

The common-equality space of the original two `Rep10` tests is linearly
homeomorphic to `Comm6 × Priv4 × Priv4`. The complement of the two zero tests
is exactly the normal complement, and its canonical normalization is the
original normalization into the two representation spheres.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairConcreteLocalModel

open PairNormalModel PairLocalEquivalence
open scoped ContinuousMap

abbrev RawNormal := Comm6 × Priv4 × Priv4
abbrev Normal := NormalComplement (U := Priv4) (V := Priv4) (W := Comm6)
abbrev Collapsed := PairLocalEquivalence.Collapsed (U := Priv4) (V := Priv4) (W := Comm6)
abbrev CommonComplement := {x : commonEquality // x.val.1 ≠ 0 ∧ x.val.2 ≠ 0}

def commonRawEquiv : commonEquality ≃ₗ[ℝ] RawNormal where
  toFun x := ((splitRep10 x.val.1).snd, (splitRep10 x.val.1).fst,
    (splitRep10 x.val.2).fst)
  invFun x := ⟨(splitRep10.symm (WithLp.toLp 2 (x.2.1, x.1)),
    splitRep10.symm (WithLp.toLp 2 (x.2.2, x.1))), by
      rw [mem_commonEquality]
      simp only [LinearIsometryEquiv.apply_symm_apply]
      rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact splitRep10.symm_apply_apply x.val.1
    · have he := (mem_commonEquality x.val).mp x.property
      change splitRep10.symm
        (WithLp.toLp 2 ((splitRep10 x.val.2).fst, (splitRep10 x.val.1).snd)) = x.val.2
      rw [he]
      exact splitRep10.symm_apply_apply x.val.2
  right_inv x := by
    change ((splitRep10 (splitRep10.symm (WithLp.toLp 2 (x.2.1, x.1)))).snd,
      (splitRep10 (splitRep10.symm (WithLp.toLp 2 (x.2.1, x.1)))).fst,
      (splitRep10 (splitRep10.symm (WithLp.toLp 2 (x.2.2, x.1)))).fst) = x
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rfl
  map_add' x y := by
    change ((splitRep10 (x.val.1 + y.val.1)).snd,
      (splitRep10 (x.val.1 + y.val.1)).fst, (splitRep10 (x.val.2 + y.val.2)).fst) = _
    rw [map_add, map_add]
    rfl
  map_smul' r x := by
    change ((splitRep10 (r • x.val.1)).snd,
      (splitRep10 (r • x.val.1)).fst, (splitRep10 (r • x.val.2)).fst) = _
    rw [map_smul, map_smul]
    rfl

def commonRawContinuousEquiv : commonEquality ≃L[ℝ] RawNormal :=
  commonRawEquiv.toContinuousLinearEquiv

theorem split_eq_zero_iff (x : Rep10) :
    x = 0 ↔ (splitRep10 x).fst = 0 ∧ (splitRep10 x).snd = 0 := by
  constructor
  · rintro rfl
    rw [splitRep10.map_zero]
    exact ⟨rfl, rfl⟩
  · intro h
    apply splitRep10.injective
    rw [splitRep10.map_zero]
    apply (WithLp.equiv 2 (Priv4 × Comm6)).injective
    exact Prod.ext h.1 h.2

theorem common_raw_safe_iff (x : commonEquality) :
    PairDeformation.Safe (commonRawEquiv x) ↔ x.val.1 ≠ 0 ∧ x.val.2 ≠ 0 := by
  classical
  change (((splitRep10 x.val.1).snd ≠ 0 ∨ (splitRep10 x.val.1).fst ≠ 0) ∧
    ((splitRep10 x.val.1).snd ≠ 0 ∨ (splitRep10 x.val.2).fst ≠ 0)) ↔ _
  simp only [ne_eq, split_eq_zero_iff, not_and_or]
  rw [(mem_commonEquality x.val).mp x.property]
  tauto

/-- The safe part of the original common-equality space is precisely the
normal complement, under the original orthogonal representation splitting. -/
def commonComplementHomeomorph : CommonComplement ≃ₜ Normal :=
  commonRawContinuousEquiv.toHomeomorph.subtype (fun x => (common_raw_safe_iff x).symm)

def commonNormalizationHomotopyEquiv : CommonComplement ≃ₕ Collapsed :=
  commonComplementHomeomorph.toHomotopyEquiv.trans normalizationHomotopyEquiv

def representationNormalize (x : Rep10) (hx : x ≠ 0) : Metric.sphere (0 : Rep10) 1 :=
  ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

def sphereNormalization (x : CommonComplement) : PairCollapse.PairSpace Priv4 Priv4 Comm6 :=
  spherePairEquiv (representationNormalize x.val.val.1 x.property.1,
    representationNormalize x.val.val.2 x.property.2)

theorem split_radius (x : Rep10) :
    PairCollapsedLocus.radius (WithLp.ofLp (splitRep10 x)) = ‖x‖ := by
  unfold PairCollapsedLocus.radius
  change Real.sqrt (‖(splitRep10 x).fst‖ ^ 2 + ‖(splitRep10 x).snd‖ ^ 2) = ‖x‖
  have h := @WithLp.prod_norm_sq_eq_of_L2 Priv4 Comm6 _ _ (splitRep10 x)
  rw [← h, splitRep10.norm_map, Real.sqrt_sq (norm_nonneg _)]

def splitTest (x : Rep10) (hx : x ≠ 0) :
    PairCollapsedLocus.NonzeroPair (F := Priv4) (W := Comm6) :=
  ⟨WithLp.ofLp (splitRep10 x), by
    have hn := not_congr (split_eq_zero_iff x)
    exact not_and_or.mp (hn.mp hx)⟩

theorem normalize_splitTest (x : Rep10) (hx : x ≠ 0) :
    (PairCollapsedLocus.normalize (splitTest x hx)).val =
      WithLp.ofLp (splitRep10 (representationNormalize x hx).val) := by
  change ((PairCollapsedLocus.radius (WithLp.ofLp (splitRep10 x)))⁻¹ •
      (splitRep10 x).fst,
    (PairCollapsedLocus.radius (WithLp.ofLp (splitRep10 x)))⁻¹ •
      (splitRep10 x).snd) = WithLp.ofLp (splitRep10 (‖x‖⁻¹ • x))
  rw [split_radius, map_smul]
  rfl

/-- The map underlying the proved homotopy equivalence is exactly the
original two-sphere normalization, expressed by `spherePairEquiv`. -/
theorem commonNormalization_eq_sphereNormalization (x : CommonComplement) :
    (commonNormalizationHomotopyEquiv x).val = sphereNormalization x := by
  apply Prod.ext <;> apply Subtype.ext
  · exact normalize_splitTest x.val.val.1 x.property.1
  · have he := (mem_commonEquality x.val.val).mp x.val.property
    have hp : secondTest (commonComplementHomeomorph x) = splitTest x.val.val.2 x.property.2 := by
      apply Subtype.ext
      exact Prod.ext rfl he
    change (PairCollapsedLocus.normalize (secondTest (commonComplementHomeomorph x))).val = _
    rw [hp]
    exact normalize_splitTest x.val.val.2 x.property.2

/-- The actual dimensions six, four, and four supply all unit basepoints;
the concrete join model has no additional nonemptiness hypothesis. -/
def actualBalancedJoinHomeomorph :
    PairBalancedJoin.JoinModel (U := Priv4) (V := Priv4) (W := Comm6) ≃ₜ
      PairLocalEquivalence.BalancedNormal (U := Priv4) (V := Priv4) (W := Comm6) := by
  letI : Nontrivial Priv4 := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_Priv4]; decide)
  letI : Nontrivial Comm6 := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_Comm6]; decide)
  exact PairBalancedJoin.canonicalBalancedJoinHomeomorph

end AkopyanResearch.PairConcreteLocalModel
