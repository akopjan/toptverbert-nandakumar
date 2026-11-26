module

public import AkopyanResearch.Completion.PairLocalEquivalence
public import AkopyanResearch.Completion.EquivariantJoinStep
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The balanced normal model is an actual topological join

For real normed spaces `W`, `V`, and `U`, the balanced normal model has
coordinates `(z,a,b)` with both squared radii equal to one. The formula
`(t,w,(v,u)) ↦ (sqrt(1-t²) • w, t • v, t • u)` identifies it with the
topological join of the unit sphere of `W` and the product of the unit spheres
of `V` and `U`. Continuity at both collapsed ends is obtained from the
quotient topology; the inverse is continuous by compactness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairBalancedJoin

open EquivariantJoinStep

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

abbrev Balanced := PairL2Deformation.Balanced2 (Z := W) (A := V) (B := U)
abbrev JoinModel := Join (UnitSphere W) (UnitSphere V × UnitSphere U)
abbrev JoinRaw := Raw (UnitSphere W) (UnitSphere V × UnitSphere U)

theorem time_sq_le_one (t : Time) : t.val ^ 2 ≤ 1 := by
  nlinarith [t.property.1, t.property.2]

def rawMap (p : JoinRaw (U := U) (V := V) (W := W)) :
    Balanced (U := U) (V := V) (W := W) :=
  ⟨(Real.sqrt (1 - p.1.val ^ 2) • p.2.1.val,
      p.1.val • p.2.2.1.val, p.1.val • p.2.2.2.val), by
    have hs := Real.sq_sqrt (sub_nonneg.mpr (time_sq_le_one p.1))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg p.1.property.1, p.2.1.property, p.2.2.1.property,
      p.2.2.2.property, mul_one]
    constructor <;> linarith⟩

theorem rawMap_private_norm (p : JoinRaw (U := U) (V := V) (W := W)) :
    ‖(rawMap p).val.2.1‖ = p.1.val := by
  change ‖p.1.val • p.2.2.1.val‖ = p.1.val
  rw [norm_smul, p.2.2.1.property, Real.norm_eq_abs,
    abs_of_nonneg p.1.property.1, mul_one]

theorem rawMap_respects (p q : JoinRaw (U := U) (V := V) (W := W))
    (h : EndpointRel p q) : rawMap p = rawMap q := by
  rcases h with ⟨hp, hq, hx⟩ | ⟨hp, hq, hg⟩
  · apply Subtype.ext
    simp [rawMap, hp, hq, hx, timeZero]
  · apply Subtype.ext
    simp [rawMap, hp, hq, hg, timeOne]

def joinMap : JoinModel (U := U) (V := V) (W := W) →
    Balanced (U := U) (V := V) (W := W) :=
  Quot.lift rawMap rawMap_respects

theorem continuous_rawMap : Continuous (rawMap (U := U) (V := V) (W := W)) := by
  unfold rawMap
  fun_prop

theorem continuous_joinMap : Continuous (joinMap (U := U) (V := V) (W := W)) :=
  continuous_quot_lift _ continuous_rawMap

private theorem cancel_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : c ≠ 0) {x y : E} (h : c • x = c • y) : x = y := by
  have hi := congrArg (fun v : E => c⁻¹ • v) h
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

theorem quotient_eq_of_rawMap_eq (p q : JoinRaw (U := U) (V := V) (W := W))
    (h : rawMap p = rawMap q) : Quot.mk EndpointRel p = Quot.mk EndpointRel q := by
  have ht : p.1 = q.1 := by
    apply Subtype.ext
    have hn := congrArg (fun x : Balanced (U := U) (V := V) (W := W) => ‖x.val.2.1‖) h
    simpa only [rawMap_private_norm] using hn
  rcases p with ⟨t, w, a, b⟩
  rcases q with ⟨s, w', a', b'⟩
  dsimp only at ht
  subst s
  have hz := congrArg (fun x : Balanced (U := U) (V := V) (W := W) => x.val.1) h
  have ha := congrArg (fun x : Balanced (U := U) (V := V) (W := W) => x.val.2.1) h
  have hb := congrArg (fun x : Balanced (U := U) (V := V) (W := W) => x.val.2.2) h
  by_cases hzero : t = timeZero
  · apply Quot.sound
    apply Or.inl
    refine ⟨hzero, hzero, ?_⟩
    apply Subtype.ext
    simpa [rawMap, hzero, timeZero] using hz
  · by_cases hone : t = timeOne
    · apply Quot.sound
      apply Or.inr
      refine ⟨hone, hone, ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · simpa [rawMap, hone, timeOne] using ha
      · simpa [rawMap, hone, timeOne] using hb
    · have ht0 : t.val ≠ 0 := fun he => hzero (Subtype.ext he)
      have ht1 : t.val < 1 := lt_of_le_of_ne t.property.2 (fun he => hone (Subtype.ext he))
      have hc : Real.sqrt (1 - t.val ^ 2) ≠ 0 := by
        apply (Real.sqrt_pos.mpr _).ne'
        nlinarith [t.property.1]
      have hw : w = w' := Subtype.ext (cancel_scalar hc hz)
      have hpa : a = a' := Subtype.ext (cancel_scalar ht0 ha)
      have hpb : b = b' := Subtype.ext (cancel_scalar ht0 hb)
      subst w'
      subst a'
      subst b'
      rfl

theorem injective_joinMap : Function.Injective (joinMap (U := U) (V := V) (W := W)) := by
  intro x y
  induction x using Quot.inductionOn with
  | h p =>
    induction y using Quot.inductionOn with
    | h q => exact quotient_eq_of_rawMap_eq p q

section Direction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def direction (base : UnitSphere E) (x : E) : UnitSphere E := by
  classical
  exact if hx : x = 0 then base else ⟨‖x‖⁻¹ • x, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem norm_smul_direction (base : UnitSphere E) (x : E) :
    ‖x‖ • (direction base x).val = x := by
  by_cases hx : x = 0
  · simp [direction, hx]
  · simp only [direction, hx, ↓reduceDIte, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

end Direction

theorem surjective_joinMap
    (w₀ : UnitSphere W) (a₀ : UnitSphere V) (b₀ : UnitSphere U) :
    Function.Surjective (joinMap (U := U) (V := V) (W := W)) := by
  intro x
  have ht : ‖x.val.2.1‖ ≤ 1 := by
    nlinarith [x.property.1, sq_nonneg ‖x.val.1‖, norm_nonneg x.val.2.1]
  let t : Time := ⟨‖x.val.2.1‖, norm_nonneg _, ht⟩
  refine ⟨joinMk t (direction w₀ x.val.1)
    (direction a₀ x.val.2.1, direction b₀ x.val.2.2), ?_⟩
  apply Subtype.ext
  have hr : Real.sqrt (1 - ‖x.val.2.1‖ ^ 2) = ‖x.val.1‖ := by
    have he : 1 - ‖x.val.2.1‖ ^ 2 = ‖x.val.1‖ ^ 2 := by linarith [x.property.1]
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  change (Real.sqrt (1 - ‖x.val.2.1‖ ^ 2) • (direction w₀ x.val.1).val,
    ‖x.val.2.1‖ • (direction a₀ x.val.2.1).val,
    ‖x.val.2.1‖ • (direction b₀ x.val.2.2).val) = x.val
  rw [hr, norm_smul_direction, norm_smul_direction,
    PairL2Deformation.balanced2_norms x, norm_smul_direction]

instance unitSphere_compact {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    CompactSpace (UnitSphere E) := by
  change CompactSpace ↥({x : E | ‖x‖ = 1} : Set E)
  apply isCompact_iff_compactSpace.mp
  change IsCompact ({x : E | ‖x‖ = 1} : Set E)
  simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1

/-- The homeomorphism uses the genuine quotient join, with no assumptions
about its connectivity or its homotopy groups. -/
def balancedJoinHomeomorph [ProperSpace U] [ProperSpace V] [ProperSpace W]
    (w₀ : UnitSphere W) (a₀ : UnitSphere V) (b₀ : UnitSphere U) :
    JoinModel (U := U) (V := V) (W := W) ≃ₜ Balanced (U := U) (V := V) (W := W) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective joinMap ⟨injective_joinMap, surjective_joinMap w₀ a₀ b₀⟩)
    continuous_joinMap

theorem balancedJoinHomeomorph_apply [ProperSpace U] [ProperSpace V] [ProperSpace W]
    (w₀ : UnitSphere W) (a₀ : UnitSphere V) (b₀ : UnitSphere U)
    (x : JoinModel (U := U) (V := V) (W := W)) :
    balancedJoinHomeomorph w₀ a₀ b₀ x = joinMap x := rfl

/-- Unit directions exist in every nontrivial real normed space. -/
def unitSpherePoint (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] : UnitSphere E :=
  ⟨Classical.choose (exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)),
    Classical.choose_spec (exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num))⟩

def canonicalBalancedJoinHomeomorph
    [ProperSpace U] [ProperSpace V] [ProperSpace W]
    [Nontrivial U] [Nontrivial V] [Nontrivial W] :
    JoinModel (U := U) (V := V) (W := W) ≃ₜ Balanced (U := U) (V := V) (W := W) :=
  balancedJoinHomeomorph (unitSpherePoint W) (unitSpherePoint V) (unitSpherePoint U)

end AkopyanResearch.PairBalancedJoin
