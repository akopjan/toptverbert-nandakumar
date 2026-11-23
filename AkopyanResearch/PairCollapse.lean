module

public import AkopyanResearch.SplitSphereChart
public import AkopyanResearch.NormalBundleTrivialization
public import AkopyanResearch.ProperCollapse
public import Mathlib.Analysis.InnerProductSpace.ProdL2


@[expose] public section

/-!
# Explicit open chart for the pair collapse

The common components must be nonzero and have different unit directions.
The chart is built from the two explicit homeomorphisms already checked in
`SplitSphereChart` and `PairNormalChart`.
-/

noncomputable section

namespace AkopyanResearch.PairCollapse

open PairNormalChart SplitSphereChart
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

abbrev FullUnit (F E : Type*) [NormedAddCommGroup F] [NormedAddCommGroup E] :=
  {vw : F × E // ‖vw.1‖ ^ 2 + ‖vw.2‖ ^ 2 = 1}

abbrev PairSpace (U V W : Type*) [NormedAddCommGroup U]
    [NormedAddCommGroup V] [NormedAddCommGroup W] := FullUnit V W × FullUnit U W

def chartDomain : Set (PairSpace U V W) :=
  {x | ‖x.2.val.2‖ • x.1.val.2 ≠ ‖x.1.val.2‖ • x.2.val.2}

lemma isOpen_chartDomain : IsOpen (chartDomain (U := U) (V := V) (W := W)) := by
  apply isOpen_ne_fun
  · fun_prop
  · fun_prop

lemma first_common_ne_zero (x : chartDomain (U := U) (V := V) (W := W)) :
    x.val.1.val.2 ≠ 0 := by
  intro h
  apply x.property
  simp [h]

lemma second_common_ne_zero (x : chartDomain (U := U) (V := V) (W := W)) :
    x.val.2.val.2 ≠ 0 := by
  intro h
  apply x.property
  simp [h]

lemma normalized_eq_iff_scaled_eq {p q : W} (hp : p ≠ 0) (hq : q ≠ 0) :
    normalizedDirection p = normalizedDirection q ↔ ‖q‖ • p = ‖p‖ • q := by
  have hp' : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  constructor
  · intro h
    have hh := congrArg (fun z : W => (‖p‖ * ‖q‖) • z) h
    simp only [normalizedDirection, smul_smul] at hh
    have h1 : (‖p‖ * ‖q‖) * ‖p‖⁻¹ = ‖q‖ := by field_simp
    have h2 : (‖p‖ * ‖q‖) * ‖q‖⁻¹ = ‖p‖ := by field_simp
    simpa only [h1, h2] using hh
  · intro h
    have hh := congrArg (fun z : W => (‖p‖ * ‖q‖)⁻¹ • z) h
    simp only [smul_smul] at hh
    have h1 : (‖p‖ * ‖q‖)⁻¹ * ‖q‖ = ‖p‖⁻¹ := by field_simp
    have h2 : (‖p‖ * ‖q‖)⁻¹ * ‖p‖ = ‖q‖⁻¹ := by field_simp
    simpa only [h1, h2, normalizedDirection] using hh

def firstSplit (x : chartDomain (U := U) (V := V) (W := W)) : UnitSplit V W :=
  ⟨x.val.1.val, x.val.1.property, first_common_ne_zero x⟩

def secondSplit (x : chartDomain (U := U) (V := V) (W := W)) : UnitSplit U W :=
  ⟨x.val.2.val, x.val.2.property, second_common_ne_zero x⟩

def commonDirections (x : chartDomain (U := U) (V := V) (W := W)) : DistinctDirections W :=
  ⟨((fromSplit (firstSplit x)).2.val, (fromSplit (secondSplit x)).2.val),
    (fromSplit (firstSplit x)).2.property, (fromSplit (secondSplit x)).2.property, by
      intro h
      exact x.property ((normalized_eq_iff_scaled_eq
        (first_common_ne_zero x) (second_common_ne_zero x)).mp h)⟩

abbrev Residual := WithLp 2 (V × U)
abbrev Parameters := UnitTangent W × Residual (U := U) (V := V)

def toParameters (x : chartDomain (U := U) (V := V) (W := W)) :
    Parameters (U := U) (V := V) (W := W) :=
  (tangentMap (commonDirections x),
    WithLp.toLp 2 ((fromSplit (firstSplit x)).1, (fromSplit (secondSplit x)).1))

def firstCoordinate (x : Parameters (U := U) (V := V) (W := W)) : UnitSplit V W :=
  toSplit ((WithLp.ofLp x.2).1,
    ⟨(directionsMap x.1).val.1, (directionsMap x.1).property.1⟩)

def secondCoordinate (x : Parameters (U := U) (V := V) (W := W)) : UnitSplit U W :=
  toSplit ((WithLp.ofLp x.2).2,
    ⟨(directionsMap x.1).val.2, (directionsMap x.1).property.2.1⟩)

lemma firstCoordinate_direction (x : Parameters (U := U) (V := V) (W := W)) :
    normalizedDirection (firstCoordinate x).val.2 = (directionsMap x.1).val.1 := by
  have h := fromSplit_toSplit ((WithLp.ofLp x.2).1,
    (⟨(directionsMap x.1).val.1, (directionsMap x.1).property.1⟩ : UnitDirections W))
  exact congrArg (fun z : V × UnitDirections W => z.2.val) h

lemma secondCoordinate_direction (x : Parameters (U := U) (V := V) (W := W)) :
    normalizedDirection (secondCoordinate x).val.2 = (directionsMap x.1).val.2 := by
  have h := fromSplit_toSplit ((WithLp.ofLp x.2).2,
    (⟨(directionsMap x.1).val.2, (directionsMap x.1).property.2.1⟩ : UnitDirections W))
  exact congrArg (fun z : U × UnitDirections W => z.2.val) h

def fromParameters (x : Parameters (U := U) (V := V) (W := W)) :
    chartDomain (U := U) (V := V) (W := W) :=
  ⟨(⟨(firstCoordinate x).val, (firstCoordinate x).property.1⟩,
    ⟨(secondCoordinate x).val, (secondCoordinate x).property.1⟩), by
      intro h
      have hd := (normalized_eq_iff_scaled_eq (firstCoordinate x).property.2
        (secondCoordinate x).property.2).mpr h
      rw [firstCoordinate_direction, secondCoordinate_direction] at hd
      exact (directionsMap x.1).property.2.2 hd⟩

lemma firstCoordinate_toParameters (x : chartDomain (U := U) (V := V) (W := W)) :
    firstCoordinate (toParameters x) = firstSplit x := by
  simpa only [firstCoordinate, toParameters, Prod.fst, Prod.snd,
    WithLp.ofLp_toLp, directions_tangentMap, commonDirections] using
    toSplit_fromSplit (firstSplit x)

lemma secondCoordinate_toParameters (x : chartDomain (U := U) (V := V) (W := W)) :
    secondCoordinate (toParameters x) = secondSplit x := by
  simpa only [secondCoordinate, toParameters, Prod.fst, Prod.snd,
    WithLp.ofLp_toLp, directions_tangentMap, commonDirections] using
    toSplit_fromSplit (secondSplit x)

theorem fromParameters_toParameters (x : chartDomain (U := U) (V := V) (W := W)) :
    fromParameters (toParameters x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun y : UnitSplit V W => y.val) (firstCoordinate_toParameters x)
  · apply Subtype.ext
    exact congrArg (fun y : UnitSplit U W => y.val) (secondCoordinate_toParameters x)

lemma firstSplit_fromParameters (x : Parameters (U := U) (V := V) (W := W)) :
    firstSplit (fromParameters x) = firstCoordinate x := by
  apply Subtype.ext
  rfl

lemma secondSplit_fromParameters (x : Parameters (U := U) (V := V) (W := W)) :
    secondSplit (fromParameters x) = secondCoordinate x := by
  apply Subtype.ext
  rfl

lemma commonDirections_fromParameters (x : Parameters (U := U) (V := V) (W := W)) :
    commonDirections (fromParameters x) = directionsMap x.1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact firstCoordinate_direction x
  · exact secondCoordinate_direction x

theorem toParameters_fromParameters (x : Parameters (U := U) (V := V) (W := W)) :
    toParameters (fromParameters x) = x := by
  apply Prod.ext
  · change tangentMap (commonDirections (fromParameters x)) = x.1
    rw [commonDirections_fromParameters, tangent_directionsMap]
  · change WithLp.toLp 2 ((fromSplit (firstSplit (fromParameters x))).1,
        (fromSplit (secondSplit (fromParameters x))).1) = x.2
    rw [firstSplit_fromParameters, secondSplit_fromParameters]
    simp only [firstCoordinate, secondCoordinate, fromSplit_toSplit]

lemma continuous_firstSplit : Continuous (firstSplit (U := U) (V := V) (W := W)) := by
  apply Continuous.subtype_mk
  fun_prop

lemma continuous_secondSplit : Continuous (secondSplit (U := U) (V := V) (W := W)) := by
  apply Continuous.subtype_mk
  fun_prop

lemma continuous_commonDirections :
    Continuous (commonDirections (U := U) (V := V) (W := W)) := by
  have h1 := continuous_fromSplit.comp (continuous_firstSplit (U := U) (V := V) (W := W))
  have h2 := continuous_fromSplit.comp (continuous_secondSplit (U := U) (V := V) (W := W))
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp h1.snd).prodMk (continuous_subtype_val.comp h2.snd)

theorem continuous_toParameters :
    Continuous (toParameters (U := U) (V := V) (W := W)) := by
  have h1 := continuous_fromSplit.comp (continuous_firstSplit (U := U) (V := V) (W := W))
  have h2 := continuous_fromSplit.comp (continuous_secondSplit (U := U) (V := V) (W := W))
  exact (continuous_tangentMap.comp continuous_commonDirections).prodMk
    ((WithLp.homeomorphProd 2 V U).symm.continuous.comp (h1.fst.prodMk h2.fst))

lemma continuous_firstCoordinate :
    Continuous (firstCoordinate (U := U) (V := V) (W := W)) := by
  have hr := (WithLp.homeomorphProd 2 V U).continuous.comp
    (continuous_snd : Continuous (fun x : Parameters (U := U) (V := V) (W := W) => x.2))
  have hd := continuous_directionsMap.comp
    (continuous_fst : Continuous (fun x : Parameters (U := U) (V := V) (W := W) => x.1))
  exact continuous_toSplit.comp
    (hr.fst.prodMk (((continuous_subtype_val.comp hd).fst).subtype_mk _))

lemma continuous_secondCoordinate :
    Continuous (secondCoordinate (U := U) (V := V) (W := W)) := by
  have hr := (WithLp.homeomorphProd 2 V U).continuous.comp
    (continuous_snd : Continuous (fun x : Parameters (U := U) (V := V) (W := W) => x.2))
  have hd := continuous_directionsMap.comp
    (continuous_fst : Continuous (fun x : Parameters (U := U) (V := V) (W := W) => x.1))
  exact continuous_toSplit.comp
    (hr.snd.prodMk (((continuous_subtype_val.comp hd).snd).subtype_mk _))

theorem continuous_fromParameters :
    Continuous (fromParameters (U := U) (V := V) (W := W)) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_firstCoordinate).subtype_mk _).prodMk
    ((continuous_subtype_val.comp continuous_secondCoordinate).subtype_mk _)

def chartHomeomorph : chartDomain (U := U) (V := V) (W := W) ≃ₜ
    Parameters (U := U) (V := V) (W := W) where
  toFun := toParameters
  invFun := fromParameters
  left_inv := fromParameters_toParameters
  right_inv := toParameters_fromParameters
  continuous_toFun := continuous_toParameters
  continuous_invFun := continuous_fromParameters

abbrev CollapseTarget (f : Residual (U := U) (V := V)) :=
  NormalBundleTrivialization.NormalFiber (W := W) f

def fiberCoordinate (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (x : chartDomain (U := U) (V := V) (W := W)) : CollapseTarget (W := W) f :=
  (NormalBundleTrivialization.toProduct f hf (toParameters x)).2

def collapse (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1) :
    PairSpace U V W → OnePoint (CollapseTarget (W := W) f) :=
  properCollapse chartDomain (fiberCoordinate f hf)

theorem continuous_collapse [ProperSpace W]
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1) :
    Continuous (collapse (W := W) f hf) := by
  let : CompactSpace (NormalBundleTrivialization.UnitDirections W) := by
    have hc : IsCompact ({w : W | ‖w‖ = 1} : Set W) := by
      simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : W) 1
    exact isCompact_iff_compactSpace.mp hc
  exact continuous_compact_chart_collapse isOpen_chartDomain
    (chartHomeomorph.trans (NormalBundleTrivialization.normalBundleHomeomorph f hf))

open scoped OnePoint

theorem collapse_eq_infty_of_not_domain
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (x : PairSpace U V W) (hx : x ∉ chartDomain) : collapse f hf x = ∞ :=
  properCollapse_of_notMem (fiberCoordinate f hf) hx

/-- Actual matching normals have positively proportional common components,
so this collapse is exactly infinity on the image of the table normal map. -/
theorem collapse_eq_infty_of_common_nonnegative_multiples
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (x : PairSpace U V W) (w : W) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfirst : x.1.val.2 = a • w) (hsecond : x.2.val.2 = b • w) :
    collapse f hf x = ∞ := by
  apply collapse_eq_infty_of_not_domain
  change ¬(‖x.2.val.2‖ • x.1.val.2 ≠ ‖x.1.val.2‖ • x.2.val.2)
  apply not_not.mpr
  rw [hfirst, hsecond]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, smul_smul]
  congr 1
  ring

theorem collapse_fromParameters
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (x : Parameters (U := U) (V := V) (W := W)) :
    collapse f hf (fromParameters x).val =
      ((NormalBundleTrivialization.toProduct f hf x).2 :
        OnePoint (CollapseTarget (W := W) f)) := by
  rw [collapse, properCollapse_of_mem _ (fromParameters x).property]
  change ((NormalBundleTrivialization.toProduct f hf (toParameters (fromParameters x))).2 :
    OnePoint (CollapseTarget (W := W) f)) = _
  rw [toParameters_fromParameters]

def zeroParameters (w : UnitDirections W) : Parameters (U := U) (V := V) (W := W) :=
  (⟨(w.val, 0), w.property, by simp⟩, 0)

def antipodalPair (w : UnitDirections W) : PairSpace U V W :=
  (⟨(0, w.val), by simp [w.property]⟩,
    ⟨(0, -w.val), by simp [w.property]⟩)

lemma fromParameters_zeroParameters (w : UnitDirections W) :
    (fromParameters (zeroParameters (U := U) (V := V) w)).val = antipodalPair w := by
  apply Prod.ext
  · apply Subtype.ext
    simp [fromParameters, zeroParameters, firstCoordinate, directionsMap,
      directionPlus, directionMinus, sharedScale, toSplit, antipodalPair]
  · apply Subtype.ext
    simp [fromParameters, zeroParameters, secondCoordinate, directionsMap,
      directionPlus, directionMinus, sharedScale, toSplit, antipodalPair]

/-- The anti-diagonal is mapped to the origin of the thirteen-dimensional
normal representation. -/
theorem collapse_antipodalPair
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1) (w : UnitDirections W) :
    collapse f hf (antipodalPair w) =
      ((0 : CollapseTarget (W := W) f) : OnePoint (CollapseTarget (W := W) f)) := by
  rw [← fromParameters_zeroParameters, collapse_fromParameters]
  simp [NormalBundleTrivialization.toProduct, zeroParameters, PairNormalFrame.forward]

lemma fiber_zero_iff_zeroParameters
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (x : Parameters (U := U) (V := V) (W := W)) :
    (NormalBundleTrivialization.toProduct f hf x).2 = 0 ↔
      ∃ w : UnitDirections W, x = zeroParameters w := by
  constructor
  · intro h
    let w : UnitDirections W := ⟨x.1.val.1, x.1.property.1⟩
    have heq : NormalBundleTrivialization.toProduct f hf x = (w, 0) := by
      apply Prod.ext
      · rfl
      · exact h
    refine ⟨w, ?_⟩
    calc
      x = NormalBundleTrivialization.fromProduct f
          (NormalBundleTrivialization.toProduct f hf x) :=
        (NormalBundleTrivialization.fromProduct_toProduct f hf x).symm
      _ = NormalBundleTrivialization.fromProduct f (w, 0) := congrArg _ heq
      _ = zeroParameters w := by
        simp [NormalBundleTrivialization.fromProduct, PairNormalFrame.backward, zeroParameters]
  · rintro ⟨w, rfl⟩
    simp [NormalBundleTrivialization.toProduct, zeroParameters, PairNormalFrame.forward]

/-- The origin has exactly the expected anti-diagonal as its inverse image. -/
theorem collapse_eq_zero_iff
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1) (x : PairSpace U V W) :
    collapse f hf x = ((0 : CollapseTarget (W := W) f) : OnePoint (CollapseTarget (W := W) f)) ↔
      ∃ w : UnitDirections W, x = antipodalPair w := by
  constructor
  · intro h
    have hx : x ∈ chartDomain := by
      by_contra hn
      have hi := collapse_eq_infty_of_not_domain f hf x hn
      exact OnePoint.infty_ne_coe (0 : CollapseTarget (W := W) f) (hi.symm.trans h)
    have hp : collapse f hf x =
        ((fiberCoordinate f hf ⟨x, hx⟩) : OnePoint (CollapseTarget (W := W) f)) :=
      properCollapse_of_mem (fiberCoordinate f hf) hx
    have hz : fiberCoordinate f hf ⟨x, hx⟩ = 0 :=
      OnePoint.coe_injective (hp.symm.trans h)
    obtain ⟨w, hw⟩ := (fiber_zero_iff_zeroParameters f hf (toParameters ⟨x, hx⟩)).mp hz
    refine ⟨w, ?_⟩
    calc
      x = (fromParameters (toParameters ⟨x, hx⟩)).val :=
        (congrArg (fun y : chartDomain (U := U) (V := V) (W := W) => y.val)
          (fromParameters_toParameters ⟨x, hx⟩)).symm
      _ = (fromParameters (zeroParameters w)).val :=
        congrArg (fun p : Parameters (U := U) (V := V) (W := W) => (fromParameters p).val) hw
      _ = antipodalPair w := fromParameters_zeroParameters w
  · rintro ⟨w, rfl⟩
    exact collapse_antipodalPair f hf w

/-- A normal slice at a chosen point of the anti-diagonal. In the collapse
coordinates this slice is literally the identity, so its local multiplicity
is one without a transversality theorem. -/
def normalSection (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (w : UnitDirections W) (z : CollapseTarget (W := W) f) : PairSpace U V W :=
  (fromParameters ((NormalBundleTrivialization.normalBundleHomeomorph f hf).symm (w, z))).val

theorem continuous_normalSection
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1) (w : UnitDirections W) :
    Continuous (normalSection f hf w) :=
  continuous_subtype_val.comp (continuous_fromParameters.comp
    ((NormalBundleTrivialization.normalBundleHomeomorph f hf).symm.continuous.comp
      (continuous_const.prodMk continuous_id)))

theorem collapse_normalSection
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (w : UnitDirections W) (z : CollapseTarget (W := W) f) :
    collapse f hf (normalSection f hf w z) = (z : OnePoint (CollapseTarget (W := W) f)) := by
  unfold normalSection
  rw [collapse_fromParameters]
  have h := (NormalBundleTrivialization.normalBundleHomeomorph (W := W) f hf).apply_symm_apply (w, z)
  exact congrArg (fun y : UnitDirections W × CollapseTarget (W := W) f =>
    (y.2 : OnePoint (CollapseTarget (W := W) f))) h

theorem normalSection_zero
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1) (w : UnitDirections W) :
    normalSection f hf w 0 = antipodalPair w := by
  have h : (NormalBundleTrivialization.normalBundleHomeomorph f hf).symm (w, (0 : CollapseTarget (W := W) f)) =
      zeroParameters (U := U) (V := V) w := by
    simp [NormalBundleTrivialization.normalBundleHomeomorph,
      NormalBundleTrivialization.fromProduct, PairNormalFrame.backward, zeroParameters]
  unfold normalSection
  rw [h, fromParameters_zeroParameters]

theorem collapseTarget_finrank_thirteen
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (f : Residual (U := U) (V := V)) (hf : ‖f‖ = 1)
    (hU : Module.finrank ℝ U = 4) (hV : Module.finrank ℝ V = 4)
    (hW : Module.finrank ℝ W = 6) :
    Module.finrank ℝ (CollapseTarget (W := W) f) = 13 := by
  have hR : Module.finrank ℝ (Residual (U := U) (V := V)) = 8 := by
    rw [(WithLp.linearEquiv 2 ℝ (V × U)).finrank_eq, Module.finrank_prod, hU, hV]
  apply NormalBundleTrivialization.normalFiber_finrank_thirteen (W := W) _ hR hW
  intro hzero
  simp [hzero] at hf

end AkopyanResearch.PairCollapse
