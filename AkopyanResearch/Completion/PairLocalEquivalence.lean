module

public import AkopyanResearch.Completion.PairCollapsedLocus
public import AkopyanResearch.Completion.PairL2Deformation
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The actual local normalization is a homotopy equivalence

The balanced subspace of the collapsed locus is canonically homeomorphic to
the balanced quadratic-norm normal model. Separately normalizing the two tests
gives a map from the actual normal complement to the actual collapsed locus.
It fixes this common balanced model and is a homotopy equivalence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairLocalEquivalence

open ContinuousMap

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

abbrev NormalComplement := PairDeformation.Complement (Z := W) (A := V) (B := U)
abbrev BalancedNormal := PairL2Deformation.Balanced2 (Z := W) (A := V) (B := U)
abbrev Collapsed := PairCollapsedLocus.Locus (U := U) (V := V) (W := W)
abbrev BalancedCollapsed := PairCollapsedLocus.Balanced (U := U) (V := V) (W := W)

def toBalancedCollapsed (x : BalancedNormal (U := U) (V := V) (W := W)) :
    BalancedCollapsed (U := U) (V := V) (W := W) :=
  ⟨⟨(⟨(x.val.2.1, x.val.1), by simpa only [add_comm] using x.property.1⟩,
      ⟨(x.val.2.2, x.val.1), by simpa only [add_comm] using x.property.2⟩), by
        change ¬ (‖x.val.1‖ • x.val.1 ≠ ‖x.val.1‖ • x.val.1)
        simp⟩, rfl⟩

def fromBalancedCollapsed (x : BalancedCollapsed (U := U) (V := V) (W := W)) :
    BalancedNormal (U := U) (V := V) (W := W) :=
  ⟨(PairCollapsedLocus.commonA x.val, PairCollapsedLocus.privateA x.val,
      PairCollapsedLocus.privateB x.val), by
    constructor
    · simpa only [add_comm] using x.val.val.1.property
    · rw [x.property]
      simpa only [add_comm] using x.val.val.2.property⟩

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem from_to_balanced (x : BalancedNormal (U := U) (V := V) (W := W)) :
    fromBalancedCollapsed (toBalancedCollapsed x) = x := by
  apply Subtype.ext
  rfl

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem to_from_balanced (x : BalancedCollapsed (U := U) (V := V) (W := W)) :
    toBalancedCollapsed (fromBalancedCollapsed x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · rfl
  · exact Prod.ext rfl x.property

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem continuous_toBalancedCollapsed :
    Continuous (toBalancedCollapsed (U := U) (V := V) (W := W)) := by
  unfold toBalancedCollapsed
  fun_prop

omit [InnerProductSpace ℝ U] [InnerProductSpace ℝ V] in
theorem continuous_fromBalancedCollapsed :
    Continuous (fromBalancedCollapsed (U := U) (V := V) (W := W)) := by
  unfold fromBalancedCollapsed
  fun_prop

/-- The two independently defined balanced subspaces are the same topological
model, with the common coordinate moved to the first position. -/
def balancedHomeomorph : BalancedNormal (U := U) (V := V) (W := W) ≃ₜ
    BalancedCollapsed (U := U) (V := V) (W := W) where
  toFun := toBalancedCollapsed
  invFun := fromBalancedCollapsed
  left_inv := from_to_balanced
  right_inv := to_from_balanced
  continuous_toFun := continuous_toBalancedCollapsed
  continuous_invFun := continuous_fromBalancedCollapsed

def firstTest (x : NormalComplement (U := U) (V := V) (W := W)) :
    PairCollapsedLocus.NonzeroPair (F := V) (W := W) :=
  ⟨(x.val.2.1, x.val.1), x.property.1.symm⟩

def secondTest (x : NormalComplement (U := U) (V := V) (W := W)) :
    PairCollapsedLocus.NonzeroPair (F := U) (W := W) :=
  ⟨(x.val.2.2, x.val.1), x.property.2.symm⟩

/-- Normalize each of the two actual tests separately. Their common
components are positive multiples of the same original common vector. -/
def normalization (x : NormalComplement (U := U) (V := V) (W := W)) :
    Collapsed (U := U) (V := V) (W := W) :=
  ⟨(PairCollapsedLocus.normalize (firstTest x),
      PairCollapsedLocus.normalize (secondTest x)), by
    apply not_not.mpr
    change ‖(PairCollapsedLocus.radius (secondTest x).val)⁻¹ • x.val.1‖ •
        ((PairCollapsedLocus.radius (firstTest x).val)⁻¹ • x.val.1) =
      ‖(PairCollapsedLocus.radius (firstTest x).val)⁻¹ • x.val.1‖ •
        ((PairCollapsedLocus.radius (secondTest x).val)⁻¹ • x.val.1)
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (PairCollapsedLocus.radius_pos (firstTest x))),
      abs_of_pos (inv_pos.mpr (PairCollapsedLocus.radius_pos (secondTest x))), smul_smul]
    congr 1
    ring⟩

theorem continuous_normalization :
    Continuous (normalization (U := U) (V := V) (W := W)) := by
  have h₁ : Continuous (firstTest (U := U) (V := V) (W := W)) := by
    unfold firstTest
    fun_prop
  have h₂ : Continuous (secondTest (U := U) (V := V) (W := W)) := by
    unfold secondTest
    fun_prop
  exact ((PairCollapsedLocus.continuous_normalize.comp h₁).prodMk
    (PairCollapsedLocus.continuous_normalize.comp h₂)).subtype_mk _

theorem normalization_inclusion (x : BalancedNormal (U := U) (V := V) (W := W)) :
    normalization (PairL2Deformation.inclusion x) = (toBalancedCollapsed x).val := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact PairCollapsedLocus.normalize_unit _ (by
      change ‖x.val.2.1‖ ^ 2 + ‖x.val.1‖ ^ 2 = 1
      simpa only [add_comm] using x.property.1)
  · exact PairCollapsedLocus.normalize_unit _ (by
      change ‖x.val.2.2‖ ^ 2 + ‖x.val.1‖ ^ 2 = 1
      simpa only [add_comm] using x.property.2)

def normalInclusion : C(BalancedNormal (U := U) (V := V) (W := W),
    NormalComplement (U := U) (V := V) (W := W)) :=
  ⟨PairL2Deformation.inclusion, PairL2Deformation.continuous_inclusion⟩

def normalRetraction : C(NormalComplement (U := U) (V := V) (W := W),
    BalancedNormal (U := U) (V := V) (W := W)) :=
  ⟨PairL2Deformation.retraction, PairL2Deformation.continuous_retraction⟩

def collapsedInclusion : C(BalancedCollapsed (U := U) (V := V) (W := W),
    Collapsed (U := U) (V := V) (W := W)) :=
  ⟨PairCollapsedLocus.inclusion, continuous_subtype_val⟩

def collapsedRetraction : C(Collapsed (U := U) (V := V) (W := W),
    BalancedCollapsed (U := U) (V := V) (W := W)) :=
  ⟨PairCollapsedLocus.retraction, PairCollapsedLocus.continuous_retraction⟩

def normalizationMap : C(NormalComplement (U := U) (V := V) (W := W),
    Collapsed (U := U) (V := V) (W := W)) :=
  ⟨normalization, continuous_normalization⟩

def balancedMap : C(BalancedNormal (U := U) (V := V) (W := W),
    BalancedCollapsed (U := U) (V := V) (W := W)) :=
  ⟨toBalancedCollapsed, continuous_toBalancedCollapsed⟩

def normalDeformation :
    (ContinuousMap.id (NormalComplement (U := U) (V := V) (W := W))).Homotopy
      (normalInclusion.comp normalRetraction) where
  toFun := PairL2Deformation.deformation
  continuous_toFun := PairL2Deformation.continuous_deformation
  map_zero_left := PairL2Deformation.deformation_start
  map_one_left := PairL2Deformation.deformation_end

def collapsedDeformation :
    (ContinuousMap.id (Collapsed (U := U) (V := V) (W := W))).Homotopy
      (collapsedInclusion.comp collapsedRetraction) where
  toFun := PairCollapsedLocus.deformation
  continuous_toFun := PairCollapsedLocus.continuous_deformation
  map_zero_left := PairCollapsedLocus.deformation_start
  map_one_left := PairCollapsedLocus.deformation_end

def normalHomotopyEquiv : NormalComplement (U := U) (V := V) (W := W) ≃ₕ
    BalancedNormal (U := U) (V := V) (W := W) where
  toFun := normalRetraction
  invFun := normalInclusion
  left_inv := ⟨normalDeformation.symm⟩
  right_inv := by
    have h : normalRetraction.comp normalInclusion =
        ContinuousMap.id (BalancedNormal (U := U) (V := V) (W := W)) := by
      apply ContinuousMap.ext
      intro x
      exact PairL2Deformation.retraction_inclusion x
    rw [h]

def collapsedHomotopyEquiv : Collapsed (U := U) (V := V) (W := W) ≃ₕ
    BalancedCollapsed (U := U) (V := V) (W := W) where
  toFun := collapsedRetraction
  invFun := collapsedInclusion
  left_inv := ⟨collapsedDeformation.symm⟩
  right_inv := by
    have h : collapsedRetraction.comp collapsedInclusion =
        ContinuousMap.id (BalancedCollapsed (U := U) (V := V) (W := W)) := by
      apply ContinuousMap.ext
      intro x
      exact PairCollapsedLocus.retraction_inclusion x
    rw [h]

theorem normalizationMap_comp_inclusion :
    (normalizationMap (U := U) (V := V) (W := W)).comp normalInclusion =
      collapsedInclusion.comp balancedMap := by
  apply ContinuousMap.ext
  intro x
  exact normalization_inclusion x

def retractionEquiv : NormalComplement (U := U) (V := V) (W := W) ≃ₕ
    Collapsed (U := U) (V := V) (W := W) :=
  (normalHomotopyEquiv.trans balancedHomeomorph.toHomotopyEquiv).trans
    collapsedHomotopyEquiv.symm

theorem normalization_homotopic_retraction :
    (normalizationMap (U := U) (V := V) (W := W)).Homotopic retractionEquiv.toFun := by
  have h := (Homotopic.refl (normalizationMap (U := U) (V := V) (W := W))).comp
    (show (ContinuousMap.id (NormalComplement (U := U) (V := V) (W := W))).Homotopic
      (normalInclusion.comp normalRetraction) from ⟨normalDeformation⟩)
  rw [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, normalizationMap_comp_inclusion] at h
  exact h

/-- The forward map is the original separate normalization, not merely an
unspecified map through the common retract. Its inverse and both homotopies
are constructed from the explicit strong deformations. -/
def normalizationHomotopyEquiv : NormalComplement (U := U) (V := V) (W := W) ≃ₕ
    Collapsed (U := U) (V := V) (W := W) where
  toFun := normalizationMap
  invFun := retractionEquiv.invFun
  left_inv := ((Homotopic.refl retractionEquiv.invFun).comp
    normalization_homotopic_retraction).trans retractionEquiv.left_inv
  right_inv := (normalization_homotopic_retraction.comp
    (Homotopic.refl retractionEquiv.invFun)).trans retractionEquiv.right_inv

theorem normalizationHomotopyEquiv_apply
    (x : NormalComplement (U := U) (V := V) (W := W)) :
    normalizationHomotopyEquiv x = normalization x := rfl

theorem normalizationHomotopyEquiv_symm_apply
    (x : Collapsed (U := U) (V := V) (W := W)) :
    normalizationHomotopyEquiv.symm x =
      PairL2Deformation.inclusion
        (fromBalancedCollapsed (PairCollapsedLocus.retraction x)) := rfl

end AkopyanResearch.PairLocalEquivalence
