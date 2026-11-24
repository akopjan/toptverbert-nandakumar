module

public import AkopyanResearch.ProperCollapse
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Collapsing the complement of an open subset

For a compact Hausdorff space `X` and an open subset `U` with nonempty
complement, the quotient identifying precisely the points outside `U` is
homeomorphic to `OnePoint U`. The quotient relation and the canonical map
are made explicit. This is a homeomorphism of spaces, not a cofibration or
a homotopy-connectivity assertion.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.OpenComplementQuotient

open Set Filter Topology
open scoped OnePoint

variable {X : Type*}

/-- The map retains a point of `U` and sends every point of its complement
to infinity. -/
def collapse (U : Set X) : X → OnePoint U := properCollapse U id

theorem collapse_of_mem {U : Set X} {x : X} (hx : x ∈ U) :
    collapse U x = (⟨x, hx⟩ : U) := properCollapse_of_mem id hx

theorem collapse_of_not_mem {U : Set X} {x : X} (hx : x ∉ U) :
    collapse U x = ∞ := properCollapse_of_notMem id hx

theorem collapse_eq_iff (U : Set X) (x y : X) :
    collapse U x = collapse U y ↔ x = y ∨ (x ∉ U ∧ y ∉ U) := by
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
  · rw [collapse_of_mem hx, collapse_of_mem hy]
    simp only [OnePoint.coe_eq_coe, Subtype.mk.injEq, not_true_eq_false,
      false_and, or_false, hx]
  · rw [collapse_of_mem hx, collapse_of_not_mem hy]
    constructor
    · exact fun h => (OnePoint.coe_ne_infty _ h).elim
    · rintro (rfl | h)
      · exact (hy hx).elim
      · exact (h.1 hx).elim
  · rw [collapse_of_not_mem hx, collapse_of_mem hy]
    constructor
    · exact fun h => (OnePoint.infty_ne_coe _ h).elim
    · rintro (rfl | h)
      · exact (hx hy).elim
      · exact (h.2 hy).elim
  · rw [collapse_of_not_mem hx, collapse_of_not_mem hy]
    exact ⟨fun _ => Or.inr ⟨hx, hy⟩, fun _ => rfl⟩

/-- Equality of quotient classes identifies exactly equal points or two
points of the collapsed complement. -/
abbrev Space (U : Set X) := Quotient (Setoid.ker (collapse U))

def point (U : Set X) (x : X) : Space U :=
  @Quotient.mk' X (Setoid.ker (collapse U)) x

theorem point_eq_iff (U : Set X) (x y : X) :
    point U x = point U y ↔ x = y ∨ (x ∉ U ∧ y ∉ U) := by
  constructor
  · intro h
    exact (collapse_eq_iff U x y).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((collapse_eq_iff U x y).mpr h)

theorem surjective_collapse {U : Set X} (hU : Uᶜ.Nonempty) :
    Function.Surjective (collapse U) := by
  change ∀ y : OnePoint U, ∃ x : X, collapse U x = y
  refine OnePoint.forall.mpr ?_
  constructor
  · obtain ⟨x, hx⟩ := hU
    exact ⟨x, collapse_of_not_mem hx⟩
  · intro x
    exact ⟨x.val, collapse_of_mem x.property⟩

variable [TopologicalSpace X] [T2Space X]

theorem continuous_collapse {U : Set X} (hU : IsOpen U) : Continuous (collapse U) :=
  continuous_properCollapse hU id isProperMap_id

def collapseMap {U : Set X} (hU : IsOpen U) : C(X, OnePoint U) :=
  ⟨collapse U, continuous_collapse hU⟩

omit [T2Space X] in
theorem continuous_point (U : Set X) : Continuous (point U) :=
  continuous_quotient_mk'

variable [CompactSpace X]

/-- The actual quotient of `X` by the closed complement is the one-point
compactification of its open part. -/
def homeomorph {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    Space U ≃ₜ OnePoint U := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact (show IsQuotientMap (collapseMap hU) from
    IsQuotientMap.of_surjective_continuous (surjective_collapse hUc)
      (continuous_collapse hU)).homeomorph

theorem homeomorph_point {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) (x : X) :
    homeomorph hU hUc (point U x) = collapse U x := rfl

variable {Y : Type*} [TopologicalSpace Y]

/-- A coordinate homeomorphism on the open part induces its precise
compactified quotient homeomorphism. -/
def chartHomeomorph {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (e : U ≃ₜ Y) : Space U ≃ₜ OnePoint Y :=
  (homeomorph hU hUc).trans e.onePointCongr

theorem chartHomeomorph_point {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (e : U ≃ₜ Y) (x : X) :
    chartHomeomorph hU hUc e (point U x) = properCollapse U e x := by
  by_cases hx : x ∈ U
  · simp only [chartHomeomorph, Homeomorph.trans_apply, homeomorph_point,
      collapse_of_mem hx, Homeomorph.onePointCongr_apply, OnePoint.map_some,
      properCollapse_of_mem _ hx]
  · simp only [chartHomeomorph, Homeomorph.trans_apply, homeomorph_point,
      collapse_of_not_mem hx, Homeomorph.onePointCongr_apply, OnePoint.map_infty,
      properCollapse_of_notMem _ hx]

omit [CompactSpace X] [T2Space X] in
/-- Proper continuous maps extend continuously across infinity. -/
theorem continuous_onePointMap {f : X → Y} (hf : IsProperMap f) :
    Continuous (OnePoint.map f) := by
  apply OnePoint.continuous_map hf.continuous
  rw [hasBasis_coclosedCompact.tendsto_right_iff]
  intro K hK
  exact (hf.isCompact_preimage hK.2).compl_mem_coclosedCompact_of_isClosed
    (hK.1.preimage hf.continuous)

end AkopyanResearch.OpenComplementQuotient
