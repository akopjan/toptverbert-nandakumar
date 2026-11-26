module

public import AkopyanResearch.Completion.OpenComplementQuotient
public import AkopyanResearch.Completion.PairSphereAction

/-!
# The concrete quotient of the pair space

The quotient collapsing the actual closed complement of the pair chart is
homeomorphic to the one-point compactification of `S⁵ × PairTarget`.
Under this exact homeomorphism, the original pair collapse is the
compactification of projection to `PairTarget`. No homotopy type of the
wedge, cofibration, or connectivity conclusion is assumed here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairCofiberModel

open Set Topology
open scoped OnePoint

abbrev PairSpace := PairCollapse.PairSpace Priv4 Priv4 Comm6
abbrev Domain : Set PairSpace := PairCollapse.chartDomain
abbrev ClosedLocus : Set PairSpace := Domainᶜ
abbrev UnitDirections := NormalBundleTrivialization.UnitDirections Comm6
abbrev Cofiber := OpenComplementQuotient.Space Domain

instance : CompactSpace PairSpace := by
  let : CompactSpace (Metric.sphere (0 : Rep10) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Rep10) 1)
  exact spherePairEquiv.compactSpace

set_option backward.isDefEq.respectTransparency false in
instance : CompactSpace UnitDirections := by
  change CompactSpace ↥({w : Comm6 | ‖w‖ = 1} : Set Comm6)
  apply isCompact_iff_compactSpace.mp
  change IsCompact ({w : Comm6 | ‖w‖ = 1} : Set Comm6)
  simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : Comm6) 1

theorem isClosed_closedLocus : IsClosed ClosedLocus :=
  PairCollapse.isOpen_chartDomain.isClosed_compl

def baseUnit : PairCollapse.FullUnit Priv4 Comm6 :=
  ⟨(ePriv 0, 0), by rw [orthonormal_ePriv.1 0]; simp⟩

theorem closedLocus_nonempty : ClosedLocus.Nonempty := by
  refine ⟨(baseUnit, baseUnit), ?_⟩
  change ¬ (‖(0 : Comm6)‖ • (0 : Comm6) ≠ ‖(0 : Comm6)‖ • (0 : Comm6))
  simp

def chart : Domain ≃ₜ UnitDirections × PairTarget :=
  PairCollapse.chartHomeomorph.trans
    (NormalBundleTrivialization.normalBundleHomeomorph pairF norm_pairF)

def quotientMap : PairSpace → Cofiber := OpenComplementQuotient.point Domain

theorem quotientMap_eq_iff (x y : PairSpace) :
    quotientMap x = quotientMap y ↔ x = y ∨ (x ∈ ClosedLocus ∧ y ∈ ClosedLocus) :=
  OpenComplementQuotient.point_eq_iff Domain x y

theorem continuous_quotientMap : Continuous quotientMap :=
  OpenComplementQuotient.continuous_point Domain

/-- The quotient has its ordinary quotient topology; the homeomorphism
uses the actual open chart and the actual thirteen-dimensional target. -/
def cofiberHomeomorph : Cofiber ≃ₜ OnePoint (UnitDirections × PairTarget) :=
  OpenComplementQuotient.chartHomeomorph PairCollapse.isOpen_chartDomain
    closedLocus_nonempty chart

theorem cofiberHomeomorph_quotientMap (x : PairSpace) :
    cofiberHomeomorph (quotientMap x) = properCollapse Domain chart x :=
  OpenComplementQuotient.chartHomeomorph_point
    PairCollapse.isOpen_chartDomain closedLocus_nonempty chart x

def projection : C(OnePoint (UnitDirections × PairTarget), OnePoint PairTarget) :=
  ⟨OnePoint.map Prod.snd,
    OpenComplementQuotient.continuous_onePointMap isProperMap_snd_of_compactSpace⟩

theorem original_collapse_factor (x : PairSpace) :
    pairCollapseMap x = projection (cofiberHomeomorph (quotientMap x)) := by
  rw [cofiberHomeomorph_quotientMap]
  change properCollapse Domain (fun y => (chart y).2) x =
    OnePoint.map Prod.snd (properCollapse Domain chart x)
  by_cases hx : x ∈ Domain
  · simp only [properCollapse_of_mem _ hx, OnePoint.map_some]
  · simp only [properCollapse_of_notMem _ hx, OnePoint.map_infty]

end AkopyanResearch.PairCofiberModel
