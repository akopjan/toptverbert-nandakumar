module

public import AkopyanResearch.Completion.SphereSourceHomology
public import AkopyanResearch.Completion.ConnectivityTransport

/-!
# Adjoining a nine-sphere preserves degrees ten through fourteen

For an eight-connected source and a nine-connected target, the actual
inclusion of the common-base homotopy fiber induces integral homology
isomorphisms in this range. All vanishing used in Mayer--Vietoris follows
from the proved connectivity theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.SphereNineSourceHomology

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel SphereSourceCover

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X × LoopSphereCover.Sphere.{0} 8, Y)) (y₀ : Y)
variable (hX : Submission.IsNConnected 8 X) (hY : Submission.IsNConnected 9 Y)

include hX hY

theorem base_isNConnected : Submission.IsNConnected 8 (BaseSpace f y₀) :=
  ConnectivityTransport.pullback
    (ContractibleSourcePullback.baseMap f (ProductHemisphereCover.commonPoint 8)) y₀ hX hY

theorem base_homology_vanish (i : ℕ) (hi : i ≤ 8) (hi0 : i ≠ 0) :
    IsZero (homology (AddCommGrpCat.of ℤ) i (TopCat.of (BaseSpace f y₀))) :=
  (base_isNConnected f y₀ hX hY).isZero_homology i hi hi0

/-- This is the map induced by the literal inclusion over the chosen common
point of the nine-sphere, not an unspecified group isomorphism. -/
theorem baseInclusion_isIso (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    IsIso (SphereSourceHomology.baseInclusionMap f y₀ (AddCommGrpCat.of ℤ) i) := by
  cases i with
  | zero => omega
  | succ i =>
    apply SphereSourceHomology.baseInclusion_isIso_of_base_vanish
      f y₀ (AddCommGrpCat.of ℤ) i (by omega)
    · exact base_homology_vanish f y₀ hX hY (i - 8) (by omega) (by omega)
    · exact base_homology_vanish f y₀ hX hY (i + 1 - 8) (by omega) (by omega)

def baseInclusionIso (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    homology (AddCommGrpCat.of ℤ) i (TopCat.of (BaseSpace f y₀)) ≅
      homology (AddCommGrpCat.of ℤ) i (TopCat.of (Total f y₀)) := by
  letI := baseInclusion_isIso f y₀ hX hY i hi hi'
  exact asIso (SphereSourceHomology.baseInclusionMap f y₀ (AddCommGrpCat.of ℤ) i)

theorem isZero_total_of_base (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14)
    (h : IsZero (homology (AddCommGrpCat.of ℤ) i (TopCat.of (BaseSpace f y₀)))) :
    IsZero (homology (AddCommGrpCat.of ℤ) i (TopCat.of (Total f y₀))) :=
  h.of_iso (baseInclusionIso f y₀ hX hY i hi hi').symm

end AkopyanResearch.SphereNineSourceHomology
