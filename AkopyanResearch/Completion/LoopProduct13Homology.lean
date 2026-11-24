module

public import AkopyanResearch.Completion.LoopProductHomology
public import AkopyanResearch.Completion.ConnectivityTransport

/-! # Integral homology of adjoining a loop thirteen-sphere -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LoopProduct13Homology

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel LoopProductGeometry

variable (X : Type) [TopologicalSpace X] (hX : Submission.IsNConnected 11 X)

include hX

theorem base_isNConnected : Submission.IsNConnected 11 (Base X 12) :=
  ConnectivityTransport.pullback
    (ContractibleSourcePullback.baseMap (sourceMap X 12) (LoopSphereCover.basepoint 12))
    (LoopSphereCover.basepoint 12) hX (ConnectivityTransport.sphere 12)

theorem product_isNConnected : Submission.IsNConnected 11 (X × LoopSphereCover.Fibre.{0} 12) :=
  ConnectivityTransport.homeomorph (baseHomeomorph X 12) (base_isNConnected X hX)

theorem base_homology_vanish (i : ℕ) (hi : i ≤ 11) (hi0 : i ≠ 0) :
    IsZero (homology (AddCommGrpCat.of ℤ) i (TopCat.of (Base X 12))) :=
  (base_isNConnected X hX).isZero_homology i hi hi0

theorem isIso_projection (i : ℕ) (hi : 0 < i) (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    IsIso (LoopProductHomology.projectionMap X (AddCommGrpCat.of ℤ) 12 i) := by
  by_cases hlt : i < 12
  · exact LoopProductHomology.isIso_projection_below X (AddCommGrpCat.of ℤ) 12 i hlt
  · exact LoopProductHomology.isIso_projection_of_base_vanish X (AddCommGrpCat.of ℤ)
      12 i (by omega) (base_homology_vanish X hX (i - 12) (by omega) (by omega))

def projectionIso (i : ℕ) (hi : 0 < i) (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    homology (AddCommGrpCat.of ℤ) i (TopCat.of (X × LoopSphereCover.Fibre 12)) ≅
      homology (AddCommGrpCat.of ℤ) i (TopCat.of X) := by
  letI := isIso_projection X hX i hi hi₁₄ hne
  exact asIso (LoopProductHomology.projectionMap X (AddCommGrpCat.of ℤ) 12 i)

def kernelDiagonalIso :
    kernel (LoopProductHomology.projectionMap X (AddCommGrpCat.of ℤ) 12 12) ≅
      AddCommGrpCat.of ℤ := by
  letI : PathConnectedSpace (Base X 12) := (base_isNConnected X hX).pathConnected
  exact LoopProductHomology.projectionKernelShiftIso X (AddCommGrpCat.of ℤ) 12 12 (by decide) ≪≫
    asIso ((TopCat.of (Base X 12)).singularHomology₀ε (AddCommGrpCat.of ℤ))

omit hX in
theorem fibre_isNConnected : Submission.IsNConnected 11 (LoopSphereCover.Fibre.{0} 12) :=
  ConnectivityTransport.homeomorph (Homeomorph.uniqueProd PUnit (LoopSphereCover.Fibre 12))
    (product_isNConnected PUnit (ConnectivityTransport.contractible PUnit 11))

end AkopyanResearch.LoopProduct13Homology
