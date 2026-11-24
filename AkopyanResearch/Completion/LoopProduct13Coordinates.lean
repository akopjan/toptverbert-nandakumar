module

public import AkopyanResearch.Completion.LoopProduct13Homology
public import AkopyanResearch.Completion.LoopSphereHomology
public import AkopyanResearch.Completion.BinaryProductHomology

/-! # The actual degree-twelve coordinates of a product with `ΩS13` -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LoopProduct13Coordinates

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel

variable (X : Type) [TopologicalSpace X] (hX : Submission.IsNConnected 11 X)

include hX in
theorem isIso_coordinates :
    IsIso (BinaryProductHomology.coordinates X (LoopSphereCover.Fibre.{0} 12)
      (AddCommGrpCat.of ℤ) 12) :=
  BinaryProductHomology.integral_coordinates_isIso X (LoopSphereCover.Fibre 12) 12 (by decide)
    (Classical.choice hX.nonempty) (LoopProductGeometry.constantLoop 12)
    (LoopProduct13Homology.kernelDiagonalIso X hX)
    (LoopSphereHomology.fibreDiagonalIso (AddCommGrpCat.of ℤ) 12 (by decide))

def coordinatesIso :
    homology (AddCommGrpCat.of ℤ) 12 (TopCat.of (X × LoopSphereCover.Fibre.{0} 12)) ≅
      homology (AddCommGrpCat.of ℤ) 12 (TopCat.of X) ⊞
        homology (AddCommGrpCat.of ℤ) 12 (TopCat.of (LoopSphereCover.Fibre.{0} 12)) := by
  letI := isIso_coordinates X hX
  exact asIso (BinaryProductHomology.coordinates X (LoopSphereCover.Fibre 12) (AddCommGrpCat.of ℤ) 12)

end AkopyanResearch.LoopProduct13Coordinates
