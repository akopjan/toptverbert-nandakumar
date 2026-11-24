module

public import AkopyanResearch.Completion.ConcreteComparisonHomology
public import AkopyanResearch.Completion.MappingCylinderConnectivity
public import AkopyanResearch.Completion.RelativeHomologyConnectivity

/-!
# Fourteen-connectivity of the original comparison

The actual mapping cylinder and its actual top are eight-connected.
The computed vanishing of relative integral homology raises the
connectivity of this same pair through degree fourteen.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.ConcreteComparisonConnectivity

open CategoryTheory AkopyanQuadratic Submission
open ConcreteComparisonCoordinates ConcreteComparisonHomology

variable {S : Finset (Fin 15)}

theorem cylinder_eight (hS : S.Nonempty) :
    IsNConnected 8 (TopCat.MapCyl (TopCat.ofHom (comparison hS))) :=
  MappingCylinderConnectivity.cylinder (TopCat.ofHom (comparison hS))
    (TargetConnectivity.isNConnected S hS)

theorem top_eight (hS : S.Nonempty) :
    IsNConnected 8 (TopCat.MapCyl.top (TopCat.ofHom (comparison hS))) :=
  MappingCylinderConnectivity.top (TopCat.ofHom (comparison hS))
    (isNConnected_quadComplement S hS)

/-- The original comparison is fourteen-connected, expressed as the
actual relative homotopy groups of its mapping-cylinder pair. -/
theorem cylinder_pair_fourteen (hS : S.Nonempty) :
    IsNConnectedPair 14 (TopCat.MapCyl (TopCat.ofHom (comparison hS)))
      (TopCat.MapCyl.top (TopCat.ofHom (comparison hS))) :=
  RelativeHomologyConnectivity.fourteen (cylinder_eight hS) (top_eight hS)
    (fun k hk hk14 => cylinder_hrelSet_zero hS k hk14 (by omega))

end AkopyanResearch.ConcreteComparisonConnectivity
