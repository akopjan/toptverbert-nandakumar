module

public import AkopyanResearch.Completion.ConnectivityTransport
public import Submission.WhiteheadTheorem.Shapes.MappingCylinder

/-!
# Connectivity of the actual mapping cylinder

Homotopy equivalences preserve the actual based homotopy groups and
path connectedness. The cylinder therefore has the connectivity of its
base, and its top has the connectivity of the domain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ConnectivityTransport

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}

/-- Transport connectivity along a homotopy equivalence, including the
paths from its chosen right inverse homotopy. -/
theorem homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (hX : Submission.IsNConnected n X) : Submission.IsNConnected n Y := by
  let : PathConnectedSpace X := hX.pathConnected
  let H := Submission.homotopyEquivRightHomotopy e
  let : PathConnectedSpace Y := {
    nonempty := ⟨e (Classical.choice hX.nonempty)⟩
    joined := fun y z => ⟨(H.evalAt y).symm.trans
      (((PathConnectedSpace.somePath (e.symm y) (e.symm z)).map e.continuous).trans
        (H.evalAt z))⟩ }
  refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
  let : Subsingleton (HomotopyGroup.Pi (k + 1) X (e.symm b)) :=
    hX.subsingleton_pi k hk (e.symm b)
  exact (Submission.homotopyGroupMulEquivOfHomotopyEquiv
    (N := Fin (k + 1)) e.symm b).injective.subsingleton

end AkopyanResearch.ConnectivityTransport

namespace AkopyanResearch.MappingCylinderConnectivity

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}

theorem cylinder (hY : Submission.IsNConnected n Y) :
    Submission.IsNConnected n (TopCat.MapCyl f) :=
  ConnectivityTransport.homotopyEquiv (TopCat.MapCyl.homotopyEquivBase f).symm hY

theorem top (hX : Submission.IsNConnected n X) :
    Submission.IsNConnected n (TopCat.MapCyl.top f) :=
  ConnectivityTransport.homeomorph (TopCat.MapCyl.domHomeoTop f) hX

end AkopyanResearch.MappingCylinderConnectivity
