module

public import Submission.Homotopy.SingletonPair

/-! # Initial connectivity of a pair from the actual homotopy exact sequence -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.RelativeHomologyConnectivity
open Submission
open scoped Topology Topology.Homotopy
variable {X : Type} [TopologicalSpace X] {A : Set X}

/-- Absolute connectivity of both spaces gives the initial relative
connectivity through the genuine homotopy exact sequence. -/
theorem initial (m : ℕ) (hX : IsNConnected m X) (hA : IsNConnected m A) :
    IsNConnectedPair m X A := by
  letI : PathConnectedSpace X := hX.pathConnected
  letI : PathConnectedSpace A := hA.pathConnected
  constructor
  · intro a z
    exact ⟨default,
      ((RelHomotopyGroup.iStar_isPointedMap 0 X A a).map_default).trans
        ((subsingleton_homotopyGroup_zero (a : X)).elim _ z)⟩
  · intro k hk a
    apply relativeUnique_of_adjacent_subsingleton k a
      (hX.subsingleton_pi k hk a)
    cases k with
    | zero => exact subsingleton_homotopyGroup_zero a
    | succ k => exact hA.subsingleton_pi k (by omega) a

end AkopyanResearch.RelativeHomologyConnectivity
