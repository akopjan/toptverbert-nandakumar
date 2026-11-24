module

public import AkopyanResearch.Completion.TargetFibration
public import AkopyanResearch.Completion.ProductConnectivity
public import AkopyanResearch.Completion.HomotopyFiberConnectivity
public import Submission.Hurewicz.ConnectedVanishing

/-!
# Eight-connectedness of the actual comparison target

This proves the connectivity of the previously constructed concrete target,
using its exact homotopy-fiber coordinates. The same target therefore has
vanishing ordinary integral homology in degrees one through eight.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.TargetConnectivity

open CategoryTheory CategoryTheory.Limits
open scoped OnePoint

theorem isNConnected_homotopyFiber {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} (f : C(X, Y)) (y₀ : Y)
    (hX : Submission.IsNConnected n X) (hY : Submission.IsNConnected (n + 1) Y) :
    Submission.IsNConnected n (HomotopyFiberFibration.Space f y₀) := by
  let : PathConnectedSpace X := hX.pathConnected
  let : PathConnectedSpace Y := hY.pathConnected
  let : PathConnectedSpace (HomotopyFiberFibration.Space f y₀) :=
    HomotopyFiberConnectivity.pathConnected_space f y₀
      (hY.subsingleton_pi 0 (by omega))
  refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
  exact HomotopyFiberConnectivity.pi_vanish f y₀ k b
    (hX.subsingleton_pi k hk _) (hY.subsingleton_pi (k + 1) (by omega) _)

variable (S : Finset (Fin 15)) (hS : S.Nonempty)

theorem singleProduct_isNConnected : Submission.IsNConnected 8 (TargetFiberModel.SingleProduct S) := by
  let : PathConnectedSpace (TargetFiberModel.SingleProduct S) :=
    ProductConnectivity.singleProduct_pathConnected S
  exact ⟨inferInstance, inferInstance,
    fun k hk b => ProductConnectivity.singleProduct_pi_vanish S (k + 1) hk b⟩

theorem pairProduct_isNConnected : Submission.IsNConnected 12 (TargetFiberModel.PairProduct S) := by
  let : PathConnectedSpace (TargetFiberModel.PairProduct S) :=
    ProductConnectivity.pairProduct_pathConnected S
  exact ⟨inferInstance, inferInstance,
    fun k hk b => ProductConnectivity.pairProduct_pi_vanish S (k + 1) hk b⟩

theorem standardFiber_isNConnected : Submission.IsNConnected 8 (TargetFiberModel.HomotopyFiber hS) :=
  isNConnected_homotopyFiber (TargetFibration.collapse hS) (fun _ => ∞)
    (singleProduct_isNConnected S) ((pairProduct_isNConnected S).mono (by decide : 9 ≤ 12))

include hS in
theorem isNConnected : Submission.IsNConnected 8 (ConcreteComparisonTarget.Space S) := by
  let e := TargetFiberModel.homotopyFiberHomeomorph hS
  let h := standardFiber_isNConnected S hS
  let : PathConnectedSpace (TargetFiberModel.HomotopyFiber hS) := h.pathConnected
  let : PathConnectedSpace (ConcreteComparisonTarget.Space S) := e.symm.pathConnectedSpace
  refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
  apply SphereConnectivity.pi_subsingleton_of_retract
    (⟨e, e.continuous⟩ : C(_, _)) (⟨e.symm, e.symm.continuous⟩ : C(_, _))
    (by apply ContinuousMap.ext; intro x; exact e.symm_apply_apply x)
  exact h.subsingleton_pi k hk (e b)

include hS in
theorem homology_vanish (i : ℕ) (hi : i ≤ 8) (hi0 : i ≠ 0) :
    IsZero (Submission.Hgrp i (TopCat.of (ConcreteComparisonTarget.Space S))) :=
  (isNConnected S hS).isZero_homology i hi hi0

end AkopyanResearch.TargetConnectivity
