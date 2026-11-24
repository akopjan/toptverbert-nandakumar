module

public import AkopyanResearch.Completion.TargetConnectivity

/-!
# Connectivity under homeomorphisms and products

These operations transport the actual homotopy groups and path-connectedness
used by the bounded integral homology vanishing theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ConnectivityTransport

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}

/-- A continuous retract inherits path connectedness and the stated
vanishing range of the actual homotopy groups. -/
theorem retract (s : C(Y, X)) (r : C(X, Y))
    (hrs : r.comp s = ContinuousMap.id Y) (hX : Submission.IsNConnected n X) :
    Submission.IsNConnected n Y := by
  let : PathConnectedSpace X := hX.pathConnected
  have hr : Function.Surjective r := fun y => ⟨s y, DFunLike.congr_fun hrs y⟩
  let : PathConnectedSpace Y := hr.pathConnectedSpace r.continuous
  refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
  exact SphereConnectivity.pi_subsingleton_of_retract s r hrs (k + 1) b
    (hX.subsingleton_pi k hk (s b))

theorem homeomorph (e : X ≃ₜ Y) (hX : Submission.IsNConnected n X) :
    Submission.IsNConnected n Y := by
  let : PathConnectedSpace X := hX.pathConnected
  let : PathConnectedSpace Y := e.pathConnectedSpace
  refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
  apply SphereConnectivity.pi_subsingleton_of_retract
    (⟨e.symm, e.symm.continuous⟩ : C(Y, X)) (⟨e, e.continuous⟩ : C(X, Y))
    (by ext y; exact e.apply_symm_apply y)
  exact hX.subsingleton_pi k hk (e.symm b)

theorem pi {ι : Type} {Z : ι → Type} [∀ i, TopologicalSpace (Z i)]
    (hZ : ∀ i, Submission.IsNConnected n (Z i)) :
    Submission.IsNConnected n (∀ i, Z i) := by
  let : ∀ i, PathConnectedSpace (Z i) := fun i => (hZ i).pathConnected
  refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
  exact ProductConnectivity.pi_product_vanish fun i => (hZ i).subsingleton_pi k hk (b i)

theorem pullback (f : C(X, Y)) (y₀ : Y)
    (hX : Submission.IsNConnected n X) (hY : Submission.IsNConnected (n + 1) Y) :
    Submission.IsNConnected n (Submission.Pullback f (Submission.ev₁ Y y₀)) :=
  homeomorph (HomotopyFiberFibration.pullbackHomeomorph f y₀)
    (TargetConnectivity.isNConnected_homotopyFiber f y₀ hX hY)

theorem contractible (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    Submission.IsNConnected n X := by
  refine ⟨inferInstance, inferInstance, fun k _ b => ?_⟩
  exact Submission.subsingleton_homotopyGroup_of_contractible (N := Fin (k + 1)) b

theorem sphere (n : ℕ) : Submission.IsNConnected n (TopCat.sphere.{0} (n + 1)) := by
  let E := EuclideanSpace ℝ (Fin ((n + 1) + 1))
  let : PathConnectedSpace (Metric.sphere (0 : E) 1) :=
    SphereConnectivity.sphere_pathConnected E (by
      change 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin ((n + 1) + 1)))
      rw [finrank_euclideanSpace_fin]
      omega)
  have h : Submission.IsNConnected n (Metric.sphere (0 : E) 1) := by
    refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
    apply SphereConnectivity.sphere_pi_vanish E (k + 1)
    change (k + 1) + 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin ((n + 1) + 1)))
    rw [finrank_euclideanSpace_fin]
    omega
  exact homeomorph Homeomorph.ulift.symm h

end AkopyanResearch.ConnectivityTransport
