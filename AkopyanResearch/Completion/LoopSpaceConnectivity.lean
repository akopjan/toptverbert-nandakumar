module

public import AkopyanResearch.Completion.LoopSphereCover
public import AkopyanResearch.Completion.SphereConnectivity

/-!
# Path connectedness of the actual loop sphere

A vanishing fundamental group makes any two based loops homotopic. The
curried path homotopy is an actual path in the compact-open loop space.
Applying the proved sphere connectivity theorem supplies the hypothesis
for every sphere of dimension at least two.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.LoopSpaceConnectivity

open ContinuousMap

theorem pathConnectedSpace_loops_of_pi1 {X : Type*} [TopologicalSpace X] (x : X)
    (h : Subsingleton (HomotopyGroup.Pi 1 X x)) : PathConnectedSpace (Path x x) := by
  have : Subsingleton (HomotopyGroup.Pi 1 X x) := h
  have : Subsingleton (FundamentalGroup X x) :=
    (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).symm.subsingleton
  have : Subsingleton (Path.Homotopic.Quotient x x) :=
    (CategoryTheory.End.homEquiv (X := FundamentalGroupoid.mk x)).symm.subsingleton
  refine ⟨⟨Path.refl x⟩, fun p q => ?_⟩
  have hpq : p.Homotopic q :=
    Path.Homotopic.Quotient.eq.mp (Subsingleton.elim _ _)
  obtain ⟨H⟩ := hpq
  exact ⟨{
    toFun := H.eval
    continuous_toFun := by
      apply continuous_induced_rng.mpr
      exact H.toHomotopy.curry.continuous
    source' := H.eval_zero
    target' := H.eval_one }⟩

open LoopSphereCover
universe w

theorem sphere_pi1_vanish (n : ℕ) (hn : 0 < n) :
    Subsingleton (HomotopyGroup.Pi 1 (Sphere.{w} n) (basepoint n)) := by
  let e : Sphere.{w} n ≃ₜ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1 := Homeomorph.ulift
  apply SphereConnectivity.pi_subsingleton_of_retract
    (⟨e, e.continuous⟩ : C(Sphere.{w} n, _))
    (⟨e.symm, e.symm.continuous⟩ : C(_, Sphere.{w} n))
    (by ext x; exact e.symm_apply_apply x) 1 (basepoint n)
  exact SphereConnectivity.sphere_pi_vanish
    (EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1
    (by rw [finrank_euclideanSpace_fin]; omega) (e (basepoint n))

theorem pathConnectedSpace_loops (n : ℕ) (hn : 0 < n) :
    PathConnectedSpace (Path (basepoint.{w} n) (basepoint n)) :=
  pathConnectedSpace_loops_of_pi1 (basepoint n) (sphere_pi1_vanish n hn)

theorem pathConnectedSpace_fibre (n : ℕ) (hn : 0 < n) :
    PathConnectedSpace (Fibre.{w} n) := by
  have := pathConnectedSpace_loops n hn
  exact (loopHomeomorph n).symm.pathConnectedSpace

end AkopyanResearch.LoopSpaceConnectivity
