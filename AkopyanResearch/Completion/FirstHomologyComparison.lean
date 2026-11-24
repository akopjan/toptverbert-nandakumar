module

public import Submission.Hurewicz.AbsoluteIsomorphism
public import Submission.Hurewicz.AbsoluteComparison
public import Submission.ForMathlib.HomotopyGroup.Product
public import AkopyanResearch.Completion.ConnectivityTransport
public import AkopyanResearch.Completion.TargetProjectionHomotopy

/-!
# Actual maps in the first nonzero homology degree

Naturality of the absolute Hurewicz isomorphism transports a bijection
of homotopy groups to the homology map induced by the same continuous
map. For products this identifies the isomorphism with the literal
family of coordinate projections.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FirstHomologyComparison

open CategoryTheory AlgebraicTopology Submission
open scoped Topology Topology.Homotopy

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isIso_of_bijective_pi (n : ℕ) (f : C(X, Y)) (x : X)
    (hX : IsNConnected (n + 1) X) (hY : IsNConnected (n + 1) Y)
    (hf : Function.Bijective (HomotopyGroup.map (N := Fin (n + 2))
      (x := x) (y := f x) f rfl)) :
    IsIso (HgrpMap (n + 2) (TopCat.ofHom f)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro u v huv
    obtain ⟨p, rfl⟩ := hX.absoluteHurewiczAdd_surjective x u
    obtain ⟨q, rfl⟩ := hX.absoluteHurewiczAdd_surjective x v
    have he : Additive.ofMul (HomotopyGroup.map f rfl p.toMul) =
        Additive.ofMul (HomotopyGroup.map f rfl q.toMul) := by
      apply hY.absoluteHurewiczAdd_injective (f x)
      simpa only [absoluteHurewiczAdd_naturality n f rfl] using huv
    have hpq : p = q := Additive.toMul.injective (hf.injective (Additive.ofMul.injective he))
    rw [hpq]
  · intro v
    obtain ⟨q, hq⟩ := hY.absoluteHurewiczAdd_surjective (f x) v
    obtain ⟨p, hp⟩ := hf.surjective q.toMul
    refine ⟨absoluteHurewiczAdd n x (Additive.ofMul p), ?_⟩
    rw [absoluteHurewiczAdd_naturality n f rfl]
    change absoluteHurewiczAdd n (f x)
      (Additive.ofMul (HomotopyGroup.map f rfl p)) = v
    rw [hp]
    exact hq

variable {ι : Type} (Z : ι → Type) [∀ i, TopologicalSpace (Z i)]

/-- The literal family of maps induced by product projections. -/
def productCoordinates (n : ℕ) : Hgrp (n + 2) (TopCat.of (∀ i, Z i)) ⟶
    AddCommGrpCat.of (∀ i, Hgrp (n + 2) (TopCat.of (Z i))) :=
  AddCommGrpCat.ofHom {
    toFun := fun z i => HgrpMap (n + 2) (TopCat.ofHom (ContinuousMap.eval i)) z
    map_zero' := funext fun _i => map_zero _
    map_add' := fun z w => funext fun _i => map_add _ z w }

theorem productCoordinates_isIso (n : ℕ) (z : ∀ i, Z i)
    (hZ : ∀ i, IsNConnected (n + 1) (Z i)) : IsIso (productCoordinates Z n) := by
  let hP := ConnectivityTransport.pi hZ
  let e := HomotopyGroup.piEquiv (N := Fin (n + 2)) z
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro u v huv
    obtain ⟨p, rfl⟩ := hP.absoluteHurewiczAdd_surjective z u
    obtain ⟨q, rfl⟩ := hP.absoluteHurewiczAdd_surjective z v
    have he : e p.toMul = e q.toMul := by
      funext i
      apply Additive.ofMul.injective
      apply (hZ i).absoluteHurewiczAdd_injective (z i)
      change absoluteHurewiczAdd n (z i)
          (Additive.ofMul (HomotopyGroup.map (ContinuousMap.eval i) rfl p.toMul)) =
        absoluteHurewiczAdd n (z i)
          (Additive.ofMul (HomotopyGroup.map (ContinuousMap.eval i) rfl q.toMul))
      have h := congrFun huv i
      change HgrpMap (n + 2) (TopCat.ofHom (ContinuousMap.eval i))
          (absoluteHurewiczAdd n z p) =
        HgrpMap (n + 2) (TopCat.ofHom (ContinuousMap.eval i))
          (absoluteHurewiczAdd n z q) at h
      simpa only [absoluteHurewiczAdd_naturality n (x := z) (y := z i)
        (ContinuousMap.eval i) rfl] using h
    rw [Additive.toMul.injective (e.injective he)]
  · intro v
    choose q hq using fun i => (hZ i).absoluteHurewiczAdd_surjective (z i) (v i)
    let p := e.symm (fun i => (q i).toMul)
    refine ⟨absoluteHurewiczAdd n z (Additive.ofMul p), ?_⟩
    funext i
    change HgrpMap (n + 2) (TopCat.ofHom (ContinuousMap.eval i))
      (absoluteHurewiczAdd n z (Additive.ofMul p)) = v i
    rw [absoluteHurewiczAdd_naturality n (ContinuousMap.eval i) rfl]
    change absoluteHurewiczAdd n (z i)
      (Additive.ofMul (HomotopyGroup.map (ContinuousMap.eval i) rfl p)) = v i
    have hp : HomotopyGroup.map (ContinuousMap.eval i) rfl p = (q i).toMul :=
      congrFun (e.apply_symm_apply (fun i => (q i).toMul)) i
    rw [hp]
    exact hq i

/-- The original target projection is an isomorphism in degree nine. -/
theorem targetProjection_isIso {S : Finset (Fin 15)} (hS : S.Nonempty) :
    IsIso (HgrpMap 9 (TopCat.ofHom (TargetFibration.projection hS))) := by
  let hP := TargetConnectivity.isNConnected S hS
  let : Nonempty (ConcreteComparisonTarget.Space S) := hP.nonempty
  let p := Classical.choice (inferInstance : Nonempty (ConcreteComparisonTarget.Space S))
  exact isIso_of_bijective_pi 7 (TargetFibration.projection hS) p hP
    (TargetConnectivity.singleProduct_isNConnected S)
    (TargetProjectionHomotopy.projection_pi_bijective hS p 8 (by decide))

end AkopyanResearch.FirstHomologyComparison
