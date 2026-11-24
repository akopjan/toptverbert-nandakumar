module

public import AkopyanResearch.Completion.RepresentationSphereInvariants
public import AkopyanResearch.Completion.TargetFiberModel

/-!
# Connectivity of the actual products of representation spheres

Coordinatewise nullhomotopies assemble continuously in the product topology.
This proves vanishing of the actual Mathlib homotopy groups of the products;
it does not replace the product by a collection of independent hypotheses.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ProductConnectivity

open scoped Topology.Homotopy

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable {n : ℕ} {x : ∀ i, X i}

def projectLoop (i : ι) (p : GenLoop (Fin n) (∀ i, X i) x) :
    GenLoop (Fin n) (X i) (x i) :=
  ⟨(ContinuousMap.eval i).comp p.val, fun z hz => congrFun (p.property z hz) i⟩

theorem pi_product_vanish
    (h : ∀ i, Subsingleton (HomotopyGroup.Pi n (X i) (x i))) :
    Subsingleton (HomotopyGroup.Pi n (∀ i, X i) x) := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b fun f g => ?_⟩
  have hh : ∀ i, GenLoop.Homotopic (projectLoop i f) (projectLoop i g) := by
    intro i
    exact Quotient.exact ((h i).elim
      (⟦projectLoop i f⟧ : HomotopyGroup.Pi n (X i) (x i))
      (⟦projectLoop i g⟧ : HomotopyGroup.Pi n (X i) (x i)))
  let H i := Classical.choice (hh i)
  exact Quotient.sound ⟨{
    toFun := fun z i => H i z
    continuous_toFun := continuous_pi fun i => (H i).continuous
    map_zero_left := fun z => funext fun i => (H i).apply_zero z
    map_one_left := fun z => funext fun i => (H i).apply_one z
    prop' := fun t z hz => funext fun i => (H i).prop t z hz }⟩

variable (S : Finset (Fin 15))

theorem singleProduct_pi_vanish (k : ℕ) (hk : k ≤ 8)
    (b : TargetFiberModel.SingleProduct S) :
    Subsingleton (HomotopyGroup.Pi k (TargetFiberModel.SingleProduct S) b) :=
  pi_product_vanish fun _ => RepresentationSphereInvariants.single_pi_vanish k hk _

theorem pairProduct_pi_vanish (k : ℕ) (hk : k ≤ 12)
    (b : TargetFiberModel.PairProduct S) :
    Subsingleton (HomotopyGroup.Pi k (TargetFiberModel.PairProduct S) b) :=
  pi_product_vanish fun _ => RepresentationSphereInvariants.pair_pi_vanish k hk _

theorem singleProduct_pathConnected : PathConnectedSpace (TargetFiberModel.SingleProduct S) := by
  let : PathConnectedSpace OriginalJoinBridge.Target :=
    RepresentationSphereInvariants.single_pathConnected
  infer_instance

theorem pairProduct_pathConnected : PathConnectedSpace (TargetFiberModel.PairProduct S) := by
  let : PathConnectedSpace (OnePoint PairTarget) :=
    RepresentationSphereInvariants.pair_pathConnected
  infer_instance

end AkopyanResearch.ProductConnectivity
