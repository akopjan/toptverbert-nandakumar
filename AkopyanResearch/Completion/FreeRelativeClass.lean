module

public import AkopyanResearch.Completion.RelativeHomotopyBasepoint
public import Submission.Homotopy.RelGroup

/-!
# Classes of free maps of cube pairs

When the subspace is path connected and simply connected, a free map of
cube pairs determines a relative homotopy class at any chosen basepoint.
The construction uses an actual based representative and the proved
basepoint-repair theorem; no quotient or homology model is substituted.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open ContinuousMap
open scoped Topology unitInterval Topology.Homotopy

namespace AkopyanResearch.FreeRelativeClass

universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
variable {A : Set X} (a : A) [PathConnectedSpace A]

/-- A based representative of a map of cube pairs. -/
def representative (f : C(I^Fin (n + 1), X))
    (hf : Cube.IsMapOfPairs X A f) : RelGenLoop (n + 1) X A a :=
  (RelativeHomotopyBasepoint.exists_relGenLoop_at_fixed_base a f hf).choose

theorem representative_homotopic (f : C(I^Fin (n + 1), X))
    (hf : Cube.IsMapOfPairs X A f) :
    f.HomotopicWith (representative a f hf).val (Cube.IsMapOfPairs X A) :=
  (RelativeHomotopyBasepoint.exists_relGenLoop_at_fixed_base a f hf).choose_spec

/-- The relative homotopy class represented by a free map of pairs. -/
def classOf (f : C(I^Fin (n + 1), X))
    (hf : Cube.IsMapOfPairs X A f) : π_rel (n + 1) X A a :=
  ⟦representative a f hf⟧

variable (hπ : Subsingleton (HomotopyGroup.Pi 1 A a))

include hπ in
/-- Free homotopies of pair maps preserve the actual based relative class. -/
theorem classOf_congr {f g : C(I^Fin (n + 1), X)}
    (hf : Cube.IsMapOfPairs X A f) (hg : Cube.IsMapOfPairs X A g)
    (h : f.HomotopicWith g (Cube.IsMapOfPairs X A)) :
    classOf a f hf = classOf a g hg := by
  apply Quotient.sound
  exact RelativeHomotopyBasepoint.relGenLoop_homotopic_of_free a hπ _ _
    ((representative_homotopic a f hf).symm.trans
      (h.trans (representative_homotopic a g hg)))

include hπ in
/-- A preexisting based loop is represented by its usual quotient class. -/
@[simp] theorem classOf_relGenLoop (p : RelGenLoop (n + 1) X A a) :
    classOf a p.val p.property.1 = (⟦p⟧ : π_rel (n + 1) X A a) := by
  apply Quotient.sound
  exact RelativeHomotopyBasepoint.relGenLoop_homotopic_of_free a hπ _ _
    (representative_homotopic a p.val p.property.1).symm

/-- A map carried entirely into the subspace is freely nullhomotopic as a map of pairs. -/
theorem homotopic_const_of_range_subset (f : C(I^Fin (n + 1), X))
    (hf : ∀ y, f y ∈ A) :
    f.HomotopicWith (ContinuousMap.const _ (a : X)) (Cube.IsMapOfPairs X A) := by
  let F : C(I^Fin (n + 1), A) := ⟨fun y => ⟨f y, hf y⟩, by fun_prop⟩
  obtain ⟨y₀, hc⟩ := (contractible_iff_id_nullhomotopic (I^Fin (n + 1))).mp inferInstance
  let H₀ : Homotopy F (ContinuousMap.const _ (F y₀)) :=
    (Homotopy.refl F).comp hc.some
  let p := (PathConnectedSpace.joined (F y₀) a).somePath
  let H₁ : Homotopy (ContinuousMap.const (I^Fin (n + 1)) (F y₀))
      (ContinuousMap.const _ a) := p.toHomotopyConst
  let H := H₀.trans H₁
  exact ⟨{
    toFun := fun ty => (H ty : X)
    continuous_toFun := H.continuous.subtype_val
    map_zero_left := fun y => congrArg Subtype.val (H.apply_zero y)
    map_one_left := fun y => congrArg Subtype.val (H.apply_one y)
    prop' := fun t y _ => (H (t, y)).property }⟩

include hπ in
/-- The relative class of a map whose image lies in the subspace is the base class. -/
theorem classOf_eq_const_of_range_subset (f : C(I^Fin (n + 1), X))
    (hf : ∀ y, f y ∈ A) :
    classOf a f (fun y _ => hf y) =
      (⟦RelGenLoop.const⟧ : π_rel (n + 1) X A a) := by
  let p : RelGenLoop (n + 1) X A a := RelGenLoop.const
  have he : classOf a f (fun y _ => hf y) = classOf a p.val p.property.1 :=
    classOf_congr a hπ _ _ (homotopic_const_of_range_subset a f hf)
  exact he.trans (classOf_relGenLoop a hπ p)

include hπ in
/-- In group dimensions the preceding base class is the identity element. -/
theorem classOf_eq_one_of_range_subset (f : C(I^Fin (n + 2), X))
    (hf : ∀ y, f y ∈ A) :
    classOf a f (fun y _ => hf y) = (1 : π_rel (n + 2) X A a) :=
  classOf_eq_const_of_range_subset a hπ f hf

end AkopyanResearch.FreeRelativeClass
