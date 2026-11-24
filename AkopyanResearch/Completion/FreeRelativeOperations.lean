module

public import AkopyanResearch.Completion.CubicalPasting
public import Submission.Homotopy.RelMap

/-!
# Changing the basepoint of a free relative class

For a path connected, simply connected subspace, changing the chosen
basepoint preserves the relative group operation. The multiplication
proof uses the already established coherent binary pasting theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FreeRelativeOperations

open ContinuousMap CubicalCut CubicalPasting FreeRelativeClass
open scoped Topology unitInterval Topology.Homotopy

universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X] {A : Set X}

theorem firstHalf_blend (t : I) :
    RelGenLoop.firstHalf (blend CubicalCut.midpoint 0 t) = t := by
  have h : 2 * (blend CubicalCut.midpoint 0 t).val = t.val := by dsimp [blend, CubicalCut.midpoint]; ring
  unfold RelGenLoop.firstHalf
  rw [h]
  exact Set.projIcc_of_mem _ t.property

theorem secondHalf_blend (t : I) :
    RelGenLoop.secondHalf (blend CubicalCut.midpoint 1 t) = t := by
  have h : 2 * (blend CubicalCut.midpoint 1 t).val - 1 = t.val := by dsimp [blend, CubicalCut.midpoint]; ring
  unfold RelGenLoop.secondHalf
  rw [h]
  exact Set.projIcc_of_mem _ t.property

theorem leftPair_transAt (i : Fin (n + 1)) {a : A}
    (p q : RelGenLoop (n + 2) X A a) :
    leftPair i (RelGenLoop.transAt i p q).val = p.val := by
  apply ContinuousMap.ext
  intro y
  change (RelGenLoop.transAt i p q).val (left i y) = p.val y
  rw [RelGenLoop.transAt_apply]
  have hh : (left i y i.castSucc).val ≤ 1 / 2 := by
    simp only [left, Function.update_self]
    dsimp [blend, CubicalCut.midpoint]
    linarith [(y i.castSucc).property.2]
  rw [if_pos hh]
  simp only [left, Function.update_self, firstHalf_blend, Function.update_idem,
    Function.update_eq_self]

theorem rightPair_transAt (i : Fin (n + 1)) {a : A}
    (p q : RelGenLoop (n + 2) X A a) :
    rightPair i (RelGenLoop.transAt i p q).val = q.val := by
  apply ContinuousMap.ext
  intro y
  change (RelGenLoop.transAt i p q).val (right i y) = q.val y
  rw [RelGenLoop.transAt_apply]
  split_ifs with h
  · have hy0 : y i.castSucc = 0 := by
      apply Subtype.ext
      simp only [right, Function.update_self] at h
      dsimp [blend, CubicalCut.midpoint] at h
      change (y i.castSucc).val = 0
      linarith [(y i.castSucc).property.1]
    have he : blend CubicalCut.midpoint 1 (y i.castSucc) = CubicalCut.midpoint := by rw [hy0]; simp
    have hm : RelGenLoop.firstHalf CubicalCut.midpoint = 1 := RelGenLoop.firstHalf_of_half rfl
    simp only [right, Function.update_self, he, hm, Function.update_idem]
    rw [RelGenLoop.transAt_wall, ← hy0, Function.update_eq_self]
  · simp only [right, Function.update_self, secondHalf_blend,
      Function.update_idem, Function.update_eq_self]

variable [PathConnectedSpace A]

theorem classOf_transAt (b : A)
    (hπ : Subsingleton (HomotopyGroup.Pi 1 A b)) (i : Fin (n + 1))
    {a : A} (p q : RelGenLoop (n + 2) X A a) :
    classOf b (RelGenLoop.transAt i p q).val (RelGenLoop.transAt i p q).property.1 =
      classOf b q.val q.property.1 * classOf b p.val p.property.1 := by
  have hm : ∀ y, y ∈ middle i → (RelGenLoop.transAt i p q).val y ∈ A := by
    intro y hy
    change y i.castSucc = CubicalCut.midpoint at hy
    rw [RelGenLoop.transAt_apply, if_pos (by rw [hy]; exact le_rfl), hy,
      RelGenLoop.firstHalf_of_half rfl]
    rw [p.property.2 _ (RelGenLoop.update_castSucc_one_mem_boundaryJar i y)]
    exact a.property
  have h := classOf_binary_pasting i (RelGenLoop.transAt i p q).val
    (RelGenLoop.transAt i p q).property.1 hm b hπ
  simpa only [rightPair_transAt, leftPair_transAt] using h

variable (a b : A)
variable (hπa : Subsingleton (HomotopyGroup.Pi 1 A a))
variable (hπb : Subsingleton (HomotopyGroup.Pi 1 A b))

/-- Change basepoint by taking the same free map of pairs. -/
def rebase : π_rel (n + 1) X A a → π_rel (n + 1) X A b :=
  Quotient.lift (fun p => classOf b p.val p.property.1) (by
    intro p q H
    apply classOf_congr b hπb p.property.1 q.property.1
    obtain ⟨H⟩ := H
    exact ⟨{
      toFun := H
      continuous_toFun := H.continuous
      map_zero_left := H.apply_zero
      map_one_left := H.apply_one
      prop' := fun t => (H.prop t).1 }⟩)

@[simp]
theorem rebase_mk (p : RelGenLoop (n + 1) X A a) :
    rebase a b hπb (⟦p⟧ : π_rel (n + 1) X A a) =
      classOf b p.val p.property.1 := rfl

@[simp]
theorem rebase_classOf (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) :
    rebase a b hπb (classOf a f hf) = classOf b f hf := by
  change classOf b (representative a f hf).val (representative a f hf).property.1 = _
  exact classOf_congr b hπb _ _ (representative_homotopic a f hf).symm

/-- The basepoint-change equivalence is independent of paths, because
the subspace has trivial fundamental group. -/
def rebaseEquiv : π_rel (n + 1) X A a ≃ π_rel (n + 1) X A b where
  toFun := rebase a b hπb
  invFun := rebase b a hπa
  left_inv z := by
    refine Quotient.inductionOn z ?_
    intro p
    rw [rebase_mk, rebase_classOf, classOf_relGenLoop a hπa]
  right_inv z := by
    refine Quotient.inductionOn z ?_
    intro p
    rw [rebase_mk, rebase_classOf, classOf_relGenLoop b hπb]

theorem rebase_mul (z w : π_rel (n + 2) X A a) :
    rebase a b hπb (z * w) = rebase a b hπb z * rebase a b hπb w := by
  refine Quotient.inductionOn₂ z w ?_
  intro p q
  rw [RelHomotopyGroup.mul_mk 0 p q]
  exact classOf_transAt b hπb 0 q p

/-- The equivalence preserves the actual relative homotopy group law. -/
def rebaseMulEquiv : π_rel (n + 2) X A a ≃* π_rel (n + 2) X A b :=
  { rebaseEquiv a b hπa hπb with map_mul' := rebase_mul a b hπb }

section Naturality

universe v
variable {Y : Type v} [TopologicalSpace Y] {B : Set Y}
variable [PathConnectedSpace B] {c : B}

/-- Naturality for a based pair map, expressed using free representatives. -/
theorem map_classOf (F : Submission.BasedPairMap A B a c)
    (hπc : Subsingleton (HomotopyGroup.Pi 1 B c))
    (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) :
    Submission.RelHomotopyGroup.map F (classOf a f hf) =
      classOf c (F.toContinuousMap.comp f) (fun y hy => F.mapsTo' (hf y hy)) := by
  let p := representative a f hf
  let q := Submission.RelGenLoop.map F p
  obtain ⟨H⟩ := representative_homotopic a f hf
  have HH : (F.toContinuousMap.comp f).HomotopicWith q.val (Cube.IsMapOfPairs Y B) :=
    ⟨{
      toFun := fun ty => F.toContinuousMap (H ty)
      continuous_toFun := F.toContinuousMap.continuous.comp H.continuous
      map_zero_left := fun y => congrArg F.toContinuousMap (H.apply_zero y)
      map_one_left := fun y => congrArg F.toContinuousMap (H.apply_one y)
      prop' := fun t y hy => F.mapsTo' (H.prop t y hy) }⟩
  change (⟦q⟧ : π_rel (n + 1) Y B c) = _
  exact ((classOf_congr c hπc _ _ HH).trans (classOf_relGenLoop c hπc q)).symm

/-- An arbitrary map of pairs induces a group homomorphism at any
chosen target basepoint when the target subspace is simply connected. -/
def postcomposeHom (F : C(X, Y)) (hF : Set.MapsTo F A B)
    (c : B) (hπB : ∀ c : B, Subsingleton (HomotopyGroup.Pi 1 B c)) :
    π_rel (n + 2) X A a →* π_rel (n + 2) Y B c := by
  let c₀ : B := ⟨F a, hF a.property⟩
  let G : Submission.BasedPairMap A B a c₀ := ⟨F, hF, rfl⟩
  exact (rebaseMulEquiv c₀ c (hπB c₀) (hπB c)).toMonoidHom.comp
    (Submission.RelHomotopyGroup.mapHom n G)

theorem postcomposeHom_classOf (F : C(X, Y)) (hF : Set.MapsTo F A B)
    (c : B) (hπB : ∀ c : B, Subsingleton (HomotopyGroup.Pi 1 B c))
    (f : C(I^Fin (n + 2), X)) (hf : Cube.IsMapOfPairs X A f) :
    postcomposeHom a F hF c hπB (classOf a f hf) =
      classOf c (F.comp f) (fun y hy => hF (hf y hy)) := by
  let c₀ : B := ⟨F a, hF a.property⟩
  let G : Submission.BasedPairMap A B a c₀ := ⟨F, hF, rfl⟩
  change rebase c₀ c (hπB c)
    (Submission.RelHomotopyGroup.map G (classOf a f hf)) = _
  rw [map_classOf a G (hπB c₀), rebase_classOf]

end Naturality

end AkopyanResearch.FreeRelativeOperations
