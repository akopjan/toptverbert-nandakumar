module

public import AkopyanResearch.Completion.CubicalCut
public import AkopyanResearch.Completion.FreeRelativeClass

/-!
# Coherent normalization and binary pasting of relative cube maps

Both half-cubes use the same contraction of the outer jar and middle
hyperplane. Their extended homotopies consequently agree on the shared
face. Gluing them gives the actual relative product representative.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.CubicalPasting

open ContinuousMap CubicalCut RelativeHomotopyBasepoint
open scoped Topology unitInterval Topology.Homotopy

variable {n : ℕ} (i : Fin (n + 1))

def unleft (y : Box (n := n)) : Box (n := n) :=
  Function.update y i.castSucc (RelGenLoop.firstHalf (y i.castSucc))

def unright (y : Box (n := n)) : Box (n := n) :=
  Function.update y i.castSucc (RelGenLoop.secondHalf (y i.castSucc))

@[fun_prop] theorem continuous_unleft : Continuous (unleft i) :=
  Cube.continuous_update _ (by fun_prop)

@[fun_prop] theorem continuous_unright : Continuous (unright i) :=
  Cube.continuous_update _ (by fun_prop)

theorem left_unleft (y : Box (n := n)) (hy : (y i.castSucc).val ≤ 1 / 2) :
    left i (unleft i y) = y := by
  funext j
  by_cases hj : j = i.castSucc
  · subst j
    simp only [left, unleft, Function.update_self]
    apply Subtype.ext
    have hm : 2 * (y i.castSucc).val ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [(y i.castSucc).property.1], by linarith⟩
    simp only [blend, CubicalCut.midpoint, RelGenLoop.firstHalf, Set.projIcc_of_mem _ hm]
    dsimp
    ring
  · simp only [left, unleft, Function.update_of_ne hj]

theorem right_unright (y : Box (n := n)) (hy : 1 / 2 ≤ (y i.castSucc).val) :
    right i (unright i y) = y := by
  funext j
  by_cases hj : j = i.castSucc
  · subst j
    simp only [right, unright, Function.update_self]
    apply Subtype.ext
    have hm : 2 * (y i.castSucc).val - 1 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [(y i.castSucc).property.2]⟩
    simp only [blend, CubicalCut.midpoint, RelGenLoop.secondHalf, Set.projIcc_of_mem _ hm]
    dsimp
    ring
  · simp only [right, unright, Function.update_of_ne hj]

theorem unleft_boundary (y : Box (n := n)) (hy : y ∈ ∂I^(n + 2))
    (ht : (y i.castSucc).val ≤ 1 / 2) : unleft i y ∈ ∂I^(n + 2) := by
  by_cases h : y i.castSucc = 0 ∨ y i.castSucc = 1
  · rcases h with h | h
    · have he : unleft i y = y := by
        funext j
        by_cases hj : j = i.castSucc
        · subst j; simp [unleft, h]
        · simp [unleft, Function.update_of_ne hj]
      rwa [he]
    · rw [h] at ht
      norm_num at ht
  · exact Cube.update_mem_boundary hy h _

theorem unright_boundary (y : Box (n := n)) (hy : y ∈ ∂I^(n + 2))
    (ht : 1 / 2 < (y i.castSucc).val) : unright i y ∈ ∂I^(n + 2) := by
  by_cases h : y i.castSucc = 0 ∨ y i.castSucc = 1
  · rcases h with h | h
    · rw [h] at ht
      norm_num at ht
    · have he : unright i y = y := by
        funext j
        by_cases hj : j = i.castSucc
        · subst j; simp [unright, h]
        · simp [unright, Function.update_of_ne hj]
      rwa [he]
  · exact Cube.update_mem_boundary hy h _

universe u
variable {X : Type u} [TopologicalSpace X] {A : Set X}
variable (f : C(Box (n := n), X))
  (hf : Cube.IsMapOfPairs X A f) (hm : ∀ y ∈ middle i, f y ∈ A)

def leftPair : C(Box (n := n), X) := f.comp (leftMap i)
def rightPair : C(Box (n := n), X) := f.comp (rightMap i)

include hf hm in
theorem leftPair_isMapOfPairs : Cube.IsMapOfPairs X A (leftPair i f) := by
  intro y hy
  rcases left_boundary_mem i y hy with h | h
  · exact hf _ h
  · exact hm _ h

include hf hm in
theorem rightPair_isMapOfPairs : Cube.IsMapOfPairs X A (rightPair i f) := by
  intro y hy
  rcases right_boundary_mem i y hy with h | h
  · exact hf _ h
  · exact hm _ h

def splitJarMap : C(splitJar i, A) where
  toFun y := ⟨f y.val, by
    rcases y.property with h | h
    · exact hf _ (Cube.boundaryJar_subset_boundary _ h)
    · exact hm _ h⟩
  continuous_toFun := by fun_prop

variable (a : A) [PathConnectedSpace A]

def splitJarNullhomotopy : Homotopy (splitJarMap i f hf hm) (ContinuousMap.const _ a) := by
  let g := splitJarMap i f hf hm
  let b : A := g ⟨center i, center_mem i⟩
  let H₀ : Homotopy g (ContinuousMap.const _ b) :=
    (Homotopy.refl g).comp (splitJarContraction i)
  let p := PathConnectedSpace.somePath b a
  let H₁ : Homotopy (ContinuousMap.const (splitJar i) b) (ContinuousMap.const _ a) := {
    toFun := fun ty => p ty.1
    continuous_toFun := by fun_prop
    map_zero_left _ := p.source
    map_one_left _ := p.target }
  exact H₀.trans H₁

def leftJarHomotopy : Homotopy
    (cubeJarMap (leftPair i f) (leftPair_isMapOfPairs i f hf hm))
    (ContinuousMap.const _ a) where
  toFun p := splitJarNullhomotopy i f hf hm a (p.1, leftJarMap i p.2)
  continuous_toFun := by fun_prop
  map_zero_left y := (splitJarNullhomotopy i f hf hm a).apply_zero (leftJarMap i y)
  map_one_left y := (splitJarNullhomotopy i f hf hm a).apply_one (leftJarMap i y)

def rightJarHomotopy : Homotopy
    (cubeJarMap (rightPair i f) (rightPair_isMapOfPairs i f hf hm))
    (ContinuousMap.const _ a) where
  toFun p := splitJarNullhomotopy i f hf hm a (p.1, rightJarMap i p.2)
  continuous_toFun := by fun_prop
  map_zero_left y := (splitJarNullhomotopy i f hf hm a).apply_zero (rightJarMap i y)
  map_one_left y := (splitJarNullhomotopy i f hf hm a).apply_one (rightJarMap i y)

include hf hm in
theorem exists_coherent_normalizations :
    ∃ p q : RelGenLoop (n + 2) X A a,
      ∃ HL : HomotopyWith (leftPair i f) p.val (Cube.IsMapOfPairs X A),
      ∃ HR : HomotopyWith (rightPair i f) q.val (Cube.IsMapOfPairs X A),
        ∀ t y, HL (t, Function.update y i.castSucc 1) =
          HR (t, Function.update y i.castSucc 0) := by
  obtain ⟨p, HL, hL⟩ := normalize_with_jar_homotopy a (leftPair i f)
    (leftPair_isMapOfPairs i f hf hm) (leftJarHomotopy i f hf hm a)
  obtain ⟨q, HR, hR⟩ := normalize_with_jar_homotopy a (rightPair i f)
    (rightPair_isMapOfPairs i f hf hm) (rightJarHomotopy i f hf hm a)
  refine ⟨p, q, HL, HR, fun t y => ?_⟩
  let yl : Cube.boundaryJar (n + 2) :=
    ⟨Function.update y i.castSucc 1, RelGenLoop.update_castSucc_one_mem_boundaryJar i y⟩
  let yr : Cube.boundaryJar (n + 2) :=
    ⟨Function.update y i.castSucc 0, RelGenLoop.update_castSucc_zero_mem_boundaryJar i y⟩
  rw [hL t yl, hR t yr]
  change ((splitJarNullhomotopy i f hf hm a) (t, leftJarMap i yl)).val =
    ((splitJarNullhomotopy i f hf hm a) (t, rightJarMap i yr)).val
  have he : leftJarMap i yl = rightJarMap i yr := Subtype.ext (middle_agreement i y)
  rw [he]

def pastedHomotopy (p q : RelGenLoop (n + 2) X A a)
    (HL : HomotopyWith (leftPair i f) p.val (Cube.IsMapOfPairs X A))
    (HR : HomotopyWith (rightPair i f) q.val (Cube.IsMapOfPairs X A))
    (hag : ∀ t y, HL (t, Function.update y i.castSucc 1) =
      HR (t, Function.update y i.castSucc 0)) :
    HomotopyWith f (RelGenLoop.transAt i p q).val (Cube.IsMapOfPairs X A) where
  toFun z := if (z.2 i.castSucc).val ≤ 1 / 2 then HL (z.1, unleft i z.2)
    else HR (z.1, unright i z.2)
  continuous_toFun := by
    refine Continuous.if_le (HL.continuous.comp ?_) (HR.continuous.comp ?_)
      (by fun_prop) continuous_const ?_
    · exact continuous_fst.prodMk ((continuous_unleft i).comp continuous_snd)
    · exact continuous_fst.prodMk ((continuous_unright i).comp continuous_snd)
    · intro z hz
      simp only [unleft, unright, RelGenLoop.firstHalf_of_half hz,
        RelGenLoop.secondHalf_of_half hz]
      exact hag z.1 z.2
  map_zero_left y := by
    change (if (y i.castSucc).val ≤ 1 / 2 then HL (0, unleft i y)
      else HR (0, unright i y)) = f y
    split_ifs with h
    · rw [HL.apply_zero]
      change f (left i (unleft i y)) = f y
      rw [left_unleft i y h]
    · rw [HR.apply_zero]
      change f (right i (unright i y)) = f y
      rw [right_unright i y (le_of_not_ge h)]
  map_one_left y := by
    change (if (y i.castSucc).val ≤ 1 / 2 then HL (1, unleft i y)
      else HR (1, unright i y)) = (RelGenLoop.transAt i p q).val y
    simp only [HL.apply_one, HR.apply_one, RelGenLoop.transAt_apply, unleft, unright]
  prop' t y hy := by
    change (if (y i.castSucc).val ≤ 1 / 2 then HL (t, unleft i y)
      else HR (t, unright i y)) ∈ A
    split_ifs with h
    · exact HL.prop' t _ (unleft_boundary i y hy h)
    · exact HR.prop' t _ (unright_boundary i y hy (lt_of_not_ge h))

variable (hπ : Subsingleton (HomotopyGroup.Pi 1 A a))

include hπ in
/-- The order reflects the fundamental-group composition convention:
the right half is multiplied by the left half. In dimensions at least
three this is an equality in an abelian relative homotopy group. -/
theorem classOf_binary_pasting :
    FreeRelativeClass.classOf a f hf =
      FreeRelativeClass.classOf a (rightPair i f) (rightPair_isMapOfPairs i f hf hm) *
        FreeRelativeClass.classOf a (leftPair i f) (leftPair_isMapOfPairs i f hf hm) := by
  obtain ⟨p, q, HL, HR, hag⟩ := exists_coherent_normalizations i f hf hm a
  have hL : FreeRelativeClass.classOf a (leftPair i f)
      (leftPair_isMapOfPairs i f hf hm) = (⟦p⟧ : π_rel (n + 2) X A a) :=
    (FreeRelativeClass.classOf_congr a hπ _ _ ⟨HL⟩).trans
      (FreeRelativeClass.classOf_relGenLoop a hπ p)
  have hR : FreeRelativeClass.classOf a (rightPair i f)
      (rightPair_isMapOfPairs i f hf hm) = (⟦q⟧ : π_rel (n + 2) X A a) :=
    (FreeRelativeClass.classOf_congr a hπ _ _ ⟨HR⟩).trans
      (FreeRelativeClass.classOf_relGenLoop a hπ q)
  rw [hL, hR]
  exact ((FreeRelativeClass.classOf_congr a hπ hf
    (RelGenLoop.transAt i p q).property.1 ⟨pastedHomotopy i f a p q HL HR hag⟩).trans
      (FreeRelativeClass.classOf_relGenLoop a hπ (RelGenLoop.transAt i p q))).trans
        (RelHomotopyGroup.mul_spec (k := i)).symm

end AkopyanResearch.CubicalPasting
