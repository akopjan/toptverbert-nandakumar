module

public import AkopyanResearch.Completion.RelativeHomotopyBasepoint
public import Submission.Homotopy.RelGroup
public import Mathlib.Tactic.Linarith

/-!
# A coherent contraction for a divided cube

The outer jar together with a middle hyperplane is contractible. First
lower the last coordinate to zero, then contract within the bottom face.
This single contraction supplies agreeing jar homotopies on both halves.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.CubicalCut

open ContinuousMap
open scoped Topology unitInterval Topology.Homotopy

def midpoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

def blend (t x y : I) : I :=
  ⟨(1 - t.val) * x.val + t.val * y.val, by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hx0 := x.property.1
    have hx1 := x.property.2
    have hy0 := y.property.1
    have hy1 := y.property.2
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hx0) (mul_nonneg ht0 hy0)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hx1),
        mul_nonneg ht0 (sub_nonneg.mpr hy1)]⟩

@[simp] theorem blend_zero (x y : I) : blend 0 x y = x := by ext; simp [blend]
@[simp] theorem blend_one (x y : I) : blend 1 x y = y := by ext; simp [blend]
@[simp] theorem blend_self (t x : I) : blend t x x = x := by ext; dsimp [blend]; ring

@[simp] theorem blend_midpoint_zero_one : blend midpoint 0 1 = midpoint := by
  ext
  norm_num [blend, midpoint]

@[simp] theorem blend_midpoint_one_zero : blend midpoint 1 0 = midpoint := by
  ext
  norm_num [blend, midpoint]

@[fun_prop] theorem continuous_blend : Continuous (fun p : I × I × I => blend p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  fun_prop

def firstRamp (t : I) : I := Set.projIcc (0 : ℝ) 1 zero_le_one (2 * t.val)
def secondRamp (t : I) : I := Set.projIcc (0 : ℝ) 1 zero_le_one (2 * t.val - 1)

@[fun_prop] theorem continuous_firstRamp : Continuous firstRamp :=
  continuous_projIcc.comp' (by fun_prop)
@[fun_prop] theorem continuous_secondRamp : Continuous secondRamp :=
  continuous_projIcc.comp' (by fun_prop)

@[simp] theorem firstRamp_zero : firstRamp 0 = 0 := by ext; simp [firstRamp, Set.projIcc]
@[simp] theorem firstRamp_one : firstRamp 1 = 1 := by ext; norm_num [firstRamp, Set.projIcc]
@[simp] theorem secondRamp_zero : secondRamp 0 = 0 := by ext; simp [secondRamp, Set.projIcc]
@[simp] theorem secondRamp_one : secondRamp 1 = 1 := by ext; norm_num [secondRamp, Set.projIcc]

theorem secondRamp_eq_zero {t : I} (ht : t.val ≤ 1 / 2) : secondRamp t = 0 := by
  unfold secondRamp
  rw [Set.projIcc_of_le_left zero_le_one (by linarith : 2 * t.val - 1 ≤ 0)]
  rfl

theorem firstRamp_eq_one {t : I} (ht : 1 / 2 ≤ t.val) : firstRamp t = 1 := by
  unfold firstRamp
  rw [Set.projIcc_of_right_le zero_le_one (by linarith : 1 ≤ 2 * t.val)]
  rfl

variable {n : ℕ} (i : Fin (n + 1))

abbrev Box := I^Fin (n + 2)

def left (y : Box (n := n)) : Box (n := n) :=
  Function.update y i.castSucc (blend midpoint 0 (y i.castSucc))

def right (y : Box (n := n)) : Box (n := n) :=
  Function.update y i.castSucc (blend midpoint 1 (y i.castSucc))

@[fun_prop] theorem continuous_left : Continuous (left i) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i.castSucc
  · subst j
    simp only [left, Function.update_self]
    fun_prop
  · simp only [left, Function.update_of_ne hj]
    fun_prop

@[fun_prop] theorem continuous_right : Continuous (right i) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i.castSucc
  · subst j
    simp only [right, Function.update_self]
    fun_prop
  · simp only [right, Function.update_of_ne hj]
    fun_prop

def leftMap : C(Box (n := n), Box (n := n)) := ⟨left i, continuous_left i⟩
def rightMap : C(Box (n := n), Box (n := n)) := ⟨right i, continuous_right i⟩

theorem middle_agreement (y : Box (n := n)) :
    left i (Function.update y i.castSucc 1) =
      right i (Function.update y i.castSucc 0) := by
  funext j
  by_cases hj : j = i.castSucc
  · subst j
    simp only [left, right, Function.update_self]
    apply Subtype.ext
    norm_num [blend, midpoint]
  · simp only [left, right, Function.update_of_ne hj]

def middle : Set (Box (n := n)) := {y | y i.castSucc = midpoint}
def splitJar : Set (Box (n := n)) := Cube.boundaryJar (n + 2) ∪ middle i

theorem left_boundary_mem (y : Box (n := n)) (hy : y ∈ ∂I^(n + 2)) :
    left i y ∈ (∂I^(n + 2)) ∨ left i y ∈ middle i := by
  by_cases h : y i.castSucc = 0 ∨ y i.castSucc = 1
  · rcases h with h | h
    · left
      exact ⟨i.castSucc, Or.inl (by simp [left, h])⟩
    · right
      simp [middle, left, h]
  · left
    exact Cube.update_mem_boundary hy h _

theorem right_boundary_mem (y : Box (n := n)) (hy : y ∈ ∂I^(n + 2)) :
    right i y ∈ (∂I^(n + 2)) ∨ right i y ∈ middle i := by
  by_cases h : y i.castSucc = 0 ∨ y i.castSucc = 1
  · rcases h with h | h
    · right
      simp [middle, right, h]
    · left
      exact ⟨i.castSucc, Or.inr (by simp [right, h])⟩
  · left
    exact Cube.update_mem_boundary hy h _

theorem left_jar_mem (y : Cube.boundaryJar (n + 2)) : left i y.val ∈ splitJar i := by
  by_cases h : y.val i.castSucc = 0 ∨ y.val i.castSucc = 1
  · rcases h with h | h
    · left
      exact Cube.mem_boundaryJar_of_exists_eq_zero _ ⟨i.castSucc, by simp [left, h]⟩
    · right
      simp [middle, left, h]
  · left
    exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) y.property h _

theorem right_jar_mem (y : Cube.boundaryJar (n + 2)) : right i y.val ∈ splitJar i := by
  by_cases h : y.val i.castSucc = 0 ∨ y.val i.castSucc = 1
  · rcases h with h | h
    · right
      simp [middle, right, h]
    · left
      exact Cube.mem_boundaryJar_of_lt_last _
        ⟨i.castSucc, Fin.castSucc_lt_last i, Or.inr (by simp [right, h])⟩
  · left
    exact Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) y.property h _

def leftJarMap : C(Cube.boundaryJar (n + 2), splitJar i) :=
  ⟨fun y => ⟨left i y.val, left_jar_mem i y⟩, by fun_prop⟩

def rightJarMap : C(Cube.boundaryJar (n + 2), splitJar i) :=
  ⟨fun y => ⟨right i y.val, right_jar_mem i y⟩, by fun_prop⟩

def center : Box (n := n) := fun j => if j = i.castSucc then midpoint else 0

theorem center_last : center i (Fin.last (n + 1)) = 0 := by
  simp only [center, if_neg (Fin.castSucc_ne_last i).symm]

theorem center_mem : center i ∈ splitJar i := Or.inr (by simp [middle, center])

theorem jar_iff (y : Box (n := n)) :
    y ∈ Cube.boundaryJar (n + 2) ↔ y (Fin.last (n + 1)) = 0 ∨
      ∃ k : Fin (n + 1), y k.castSucc = 0 ∨ y k.castSucc = 1 := by
  rw [Cube.mem_boundaryJar_iff_splitAtLast]
  simp only [Cube.splitAtLast_fst_eq]
  constructor
  · rintro (h | ⟨k, hk⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, by simpa only [Cube.splitAtLast_snd_apply_eq] using hk⟩
  · rintro (h | ⟨k, hk⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, by simpa only [Cube.splitAtLast_snd_apply_eq] using hk⟩

def lower (t : I) (y : Box (n := n)) : Box (n := n) :=
  Function.update y (Fin.last (n + 1)) (blend (firstRamp t) (y (Fin.last (n + 1))) 0)

def contraction (t : I) (y : Box (n := n)) : Box (n := n) :=
  fun j => blend (secondRamp t) (lower t y j) (center i j)

@[fun_prop] theorem continuous_lower :
    Continuous (fun p : I × Box (n := n) => lower p.1 p.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    simp only [lower, Function.update_self]
    fun_prop
  · simp only [lower, Function.update_of_ne hj]
    fun_prop

@[fun_prop] theorem continuous_contraction :
    Continuous (fun p : I × Box (n := n) => contraction i p.1 p.2) := by
  apply continuous_pi
  intro j
  unfold contraction
  fun_prop

@[simp] theorem contraction_zero (y : Box (n := n)) : contraction i 0 y = y := by
  funext j
  simp only [contraction, lower, firstRamp_zero, secondRamp_zero, blend_zero,
    Function.update_eq_self]

@[simp] theorem contraction_one (y : Box (n := n)) : contraction i 1 y = center i := by
  funext j
  simp only [contraction, secondRamp_one, blend_one]

theorem contraction_mem (t : I) (y : splitJar i) : contraction i t y.val ∈ splitJar i := by
  by_cases ht : t.val ≤ 1 / 2
  · have hb := secondRamp_eq_zero ht
    have hc : contraction i t y.val = lower t y.val := by
      funext j
      simp only [contraction, hb, blend_zero]
    rw [hc]
    rcases y.property with hy | hy
    · left
      rcases (jar_iff y.val).mp hy with hz | ⟨k, hk⟩
      · apply (jar_iff _).mpr
        left
        simp only [lower, Function.update_self, hz, blend_self]
      · exact (jar_iff _).mpr (Or.inr ⟨k, by
          simpa only [lower, Function.update_of_ne (Fin.castSucc_ne_last k)] using hk⟩)
    · right
      simpa only [middle, Set.mem_setOf_eq, lower,
        Function.update_of_ne (Fin.castSucc_ne_last i)] using hy
  · have ha := firstRamp_eq_one (le_of_not_ge ht)
    left
    apply (jar_iff _).mpr
    left
    simp only [contraction, lower, Function.update_self, ha, blend_one, center_last, blend_self]

def splitJarContraction : Homotopy (ContinuousMap.id (splitJar i))
    (ContinuousMap.const _ ⟨center i, center_mem i⟩) where
  toFun p := ⟨contraction i p.1 p.2.val, contraction_mem i p.1 p.2⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  map_zero_left y := Subtype.ext (contraction_zero i y.val)
  map_one_left y := Subtype.ext (contraction_one i y.val)

end AkopyanResearch.CubicalCut
