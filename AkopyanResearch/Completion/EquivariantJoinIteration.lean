module

public import AkopyanResearch.Completion.EquivariantJoinStep
public import Mathlib.Logic.Function.Iterate

/-!
# Finite iteration of the explicit equivariant join construction

Starting from the explicit `ExtensionData` of `EquivariantJoinStep`, this
module constructs a continuous equivariant map on every finite iterated
quotient join `(...((X * G) * G)...) * G`.  Its restriction to the old face
is postcomposed with `phi`; on the original seed it is `phi^[n] ∘ F`.

The self-map `phi` and its ordinary nullhomotopy remain explicit inputs.
No degree-zero existence theorem, identification with a weighted colored
join, or subgroup-equivariant contraction is asserted here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AkopyanResearch.EquivariantJoinIteration

open EquivariantJoinStep

universe u v

/-- The parenthesized finite iterated topological quotient join. -/
def IteratedJoin (G X : Type u) : ℕ → Type u
  | 0 => X
  | n + 1 => Join (IteratedJoin G X n) G

variable {G X : Type u} {Y : Type v}

instance [TopologicalSpace G] [TopologicalSpace X] (n : ℕ) :
    TopologicalSpace (IteratedJoin G X n) := by
  induction n with
  | zero => exact inferInstanceAs (TopologicalSpace X)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (TopologicalSpace (Join (IteratedJoin G X n) G))

instance [Group G] [MulAction G X] (n : ℕ) :
    MulAction G (IteratedJoin G X n) := by
  induction n with
  | zero => exact inferInstanceAs (MulAction G X)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (MulAction G (Join (IteratedJoin G X n) G))

section Faces

variable [Group G] [MulAction G X]

/-- The previous join is the time-zero face of the next join. -/
def oldFace (n : ℕ) (x : IteratedJoin G X n) : IteratedJoin G X (n + 1) :=
  joinMk timeZero x (1 : G)

theorem oldFace_equivariant (n : ℕ) (a : G) (x : IteratedJoin G X n) :
    oldFace n (a • x) = a • oldFace n x := by
  change joinMk timeZero (a • x) (1 : G) = joinMk timeZero (a • x) (a * 1)
  exact joinMk_zero _ _ _

/-- The canonical inclusion of the original seed into all old faces. -/
def seedFace : (n : ℕ) → X → IteratedJoin G X n
  | 0 => id
  | n + 1 => oldFace n ∘ seedFace n

theorem seedFace_equivariant (n : ℕ) (a : G) (x : X) :
    seedFace (G := G) n (a • x) = a • seedFace (G := G) n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change oldFace n (seedFace n (a • x)) = a • oldFace n (seedFace n x)
      rw [ih, oldFace_equivariant]

variable [TopologicalSpace G] [TopologicalSpace X]

omit [MulAction G X] in
theorem continuous_oldFace (n : ℕ) : Continuous (oldFace (G := G) (X := X) n) := by
  change Continuous (fun x : IteratedJoin G X n => Quot.mk _ (timeZero, x, (1 : G)))
  exact continuous_quot_mk.comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))

omit [MulAction G X] in
theorem continuous_seedFace (n : ℕ) : Continuous (seedFace (G := G) (X := X) n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact (continuous_oldFace n).comp ih

end Faces

section Iteration

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [MulAction G Y] [ContinuousSMul G Y]

variable (d : ExtensionData G X Y)

/-- At each step the same self-map and ordinary nullhomotopy are reused. -/
def iteratedData : (n : ℕ) → ExtensionData G (IteratedJoin G X n) Y
  | 0 => d
  | n + 1 =>
      { F := step (iteratedData n)
        phi := d.phi
        h := d.h
        c := d.c
        continuous_F := continuous_step (iteratedData n)
        continuous_phi := d.continuous_phi
        continuous_h := d.continuous_h
        equivariant_F := step_equivariant (iteratedData n)
        equivariant_phi := d.equivariant_phi
        start := d.start
        finish := d.finish }

def iteratedMap (n : ℕ) : IteratedJoin G X n → Y := (iteratedData d n).F

theorem continuous_iteratedMap (n : ℕ) : Continuous (iteratedMap d n) :=
  (iteratedData d n).continuous_F

theorem iteratedMap_equivariant (n : ℕ) (a : G) (x : IteratedJoin G X n) :
    iteratedMap d n (a • x) = a • iteratedMap d n x :=
  (iteratedData d n).equivariant_F a x

@[simp] theorem iteratedData_phi (n : ℕ) : (iteratedData d n).phi = d.phi := by
  cases n <;> rfl

@[simp] theorem iteratedMap_zero (x : X) : iteratedMap d 0 x = d.F x := rfl

theorem iteratedMap_oldFace (n : ℕ) (x : IteratedJoin G X n) :
    iteratedMap d (n + 1) (oldFace n x) = d.phi (iteratedMap d n x) := by
  change step (iteratedData d n) (joinMk timeZero x (1 : G)) = _
  rw [step_zero, iteratedData_phi]
  rfl

/-- Restriction to the seed records all postcompositions exactly. -/
theorem iteratedMap_seedFace (n : ℕ) (x : X) :
    iteratedMap d n (seedFace n x) = (d.phi^[n]) (d.F x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change iteratedMap d (n + 1) (oldFace n (seedFace n x)) = _
      rw [iteratedMap_oldFace, ih, Function.iterate_succ_apply']

theorem exists_continuous_equivariant_iteratedMap (n : ℕ) :
    ∃ f : IteratedJoin G X n → Y, Continuous f ∧
      (∀ (a : G) (x : IteratedJoin G X n), f (a • x) = a • f x) ∧
      (∀ x : X, f (seedFace n x) = (d.phi^[n]) (d.F x)) :=
  ⟨iteratedMap d n, continuous_iteratedMap d n,
    iteratedMap_equivariant d n, iteratedMap_seedFace d n⟩

end Iteration

end AkopyanResearch.EquivariantJoinIteration
