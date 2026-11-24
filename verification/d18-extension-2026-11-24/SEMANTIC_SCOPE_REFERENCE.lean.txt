module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

/-! This diagnostic imports only Mathlib. Its definitions therefore capture
Mathlib's standard real, finite-product, Euclidean, measure, and body instances
before any proof-project module is imported. -/
namespace SemanticReference

def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1}

def disjointSupports {n : ℕ} (x : Fin 6 → Fin n → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ v, x i v = 0 ∨ x j v = 0

def theoremA : Prop :=
  ∃ f : (Fin 36 → ℝ) → Fin 6 → ℝ,
    ContinuousOn f (simplex 36) ∧
    ∀ x : Fin 6 → Fin 36 → ℝ,
      (∀ i, x i ∈ simplex 36) → disjointSupports x →
      ∃ i, f (x i) ≠ f (x 0)

def euclideanTheoremA : Prop :=
  ∃ f : C(simplex 36, EuclideanSpace ℝ (Fin 6)),
    ∀ x : Fin 6 → simplex 36,
      disjointSupports (fun i => (x i).val) → ∃ i, f (x i) ≠ f (x 0)

def heightExtension : Prop :=
  ∃ H : (Fin 6 → ℝ) → (Fin 6 → Fin 6) → ℝ,
    ContinuousOn H (simplex 6) ∧
    (∀ l ∈ simplex 6, ∀ i, l i = 0 → ∀ u v : Fin 6 → Fin 6,
      (∀ j, j ≠ i → u j = v j) → H l u = H l v) ∧
    (∀ l ∈ simplex 6, ∀ m : Fin 6 → Fin 6 → Fin 6,
      (∀ p, Function.Injective (fun j => m j p)) →
      ∃ j, H l (m j) ≠ H l (m 0))

abbrev ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev body (d : ℕ) := ConvexBody (ambient d)
def unitBall (d : ℕ) : Set (ambient d) := Metric.closedBall 0 1
def sixPartition {d : ℕ} (C : Fin 6 → body d) : Prop :=
  unitBall d = (⋃ i, (C i : Set (ambient d))) ∧
  (∀ i, (interior (C i : Set (ambient d))).Nonempty) ∧
  ∀ i j, i ≠ j →
    Disjoint (interior (C i : Set (ambient d))) (interior (C j : Set (ambient d)))

def theoremB (d : ℕ) : Prop :=
  ∃ (Phi : body d → Fin (d - 1) → ℝ) (mu : Measure (ambient d)),
    Continuous Phi ∧ IsProbabilityMeasure mu ∧ mu.AbsolutelyContinuous volume ∧
    ∀ C : Fin 6 → body d, sixPartition C →
      (∀ i, mu (C i : Set (ambient d)) = mu (unitBall d) / 6) →
      ∃ i, Phi (C i) ≠ Phi (C 0)

def sixVertices (i : Fin 6) (v : Fin 36) : ℝ :=
  if v = Fin.castAdd 30 i then 1 else 0

theorem sixVertices_mem (i : Fin 6) : sixVertices i ∈ simplex 36 := by
  constructor
  · intro v
    dsimp [sixVertices]
    split_ifs <;> norm_num
  · simp [sixVertices]

theorem sixVertices_disjoint : disjointSupports sixVertices := by
  intro i j hij v
  by_cases hvi : v = Fin.castAdd 30 i
  · right
    have hvj : v ≠ Fin.castAdd 30 j := by
      intro hvj
      exact hij (Fin.ext (congrArg (fun w : Fin 36 => w.val) (hvi.symm.trans hvj)))
    simp [sixVertices, hvj]
  · left
    simp [sixVertices, hvi]

theorem matching_exists :
    ∃ m : Fin 6 → Fin 6 → Fin 6, ∀ p, Function.Injective (fun j => m j p) :=
  ⟨fun j _ => j, fun _ => Function.injective_id⟩

end SemanticReference
