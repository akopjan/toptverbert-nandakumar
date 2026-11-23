module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic


@[expose] public section

/-!
Elementary finite-cap facts: centered subset vectors are distinct after any
positive normalization, covariance under permutations, and the fact that a
fixed point can only belong to a cap with fixed index when caps are disjoint.
No global sphere map or degree theorem is asserted here.
-/

open Set

namespace InvariantCaps

noncomputable section

def contrast (A : Finset (Fin 6)) (i : Fin 6) : ℝ :=
  (if i ∈ A then 1 else 0) - (A.card : ℝ) / 6

lemma contrast_pos_iff (A : Finset (Fin 6)) (hA : A.card < 6) (i : Fin 6) :
    0 < contrast A i ↔ i ∈ A := by
  have hcard : (A.card : ℝ) < 6 := by exact_mod_cast hA
  have hcard0 : 0 ≤ (A.card : ℝ) := by positivity
  by_cases hi : i ∈ A
  · simp [contrast, hi]
    linarith
  · simp [contrast, hi]
    linarith

lemma contrast_map (e : Equiv.Perm (Fin 6)) (A : Finset (Fin 6)) (i : Fin 6) :
    contrast (A.map e.toEmbedding) (e i) = contrast A i := by
  simp [contrast]

def CapLabel := {A : Finset (Fin 6) // 1 ≤ A.card ∧ A.card ≤ 3}

def normalizedContrast (r : CapLabel → ℝ) (A : CapLabel) (i : Fin 6) : ℝ :=
  r A * contrast A.val i

lemma normalizedContrast_injective (r : CapLabel → ℝ) (hr : ∀ A, 0 < r A) :
    Function.Injective (normalizedContrast r) := by
  intro A B h
  apply Subtype.ext
  apply Finset.ext
  intro i
  have hA : A.val.card < 6 := by
    have h := A.property.2
    omega
  have hB : B.val.card < 6 := by
    have h := B.property.2
    omega
  have hh := congrFun h i
  have hpos : 0 < normalizedContrast r A i ↔ 0 < normalizedContrast r B i := by rw [hh]
  simpa only [normalizedContrast, mul_pos_iff_of_pos_left (hr A),
    mul_pos_iff_of_pos_left (hr B), contrast_pos_iff A.val hA i,
    contrast_pos_iff B.val hB i] using hpos

lemma fixed_index_of_fixed_point {G I X : Type*} [Group G]
    [MulAction G I] [MulAction G X] (caps : I → Set X)
    (hdisj : Pairwise (fun i j => Disjoint (caps i) (caps j)))
    (hcov : ∀ (g : G) (i : I) (x : X), x ∈ caps i → g • x ∈ caps (g • i))
    {x : X} (hfixed : ∀ g : G, g • x = x) {i : I} (hxi : x ∈ caps i) :
    ∀ g : G, g • i = i := by
  intro g
  by_contra hgi
  have hxg : x ∈ caps (g • i) := by simpa [hfixed g] using hcov g i x hxi
  exact Set.disjoint_left.mp (hdisj hgi) hxg hxi

end
end InvariantCaps
