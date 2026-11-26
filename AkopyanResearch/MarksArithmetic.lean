module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum


@[expose] public section

/-!
Finite arithmetic for the planar orbit-bubble map.

`a`, `b`, `c` count orbits of sizes 1, 2, 4 in a six-element set.
The two powerset counts used below are explicit hypotheses of the geometric
application, not claims about arbitrary group actions proved in this file.

The preferred geometric route only uses `seventh_power_bubbleDegree`.
It does not postulate an equivariant Hopf theorem or any topological
realization theorem.
-/

open scoped BigOperators

namespace PlanarMarksArithmetic

def bubbleDegree (a b : ℕ) : ℤ :=
  1 - (a : ℤ) - ((a.choose 2 : ℤ) + (b : ℤ)) +
    ((a.choose 3 : ℤ) + (a : ℤ) * (b : ℤ))

lemma orbit_types_of_card_six {a b c : ℕ} (h : a + 2 * b + 4 * c = 6) :
    (a = 6 ∧ b = 0 ∧ c = 0) ∨
    (a = 4 ∧ b = 1 ∧ c = 0) ∨
    (a = 2 ∧ b = 2 ∧ c = 0) ∨
    (a = 0 ∧ b = 3 ∧ c = 0) ∨
    (a = 2 ∧ b = 0 ∧ c = 1) ∨
    (a = 0 ∧ b = 1 ∧ c = 1) := by
  omega

lemma bubbleDegree_eq_zero_or_neg_two {a b c : ℕ}
    (h : a + 2 * b + 4 * c = 6) :
    bubbleDegree a b = 0 ∨ bubbleDegree a b = -2 := by
  rcases orbit_types_of_card_six h with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    norm_num [bubbleDegree, Nat.choose]

/-- Seven iterates have the same fixed degree as 64 positive copies of the
original map. This avoids subgroup-lattice inversion in the preferred route. -/
lemma seventh_power_of_zero_or_neg_two {d : ℤ} (hd : d = 0 ∨ d = -2) :
    d ^ 7 = 64 * d := by
  rcases hd with rfl | rfl <;> norm_num

lemma seventh_power_bubbleDegree {a b c : ℕ}
    (h : a + 2 * b + 4 * c = 6) :
    bubbleDegree a b ^ 7 = 64 * bubbleDegree a b :=
  seventh_power_of_zero_or_neg_two (bubbleDegree_eq_zero_or_neg_two h)


end PlanarMarksArithmetic
