module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic.Abel


@[expose] public section

/-!
# The algebra of the two-stage odd-index transfer argument

These lemmas deliberately do not postulate a topological transfer. They isolate
the exact algebraic hypotheses needed of such a transfer. In particular, the
false blanket identity `transfer ∘ restriction = 3 • id` is not assumed.
-/

namespace AkopyanResearch

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]

/-- A primary invariant of exponent 16 with a kernel of exponent 2 gives
an exponent bound of 32 for the whole group. -/
theorem exponent_thirty_two_of_two_layers (κ : A →+ C)
    (hprimary : ∀ a : A, (16 : ℕ) • κ a = 0)
    (hsecondary : ∀ a : A, κ a = 0 → (2 : ℕ) • a = 0) :
    ∀ a : A, (32 : ℕ) • a = 0 := by
  intro a
  have hk : κ ((16 : ℕ) • a) = 0 := by
    rw [map_nsmul, hprimary]
  have hz := hsecondary ((16 : ℕ) • a) hk
  simpa only [← mul_nsmul, show (2 : ℕ) * 16 = 32 from rfl] using hz

/-- The exact two-layer correction to an index-three transfer argument.

The composite `T` multiplies the primary invariant by three and acts by three
on its kernel. It need not act by three on the whole group.
-/
theorem zero_of_filtered_index_three_transfer
    (κ : A →+ C) (T : A →+ A)
    (hprimary : ∀ a : A, (16 : ℕ) • κ a = 0)
    (hsecondary : ∀ a : A, κ a = 0 → (2 : ℕ) • a = 0)
    (hTprimary : ∀ a : A, κ (T a) = (3 : ℕ) • κ a)
    (hTsecondary : ∀ a : A, κ a = 0 → T a = (3 : ℕ) • a)
    (a : A) (hTa : T a = 0) : a = 0 := by
  have h3 : (3 : ℕ) • κ a = 0 := by
    rw [← hTprimary, hTa, map_zero]
  have hk : κ a = 0 := by
    calc
      κ a = (16 : ℕ) • κ a - (5 : ℕ) • ((3 : ℕ) • κ a) := by abel
      _ = 0 := by rw [hprimary, h3, nsmul_zero, sub_zero]
  have h2a := hsecondary a hk
  have h3a : (3 : ℕ) • a = 0 := by rw [← hTsecondary a hk, hTa]
  calc
    a = (3 : ℕ) • a - (2 : ℕ) • a := by abel
    _ = 0 := by rw [h3a, h2a, sub_zero]

end AkopyanResearch
