module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# Extracting a matching from disjoint points with equal color masses

For a finite row type `R`, consider a nonnegative square matrix whose rows have
the same positive sum and whose row supports are pairwise disjoint. Each row
has exactly one nonzero entry, and these entries occupy the positions of a
permutation matrix. The same argument applies independently in every active
color of a family of simplex points.

The statement is independent of a particular simplex representation. In the
sixfold application, instantiate `R` with `Fin 6` and use the color masses as
the common row sums.
-/

set_option autoImplicit false

namespace AkopyanResearch.MatchingExtraction

universe u v

/-- Two different rows never have a nonzero entry in the same column. -/
def DisjointRows {R : Type u} {L : Type v} (x : R → L → ℝ) : Prop :=
  ∀ (r s : R), r ≠ s → ∀ l : L, x r l = 0 ∨ x s l = 0

/-- A nonnegative square matrix with disjoint supports and equal positive row sums
is a positive scalar multiple of a permutation matrix. -/
theorem exists_permutation_of_disjoint_equal_pos_mass
    {R : Type u} [Fintype R] [DecidableEq R]
    (x : R → R → ℝ) (m : ℝ)
    (hnonneg : ∀ r l : R, 0 ≤ x r l)
    (hmass : ∀ r : R, ∑ l : R, x r l = m)
    (hpositive : 0 < m) (hdisjoint : DisjointRows x) :
    ∃ σ : Equiv.Perm R, ∀ r l : R, x r l = if l = σ r then m else 0 := by
  classical
  have hpos : ∀ r : R, ∃ l : R, 0 < x r l := by
    intro r
    have hsum : 0 < ∑ l : R, x r l := by rw [hmass]; exact hpositive
    obtain ⟨l, _, hl⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun l _ => hnonneg r l)).mp hsum
    exact ⟨l, hl⟩
  choose f hf using hpos
  have hinj : Function.Injective f := by
    intro r s hrs
    by_contra hne
    rcases hdisjoint r s hne (f r) with hz | hz
    · have hp := hf r
      rw [hz] at hp
      exact (lt_irrefl 0) hp
    · have hp := hf s
      rw [← hrs, hz] at hp
      exact (lt_irrefl 0) hp
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  have hzero : ∀ r l : R, l ≠ f r → x r l = 0 := by
    intro r l hne
    obtain ⟨s, hs⟩ := hsurj l
    have hrs : r ≠ s := by
      intro hrs
      subst s
      exact hne hs.symm
    rcases hdisjoint r s hrs l with hz | hz
    · exact hz
    · have hp := hf s
      rw [hs, hz] at hp
      exact False.elim ((lt_irrefl 0) hp)
  have hvalue : ∀ r : R, x r (f r) = m := by
    intro r
    calc
      x r (f r) = ∑ l : R, x r l := by
        symm
        exact Finset.sum_eq_single (f r)
          (fun l _ hne => hzero r l hne) (by simp)
      _ = m := hmass r
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro r l
  change x r l = if l = f r then m else 0
  by_cases h : l = f r
  · simp [h, hvalue]
  · simp [h, hzero r l h]

/-- The corresponding conditional distribution is deterministic. -/
theorem exists_permutation_of_disjoint_equal_pos_mass_div
    {R : Type u} [Fintype R] [DecidableEq R]
    (x : R → R → ℝ) (m : ℝ)
    (hnonneg : ∀ r l : R, 0 ≤ x r l)
    (hmass : ∀ r : R, ∑ l : R, x r l = m)
    (hpositive : 0 < m) (hdisjoint : DisjointRows x) :
    ∃ σ : Equiv.Perm R,
      (∀ r l : R, x r l = if l = σ r then m else 0) ∧
      (∀ r l : R, x r l / m = if l = σ r then 1 else 0) := by
  obtain ⟨σ, hσ⟩ := exists_permutation_of_disjoint_equal_pos_mass
    x m hnonneg hmass hpositive hdisjoint
  refine ⟨σ, hσ, ?_⟩
  intro r l
  rw [hσ]
  split_ifs <;> simp [ne_of_gt hpositive]

/-- A nonnegative row of zero total mass vanishes entrywise. -/
theorem eq_zero_of_zero_mass
    {L : Type u} [Fintype L] [DecidableEq L]
    (x : L → ℝ) (hnonneg : ∀ l : L, 0 ≤ x l)
    (hmass : ∑ l : L, x l = 0) (l : L) : x l = 0 := by
  have hle : x l ≤ ∑ k : L, x k :=
    Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ l)
  rw [hmass] at hle
  exact le_antisymm hle (hnonneg l)

/-- For each active color, six disjoint rows with equal color masses determine a
permutation of the six labels. The statement is valid for every finite row type. -/
theorem exists_colored_matching
    {R : Type u} {C : Type v} [Fintype R] [DecidableEq R]
    (x : R → C → R → ℝ) (mass : C → ℝ)
    (hnonneg : ∀ (r : R) (c : C) (l : R), 0 ≤ x r c l)
    (hmass : ∀ (r : R) (c : C), ∑ l : R, x r c l = mass c)
    (hdisjoint : ∀ (r s : R), r ≠ s →
      ∀ (c : C) (l : R), x r c l = 0 ∨ x s c l = 0) :
    ∃ M : C → Equiv.Perm R,
      (∀ (c : C), 0 < mass c →
        ∀ (r l : R), x r c l = if l = M c r then mass c else 0) ∧
      (∀ (c : C), 0 < mass c →
        ∀ (r l : R), x r c l / mass c = if l = M c r then 1 else 0) ∧
      (∀ (c : C), mass c = 0 → ∀ (r l : R), x r c l = 0) := by
  classical
  have hactive : ∀ c : C, 0 < mass c →
      ∃ σ : Equiv.Perm R,
        (∀ r l : R, x r c l = if l = σ r then mass c else 0) ∧
        (∀ r l : R, x r c l / mass c = if l = σ r then 1 else 0) := by
    intro c hc
    exact exists_permutation_of_disjoint_equal_pos_mass_div
      (fun r l => x r c l) (mass c) (fun r l => hnonneg r c l)
      (fun r => hmass r c) hc (fun r s hrs l => hdisjoint r s hrs c l)
  let M : C → Equiv.Perm R := fun c =>
    if hc : 0 < mass c then Classical.choose (hactive c hc) else Equiv.refl R
  refine ⟨M, ?_, ?_, ?_⟩
  · intro c hc r l
    simpa [M, hc] using (Classical.choose_spec (hactive c hc)).1 r l
  · intro c hc r l
    simpa [M, hc] using (Classical.choose_spec (hactive c hc)).2 r l
  · intro c hc r l
    exact eq_zero_of_zero_mass (x r c) (hnonneg r c) (by rw [hmass, hc]) l

end AkopyanResearch.MatchingExtraction


end
