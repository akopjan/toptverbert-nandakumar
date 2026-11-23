module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
# Factoring boundary-vanishing continuous coefficients

The first lemma is the analytic reason that a compatible coefficient can be
replaced, arbitrarily closely, by a coefficient carrying its mass factors.
It does not construct a safe table. The final lemma records the elementary
compactness argument which makes a known nonvanishing certificate robust.
-/

noncomputable section

namespace AkopyanResearch

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Near the zero set of a nonnegative continuous function, every continuous
function vanishing on that zero set is uniformly small. -/
theorem small_of_small_nonnegative
    (p a : X → ℝ) (hp : Continuous p) (ha : Continuous a)
    (hp0 : ∀ x, 0 ≤ p x) (hvanish : ∀ x, p x = 0 → a x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, p x < δ → |a x| < ε := by
  let K : Set X := {x | ε ≤ |a x|}
  have hK : IsCompact K := (isClosed_le continuous_const ha.abs).isCompact
  have hpK : ∀ x ∈ K, 0 < p x := by
    intro x hx
    have hn : p x ≠ 0 := by
      intro hz
      have ha0 := hvanish x hz
      have he : ε ≤ |a x| := hx
      simp only [ha0, abs_zero] at he
      exact (not_le_of_gt hε) he
    exact lt_of_le_of_ne (hp0 x) (Ne.symm hn)
  obtain ⟨δ, hδ, hbound⟩ := hK.exists_forall_le' hp.continuousOn hpK
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_contra h
  exact (not_le_of_gt hx) (hbound x (le_of_not_gt h))

/-- A boundary-vanishing coefficient is uniformly approximable by `p * b`,
with `b` continuous. No division by a possibly zero mass is used. -/
theorem exists_continuous_factored_approximation
    (p a : X → ℝ) (hp : Continuous p) (ha : Continuous a)
    (hp0 : ∀ x, 0 ≤ p x) (hvanish : ∀ x, p x = 0 → a x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : X → ℝ, Continuous b ∧ ∀ x, |p x * b x - a x| < ε := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    small_of_small_nonnegative p a hp ha hp0 hvanish ε hε
  let b : X → ℝ := fun x => a x / max δ (p x)
  have hden (x : X) : max δ (p x) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _))
  refine ⟨b, ha.div (continuous_const.max hp) hden, ?_⟩
  intro x
  by_cases hx : δ ≤ p x
  · have hpne : p x ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hx)
    have heq : p x * b x = a x := by
      dsimp [b]
      rw [max_eq_right hx, mul_div_cancel₀ _ hpne]
    simpa only [heq, sub_self, abs_zero] using hε
  · have hxlt : p x < δ := lt_of_not_ge hx
    have hratio0 : 0 ≤ p x / δ := div_nonneg (hp0 x) hδ.le
    have hratio1 : p x / δ ≤ 1 := (div_le_one hδ).2 hxlt.le
    have hfactor : |p x / δ - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |p x * b x - a x| = |p x / δ - 1| * |a x| := by
        dsimp [b]
        rw [max_eq_left hxlt.le]
        rw [show p x * (a x / δ) - a x = (p x / δ - 1) * a x by ring]
        exact abs_mul _ _
      _ ≤ 1 * |a x| := mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
      _ = |a x| := one_mul _
      _ < ε := hsmall x hxlt

/-- Uniform perturbations preserve a known nonzero continuous certificate on
a compact space. This is the only robustness input needed for regularization. -/
theorem uniform_nonzero_stability
    {E : Type*} [NormedAddCommGroup E]
    (f : X → E) (hf : Continuous f) (hzero : ∀ x, f x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : X → E, (∀ x, dist (g x) (f x) < δ) → ∀ x, g x ≠ 0 := by
  obtain ⟨δ, hδ, hbound⟩ := isCompact_univ.exists_forall_le'
    hf.norm.continuousOn (fun x _ => norm_pos_iff.mpr (hzero x))
  refine ⟨δ, hδ, ?_⟩
  intro g hg x hx
  have hh := hg x
  rw [hx, dist_zero_left] at hh
  exact (not_le_of_gt hh) (hbound x (Set.mem_univ x))

end AkopyanResearch
