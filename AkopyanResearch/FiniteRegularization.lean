module

public import AkopyanResearch.BoundaryRegularization
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Tactic.Linarith


@[expose] public section

/-!
# Simultaneous regularization of finitely many coefficients

A compact continuous family of coefficients avoiding finitely many linear
kernels can be approximated by coefficients carrying prescribed nonnegative
mass factors, while still avoiding every kernel. Safety is an explicit input.
-/

noncomputable section

namespace AkopyanResearch

open scoped BigOperators

variable {X F J E : Type*}
variable [TopologicalSpace X] [CompactSpace X]
variable [Fintype F] [Fintype J]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Simultaneously factor all coefficients without destroying any of the
finitely many nonvanishing linear tests. -/
theorem exists_safe_finite_factored_coefficients
    (p : F → X → ℝ) (a : X → F → ℝ)
    (hp : ∀ i, Continuous (p i)) (ha : Continuous a)
    (hp0 : ∀ i x, 0 ≤ p i x)
    (hvanish : ∀ i x, p i x = 0 → a x i = 0)
    (Q : J → (F → ℝ) →L[ℝ] E)
    (hsafe : ∀ j x, Q j (a x) ≠ 0) :
    ∃ b : F → X → ℝ,
      (∀ i, Continuous (b i)) ∧
      ∀ j x, Q j (fun i => p i x * b i x) ≠ 0 := by
  classical
  let : TopologicalSpace J := ⊥
  have : DiscreteTopology J := ⟨rfl⟩
  have hQ : Continuous Q := continuous_of_discreteTopology
  have htest : Continuous (fun z : X × J => Q z.2 (a z.1)) :=
    (hQ.comp continuous_snd).clm_apply (ha.comp continuous_fst)
  obtain ⟨δ, hδ, hstable⟩ := uniform_nonzero_stability
    (fun z : X × J => Q z.2 (a z.1)) htest (fun z => hsafe z.2 z.1)
  let C : ℝ := 1 + ∑ j, ‖Q j‖
  have hsum : 0 ≤ ∑ j, ‖Q j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (Q j))
  have hC : 0 < C := by dsimp [C]; linarith
  have hQbound (j : J) : ‖Q j‖ ≤ C := by
    have h := Finset.single_le_sum (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ j)
    dsimp [C]
    linarith
  let ε : ℝ := δ / C
  have hε : 0 < ε := div_pos hδ hC
  have hex (i : F) : ∃ b : X → ℝ, Continuous b ∧
      ∀ x, |p i x * b x - a x i| < ε :=
    exists_continuous_factored_approximation (p i) (fun x => a x i)
      (hp i) ((continuous_apply i).comp ha) (hp0 i) (hvanish i) ε hε
  choose b hb happ using hex
  refine ⟨b, hb, ?_⟩
  have hnorm (x : X) : ‖(fun i => p i x * b i x) - a x‖ < ε := by
    apply (pi_norm_lt_iff hε).mpr
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using happ i x
  have hclose : ∀ z : X × J,
      dist (Q z.2 (fun i => p i z.1 * b i z.1)) (Q z.2 (a z.1)) < δ := by
    intro z
    rw [dist_eq_norm, ← map_sub]
    calc
      ‖Q z.2 ((fun i => p i z.1 * b i z.1) - a z.1)‖
          ≤ ‖Q z.2‖ * ‖(fun i => p i z.1 * b i z.1) - a z.1‖ :=
        (Q z.2).le_opNorm _
      _ ≤ C * ‖(fun i => p i z.1 * b i z.1) - a z.1‖ :=
        mul_le_mul_of_nonneg_right (hQbound z.2) (norm_nonneg _)
      _ < C * ε := mul_lt_mul_of_pos_left (hnorm z.1) hC
      _ = δ := by dsimp [ε]; exact mul_div_cancel₀ δ (ne_of_gt hC)
  intro j x
  exact hstable (fun z : X × J => Q z.2 (fun i => p i z.1 * b i z.1)) hclose (x, j)

end AkopyanResearch
