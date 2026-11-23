module

public import AkopyanResearch.CanonicalExtraction
public import AkopyanResearch.FiniteRegularization
public import AkopyanResearch.QuadraticRealization
public import Mathlib.Analysis.Normed.Module.FiniteDimension


@[expose] public section

/-!
# From a safe compatible quadratic table to a factored certificate

Every safety and compatibility hypothesis is explicit. This file does not
construct the safe table; it carries out the analytic conversion once supplied.
-/

noncomputable section

namespace AkopyanResearch

open scoped BigOperators Classical
open AkopyanQuadratic

abbrev PlanarFeatures := Fin 2 × QuadraticFeature 15
abbrev TableWords := Fin 15 → Fin 6
abbrev MatchingColumns := Fin 15 → Equiv.Perm (Fin 6)

instance compactSpaceMassSimplex : CompactSpace MassSimplex := by
  apply isCompact_iff_compactSpace.mp
  have hzero : IsClosed (⋂ i : Fin 15, {x : Fin 15 → ℝ | 0 ≤ x i}) :=
    isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have hsum : IsClosed {x : Fin 15 → ℝ | ∑ i, x i = 1} :=
    isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
  have heq : coordinateSimplex (Fin 15) =
      (⋂ i : Fin 15, {x : Fin 15 → ℝ | 0 ≤ x i}) ∩ {x : Fin 15 → ℝ | ∑ i, x i = 1} := by
    ext x
    simp only [coordinateSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  have hclosed : IsClosed (coordinateSimplex (Fin 15)) := heq.symm ▸ hzero.inter hsum
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin 15 → ℝ)) (b := 1)) hclosed
  intro x hx
  constructor
  · exact hx.1
  · intro i
    have h := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
    simpa only [hx.2, Pi.one_apply] using h

def coefficientEvaluation (v : PlanarFeatures → ℝ) (w : TableWords) (t : Fin 2) : ℝ :=
  ∑ f : QuadraticFeature 15, v (t, f) * canonicalFeature f w

def featureMass (z : MassSimplex) : QuadraticFeature 15 → ℝ
  | .inl _ => 1
  | .inr (.inl (i, _)) => z.val i
  | .inr (.inr (p, _, _)) => z.val p.val.1 * z.val p.val.2

def normalEvaluation (σ : MatchingColumns) :
    (PlanarFeatures → ℝ) →ₗ[ℝ] (Fin 6 × Fin 2 → ℝ) where
  toFun v := fun jt => coefficientEvaluation v (fun i => σ i jt.1) jt.2 -
    coefficientEvaluation v (fun i => σ i 0) jt.2
  map_add' v u := by
    ext jt
    simp only [coefficientEvaluation, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r v := by
    ext jt
    simp only [coefficientEvaluation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      ← Finset.mul_sum]
    ring

def normalEvaluationCLM (σ : MatchingColumns) :
    (PlanarFeatures → ℝ) →L[ℝ] (Fin 6 × Fin 2 → ℝ) :=
  (normalEvaluation σ).toContinuousLinearMap

def extractedCoefficients (H : MassSimplex → TableWords → Fin 2 → ℝ)
    (z : MassSimplex) (tf : PlanarFeatures) : ℝ :=
  canonicalCoefficient tf.2 (fun w => H z w tf.1)

lemma extractedCoefficients_reconstruct
    (H : MassSimplex → TableWords → Fin 2 → ℝ)
    (hq : ∀ z t, (fun w => H z w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6))
    (z : MassSimplex) (w : TableWords) (t : Fin 2) :
    coefficientEvaluation (extractedCoefficients H z) w t = H z w t := by
  have h := congrFun (canonical_coefficient_expansion (fun w => H z w t) (hq z t)) w
  simpa only [coefficientEvaluation, extractedCoefficients, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using h

/-- A compatible safe quadratic table admits continuous factored coefficients
which are still safe on every six-matching. -/
theorem exists_safe_factored_quadratic_coefficients
    (H : MassSimplex → TableWords → Fin 2 → ℝ) (hH : Continuous H)
    (hq : ∀ z t, (fun w => H z w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6))
    (hcompat : ∀ z i, z.val i = 0 → ∀ t,
      IgnoresColor (fun w => H z w t) i)
    (hsafe : ∀ z : MassSimplex, ∀ σ : MatchingColumns,
      ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) :
    ∃ b : PlanarFeatures → MassSimplex → ℝ,
      (∀ tf, Continuous (b tf)) ∧
      ∀ z : MassSimplex, ∀ σ : MatchingColumns,
        ∃ j, coefficientEvaluation (fun tf => featureMass z tf.2 * b tf z)
            (fun i => σ i j) ≠
          coefficientEvaluation (fun tf => featureMass z tf.2 * b tf z)
            (fun i => σ i 0) := by
  have hcoord (t : Fin 2) : Continuous (fun z w => H z w t) := by
    apply continuous_pi
    intro w
    exact (continuous_apply t).comp ((continuous_apply w).comp hH)
  have ha : Continuous (extractedCoefficients H) := by
    apply continuous_pi
    intro tf
    exact continuous_canonicalCoefficient (fun z w => H z w tf.1) (hcoord tf.1) tf.2
  have hp (tf : PlanarFeatures) : Continuous (fun z : MassSimplex => featureMass z tf.2) := by
    rcases tf with ⟨t, ⟨⟩ | ⟨i, a⟩ | ⟨p, a, b⟩⟩
    · exact continuous_const
    · exact (continuous_apply i).comp continuous_subtype_val
    · exact ((continuous_apply p.val.1).comp continuous_subtype_val).mul
        ((continuous_apply p.val.2).comp continuous_subtype_val)
  have hp0 (tf : PlanarFeatures) (z : MassSimplex) : 0 ≤ featureMass z tf.2 := by
    rcases tf with ⟨t, ⟨⟩ | ⟨i, a⟩ | ⟨p, a, b⟩⟩
    · exact zero_le_one
    · exact z.property.1 i
    · exact mul_nonneg (z.property.1 p.val.1) (z.property.1 p.val.2)
  have hvanish (tf : PlanarFeatures) (z : MassSimplex)
      (hz : featureMass z tf.2 = 0) : extractedCoefficients H z tf = 0 := by
    rcases tf with ⟨t, ⟨⟩ | ⟨i, a⟩ | ⟨p, a, b⟩⟩
    · exact False.elim (one_ne_zero hz)
    · exact ignored_single_coefficient (fun w => H z w t) i a (hcompat z i hz t)
    · rcases mul_eq_zero.mp hz with hi | hj
      · exact ignored_pair_first_coefficient (fun w => H z w t) p a b
          (hcompat z p.val.1 hi t)
      · exact ignored_pair_second_coefficient (fun w => H z w t) p a b
          (hcompat z p.val.2 hj t)
  have htest (σ : MatchingColumns) (z : MassSimplex) :
      normalEvaluationCLM σ (extractedCoefficients H z) ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ := hsafe z σ
    apply hj
    funext t
    have h := congrFun hz (j, t)
    change coefficientEvaluation (extractedCoefficients H z) (fun i => σ i j) t -
      coefficientEvaluation (extractedCoefficients H z) (fun i => σ i 0) t = 0 at h
    rw [extractedCoefficients_reconstruct H hq, extractedCoefficients_reconstruct H hq] at h
    exact sub_eq_zero.mp h
  obtain ⟨b, hb, htestb⟩ := exists_safe_finite_factored_coefficients
    (fun tf z => featureMass z tf.2) (extractedCoefficients H) hp ha hp0 hvanish
    normalEvaluationCLM htest
  refine ⟨b, hb, ?_⟩
  intro z σ
  by_contra h
  push Not at h
  apply htestb σ z
  ext jt
  change coefficientEvaluation (fun tf => featureMass z tf.2 * b tf z)
      (fun i => σ i jt.1) jt.2 -
    coefficientEvaluation (fun tf => featureMass z tf.2 * b tf z)
      (fun i => σ i 0) jt.2 = 0
  exact sub_eq_zero.mpr (congrFun (h jt.1) jt.2)

end AkopyanResearch
