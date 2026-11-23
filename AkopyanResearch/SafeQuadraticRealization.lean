module

public import AkopyanResearch.SafeQuadraticBridge

@[expose] public section

/-!
# The conditional bridge to the requested ambient map

A continuous, boundary-compatible, safe quadratic label table is the sole
existence hypothesis. The resulting map is defined on the entire ambient
space `(Fin 90 → ℝ)` and is continuous there.
-/

noncomputable section

namespace AkopyanResearch

open scoped BigOperators Classical
open AkopyanQuadratic

abbrev FactoredCoefficients := PlanarFeatures → MassSimplex → ℝ

def linearCertificateFromFeatures (b : FactoredCoefficients) : SimplexLinearCoefficients :=
  fun z i a t => ∑ u : Fin 5, if a = u.succ then b (t, .inr (.inl (i, u))) z else 0

def pairCertificateFromFeatures (b : FactoredCoefficients) : SimplexPairCoefficients :=
  fun z i j a d t => ∑ p : OrderedColorPairs 15,
    if (i, j) = p.val then
      ∑ u : Fin 5, ∑ v : Fin 5,
        if a = u.succ then if d = v.succ then b (t, .inr (.inr (p, u, v))) z else 0 else 0
    else 0

lemma coefficientEvaluation_expanded (v : PlanarFeatures → ℝ) (w : TableWords) (t : Fin 2) :
    coefficientEvaluation v w t = v (t, .inl ()) +
      ((∑ i : Fin 15, ∑ a : Fin 5,
        v (t, .inr (.inl (i, a))) * labelIndicator i a.succ w) +
      ∑ p : OrderedColorPairs 15, ∑ a : Fin 5, ∑ b : Fin 5,
        v (t, .inr (.inr (p, a, b))) *
          (labelIndicator p.val.1 a.succ w * labelIndicator p.val.2 b.succ w)) := by
  simp [coefficientEvaluation, Fintype.sum_sum_type, Fintype.sum_prod_type,
    canonicalFeature]

lemma pairCertificateFromFeatures_evaluation
    (b : FactoredCoefficients) (z : MassSimplex) (w : TableWords) (t : Fin 2) :
    (∑ ij : Fin 15 × Fin 15, z.val ij.1 * z.val ij.2 *
      pairCertificateFromFeatures b z ij.1 ij.2 (w ij.1) (w ij.2) t) =
      ∑ p : OrderedColorPairs 15, ∑ a : Fin 5, ∑ d : Fin 5,
        (z.val p.val.1 * z.val p.val.2 * b (t, .inr (.inr (p, a, d))) z) *
          (labelIndicator p.val.1 a.succ w * labelIndicator p.val.2 d.succ w) := by
  simp only [pairCertificateFromFeatures, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [labelIndicator, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  by_cases ha : w p.val.1 = a.succ <;> by_cases hd : w p.val.2 = d.succ <;> simp [ha, hd]

lemma certificateFromFeatures_evaluation
    (b : FactoredCoefficients) (z : MassSimplex) (w : TableWords) (t : Fin 2) :
    simplexCertificateTable Finset.univ (linearCertificateFromFeatures b)
      (pairCertificateFromFeatures b) z w t =
    coefficientEvaluation (fun tf => featureMass z tf.2 * b tf z) w t - b (t, .inl ()) z := by
  rw [coefficientEvaluation_expanded]
  simp only [featureMass, one_mul, simplexCertificateTable]
  rw [pairCertificateFromFeatures_evaluation]
  simp only [linearCertificateFromFeatures, Finset.mul_sum, labelIndicator,
    mul_ite, mul_one, mul_zero]
  ring

lemma continuous_linearCertificateFromFeatures (b : FactoredCoefficients)
    (hb : ∀ tf, Continuous (b tf)) :
    ∀ i a t, Continuous (fun z => linearCertificateFromFeatures b z i a t) := by
  intro i a t
  unfold linearCertificateFromFeatures
  apply continuous_finsetSum
  intro u _
  split_ifs
  · exact hb _
  · exact continuous_const

lemma continuous_pairCertificateFromFeatures (b : FactoredCoefficients)
    (hb : ∀ tf, Continuous (b tf)) :
    ∀ i j a d t, Continuous (fun z => pairCertificateFromFeatures b z i j a d t) := by
  intro i j a d t
  unfold pairCertificateFromFeatures
  apply continuous_finsetSum
  intro p _
  split_ifs
  · apply continuous_finsetSum
    intro u _
    apply continuous_finsetSum
    intro v _
    split_ifs
    · exact hb _
    · exact continuous_const
    · exact continuous_const
  · exact continuous_const

/-- Conditional realization of the exact almost-six embedding requested by the
problem. No safe table is postulated by an axiom: `H`, safety, and compatibility
are explicit theorem arguments. -/
theorem exists_almostSix_of_safe_compatible_quadratic_table
    (H : MassSimplex → TableWords → Fin 2 → ℝ) (hH : Continuous H)
    (hq : ∀ z t, (fun w => H z w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6))
    (hcompat : ∀ z i, z.val i = 0 → ∀ t,
      IgnoresColor (fun w => H z w t) i)
    (hsafe : ∀ z : MassSimplex, ∀ σ : MatchingColumns,
      ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) :
    ∃ g : (Fin 90 → ℝ) → (Fin 16 → ℝ), Continuous g ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ j, x j ∈ coordinateSimplex (Fin 90)) → SixDisjointSupports x →
        ∃ j, g (x j) ≠ g (x 0) := by
  obtain ⟨b, hb, hsafe_b⟩ := exists_safe_factored_quadratic_coefficients H hH hq hcompat hsafe
  apply exists_almostSix_of_simplex_quadratic_certificate Finset.univ
    (linearCertificateFromFeatures b) (pairCertificateFromFeatures b)
    (continuous_linearCertificateFromFeatures b hb)
    (continuous_pairCertificateFromFeatures b hb)
  intro z σ
  obtain ⟨j, hj⟩ := hsafe_b z σ
  refine ⟨j, ?_⟩
  intro heq
  apply hj
  funext t
  have h := congrFun heq t
  simp only [certificateFromFeatures_evaluation] at h
  linarith only [h]

end AkopyanResearch
