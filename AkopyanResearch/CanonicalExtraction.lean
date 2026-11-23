module

public import AkopyanResearch.CanonicalQuadratic
public import Mathlib.Topology.Instances.Real.Lemmas


@[expose] public section

/-!
# Canonical coefficients, continuity, and inactive colors

The coefficients of a quadratic label table are finite differences of its
values on words with at most two nonzero labels. This gives uniqueness,
continuity, and exact vanishing of coefficients involving an inactive color.
-/

namespace AkopyanQuadratic

open scoped BigOperators Classical

@[simp] private lemma zero_ne_fin_succ (a : Fin 5) : (0 : Fin 6) ≠ a.succ :=
  (Fin.succ_ne_zero a).symm

def zeroWord (c : ℕ) : Fin c → Fin 6 := fun _ => 0

def singleWord {c : ℕ} (i : Fin c) (a : Fin 5) : Fin c → Fin 6 :=
  Function.update (zeroWord c) i a.succ

def doubleWord {c : ℕ} (p : OrderedColorPairs c) (a b : Fin 5) : Fin c → Fin 6 :=
  Function.update (singleWord p.val.1 a) p.val.2 b.succ

def evaluateWord {c : ℕ} (w : Fin c → Fin 6) :
    (((Fin c → Fin 6) → ℝ) →ₗ[ℝ] ℝ) := LinearMap.proj w

noncomputable def canonicalCoefficient {c : ℕ} :
    QuadraticFeature c → (((Fin c → Fin 6) → ℝ) →ₗ[ℝ] ℝ)
  | .inl _ => evaluateWord (zeroWord c)
  | .inr (.inl (i, a)) =>
      evaluateWord (singleWord i a) - evaluateWord (zeroWord c)
  | .inr (.inr (p, a, b)) =>
      evaluateWord (doubleWord p a b) - evaluateWord (singleWord p.val.1 a) -
        evaluateWord (singleWord p.val.2 b) + evaluateWord (zeroWord c)

lemma canonicalCoefficient_feature {c : ℕ} (t s : QuadraticFeature c) :
    canonicalCoefficient t (canonicalFeature s) = if t = s then 1 else 0 := by
  classical
  rcases t with ⟨⟩ | ⟨i, a⟩ | ⟨⟨⟨i, j⟩, hij⟩, a, b⟩ <;>
    rcases s with ⟨⟩ | ⟨k, d⟩ | ⟨⟨⟨k, l⟩, hkl⟩, d, e⟩
  · simp [canonicalCoefficient, evaluateWord, canonicalFeature]
  · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, zeroWord]
  · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, zeroWord]
  · simp [canonicalCoefficient, evaluateWord, canonicalFeature]
  · by_cases hki : k = i
    · subst k
      by_cases had : a = d
      · subst d
        simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, singleWord, zeroWord]
      · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, singleWord, zeroWord,
          had]
    · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, singleWord, zeroWord,
        hki, Ne.symm hki]
  · have hklne : k ≠ l := ne_of_lt hkl
    by_cases hki : k = i
    · subst k
      simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, singleWord, zeroWord,
        Ne.symm hklne]
    · by_cases hli : l = i
      · subst l
        simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, singleWord, zeroWord,
          hki]
      · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, singleWord, zeroWord,
          hli]
  · simp [canonicalCoefficient, evaluateWord, canonicalFeature]
  · have hijne : i ≠ j := ne_of_lt hij
    by_cases hki : k = i
    · subst k
      simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
        zeroWord, hijne]
    · by_cases hkj : k = j
      · subst k
        simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
          zeroWord, Ne.symm hijne]
      · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
          zeroWord, hki, hkj]
  · have hijne : i ≠ j := ne_of_lt hij
    have hklne : k ≠ l := ne_of_lt hkl
    by_cases hki : k = i
    · subst k
      by_cases hlj : l = j
      · subst l
        by_cases had : a = d <;> by_cases hbe : b = e <;>
          simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
            zeroWord, hijne, Ne.symm hijne, had, hbe, Ne.symm, Prod.mk.injEq]
      · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
          zeroWord, Ne.symm hklne, hlj, Ne.symm hlj,
          Prod.mk.injEq]
    · by_cases hkj : k = j
      · subst k
        have hli : l ≠ i := ne_of_gt (lt_trans hij hkl)
        simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
          zeroWord, hijne, hklne, Ne.symm hklne, hli,
          Prod.mk.injEq]
      · simp [canonicalCoefficient, evaluateWord, canonicalFeature, labelIndicator, doubleWord, singleWord,
          zeroWord, hki, Ne.symm hki, hkj, Prod.mk.injEq]

lemma canonicalCoefficient_sum {c : ℕ} (coefficients : QuadraticFeature c → ℝ)
    (t : QuadraticFeature c) :
    canonicalCoefficient t (∑ s, coefficients s • canonicalFeature s) = coefficients t := by
  classical
  simp only [map_sum, map_smul, canonicalCoefficient_feature, smul_eq_mul]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hst
    simp [Ne.symm hst]
  · simp

theorem canonicalFeature_linearIndependent (c : ℕ) :
    LinearIndependent ℝ (canonicalFeature (c := c)) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients h t
  have he := congrArg (canonicalCoefficient t) h
  simpa only [canonicalCoefficient_sum, map_zero] using he

theorem quadratic_finrank_eq_card_features (c : ℕ) :
    Module.finrank ℝ (quadraticLabelSpace (Fin c) (Fin 6)) =
      Fintype.card (QuadraticFeature c) := by
  rw [quadraticLabelSpace_eq_canonical]
  exact finrank_span_eq_card (canonicalFeature_linearIndependent c)

theorem quadratic_finrank_fifteen :
    Module.finrank ℝ (quadraticLabelSpace (Fin 15) (Fin 6)) = 2701 := by
  rw [quadratic_finrank_eq_card_features, quadraticFeature_fifteen_card]

theorem canonical_coefficient_expansion {c : ℕ}
    (f : (Fin c → Fin 6) → ℝ) (hf : f ∈ quadraticLabelSpace (Fin c) (Fin 6)) :
    (∑ t, canonicalCoefficient t f • canonicalFeature t) = f := by
  rw [quadraticLabelSpace_eq_canonical] at hf
  obtain ⟨coefficients, hcoeff⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  have h : ∀ t, canonicalCoefficient t f = coefficients t := by
    intro t
    rw [← hcoeff]
    exact canonicalCoefficient_sum coefficients t
  simpa only [h] using hcoeff

theorem canonical_coefficients_unique {c : ℕ}
    (f : (Fin c → Fin 6) → ℝ) (coefficients : QuadraticFeature c → ℝ)
    (hcoeff : (∑ t, coefficients t • canonicalFeature t) = f) :
    ∀ t, coefficients t = canonicalCoefficient t f := by
  intro t
  rw [← hcoeff, canonicalCoefficient_sum]

def IgnoresColor {c : ℕ} (f : (Fin c → Fin 6) → ℝ) (i : Fin c) : Prop :=
  ∀ w a, f (Function.update w i a) = f w

lemma ignored_single_coefficient {c : ℕ}
    (f : (Fin c → Fin 6) → ℝ) (i : Fin c) (a : Fin 5)
    (hi : IgnoresColor f i) :
    canonicalCoefficient (.inr (.inl (i, a))) f = 0 := by
  have h := hi (zeroWord c) a.succ
  simpa [canonicalCoefficient, evaluateWord, singleWord] using sub_eq_zero.mpr h

lemma ignored_pair_first_coefficient {c : ℕ}
    (f : (Fin c → Fin 6) → ℝ) (p : OrderedColorPairs c) (a b : Fin 5)
    (hi : IgnoresColor f p.val.1) :
    canonicalCoefficient (.inr (.inr (p, a, b))) f = 0 := by
  have hne : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  have hword : doubleWord p a b = Function.update (singleWord p.val.2 b) p.val.1 a.succ := by
    funext i
    simp [doubleWord, singleWord, Function.update_comm hne]
  have h₁ := hi (zeroWord c) a.succ
  have h₂ := hi (singleWord p.val.2 b) a.succ
  simp only [canonicalCoefficient, evaluateWord, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.proj_apply]
  rw [hword, h₂]
  change f (singleWord p.val.2 b) - f (singleWord p.val.1 a) -
    f (singleWord p.val.2 b) + f (zeroWord c) = 0
  have hs : f (singleWord p.val.1 a) = f (zeroWord c) := h₁
  rw [hs]
  ring

lemma ignored_pair_second_coefficient {c : ℕ}
    (f : (Fin c → Fin 6) → ℝ) (p : OrderedColorPairs c) (a b : Fin 5)
    (hi : IgnoresColor f p.val.2) :
    canonicalCoefficient (.inr (.inr (p, a, b))) f = 0 := by
  have h₁ := hi (zeroWord c) b.succ
  have h₂ := hi (singleWord p.val.1 a) b.succ
  simp only [canonicalCoefficient, evaluateWord, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.proj_apply]
  change f (Function.update (singleWord p.val.1 a) p.val.2 b.succ) -
    f (singleWord p.val.1 a) - f (singleWord p.val.2 b) + f (zeroWord c) = 0
  rw [h₂]
  have hs : f (singleWord p.val.2 b) = f (zeroWord c) := h₁
  rw [hs]
  ring

theorem continuous_canonicalCoefficient {c : ℕ} {X : Type*} [TopologicalSpace X]
    (F : X → (Fin c → Fin 6) → ℝ) (hF : Continuous F) (t : QuadraticFeature c) :
    Continuous (fun x => canonicalCoefficient t (F x)) := by
  rcases t with ⟨⟩ | ⟨i, a⟩ | ⟨p, a, b⟩
  · simpa only [canonicalCoefficient, evaluateWord, Function.comp_def, Pi.sub_def, Pi.add_def, LinearMap.proj_apply] using
      (continuous_apply (zeroWord c)).comp hF
  · simpa only [canonicalCoefficient, evaluateWord, Function.comp_def, Pi.sub_def, Pi.add_def, LinearMap.sub_apply, LinearMap.proj_apply] using
      ((continuous_apply (singleWord i a)).comp hF).sub
        ((continuous_apply (zeroWord c)).comp hF)
  · simpa only [canonicalCoefficient, evaluateWord, Function.comp_def, Pi.sub_def, Pi.add_def, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.proj_apply] using
      ((((continuous_apply (doubleWord p a b)).comp hF).sub
        ((continuous_apply (singleWord p.val.1 a)).comp hF)).sub
        ((continuous_apply (singleWord p.val.2 b)).comp hF)).add
        ((continuous_apply (zeroWord c)).comp hF)

end AkopyanQuadratic
