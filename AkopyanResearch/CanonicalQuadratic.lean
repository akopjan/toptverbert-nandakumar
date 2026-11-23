module

public import AkopyanResearch.QuadraticInterpolation
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


@[expose] public section

/-!
# A small canonical coordinate system for quadratic label tables

Only the five nonzero labels are needed. In fifteen colors there are 2701
scalar coordinates, hence 5402 coordinates for two real heights.
-/

namespace AkopyanQuadratic

open scoped BigOperators Classical

abbrev OrderedColorPairs (c : ℕ) := {p : Fin c × Fin c // p.1 < p.2}

abbrev QuadraticFeature (c : ℕ) :=
  Unit ⊕ ((Fin c × Fin 5) ⊕ (OrderedColorPairs c × Fin 5 × Fin 5))

noncomputable def canonicalFeature {c : ℕ} :
    QuadraticFeature c → ((Fin c → Fin 6) → ℝ)
  | .inl _ => fun _ => 1
  | .inr (.inl (i, a)) => labelIndicator i a.succ
  | .inr (.inr (p, a, b)) =>
      fun w => labelIndicator p.val.1 a.succ w * labelIndicator p.val.2 b.succ w

noncomputable def canonicalQuadraticSpace (c : ℕ) :
    Submodule ℝ ((Fin c → Fin 6) → ℝ) :=
  Submodule.span ℝ (Set.range (canonicalFeature (c := c)))

noncomputable def nonzeroAffineSpace (c : ℕ) :
    Submodule ℝ ((Fin c → Fin 6) → ℝ) :=
  Submodule.span ℝ
    ({fun _ => (1 : ℝ)} ∪
      Set.range (fun p : Fin c × Fin 5 => labelIndicator p.1 p.2.succ))

lemma one_mem_nonzeroAffine (c : ℕ) :
    (fun _ : Fin c → Fin 6 => (1 : ℝ)) ∈ nonzeroAffineSpace c :=
  Submodule.subset_span (Or.inl rfl)

lemma nonzero_indicator_mem_nonzeroAffine {c : ℕ} (i : Fin c) (a : Fin 5) :
    labelIndicator i a.succ ∈ nonzeroAffineSpace c :=
  Submodule.subset_span (Or.inr ⟨(i, a), rfl⟩)

lemma zero_indicator_eq {c : ℕ} (i : Fin c) :
    labelIndicator i (0 : Fin 6) =
      (fun _ => (1 : ℝ)) - ∑ a : Fin 5, labelIndicator i a.succ := by
  funext w
  have h : (∑ a : Fin 6, labelIndicator i a w) = 1 := by
    rw [Finset.sum_eq_single (w i)]
    · simp [labelIndicator]
    · intro a _ ha
      simp [labelIndicator, Ne.symm ha]
    · simp
  rw [Fin.sum_univ_succ] at h
  simp only [Pi.sub_apply, Finset.sum_apply]
  linarith

lemma indicator_mem_nonzeroAffine {c : ℕ} (i : Fin c) (a : Fin 6) :
    labelIndicator i a ∈ nonzeroAffineSpace c := by
  obtain rfl | ⟨a, rfl⟩ := a.eq_zero_or_eq_succ
  · rw [zero_indicator_eq]
    exact (nonzeroAffineSpace c).sub_mem (one_mem_nonzeroAffine c)
      ((nonzeroAffineSpace c).sum_mem (fun a _ =>
        nonzero_indicator_mem_nonzeroAffine i a))
  · exact nonzero_indicator_mem_nonzeroAffine i a

lemma one_mem_canonical (c : ℕ) :
    (fun _ : Fin c → Fin 6 => (1 : ℝ)) ∈ canonicalQuadraticSpace c :=
  Submodule.subset_span ⟨.inl (), rfl⟩

lemma nonzero_indicator_mem_canonical {c : ℕ} (i : Fin c) (a : Fin 5) :
    labelIndicator i a.succ ∈ canonicalQuadraticSpace c :=
  Submodule.subset_span ⟨.inr (.inl (i, a)), rfl⟩

lemma nonzeroAffine_le_canonical (c : ℕ) :
    nonzeroAffineSpace c ≤ canonicalQuadraticSpace c := by
  apply Submodule.span_le.mpr
  rintro f (h | ⟨⟨i, a⟩, rfl⟩)
  · rcases h with rfl
    exact one_mem_canonical c
  · exact nonzero_indicator_mem_canonical i a

lemma nonzero_indicator_mul_mem_canonical {c : ℕ}
    (i j : Fin c) (a b : Fin 5) :
    (fun w => labelIndicator i a.succ w * labelIndicator j b.succ w) ∈
      canonicalQuadraticSpace c := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact Submodule.subset_span ⟨.inr (.inr (⟨(i, j), hij⟩, a, b)), rfl⟩
  · by_cases hab : a = b
    · subst b
      have heq : (fun w => labelIndicator i a.succ w * labelIndicator i a.succ w) =
          labelIndicator i a.succ := by
        funext w
        simp [labelIndicator]
      rw [heq]
      exact nonzero_indicator_mem_canonical i a
    · have heq : (fun w => labelIndicator i a.succ w * labelIndicator i b.succ w) = 0 := by
        funext w
        have hab' : a.succ ≠ b.succ := fun h => hab (Fin.succ_inj.mp h)
        simp only [labelIndicator, Pi.zero_apply]
        split_ifs with ha hb hb
        · exact (hab' (ha.symm.trans hb)).elim
        all_goals simp
      rw [heq]
      exact (canonicalQuadraticSpace c).zero_mem
  · have hmem : (fun w => labelIndicator j b.succ w * labelIndicator i a.succ w) ∈
        canonicalQuadraticSpace c :=
      Submodule.subset_span ⟨.inr (.inr (⟨(j, i), hji⟩, b, a)), rfl⟩
    simpa only [mul_comm] using hmem

lemma nonzeroAffine_mul_mem_canonical {c : ℕ}
    {f g : (Fin c → Fin 6) → ℝ}
    (hf : f ∈ nonzeroAffineSpace c) (hg : g ∈ nonzeroAffineSpace c) :
    f * g ∈ canonicalQuadraticSpace c := by
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
      rcases hf with hf | ⟨⟨i, a⟩, rfl⟩
      · rcases hf with rfl
        change (1 : (Fin c → Fin 6) → ℝ) * g ∈ canonicalQuadraticSpace c
        simpa using nonzeroAffine_le_canonical c (Submodule.subset_span hg)
      · rcases hg with hg | ⟨⟨j, b⟩, rfl⟩
        · rcases hg with rfl
          change labelIndicator i a.succ * (1 : (Fin c → Fin 6) → ℝ) ∈
            canonicalQuadraticSpace c
          simpa using nonzero_indicator_mem_canonical i a
        · exact nonzero_indicator_mul_mem_canonical i j a b
  | zero_left g hg => simp
  | zero_right f hf => simp
  | add_left f g h hf hg hh h₁ h₂ =>
      simpa only [add_mul] using (canonicalQuadraticSpace c).add_mem h₁ h₂
  | add_right f g h hf hg hh h₁ h₂ =>
      simpa only [mul_add] using (canonicalQuadraticSpace c).add_mem h₁ h₂
  | smul_left r f g hf hg h =>
      simpa only [smul_mul_assoc] using (canonicalQuadraticSpace c).smul_mem r h
  | smul_right r f g hf hg h =>
      simpa only [mul_smul_comm] using (canonicalQuadraticSpace c).smul_mem r h

theorem quadraticLabelSpace_eq_canonical (c : ℕ) :
    quadraticLabelSpace (Fin c) (Fin 6) = canonicalQuadraticSpace c := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ((hf | ⟨⟨i, a⟩, rfl⟩) | ⟨⟨⟨i, a⟩, ⟨j, b⟩⟩, rfl⟩)
    · rcases hf with rfl
      exact one_mem_canonical c
    · exact nonzeroAffine_le_canonical c (indicator_mem_nonzeroAffine i a)
    · exact nonzeroAffine_mul_mem_canonical
        (indicator_mem_nonzeroAffine i a) (indicator_mem_nonzeroAffine j b)
  · apply Submodule.span_le.mpr
    rintro f ⟨t, rfl⟩
    rcases t with ⟨⟩ | ⟨i, a⟩ | ⟨p, a, b⟩
    · exact Submodule.subset_span (Or.inl (Or.inl rfl))
    · exact indicator_mem_quadratic i a.succ
    · exact indicator_mul_mem_quadratic p.val.1 p.val.2 a.succ b.succ

theorem quadratic_finrank_le_card_features (c : ℕ) :
    Module.finrank ℝ (quadraticLabelSpace (Fin c) (Fin 6)) ≤
      Fintype.card (QuadraticFeature c) := by
  rw [quadraticLabelSpace_eq_canonical]
  exact finrank_range_le_card (canonicalFeature (c := c))

lemma orderedColorPairs_fifteen_card : Fintype.card (OrderedColorPairs 15) = 105 := by
  decide

lemma quadraticFeature_fifteen_card : Fintype.card (QuadraticFeature 15) = 2701 := by
  simp [QuadraticFeature, Fintype.card_sum, Fintype.card_prod, orderedColorPairs_fifteen_card]

theorem planar_coefficient_finrank_fifteen :
    Module.finrank ℝ ((Fin 2 × QuadraticFeature 15) → ℝ) = 5402 := by
  rw [Module.finrank_pi, Fintype.card_prod, quadraticFeature_fifteen_card]
  norm_num

theorem quadratic_finrank_fifteen_le :
    Module.finrank ℝ (quadraticLabelSpace (Fin 15) (Fin 6)) ≤ 2701 := by
  simpa only [quadraticFeature_fifteen_card] using quadratic_finrank_le_card_features 15

/-- The interpolation statement with an explicit, small coefficient type. -/
theorem canonical_quadratic_interpolation {c : ℕ}
    (s : Finset (Fin c → Fin 6)) (i₀ : Fin c)
    (hc : ∀ a, (s.filter (fun w => w i₀ = a)).card ≤ 3)
    (values : {w // w ∈ s} → ℝ) :
    ∃ coefficients : QuadraticFeature c → ℝ,
      ∀ u : {w // w ∈ s},
        ∑ t, coefficients t * canonicalFeature t u.val = values u := by
  classical
  obtain ⟨f, hf, hvals⟩ := quadratic_interpolation s i₀
    (fun a => by convert hc a using 1; congr) values
  rw [quadraticLabelSpace_eq_canonical] at hf
  obtain ⟨coefficients, hcoeff⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  refine ⟨coefficients, ?_⟩
  intro u
  have h := (congrFun hcoeff u.val).trans (hvals u)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

theorem canonical_planar_interpolation {c : ℕ}
    (s : Finset (Fin c → Fin 6)) (i₀ : Fin c)
    (hc : ∀ a, (s.filter (fun w => w i₀ = a)).card ≤ 3)
    (values : {w // w ∈ s} → Fin 2 → ℝ) :
    ∃ coefficients : (Fin 2 × QuadraticFeature c) → ℝ,
      ∀ u : {w // w ∈ s}, ∀ k : Fin 2,
        ∑ t, coefficients (k, t) * canonicalFeature t u.val = values u k := by
  have h : ∀ k : Fin 2, ∃ coefficients : QuadraticFeature c → ℝ,
      ∀ u : {w // w ∈ s},
        ∑ t, coefficients t * canonicalFeature t u.val = values u k := by
    intro k
    exact canonical_quadratic_interpolation s i₀ hc (fun u => values u k)
  choose coefficients hcoefficients using h
  exact ⟨fun p => coefficients p.1 p.2, fun u k => hcoefficients k u⟩

end AkopyanQuadratic
