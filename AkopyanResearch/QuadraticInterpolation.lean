module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic


@[expose] public section

/-!
# Quadratic interpolation on unions of at most three matchings

Words are functions `I → A`. A quadratic label table is a linear combination of
the constant function, single-label indicators, and products of two indicators.

The main theorem says that arbitrary values can be prescribed on a finite set
of words having at most three words in each fiber of one coordinate. In
particular this applies to the union of three matchings.

This file does not assert the existence of the safe table needed for the
almost-six-embedding. It proves the finite-dimensional reduction used in that
separate existence problem.
-/

namespace AkopyanQuadratic

open scoped BigOperators Classical

variable {I A : Type*}

noncomputable def labelIndicator (i : I) (a : A) : (I → A) → ℝ :=
  fun w => if w i = a then 1 else 0

noncomputable def affineLabelSpace (I A : Type*) : Submodule ℝ ((I → A) → ℝ) :=
  Submodule.span ℝ
    ({fun _ => (1 : ℝ)} ∪ Set.range (fun p : I × A => labelIndicator p.1 p.2))

noncomputable def quadraticLabelSpace (I A : Type*) : Submodule ℝ ((I → A) → ℝ) :=
  Submodule.span ℝ
    (({fun _ => (1 : ℝ)} ∪ Set.range (fun p : I × A => labelIndicator p.1 p.2)) ∪
      Set.range (fun p : (I × A) × (I × A) =>
        fun w => labelIndicator p.1.1 p.1.2 w * labelIndicator p.2.1 p.2.2 w))

lemma const_mem_affine : (fun _ : I → A => (1 : ℝ)) ∈ affineLabelSpace I A :=
  Submodule.subset_span (Or.inl rfl)

lemma indicator_mem_affine (i : I) (a : A) :
    labelIndicator i a ∈ affineLabelSpace I A :=
  Submodule.subset_span (Or.inr ⟨(i, a), rfl⟩)

lemma indicator_mem_quadratic (i : I) (a : A) :
    labelIndicator i a ∈ quadraticLabelSpace I A :=
  Submodule.subset_span (Or.inl (Or.inr ⟨(i, a), rfl⟩))

lemma indicator_mul_mem_quadratic (i j : I) (a b : A) :
    (fun w => labelIndicator i a w * labelIndicator j b w) ∈
      quadraticLabelSpace I A :=
  Submodule.subset_span (Or.inr ⟨((i, a), (j, b)), rfl⟩)

noncomputable def multiplyIndicator (i : I) (a : A) :
    ((I → A) → ℝ) →ₗ[ℝ] ((I → A) → ℝ) where
  toFun f := fun w => labelIndicator i a w * f w
  map_add' f g := by ext w; exact mul_add _ _ _
  map_smul' r f := by ext w; simp [mul_left_comm]

lemma indicator_mul_affine_mem_quadratic (i : I) (a : A)
    {f : (I → A) → ℝ} (hf : f ∈ affineLabelSpace I A) :
    (fun w => labelIndicator i a w * f w) ∈ quadraticLabelSpace I A := by
  have hle : affineLabelSpace I A ≤
      (quadraticLabelSpace I A).comap (multiplyIndicator i a) := by
    apply Submodule.span_le.mpr
    rintro g (hg | ⟨⟨j, b⟩, rfl⟩)
    · rcases hg with rfl
      simpa [Submodule.mem_comap, multiplyIndicator] using indicator_mem_quadratic i a
    · exact indicator_mul_mem_quadratic i j a b
  exact hle hf

private lemma exists_coordinate_ne {u v : I → A} (h : u ≠ v) :
    ∃ i, u i ≠ v i := by
  classical
  by_contra h'
  apply h
  funext i
  by_contra hi
  exact h' ⟨i, hi⟩

/-- At most three different words can be separated by an affine label table.
The conclusion permits repeated words among `u`, `v`, and `w`. -/
lemma exists_affine_three_separator (u v w : I → A) :
    ∃ f ∈ affineLabelSpace I A,
      f u = 1 ∧ (v ≠ u → f v = 0) ∧ (w ≠ u → f w = 0) := by
  classical
  by_cases hv : v = u
  · subst v
    by_cases hw : w = u
    · subst w
      exact ⟨_, const_mem_affine, rfl, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := exists_coordinate_ne (Ne.symm hw)
      refine ⟨labelIndicator j (u j), indicator_mem_affine j (u j), ?_, ?_, ?_⟩
      · simp [labelIndicator]
      · simp
      · intro _; simp [labelIndicator, Ne.symm hj]
  · by_cases hw : w = u
    · subst w
      obtain ⟨j, hj⟩ := exists_coordinate_ne (Ne.symm hv)
      refine ⟨labelIndicator j (u j), indicator_mem_affine j (u j), ?_, ?_, ?_⟩
      · simp [labelIndicator]
      · intro _; simp [labelIndicator, Ne.symm hj]
      · simp
    · obtain ⟨j, hjv⟩ := exists_coordinate_ne (Ne.symm hv)
      by_cases hjw : u j ≠ w j
      · refine ⟨labelIndicator j (u j), indicator_mem_affine j (u j), ?_, ?_, ?_⟩
        · simp [labelIndicator]
        · intro _; simp [labelIndicator, Ne.symm hjv]
        · intro _; simp [labelIndicator, Ne.symm hjw]
      · have hjw' : u j = w j := not_ne_iff.mp hjw
        obtain ⟨l, hlw⟩ := exists_coordinate_ne (Ne.symm hw)
        by_cases hlv : u l ≠ v l
        · refine ⟨labelIndicator l (u l), indicator_mem_affine l (u l), ?_, ?_, ?_⟩
          · simp [labelIndicator]
          · intro _; simp [labelIndicator, Ne.symm hlv]
          · intro _; simp [labelIndicator, Ne.symm hlw]
        · have hlv' : u l = v l := not_ne_iff.mp hlv
          refine ⟨labelIndicator j (u j) + labelIndicator l (u l) - (fun _ => 1),
            (affineLabelSpace I A).sub_mem
              ((affineLabelSpace I A).add_mem
                (indicator_mem_affine j (u j)) (indicator_mem_affine l (u l)))
              const_mem_affine, ?_, ?_, ?_⟩
          · simp [labelIndicator]
          · intro _; simp [labelIndicator, Ne.symm hjv, hlv']
          · intro _; simp [labelIndicator, hjw', Ne.symm hlw]

private lemma cover_by_three {W : Type*} (s : Finset W) (u : W)
    (hu : u ∈ s) (hc : s.card ≤ 3) :
    ∃ v w, ∀ z ∈ s, z = u ∨ z = v ∨ z = w := by
  classical
  have hp : 0 < s.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hn : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hn with h | h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have : u = a := Finset.mem_singleton.mp hu
    subst a
    exact ⟨u, u, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨b, b, by simp⟩
    · refine ⟨a, a, ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      aesop
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨b, c, by simp⟩
    · refine ⟨a, c, ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      aesop
    · refine ⟨a, b, ?_⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      aesop

/-- A quadratic table isolates a chosen word inside any finite set with at most
three words in its coordinate fiber. -/
lemma exists_quadratic_separator (s : Finset (I → A)) (i₀ : I) (u : I → A)
    (hu : u ∈ s) (hc : (s.filter (fun w => w i₀ = u i₀)).card ≤ 3) :
    ∃ f ∈ quadraticLabelSpace I A,
      ∀ z ∈ s, f z = if z = u then 1 else 0 := by
  classical
  have huf : u ∈ s.filter (fun w => w i₀ = u i₀) := by simp [hu]
  obtain ⟨v, w, hcover⟩ := cover_by_three _ u huf hc
  obtain ⟨q, hq, hqu, hqv, hqw⟩ := exists_affine_three_separator u v w
  refine ⟨fun z => labelIndicator i₀ (u i₀) z * q z,
    indicator_mul_affine_mem_quadratic i₀ (u i₀) hq, ?_⟩
  intro z hz
  by_cases hz₀ : z i₀ = u i₀
  · have hzf : z ∈ s.filter (fun w => w i₀ = u i₀) := by simp [hz, hz₀]
    rcases hcover z hzf with hzu | hzv | hzw
    · subst z
      simp [labelIndicator, hqu]
    · subst z
      by_cases h : v = u
      · subst v; simp [labelIndicator, hqu]
      · simp [labelIndicator, hz₀, h, hqv h]
    · subst z
      by_cases h : w = u
      · subst w; simp [labelIndicator, hqu]
      · simp [labelIndicator, hz₀, h, hqw h]
  · have hzu : z ≠ u := fun h => hz₀ (congrFun h i₀)
    simp [labelIndicator, hz₀, hzu]

/-- Evaluation of quadratic label tables is surjective on any finite set whose
fibers over one coordinate have size at most three. -/
theorem quadratic_interpolation (s : Finset (I → A)) (i₀ : I)
    (hc : ∀ a, (s.filter (fun w => w i₀ = a)).card ≤ 3)
    (values : {w // w ∈ s} → ℝ) :
    ∃ f ∈ quadraticLabelSpace I A, ∀ u : {w // w ∈ s}, f u = values u := by
  classical
  have hsep : ∀ u : {w // w ∈ s}, ∃ f ∈ quadraticLabelSpace I A,
      ∀ z ∈ s, f z = if z = u.val then 1 else 0 := by
    intro u
    exact exists_quadratic_separator s i₀ u.val u.property (hc (u.val i₀))
  choose φ hφmem hφ using hsep
  refine ⟨∑ u : {w // w ∈ s}, values u • φ u,
    (quadraticLabelSpace I A).sum_mem (fun u _ =>
      (quadraticLabelSpace I A).smul_mem (values u) (hφmem u)), ?_⟩
  intro u
  rw [Finset.sum_apply, Finset.sum_eq_single u]
  · simp [hφ u u.val u.property]
  · intro v _ hv
    have huv : u.val ≠ v.val := by
      intro h
      exact hv (Subtype.ext h.symm)
    simp [hφ v u.val u.property, huv]
  · simp

/-- Coordinate injectivity is the only property of matchings needed here. -/
def CoordinateInjectiveOn (s : Finset (I → A)) (i₀ : I) : Prop :=
  Set.InjOn (fun w : I → A => w i₀) (s : Set (I → A))

lemma coordinate_fiber_card_le_one (s : Finset (I → A)) (i₀ : I)
    (hs : CoordinateInjectiveOn s i₀) (a : A) :
    (s.filter (fun w => w i₀ = a)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hus, hua⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvs, hva⟩ := Finset.mem_filter.mp hv
  exact hs hus hvs (hua.trans hva.symm)

lemma three_matchings_fiber_card_le_three (s₁ s₂ s₃ : Finset (I → A)) (i₀ : I)
    (h₁ : CoordinateInjectiveOn s₁ i₀)
    (h₂ : CoordinateInjectiveOn s₂ i₀)
    (h₃ : CoordinateInjectiveOn s₃ i₀) (a : A) :
    ((s₁ ∪ s₂ ∪ s₃).filter (fun w => w i₀ = a)).card ≤ 3 := by
  classical
  rw [Finset.filter_union, Finset.filter_union]
  have h₁' := coordinate_fiber_card_le_one s₁ i₀ h₁ a
  have h₂' := coordinate_fiber_card_le_one s₂ i₀ h₂ a
  have h₃' := coordinate_fiber_card_le_one s₃ i₀ h₃ a
  have h₁₂ := Finset.card_union_le
    (s₁.filter (fun w => w i₀ = a)) (s₂.filter (fun w => w i₀ = a))
  have h₁₂₃ := Finset.card_union_le
    (s₁.filter (fun w => w i₀ = a) ∪ s₂.filter (fun w => w i₀ = a))
    (s₃.filter (fun w => w i₀ = a))
  omega

/-- Every prescribed scalar table on the union of three coordinate-injective
matchings is the restriction of a quadratic label table. -/
theorem quadratic_interpolation_three_matchings
    (s₁ s₂ s₃ : Finset (I → A)) (i₀ : I)
    (h₁ : CoordinateInjectiveOn s₁ i₀)
    (h₂ : CoordinateInjectiveOn s₂ i₀)
    (h₃ : CoordinateInjectiveOn s₃ i₀)
    (values : {w // w ∈ s₁ ∪ s₂ ∪ s₃} → ℝ) :
    ∃ f ∈ quadraticLabelSpace I A,
      ∀ u : {w // w ∈ s₁ ∪ s₂ ∪ s₃}, f u = values u :=
  quadratic_interpolation (s₁ ∪ s₂ ∪ s₃) i₀
    (three_matchings_fiber_card_le_three s₁ s₂ s₃ i₀ h₁ h₂ h₃) values

noncomputable def evaluation (s : Finset (I → A)) :
    quadraticLabelSpace I A →ₗ[ℝ] ({w // w ∈ s} → ℝ) where
  toFun f := fun u => f.val u.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_surjective (s : Finset (I → A)) (i₀ : I)
    (hc : ∀ a, (s.filter (fun w => w i₀ = a)).card ≤ 3) :
    Function.Surjective (evaluation s) := by
  intro values
  obtain ⟨f, hf, hvals⟩ := quadratic_interpolation s i₀ hc values
  exact ⟨⟨f, hf⟩, funext hvals⟩

end AkopyanQuadratic
