module

public import AkopyanResearch.QuadraticInterpolation

@[expose] public section

/-!
# Preservation of the normal-map ranks

Evaluation on a union of at most three matchings is surjective also for
vector-valued quadratic label tables. Therefore every collection of linear
normal equations depending on those entries has exactly its original range.
-/

namespace AkopyanQuadratic

open scoped Classical

variable {I A K E : Type*}

noncomputable def vectorEvaluation (s : Finset (I → A)) :
    (K → quadraticLabelSpace I A) →ₗ[ℝ] ({w // w ∈ s} → K → ℝ) where
  toFun f := fun u k => (f k).val u.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vectorEvaluation_surjective (s : Finset (I → A)) (i₀ : I)
    (hc : ∀ a, (s.filter (fun w => w i₀ = a)).card ≤ 3) :
    Function.Surjective (vectorEvaluation (K := K) s) := by
  intro values
  have h : ∀ k : K, ∃ f : quadraticLabelSpace I A,
      evaluation s f = fun u => values u k := by
    intro k
    exact evaluation_surjective s i₀ hc (fun u => values u k)
  choose f hf using h
  refine ⟨f, ?_⟩
  funext u k
  exact congrFun (hf k) u

variable [AddCommGroup E] [Module ℝ E]

/-- Restricting any linear system on these entries to quadratic tables does
not change its range, hence does not change its rank. -/
theorem normal_range_preserved (s : Finset (I → A)) (i₀ : I)
    (hc : ∀ a, (s.filter (fun w => w i₀ = a)).card ≤ 3)
    (q : ({w // w ∈ s} → K → ℝ) →ₗ[ℝ] E) :
    LinearMap.range (q.comp (vectorEvaluation s)) = LinearMap.range q := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨vectorEvaluation s f, rfl⟩
  · rintro ⟨values, rfl⟩
    obtain ⟨f, hf⟩ := vectorEvaluation_surjective s i₀ hc values
    exact ⟨f, by simp [hf]⟩

theorem three_matchings_normal_range_preserved
    (s₁ s₂ s₃ : Finset (I → A)) (i₀ : I)
    (h₁ : CoordinateInjectiveOn s₁ i₀)
    (h₂ : CoordinateInjectiveOn s₂ i₀)
    (h₃ : CoordinateInjectiveOn s₃ i₀)
    (q : ({w // w ∈ s₁ ∪ s₂ ∪ s₃} → K → ℝ) →ₗ[ℝ] E) :
    LinearMap.range (q.comp (vectorEvaluation (s₁ ∪ s₂ ∪ s₃))) = LinearMap.range q :=
  normal_range_preserved (s₁ ∪ s₂ ∪ s₃) i₀
    (three_matchings_fiber_card_le_three s₁ s₂ s₃ i₀ h₁ h₂ h₃) q

end AkopyanQuadratic
