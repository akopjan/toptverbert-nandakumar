module

public import AkopyanResearch.QuadraticInterpolation

@[expose] public section

/-!
# Naturality of the quadratic table space

Forgetting or identifying colors, and permuting labels separately in each
color, preserves the quadratic label space exactly. No enumeration of words
is used.
-/

namespace AkopyanQuadratic

variable {I J A : Type*}

noncomputable def pullbackQuadraticTable (f : I → J) (σ : I → Equiv.Perm A) :
    (((I → A) → ℝ) →ₗ[ℝ] ((J → A) → ℝ)) where
  toFun H := fun w => H (fun i => σ i (w (f i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pullback_labelIndicator (f : I → J) (σ : I → Equiv.Perm A) (i : I) (a : A) :
    pullbackQuadraticTable f σ (labelIndicator i a) =
      labelIndicator (f i) ((σ i).symm a) := by
  classical
  ext w
  simp [pullbackQuadraticTable, labelIndicator, ← Equiv.eq_symm_apply]

/-- The same degree-two space is used on every face and under every row relabeling. -/
theorem pullback_mem_quadratic (f : I → J) (σ : I → Equiv.Perm A)
    {H : (I → A) → ℝ} (hH : H ∈ quadraticLabelSpace I A) :
    pullbackQuadraticTable f σ H ∈ quadraticLabelSpace J A := by
  have hle : quadraticLabelSpace I A ≤
      (quadraticLabelSpace J A).comap (pullbackQuadraticTable f σ) := by
    apply Submodule.span_le.mpr
    rintro H ((h | ⟨⟨i, a⟩, rfl⟩) | ⟨⟨⟨i, a⟩, ⟨j, b⟩⟩, rfl⟩)
    · rcases h with rfl
      exact Submodule.subset_span (Or.inl (Or.inl rfl))
    · change pullbackQuadraticTable f σ (labelIndicator i a) ∈ quadraticLabelSpace J A
      rw [pullback_labelIndicator]
      exact indicator_mem_quadratic _ _
    · change (fun w => labelIndicator i a (fun t => σ t (w (f t))) *
          labelIndicator j b (fun t => σ t (w (f t)))) ∈ quadraticLabelSpace J A
      have hi := pullback_labelIndicator f σ i a
      have hj := pullback_labelIndicator f σ j b
      change (fun w => pullbackQuadraticTable f σ (labelIndicator i a) w *
          pullbackQuadraticTable f σ (labelIndicator j b) w) ∈ quadraticLabelSpace J A
      rw [hi, hj]
      exact indicator_mul_mem_quadratic _ _ _ _
  exact hle hH

theorem color_duplication_mem_quadratic (f : I → J)
    {H : (I → A) → ℝ} (hH : H ∈ quadraticLabelSpace I A) :
    (fun w : J → A => H (w ∘ f)) ∈ quadraticLabelSpace J A := by
  simpa [pullbackQuadraticTable, Function.comp_def] using
    pullback_mem_quadratic f (fun _ => Equiv.refl A) hH

end AkopyanQuadratic
