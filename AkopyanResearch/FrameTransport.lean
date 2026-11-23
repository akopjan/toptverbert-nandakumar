module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic


@[expose] public section

/-!
A continuous rotation transporting one unit vector to another, on the
complement of the antipodal vector. The construction uses two Householder
reflections and is independent of sphere homotopy-group calculations.
-/

open scoped InnerProductSpace

namespace FrameTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable section

def reflect (a x : E) : E := x - (2 * ⟪a, x⟫_ℝ / ‖a‖ ^ 2) • a

omit [FiniteDimensional ℝ E] in
lemma reflect_eq (a x : E) : reflect a x = (ℝ ∙ a)ᗮ.reflection x := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [reflect, two_smul, neg_sub]
  module

def transport (u v : E) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ u)ᗮ.reflection.trans (ℝ ∙ (u + v))ᗮ.reflection

omit [FiniteDimensional ℝ E] in
lemma transport_apply (u v x : E) : transport u v x = reflect (u + v) (reflect u x) := by
  simp [transport, reflect_eq]

omit [FiniteDimensional ℝ E] in
lemma span_neg_singleton (x : E) : (ℝ ∙ (-x)) = ℝ ∙ x := by
  simpa using Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0)) x

omit [FiniteDimensional ℝ E] in
lemma transport_vector {u v : E} (h : ‖u‖ = ‖v‖) : transport u v u = v := by
  rw [transport, LinearIsometryEquiv.trans_apply,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg]
  have hr := Submodule.reflection_sub (v := -u) (w := v) (by simpa using h)
  have hs : (ℝ ∙ (-u - v)) = ℝ ∙ (u + v) := by
    rw [show -u - v = -(u + v) by abel, span_neg_singleton]
  simpa only [hs] using hr

omit [FiniteDimensional ℝ E] in
lemma transport_self (u : E) : transport u u = LinearIsometryEquiv.refl ℝ E := by
  have hs : (ℝ ∙ (u + u)) = ℝ ∙ u := by
    simpa only [two_smul] using
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0)) u
  simp only [transport, hs, Submodule.reflection_trans_reflection]

lemma det_reflect {a : E} (ha : a ≠ 0) :
    LinearMap.det ((ℝ ∙ a)ᗮ.reflection.toLinearMap) = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton ha]
  norm_num

lemma det_transport {u v : E} (hu : u ≠ 0) (huv : u + v ≠ 0) :
    LinearMap.det (transport u v).toLinearMap = 1 := by
  change LinearMap.det
    (((ℝ ∙ (u + v))ᗮ.reflection.toLinearMap).comp ((ℝ ∙ u)ᗮ.reflection.toLinearMap)) = 1
  rw [LinearMap.det_comp, det_reflect huv, det_reflect hu]
  norm_num

omit [FiniteDimensional ℝ E] in
lemma continuousAt_reflect {a x : E} (ha : a ≠ 0) :
    ContinuousAt (fun p : E × E => reflect p.1 p.2) (a, x) := by
  unfold reflect
  apply ContinuousAt.sub continuousAt_snd
  apply ContinuousAt.smul
  · apply ContinuousAt.div
    · exact continuousAt_const.mul (continuous_fst.inner continuous_snd).continuousAt
    · exact (continuous_fst.norm.pow 2).continuousAt
    · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  · exact continuousAt_fst


omit [FiniteDimensional ℝ E] in
/-- Joint continuity in both transported vectors and the vector acted on. -/
lemma continuousAt_transport {u v x : E} (hu : u ≠ 0) (huv : u + v ≠ 0) :
    ContinuousAt (fun p : E × E × E => transport p.1 p.2.1 p.2.2) (u, v, x) := by
  simp only [transport_apply]
  have hc : Continuous (fun p : E × E × E => (p.1, p.2.2)) := by fun_prop
  have hi : ContinuousAt (fun p : E × E × E => reflect p.1 p.2.2) (u, v, x) :=
    (continuousAt_reflect (a := u) (x := x) hu).comp
      (x := (u, v, x)) (f := fun p : E × E × E => (p.1, p.2.2)) hc.continuousAt
  have ha : Continuous (fun p : E × E × E => p.1 + p.2.1) := by fun_prop
  exact (continuousAt_reflect (a := u + v) (x := reflect u x) huv).comp
    (x := (u, v, x)) (f := fun p : E × E × E => (p.1 + p.2.1, reflect p.1 p.2.2))
    (ha.continuousAt.prodMk hi)

omit [FiniteDimensional ℝ E] in
lemma continuousOn_transport (u : E) (hu : u ≠ 0) :
    ContinuousOn (fun p : E × E => transport u p.1 p.2)
      {p | u + p.1 ≠ 0} := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  simp only [transport_apply]
  have hi : ContinuousAt (fun q : E × E => reflect u q.2) p :=
    (continuousAt_reflect (a := u) (x := p.2) hu).comp
      (x := p) (f := fun q : E × E => (u, q.2))
      (continuousAt_const.prodMk continuousAt_snd :
        ContinuousAt (fun q : E × E => (u, q.2)) p)
  exact (continuousAt_reflect (a := u + p.1) (x := reflect u p.2) hp).comp
    (x := p) (f := fun q : E × E => (u + q.1, reflect u q.2))
    ((continuousAt_const.add continuousAt_fst).prodMk hi :
      ContinuousAt (fun q : E × E => (u + q.1, reflect u q.2)) p)

end
end FrameTransport
