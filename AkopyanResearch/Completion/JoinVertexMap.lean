module

public import AkopyanResearch.Completion.PhaseExtension

/-!
# Continuous pushforward on finite colored-join coordinates

A map of finite vertex sets pushes weights forward by summing over its
fibers. The one-active-vertex condition is preserved. This gives actual
continuous projections even when the vertex map is not injective.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.JoinVertexMap

open scoped BigOperators Classical
open PhaseExtension

universe u v w t
variable {C : Type u} {V : Type v} {W : Type w} {Z : Type t}
  [Fintype C] [Fintype V] [Fintype W] [Fintype Z]

def mapVertices (f : V → W) (x : Join C V) : Join C W := by
  classical
  refine ⟨fun i => ∑ v : V, if f v = i.2 then x.val (i.1, v) else 0, ?_, ?_, ?_⟩
  · intro i
    refine Finset.sum_nonneg fun v _ => ?_
    split_ifs
    · exact x.property.1 _
    · exact le_rfl
  · calc
      (∑ i : C × W, ∑ v : V, if f v = i.2 then x.val (i.1, v) else 0) =
          ∑ c : C, ∑ v : V, ∑ w : W, if f v = w then x.val (c, v) else 0 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro c _
            exact Finset.sum_comm
      _ = ∑ i : C × V, x.val i := by simp [Fintype.sum_prod_type]
      _ = 1 := x.property.2.1
  · intro c a b ha hb
    have active : ∀ w : W,
        (∑ v : V, if f v = w then x.val (c, v) else 0) ≠ 0 →
        ∃ v : V, f v = w ∧ x.val (c, v) ≠ 0 := by
      intro w hw
      by_contra hn
      push Not at hn
      apply hw
      apply Finset.sum_eq_zero
      intro v _
      by_cases hv : f v = w
      · simp [hv, hn v hv]
      · simp [hv]
    obtain ⟨v, hv, hvc⟩ := active a ha
    obtain ⟨w, hw, hwc⟩ := active b hb
    have he := x.property.2.2 c v w hvc hwc
    exact hv.symm.trans ((congrArg f he).trans hw)

@[simp] theorem mapVertices_val (f : V → W) (x : Join C V) (c : C) (w : W) :
    (mapVertices f x).val (c, w) = ∑ v : V, if f v = w then x.val (c, v) else 0 := by
  classical
  rfl

theorem continuous_mapVertices (f : V → W) : Continuous (mapVertices (C := C) f) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : Join C V => ∑ v : V, if f v = i.2 then x.val (i.1, v) else 0)
  exact continuous_finsetSum _ fun v _ => continuous_if_const (f v = i.2)
    (fun _ => (continuous_apply (i.1, v)).comp continuous_subtype_val)
    (fun _ => continuous_const)

theorem mapVertices_comp (f : V → W) (g : W → Z) (x : Join C V) :
    mapVertices g (mapVertices f x) = mapVertices (g ∘ f) x := by
  classical
  apply Subtype.ext
  funext i
  change (∑ w : W, if g w = i.2 then (∑ v : V, if f v = w then x.val (i.1, v) else 0) else 0) =
    ∑ v : V, if g (f v) = i.2 then x.val (i.1, v) else 0
  have hs : ∀ w : W,
      (if g w = i.2 then (∑ v : V, if f v = w then x.val (i.1, v) else 0) else 0) =
      ∑ v : V, if f v = w then (if g w = i.2 then x.val (i.1, v) else 0) else 0 := by
    intro w
    by_cases hw : g w = i.2 <;> simp [hw]
  rw [Finset.sum_congr rfl (fun w _ => hs w), Finset.sum_comm]
  simp

theorem mapVertices_equiv (e : V ≃ W) (x : Join C V) (w : W) (c : C) :
    (mapVertices e x).val (c, w) = x.val (c, e.symm w) := by
  classical
  rw [mapVertices_val, Finset.sum_eq_single (e.symm w)]
  · simp
  · intro v _ hv
    have he : e v ≠ w := by
      intro h
      exact hv (e.injective (h.trans (e.apply_symm_apply w).symm))
    simp [he]
  · simp

theorem mapVertices_perm (e : Equiv.Perm V) (x : Join C V) :
    mapVertices e x = relabel e x := by
  apply Subtype.ext
  funext i
  exact mapVertices_equiv e x i.2 i.1

theorem mapVertices_relabel (f : V → W) (e : Equiv.Perm V) (x : Join C V) :
    mapVertices f (relabel e x) = mapVertices (f ∘ e) x := by
  rw [← mapVertices_perm, mapVertices_comp]

theorem mapVertices_natural (f : V → W) (e : Equiv.Perm V) (p : Equiv.Perm W)
    (h : ∀ v, f (e v) = p (f v)) (x : Join C V) :
    mapVertices f (relabel e x) = relabel p (mapVertices f x) := by
  rw [mapVertices_relabel, ← mapVertices_perm, mapVertices_comp]
  congr 1
  funext v
  exact h v

/-- Agreement is needed only at vertices with nonzero coordinate weight. -/
theorem mapVertices_congr_of_support (f g : V → W) (x : Join C V)
    (h : ∀ c v, x.val (c, v) ≠ 0 → f v = g v) :
    mapVertices f x = mapVertices g x := by
  classical
  apply Subtype.ext
  funext i
  change (∑ v : V, if f v = i.2 then x.val (i.1, v) else 0) =
    ∑ v : V, if g v = i.2 then x.val (i.1, v) else 0
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : x.val (i.1, v) = 0
  · simp [hv]
  · rw [h i.1 v hv]

end AkopyanResearch.JoinVertexMap
