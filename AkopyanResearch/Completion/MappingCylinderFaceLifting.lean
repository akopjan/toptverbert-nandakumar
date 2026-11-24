module

public import AkopyanResearch.Completion.MappingCylinderLifting
public import AkopyanResearch.Completion.FaceCubicalHomeomorph

/-!
# Exact relative lifting on the actual finite simplex faces

The cubical lifting theorem is transported through the verified
boundary-preserving face homeomorphism. Both the boundary map and the
prescribed boundary homotopy remain literal equalities.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingCylinderFaceLifting

open CategoryTheory TopCat AkopyanQuadratic FaceCubicalHomeomorph
open CubicalHomotopyRectification
open scoped unitInterval Topology

variable {X Y : TopCat} (f : X ⟶ Y) [PathConnectedSpace X]

/-- Extension over a face of dimension at most the actual mapping-cylinder
connectivity bound. -/
theorem extend (S : Finset (Fin 15)) (hS : S.Nonempty) {N : ℕ}
    (h : Submission.IsNConnectedPair N (MapCyl f) (MapCyl.top f))
    (hN : S.card - 1 ≤ N)
    (g : C(FaceBoundary S, X)) (p : C(FaceSimplex S, Y))
    (eta : C(FaceBoundary S, C(I, Y)))
    (h₀ : ∀ a, eta a 0 = f (g a)) (h₁ : ∀ a, eta a 1 = p a.val) :
    ∃ G : C(FaceSimplex S, X), ∃ H : C(FaceSimplex S, C(I, Y)),
      (∀ a : FaceBoundary S, G a.val = g a) ∧
      (∀ a : FaceBoundary S, H a.val = eta a) ∧
      (∀ x, H x 0 = f (G x)) ∧ (∀ x, H x 1 = p x) := by
  let e := faceCube S hS
  let b := faceBoundaryCube S hS
  let gc : C(Boundary (S.card - 1), X) := g.comp ⟨b.symm, b.symm.continuous⟩
  let pc : C(Domain (S.card - 1), Y) := p.comp ⟨e.symm, e.symm.continuous⟩
  let ec : C(Boundary (S.card - 1), C(I, Y)) := eta.comp ⟨b.symm, b.symm.continuous⟩
  have h₀c (a : Boundary (S.card - 1)) : ec a 0 = f (gc a) := h₀ (b.symm a)
  have h₁c (a : Boundary (S.card - 1)) : ec a 1 = pc a.val := h₁ (b.symm a)
  obtain ⟨G, H, hG, hH, hH₀, hH₁⟩ :=
    MappingCylinderLifting.extend f gc pc ec h₀c h₁c h hN
  refine ⟨G.comp ⟨e, e.continuous⟩, H.comp ⟨e, e.continuous⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    change G (b a).val = g a
    rw [hG]
    change g (b.symm (b a)) = g a
    rw [b.symm_apply_apply]
  · intro a
    change H (b a).val = eta a
    rw [hH]
    change eta (b.symm (b a)) = eta a
    rw [b.symm_apply_apply]
  · intro x
    exact hH₀ (e x)
  · intro x
    change H (e x) 1 = p x
    rw [hH₁]
    exact congrArg p (e.symm_apply_apply x)

end AkopyanResearch.MappingCylinderFaceLifting
