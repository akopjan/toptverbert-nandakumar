module

public import AkopyanResearch.QuadraticArrangement

/-!
# What the original comparison interface actually assumes

`ComparisonTarget.extend_high` is an extension theorem for every boundary map.
Together with `CoherentComparison.lift_ball_along_comp`, it gives the same
universal extension property for the arrangement complement itself. This is
stronger than extending the particular compatible boundaries in the intended
construction. A comparison with sphere factors cannot be justified merely by
constructing one compatible target map.

The theorem below records this consequence in Lean. It does not assert the
existence of a comparison, a safe table, or the dimension-eighteen result.
-/

@[expose] public section
set_option autoImplicit false

namespace AkopyanResearch

/-- The original comparison assumptions force extension of every boundary map
into the arrangement complement, not only skeleton boundaries. -/
theorem CoherentComparison.extends_every_boundary {k : ℕ}
    {P : ComparisonTarget k} (C : CoherentComparison k P)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : k + 1 ≤ S.card)
    (g : FaceBoundary S → QuadComplement S) (hg : Continuous g) :
    ∃ G : FaceSimplex S → QuadComplement S,
      Continuous G ∧ ∀ z : FaceBoundary S, G z.1 = g z := by
  obtain ⟨F, hF, hboundary⟩ :=
    P.extend_high S hS hcard (fun z => C.comp S hS (g z))
      ((C.continuous_comp S hS).comp hg)
  exact C.lift_ball_along_comp S hS hcard g hg F hF hboundary

/-- Every retract of a complement would inherit that universal extension
property. This makes the strength of the proposed comparison contract explicit.
-/
theorem CoherentComparison.extends_boundary_into_retract {k : ℕ}
    {P : ComparisonTarget k} (C : CoherentComparison k P)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : k + 1 ≤ S.card)
    {Y : Type*} [TopologicalSpace Y]
    (sectionMap : Y → QuadComplement S) (retraction : QuadComplement S → Y)
    (hsection : Continuous sectionMap) (hretraction : Continuous retraction)
    (hleft : Function.LeftInverse retraction sectionMap)
    (f : FaceBoundary S → Y) (hf : Continuous f) :
    ∃ F : FaceSimplex S → Y,
      Continuous F ∧ ∀ z : FaceBoundary S, F z.1 = f z := by
  obtain ⟨G, hG, hboundary⟩ := C.extends_every_boundary S hS hcard
    (fun z => sectionMap (f z)) (hsection.comp hf)
  refine ⟨fun z => retraction (G z), hretraction.comp hG, ?_⟩
  intro z
  change retraction (G z.1) = f z
  rw [hboundary z, hleft]

end AkopyanResearch
