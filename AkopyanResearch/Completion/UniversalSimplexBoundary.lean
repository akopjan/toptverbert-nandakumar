module

public import AkopyanResearch.Completion.RelativeSimplexBoundary

/-! # The actual universal simplex with its codimension-two skeleton -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.deprecated false
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

namespace AkopyanResearch.UniversalSimplexAddition
open Submission RelativeSimplexBoundary RelativeHurewiczDescent SimplexSkeletonRetraction

variable (n : ℕ)

abbrev UniversalSpace := Simplex (n + 3)
abbrev UniversalSkeleton := skeleton (n + 3)

theorem doubleFace_mem (i : Fin (n + 5)) (j : Fin (n + 4))
    (z : stdSimplex ℝ (Fin (n + 3))) :
    faceMap i (faceMap j z) ∈ UniversalSkeleton n := by
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, ?_, ?_⟩
  · exact faceMap_coe_same i _
  · simp only [faceMap_coe_succAbove, faceMap_coe_same]

/-- The identity simplex, with its actual geometric faces in the universal pair. -/
def universalBoundary : Boundary (n + 1) (TopCat.of (UniversalSpace n))
    (UniversalSkeleton n) where
  simplex := sng (ContinuousMap.id (UniversalSpace n))
  face i := {
    simplex := sng ⟨faceMap i, continuous_faceMap i⟩
    face_lift j := by
      let q : C(stdSimplex ℝ (Fin (n + 3)), UniversalSkeleton n) :=
        ⟨fun z => ⟨faceMap i (faceMap j z), doubleFace_mem n i j z⟩,
          ((continuous_faceMap i).comp (continuous_faceMap j)).subtype_mk _⟩
      refine ⟨sng q, ?_⟩
      apply (sngEquiv (TopCat.of (UniversalSpace n)) (n + 2)).injective
      ext y
      rw [sngEquiv_incl, sngEquiv_sng, sngEquiv_δ, sngEquiv_sng]
      rfl }
  face_simplex i := by
    apply (sngEquiv (TopCat.of (UniversalSpace n)) (n + 3)).injective
    rw [sngEquiv_sng, sngEquiv_δ, sngEquiv_sng]
    rfl

end AkopyanResearch.UniversalSimplexAddition
