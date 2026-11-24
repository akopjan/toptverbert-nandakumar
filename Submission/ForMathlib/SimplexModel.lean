module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Compatibility of the two standard simplex models

Lean 4.35's singular simplices use `Convexity.StdSimplex`, represented by
finitely supported weights. The imported geometric constructions use the
older finite-coordinate subtype. This homeomorphism preserves every weight
and commutes with maps of finite vertex sets.
-/

@[expose] public section
noncomputable section

namespace Submission

open Convexity

variable (ι : Type*) [Fintype ι]

/-- The actual coordinate-preserving identification of the simplex models. -/
def simplexModelHomeomorph : StdSimplex ℝ ι ≃ₜ stdSimplex ℝ ι where
  toFun x := ⟨x.weights, x.weights_nonneg, x.total_of_fintype⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm x.1
    nonneg := by
      intro i
      exact x.2.1 i
    total := by simpa [Finsupp.sum_fintype] using x.2.2 }
  left_inv x := by
    apply StdSimplex.ext
    ext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp
  continuous_toFun := (continuous_pi fun i => StdSimplex.continuous_weights_apply ℝ i).subtype_mk _
  continuous_invFun := by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.mpr
    change Continuous (Subtype.val : stdSimplex ℝ ι → ι → ℝ)
    exact continuous_subtype_val

@[simp] theorem simplexModelHomeomorph_apply_weights (x : StdSimplex ℝ ι) (i : ι) :
    (simplexModelHomeomorph ι x).1 i = x.weights i := rfl

@[simp] theorem simplexModelHomeomorph_symm_weights (x : stdSimplex ℝ ι) (i : ι) :
    ((simplexModelHomeomorph ι).symm x).weights i = x.1 i := by
  simp [simplexModelHomeomorph]

theorem simplexModelHomeomorph_map {κ : Type*} [Fintype κ]
    (f : ι → κ) (x : StdSimplex ℝ ι) :
    simplexModelHomeomorph κ (x.map f) =
      stdSimplex.map f (simplexModelHomeomorph ι x) := by
  classical
  apply Subtype.ext
  funext i
  change (x.weights.mapDomain f) i = (FunOnFinite.linearMap ℝ ℝ f x.weights) i
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply,
    FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rw [Finsupp.sum_fintype _ _ (by simp)]

end Submission
