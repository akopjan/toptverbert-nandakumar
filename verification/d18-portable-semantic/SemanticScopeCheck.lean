module
import SemanticReference
import Solution
import AkopyanResearch.Completion.DimensionEighteen

set_option autoImplicit false
noncomputable section

namespace SemanticScopeCheck

theorem originalA : SemanticReference.theoremA :=
  AkopyanSixfold.tverberg_counterexample

theorem directHeightBridge : SemanticReference.theoremA :=
  Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension

theorem originalHeight : SemanticReference.heightExtension :=
  Tverberg6R.heightExtension

theorem finalB (d : ℕ) (hd : 17 < d) : SemanticReference.theoremB d :=
  AkopyanSixfold.convex_partition_counterexample_gt_17 d hd

/-- The finite-function target is transported to the actual Euclidean
metric space; the map is continuous on the standard simplex subtype. -/
theorem euclideanA : SemanticReference.euclideanTheoremA := by
  obtain ⟨f, hf, hsep⟩ := originalA
  let e := PiLp.homeomorph 2 (fun _ : Fin 6 => ℝ)
  let F : C(SemanticReference.simplex 36, EuclideanSpace ℝ (Fin 6)) :=
    ⟨fun x => e.symm (f x.val),
      e.symm.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hf)⟩
  refine ⟨F, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hsep (fun j => (x j).val) (fun j => (x j).property) hx
  exact ⟨i, fun he => hi (e.symm.injective he)⟩

#check originalA
#check originalHeight
#check finalB
#check euclideanA
#check SemanticReference.sixVertices_mem
#check SemanticReference.sixVertices_disjoint
#check SemanticReference.matching_exists
#print axioms originalA
#print axioms directHeightBridge
#print axioms originalHeight
#print axioms finalB
#print axioms euclideanA

end SemanticScopeCheck
