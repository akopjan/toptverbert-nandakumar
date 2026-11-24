module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

Extension of the concrete simplex/cube evaluation argument to arbitrary pairs.
The induced homology map is the ordinary map on the singular quotient complex.
-/

public import Submission.Hurewicz.RelativeNormalization

@[expose] public section
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

namespace Submission
namespace PairCube
variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X}

/-- The image of the distinguished cube-boundary point. -/
def basepoint (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) : A :=
  ⟨f (cubeBoundaryBase n), hf _ (cubeBoundaryBase n).property⟩

/-- A map of cube pairs is based at the actual image of its distinguished point. -/
def basedMap (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) :
    BasedPairMap (∂I^(n + 1)) A (cubeBoundaryBase n) (basepoint f hf) where
  toContinuousMap := f
  mapsTo' := hf
  map_basepoint' := rfl

/-- The actual induced map of relative singular homology, without requiring
that a homotopy preserve the chosen image basepoint. -/
def homologyMap (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) (k : ℕ) :
    HrelSet (Y := TopCat.of (I^Fin (n + 1))) k (∂I^(n + 1)) ⟶
      HrelSet (Y := TopCat.of X) k A :=
  (basedMap f hf).hrelMap k

/-- Homotopies of pairs preserve this induced map; their image basepoint
may vary within `A`. -/
theorem homologyMap_congr {f g : C(I^Fin (n + 1), X)}
    (hf : Cube.IsMapOfPairs X A f) (hg : Cube.IsMapOfPairs X A g)
    (H : f.HomotopicWith g (Cube.IsMapOfPairs X A)) (k : ℕ) :
    homologyMap f hf k = homologyMap g hg k := by
  obtain ⟨H⟩ := H
  let sub : TopCat.Homotopy (basedMap f hf).subspaceHom (basedMap g hg).subspaceHom :=
    { toFun := fun ty => ⟨H (ty.1, ty.2.1), H.prop ty.1 ty.2.1 ty.2.2⟩
      continuous_toFun := Continuous.subtype_mk
        (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
      map_zero_left := fun y => Subtype.ext (H.map_zero_left y.1)
      map_one_left := fun y => Subtype.ext (H.map_one_left y.1) }
  exact HrelMap_congr (basedMap f hf).subIncl_naturality
    (basedMap g hg).subIncl_naturality
    (PairHomotopy.ofPointwise (basedMap f hf).subIncl_naturality
      (basedMap g hg).subIncl_naturality sub H.toHomotopy (fun _ _ => rfl)) k

/-- On an actual relative generalized loop this is its usual relative homology map. -/
theorem homologyMap_relGenLoop {a : A} (p : RelGenLoop (n + 1) X A a) (k : ℕ) :
    homologyMap p.val p.property.1 k = RelGenLoop.hrelMap k p := rfl

end PairCube

namespace PairNormalizedSimplex
variable {n : ℕ} {X : TopCat.{0}} {A : Set X}

/-- The cube reparametrization sends the fundamental singular simplex to the
original simplex, including when its boundary is nonconstant. -/
theorem pairMap_cubeFundamentalSimplex (s : PairNormalizedSimplex n X A) :
    (TopCat.toSSet.map (PairCube.basedMap s.cubeMap s.cubeMap_isMapOfPairs).ambientHom).app _
      (cubeFundamentalSimplex (n + 2)) = s.simplex := by
  apply (sngEquiv X (n + 2)).injective
  rw [sngEquiv_map]
  ext z
  change s.cubeMap ((cubeHomeoSimplex (n + 2)).symm z) =
    sngEquiv X (n + 2) s.simplex z
  rw [cubeMap]
  simp

/-- The same identity on the actual relative singular chains. -/
theorem pairMap_cubeFundamentalChain (s : PairNormalizedSimplex n X A) :
    (relComplexMap
      (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2))) (subIncl A)
      (PairCube.basedMap s.cubeMap s.cubeMap_isMapOfPairs).subIncl_naturality).f (n + 2)
      (relativeSimplexChain (X := TopCat.of (I^Fin (n + 2)))
        (∂I^(n + 2)) (cubeFundamentalSimplex (n + 2))) =
      relativeSimplexChain A s.simplex := by
  rw [relativeSimplexChain, relativeSimplexChain, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, relProj_comp_relComplexMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, CsingMap_gen, s.pairMap_cubeFundamentalSimplex]

/-- Evaluating the explicit cube fundamental class gives precisely the
relative homology class of the original simplex. -/
theorem homologyMap_cubeSimplexRelativeClass (s : PairNormalizedSimplex n X A) :
    PairCube.homologyMap s.cubeMap s.cubeMap_isMapOfPairs (n + 2)
      (cubeSimplexRelativeClass n) = s.relativeClass := by
  let F := relComplexMap
    (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2))) (subIncl A)
    (PairCube.basedMap s.cubeMap s.cubeMap_isMapOfPairs).subIncl_naturality
  exact homologyMap_relativeSimplexClass
    (X := TopCat.of (I^Fin (n + 2))) (Y := X)
    (A := ∂I^(n + 2)) (B := A) (n := n + 1) F
    (cubeFundamentalSimplex (n + 2)) (cubeFundamentalSimplex_face_lift n)
    s.simplex s.face_lift s.pairMap_cubeFundamentalChain

/-- Every normalized relative simplex class is represented by an actual
relative homotopy class at some point of `A`. -/
theorem exists_relativeHomotopyClass (s : PairNormalizedSimplex n X A) :
    ∃ a : A, ∃ z : π_rel (n + 2) X A a,
      simplexRelativeHurewicz n A a z = s.relativeClass := by
  obtain ⟨a, p, H⟩ := s.exists_relGenLoop
  refine ⟨a, ⟦p⟧, ?_⟩
  rw [simplexRelativeHurewicz_mk]
  have h := PairCube.homologyMap_congr s.cubeMap_isMapOfPairs p.property.1 H (n + 2)
  rw [PairCube.homologyMap_relGenLoop] at h
  rw [← h]
  exact s.homologyMap_cubeSimplexRelativeClass

end PairNormalizedSimplex
end Submission
