module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The chain-level normalization below generalizes the singleton constructions
in Hurewicz/SimplexCubeOrientation.lean to an arbitrary subspace. It uses the
same singular chains, relative quotient complex, and coherent deformation.
-/

public import Submission.Hurewicz.SimplexCubeClass
public import Submission.Hurewicz.ConnectedVanishing

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

namespace Submission

/-- A singular simplex whose entire boundary is carried into a specified
subspace. No constancy of that boundary is required. -/
structure PairNormalizedSimplex (n : ℕ) (X : TopCat.{0}) (A : Set X) where
  simplex : Sng X _⦋n + 2⦌
  face_lift (i : Fin (n + 3)) :
    ∃ t : Sng (TopCat.of A) _⦋n + 1⦌,
      (sngIncl A).app _ t = (Sng X).δ i simplex

namespace PairNormalizedSimplex
variable {n : ℕ} {X : TopCat.{0}} {A : Set X}

/-- The actual relative singular homology class of the simplex. -/
def relativeClass (s : PairNormalizedSimplex n X A) : HrelSet (n + 2) A :=
  relativeSimplexClass s.simplex s.face_lift

/-- The geometric simplex map takes its boundary into the subspace. -/
theorem simplex_boundary (s : PairNormalizedSimplex n X A)
    (z : stdSimplex ℝ (Fin (n + 3))) (hz : z ∈ bdry (n + 2)) :
    sngEquiv X (n + 2) s.simplex z ∈ A := by
  refine bdry_induction (j := n + 1) (P := fun z =>
    sngEquiv X (n + 2) s.simplex z ∈ A) ?_ hz
  intro i y
  rw [← apply_δ]
  obtain ⟨t, ht⟩ := s.face_lift i
  rw [← ht, sngEquiv_incl]
  exact (sngEquiv (TopCat.of A) (n + 1) t y).property

/-- Reparametrization by the genuine cube/simplex homeomorphism. -/
def cubeMap (s : PairNormalizedSimplex n X A) : C(I^Fin (n + 2), X) :=
  (sngEquiv X (n + 2) s.simplex).comp
    ⟨cubeHomeoSimplex (n + 2), (cubeHomeoSimplex (n + 2)).continuous⟩

theorem cubeMap_isMapOfPairs (s : PairNormalizedSimplex n X A) :
    Cube.IsMapOfPairs X A s.cubeMap :=
  fun y hy => s.simplex_boundary _ (cubeHomeoSimplex_mem_bdry _ y hy)

/-- Every such simplex has a genuine relative cubical representative up to
homotopy through maps of pairs. The basepoint is an actual point of `A`. -/
theorem exists_relGenLoop (s : PairNormalizedSimplex n X A) :
    ∃ a : A, ∃ g : RelGenLoop (n + 2) X A a,
      s.cubeMap.HomotopicWith g (Cube.IsMapOfPairs X A) :=
  Cube.exists_relGenLoop_homotopicWith_isMapOfPairs X A s.cubeMap
    s.cubeMap_isMapOfPairs

/-- A genuine relative loop gives a normalized singular simplex, without
changing its cube map. -/
def ofRelGenLoop {a : A} (p : RelGenLoop (n + 2) X A a) :
    PairNormalizedSimplex n X A where
  simplex := sng (p.val.comp
    ⟨(cubeHomeoSimplex (n + 2)).symm, (cubeHomeoSimplex (n + 2)).continuous_symm⟩)
  face_lift i := by
    let q : C(stdSimplex ℝ (Fin (n + 2)), A) :=
      ⟨fun y => ⟨p.val ((cubeHomeoSimplex (n + 2)).symm (faceMap i y)),
        p.property.1 _ (cubeHomeoSimplex_symm_mem_boundary (n + 2) _
          (faceMap_mem_bdry i y))⟩,
        (p.val.continuous.comp ((cubeHomeoSimplex (n + 2)).continuous_symm.comp
          (continuous_faceMap i))).subtype_mk _⟩
    refine ⟨sng q, ?_⟩
    apply (sngEquiv X (n + 1)).injective
    ext y
    rw [sngEquiv_incl, sngEquiv_sng, sngEquiv_δ, sngEquiv_sng]
    rfl

@[simp] theorem ofRelGenLoop_cubeMap {a : A} (p : RelGenLoop (n + 2) X A a) :
    (ofRelGenLoop p).cubeMap = p.val := by
  ext y
  simp only [cubeMap, ofRelGenLoop, sngEquiv_sng, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]

end PairNormalizedSimplex

namespace SimplicialDeformation
variable {n : ℕ} {X : TopCat.{0}} {A : Set X}
variable (c : SimplicialDeformation X A (n + 1))

/-- After coherent compression through dimension `n+1`, every top simplex
has all of its faces in `A`. -/
def normalizeRelativeTopSimplex (s : Sng X _⦋n + 2⦌) :
    PairNormalizedSimplex n X A where
  simplex := c.ρ (n + 2) s
  face_lift i := by
    rw [← c.ρ_δ]
    exact c.ρ_mem (by omega) ((Sng X).δ i s)

/-- The degreewise relative-chain quotient is surjective. -/
theorem relativeProjection_surjective (k : ℕ) :
    Function.Surjective ((relProj (subIncl A)).f k) := by
  letI : Epi (cokernel.π (CsingMap (subIncl A))) := coequalizer.π_epi
  exact (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi ((cokernel.π (CsingMap (subIncl A))).f k))

/-- The normalized relative self-map is zero in the last compressed degree. -/
theorem relativeSelfMap_f_prev_eq_zero :
    c.relativeSelfMap.f (n + 1) = 0 := by
  ext r
  obtain ⟨a, rfl⟩ := relativeProjection_surjective (A := A) (n + 1) r
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    c.relProj_comp_relativeSelfMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    c.selfMap_comp_relProj (n + 1) (by omega), zero_hom_apply]
  rfl

/-- Normalization takes every absolute top chain to a relative cycle. -/
theorem relativeTopCycle (a : (Csing X).X (n + 2)) :
    (relComplex (subIncl A)).d (n + 2) (n + 1)
      (c.relativeSelfMap.f (n + 2) ((relProj (subIncl A)).f (n + 2) a)) = 0 := by
  rw [← ConcreteCategory.comp_apply,
    c.relativeSelfMap.comm (n + 2) (n + 1), ConcreteCategory.comp_apply,
    c.relativeSelfMap_f_prev_eq_zero, zero_hom_apply]

/-- The homology class of the normalized relative top chain. -/
def relativeTopClassHom : ((Csing X).X (n + 2) : Type) →+ HrelSet (n + 2) A where
  toFun a := homologyMk
    (c.relativeSelfMap.f (n + 2) ((relProj (subIncl A)).f (n + 2) a)) (by
      rw [ChainComplex.next_nat_succ]
      exact c.relativeTopCycle a)
  map_zero' := by
    simp only [map_zero]
    change homologyMk 0 _ = 0
    exact homologyMk_zero
  map_add' a b := by
    simp only [map_add]
    change homologyMk (_ + _) _ = _
    exact homologyMk_add _ _ _ _

/-- The same map as a morphism of abelian groups. -/
def relativeTopClassChain : (Csing X).X (n + 2) ⟶ HrelSet (n + 2) A :=
  AddCommGrpCat.ofHom c.relativeTopClassHom

/-- On a singular generator this is precisely the class of its normalized
simplex; the boundary can be nonconstant in `A`. -/
@[simp] theorem relativeTopClassChain_gen (s : Sng X _⦋n + 2⦌) :
    c.relativeTopClassChain (gen s) =
      (c.normalizeRelativeTopSimplex s).relativeClass := by
  unfold relativeTopClassChain relativeTopClassHom
  change homologyMk
    (c.relativeSelfMap.f (n + 2) (relativeSimplexChain A s)) _ = _
  unfold PairNormalizedSimplex.relativeClass relativeSimplexClass
  exact homologyMk_congr _ _ (c.relativeSelfMap_relativeSimplexChain s)

/-- Every relative homology class in the first uncompressed degree is a
finite integral combination of these actual normalized simplex classes. -/
theorem relativeTopClassChain_surjective : Function.Surjective c.relativeTopClassChain := by
  intro z
  obtain ⟨r, hr, hzr⟩ := homologyMk_surjective z
  obtain ⟨a, rfl⟩ := relativeProjection_surjective (A := A) (n + 2) r
  refine ⟨a, ?_⟩
  change homologyMk
    (c.relativeSelfMap.f (n + 2) ((relProj (subIncl A)).f (n + 2) a)) _ = z
  rw [← hzr, ← homologyMap_homologyMk]
  rw [c.homologyMap_relativeSelfMap_eq_id, ConcreteCategory.id_apply]

end SimplicialDeformation

namespace IsNConnectedPair
variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X}

/-- The actual coherent relative tower; retaining it makes the geometric
simplex homotopies available in addition to their induced chain homotopy. -/
def relativeTowerLE {M : ℕ} (h : IsNConnectedPair M X A) (hA : A.Nonempty) (j : ℕ) :
    StepLE (X := TopCat.of X) A M j :=
  towerLE (X := TopCat.of X) (A := A) M hA h.surjective_iStar_zero
    (fun k hk => h.unique_piRel k (by omega)) j

def relativeStep {M : ℕ} (h : IsNConnectedPair M X A) (hA : A.Nonempty) (j : ℕ) :
    Step (X := TopCat.of X) A j :=
  (h.relativeTowerLE hA j).step

theorem relativeStep_isNext {M : ℕ} (h : IsNConnectedPair M X A)
    (hA : A.Nonempty) (j : ℕ) :
    IsNext (h.relativeStep hA j) (h.relativeStep hA (j + 1)) :=
  towerLE_isNext (X := TopCat.of X) (A := A) M hA h.surjective_iStar_zero
    (fun k hk => h.unique_piRel k (by omega)) j

theorem relativeStep_compresses {M : ℕ} (h : IsNConnectedPair M X A)
    (hA : A.Nonempty) (j : ℕ) (hj : j ≤ M) : (h.relativeStep hA j).Compresses :=
  (h.relativeTowerLE hA j).compresses hj

/-- The coherent relative deformation provided by actual relative connectivity. -/
def normalization (h : IsNConnectedPair (n + 1) X A) (hA : A.Nonempty) :
    SimplicialDeformation (TopCat.of X) A (n + 1) :=
  deformation (h.relativeStep hA) (h.relativeStep_isNext hA) (n + 1)
    (h.relativeStep_compresses hA)

@[simp] theorem normalization_rho (h : IsNConnectedPair (n + 1) X A)
    (hA : A.Nonempty) (j : ℕ) (s : Sng (TopCat.of X) _⦋j⦌) :
    (h.normalization hA).ρ j s = defRho (h.relativeStep hA) j s := rfl

/-- Relative connectivity supplies the surjective normalization map on the
ordinary relative singular homology group. -/
theorem normalization_surjective (h : IsNConnectedPair (n + 1) X A) (hA : A.Nonempty) :
    Function.Surjective (h.normalization hA).relativeTopClassChain :=
  (h.normalization hA).relativeTopClassChain_surjective

end IsNConnectedPair

namespace PairNormalizedSimplex
variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X}

/-- Coherent relative normalization fixes a normalized simplex on its full
boundary, pointwise, even when that boundary is not constant. -/
theorem normalizationCompHom_boundary (h : IsNConnectedPair (n + 1) X A)
    (hA : A.Nonempty) (s : PairNormalizedSimplex n (TopCat.of X) A)
    (z : stdSimplex ℝ (Fin (n + 3))) (hz : z ∈ bdry (n + 2)) (t : I) :
    compHom (h.relativeStep hA) (n + 2) s.simplex (z, t) =
      sngEquiv (TopCat.of X) (n + 2) s.simplex z := by
  refine bdry_induction (j := n + 1) (P := fun z =>
    compHom (h.relativeStep hA) (n + 2) s.simplex (z, t) =
      sngEquiv (TopCat.of X) (n + 2) s.simplex z) ?_ hz
  intro i y
  rw [← apply_δ]
  rw [compHom_δ (h.relativeStep hA) (h.relativeStep_isNext hA) (n + 1) i s.simplex y t]
  obtain ⟨τ, hτ⟩ := s.face_lift i
  rw [← hτ, compHom_incl, sngEquiv_incl]

/-- The actual homotopy of cube-pair maps supplied by coherent normalization. -/
def normalizationHomotopy (h : IsNConnectedPair (n + 1) X A)
    (hA : A.Nonempty) (s : PairNormalizedSimplex n (TopCat.of X) A) :
    ContinuousMap.HomotopyRel s.cubeMap
      ((h.normalization hA).normalizeRelativeTopSimplex s.simplex).cubeMap
      (Cube.boundary (Fin (n + 2))) where
  toFun ty := compHom (h.relativeStep hA) (n + 2) s.simplex
    (cubeHomeoSimplex (n + 2) ty.2, ty.1)
  continuous_toFun := (compHom (h.relativeStep hA) (n + 2) s.simplex).continuous.comp
    (((cubeHomeoSimplex (n + 2)).continuous.comp continuous_snd).prodMk continuous_fst)
  map_zero_left y := compHom_zero (h.relativeStep hA) (n + 2) s.simplex
    (cubeHomeoSimplex (n + 2) y)
  map_one_left y := by
    change compHom (h.relativeStep hA) (n + 2) s.simplex
      (cubeHomeoSimplex (n + 2) y, 1) =
      sngEquiv (TopCat.of X) (n + 2) ((h.normalization hA).ρ (n + 2) s.simplex)
        (cubeHomeoSimplex (n + 2) y)
    rw [h.normalization_rho]
    exact (sngEquiv_defRho (h.relativeStep hA) (n + 2) s.simplex _).symm
  prop' t y hy := s.normalizationCompHom_boundary h hA _
    (cubeHomeoSimplex_mem_bdry _ y hy) t

/-- In particular normalization does not change the free homotopy class of
this concrete map of pairs. -/
theorem normalization_homotopicWith (h : IsNConnectedPair (n + 1) X A)
    (hA : A.Nonempty) (s : PairNormalizedSimplex n (TopCat.of X) A) :
    s.cubeMap.HomotopicWith
      ((h.normalization hA).normalizeRelativeTopSimplex s.simplex).cubeMap
      (Cube.IsMapOfPairs X A) := by
  let H := s.normalizationHomotopy h hA
  refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
  intro t y hy
  change H.curry t y ∈ A
  rw [H.prop t y hy]
  exact s.cubeMap_isMapOfPairs y hy

end PairNormalizedSimplex
end Submission
