module

public import AkopyanResearch.Completion.MappingPathPair
public import AkopyanResearch.Completion.PairBoundaryComparison
public import AkopyanResearch.Completion.HomotopyPullbackCoordinates
public import Hatcher.Singular.Homology

/-!
# Homology comparison through the unrestricted mapping-path pair

Path reversal identifies the fixed-source subspace inclusion with the
literal path-fiber inclusion used in the sphere-source calculation. The
remaining relative comparison is transported through the natural pair
boundary maps, with all hypotheses stated on the actual homology maps.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingPathHomology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel ContinuousMap
open MappingPathReplacement MappingPathPair

universe w v u
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y₀ : Y)

def fibrePullbackHomeomorph : (pair f y₀).snd ≃ₜ HomotopyPullback.Space f y₀ :=
  (fibreHomeomorph f y₀).trans (HomotopyFiberFibration.pullbackHomeomorph f y₀)

def basedFibreReverse (x : X) : (basedPair f y₀ x).snd ≃ₜ Submission.PathFibre Y y₀ (f x) :=
  (basedFibreHomeomorph f y₀ x).trans
    ((PathFibreEquivalences.pathFibreHomeomorph (f x) y₀).trans
      ((PathFibreEquivalences.reverseHomeomorph (f x) y₀).trans
        (PathFibreEquivalences.pathFibreHomeomorph y₀ (f x)).symm))

theorem basedFibreInclusion_reversal (x : X) :
    (⟨fibrePullbackHomeomorph f y₀, (fibrePullbackHomeomorph f y₀).continuous⟩ : C(_, _)).comp
      (basedFibreInclusion f y₀ x) =
    (HomotopyPullbackCoordinates.fibreInclusion f x y₀).comp
      ⟨basedFibreReverse f y₀ x, (basedFibreReverse f y₀ x).continuous⟩ := by
  ext γ
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  ext t
  rfl

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (R : C)

theorem ambient_homology_vanish (i : ℕ) (h : IsZero (homology R i (TopCat.of X))) :
    IsZero (homology R i (pair f y₀).fst) :=
  h.of_iso (Hatcher.Singular.homologyIsoOfHomotopyEquiv (projectionEquiv f) R i)

theorem based_ambient_homology_vanish (x : X) (i : ℕ) (hi : i ≠ 0) :
    IsZero (homology R i (basedPair f y₀ x).fst) := by
  let e : Submission.PathSpace Y (f x) ≃ₕ PUnit.{w + 1} := (ContractibleSpace.hequiv _ _).some
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C i R
    (TopCat.of PUnit.{w + 1}) hi).of_iso (Hatcher.Singular.homologyIsoOfHomotopyEquiv e R i)

theorem basedFibreInclusion_isIso (x : X) (i : ℕ)
    (h : IsIso ((homologyFunctor R i).map
      (TopCat.ofHom (HomotopyPullbackCoordinates.fibreInclusion f x y₀)))) :
    IsIso ((homologyFunctor R i).map (TopCat.ofHom (basedFibreInclusion f y₀ x))) := by
  let eA : (basedPair f y₀ x).snd ≅ TopCat.of (Submission.PathFibre Y y₀ (f x)) :=
    TopCat.isoOfHomeo (basedFibreReverse f y₀ x)
  let eB : (pair f y₀).snd ≅ TopCat.of (HomotopyPullback.Space f y₀) :=
    TopCat.isoOfHomeo (fibrePullbackHomeomorph f y₀)
  have heq : (homologyFunctor R i).map (TopCat.ofHom (basedFibreInclusion f y₀ x)) ≫
      (homologyFunctor R i).map eB.hom =
      (homologyFunctor R i).map eA.hom ≫ (homologyFunctor R i).map
        (TopCat.ofHom (HomotopyPullbackCoordinates.fibreInclusion f x y₀)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  apply (isIso_comp_right_iff _ ((homologyFunctor R i).map eB.hom)).mp
  rw [heq]
  infer_instance

theorem basedPairInclusion_isIso (x : X) (i : ℕ) (hi : i ≠ 0)
    (hXhi : IsZero (homology R (i + 1) (TopCat.of X)))
    (hXlo : IsZero (homology R i (TopCat.of X)))
    (h : IsIso ((homologyFunctor R i).map
      (TopCat.ofHom (HomotopyPullbackCoordinates.fibreInclusion f x y₀)))) :
    IsIso ((Hatcher.Relative.homologyFunctor R (i + 1)).map (basedPairInclusion f y₀ x)) := by
  apply (PairBoundaryComparison.relative_isIso_iff_subspace R i
    (based_ambient_homology_vanish f y₀ R x (i + 1) (by omega))
    (based_ambient_homology_vanish f y₀ R x i hi) (basedPairInclusion f y₀ x)
    (ambient_homology_vanish f y₀ R (i + 1) hXhi)
    (ambient_homology_vanish f y₀ R i hXlo)).mpr
  exact basedFibreInclusion_isIso f y₀ R x i h

theorem endpointPair_isIso (x : X) (i : ℕ)
    (hI : IsIso ((Hatcher.Relative.homologyFunctor R i).map (basedPairInclusion f y₀ x)))
    (hE : IsIso ((Hatcher.Relative.homologyFunctor R i).map (basedEndpointPair f y₀ x))) :
    IsIso ((Hatcher.Relative.homologyFunctor R i).map (endpointPair f y₀)) := by
  apply (isIso_comp_left_iff
    ((Hatcher.Relative.homologyFunctor R i).map (basedPairInclusion f y₀ x)) _).mp
  rw [← Functor.map_comp, basedEndpoint_factor]
  exact hE

theorem sourceFibreInclusion_isIso (A : Set X) (hA : ∀ x ∈ A, f x = y₀)
    (i : ℕ) (hXhi : IsZero (homology R (i + 1) (TopCat.of X)))
    (hXlo : IsZero (homology R i (TopCat.of X)))
    (hO : IsIso ((Hatcher.Relative.homologyFunctor R (i + 1)).map (originalPairMap f y₀ A hA)))
    (hE : IsIso ((Hatcher.Relative.homologyFunctor R (i + 1)).map (endpointPair f y₀))) :
    IsIso ((homologyFunctor R i).map (TopCat.ofHom (sourceFibreInclusion f y₀ A hA))) := by
  have hI : IsIso ((Hatcher.Relative.homologyFunctor R (i + 1)).map (sourcePairMap f y₀ A hA)) := by
    apply (isIso_comp_right_iff _
      ((Hatcher.Relative.homologyFunctor R (i + 1)).map (endpointPair f y₀))).mp
    rw [← Functor.map_comp, originalPairMap_factor]
    exact hO
  exact (PairBoundaryComparison.relative_isIso_iff_subspace
    (P := sourcePair A) (Q := pair f y₀) R i hXhi hXlo
    (sourcePairMap f y₀ A hA)
    (ambient_homology_vanish f y₀ R (i + 1) hXhi)
    (ambient_homology_vanish f y₀ R i hXlo)).mp hI

end AkopyanResearch.MappingPathHomology
