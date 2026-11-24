module

public import AkopyanResearch.Completion.PathProductCoordinates
public import AkopyanResearch.Completion.FiniteLoopModelHomology
public import AkopyanResearch.Completion.LoopSphereHomology

/-!
# Homology of path fibers in finite products of thirteen-spheres

The endpoints may be arbitrary. Explicit changes of endpoint and sphere
coordinates reduce each factor to the checked based loop model. The
degree-twelve isomorphism is induced by the actual path coordinates.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.Sphere13FibreHomology

open CategoryTheory CategoryTheory.Limits ContinuousMap ProductSphereKernel

abbrev Sphere := LoopSphereCover.Sphere.{0} 12
abbrev Loop := LoopSphereCover.Fibre.{0} 12
abbrev Coefficients := AddCommGrpCat.of ℤ

def toCommonPath (x : Sphere) : Path x (LoopSphereCover.basepoint 12) := by
  letI : PathConnectedSpace Sphere := (ConnectivityTransport.sphere 12).pathConnected
  exact (PathConnectedSpace.joined x (LoopSphereCover.basepoint 12)).somePath

def pathModel {Y : Type} [TopologicalSpace Y] (e : Y ≃ₜ Sphere) (a b : Y) :
    Path a b ≃ₕ Loop :=
  (PathProductCoordinates.pathHomeomorph e a b).toHomotopyEquiv.trans
    ((PathFibreEquivalences.endpointEquiv (e a) (toCommonPath (e b))).trans
      ((PathFibreEquivalences.endpointLoopEquiv (toCommonPath (e a))).trans
        (LoopSphereCover.loopHomeomorph 12).symm.toHomotopyEquiv))

def fibreModel {Y : Type} [TopologicalSpace Y] (e : Y ≃ₜ Sphere) (a b : Y) :
    Submission.PathFibre Y a b ≃ₕ Loop :=
  (PathFibreEquivalences.pathFibreHomeomorph a b).toHomotopyEquiv.trans (pathModel e a b)

variable {ι : Type} [Fintype ι] {Y : ι → Type} [∀ j, TopologicalSpace (Y j)]
variable (e : ∀ j, Y j ≃ₜ Sphere) (a b : ∀ j, Y j)

def homologyIso (i : ℕ) :
    homology Coefficients i (TopCat.of (Submission.PathFibre (∀ j, Y j) a b)) ≅
      homology Coefficients i (TopCat.of (ι → Loop)) :=
  (homologyFunctor Coefficients i).mapIso
      (TopCat.isoOfHomeo (PathProductCoordinates.fibrePiHomeomorph a b)) ≪≫
    FiniteLoopModelHomology.homologyIso (fun j => fibreModel (e j) (a j) (b j)) i

include e in
theorem homology_vanish (i : ℕ) (hi : 0 < i) (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    IsZero (homology Coefficients i (TopCat.of (Submission.PathFibre (∀ j, Y j) a b))) :=
  (FiniteLoop13Homology.homology_vanish ι i hi hi₁₄ hne).of_iso (homologyIso e a b i)

def projection (j : ι) : C(Submission.PathFibre (∀ j, Y j) a b,
    Submission.PathFibre (Y j) (a j) (b j)) :=
  (FiniteLoopModelHomology.evaluation (Y := fun j => Submission.PathFibre (Y j) (a j) (b j)) j).comp
    ⟨PathProductCoordinates.fibrePiHomeomorph a b,
      (PathProductCoordinates.fibrePiHomeomorph a b).continuous⟩

def coordinatesIso :
    homology Coefficients 12 (TopCat.of (Submission.PathFibre (∀ j, Y j) a b)) ≅
      AddCommGrpCat.of (∀ j, ↥(homology Coefficients 12
        (TopCat.of (Submission.PathFibre (Y j) (a j) (b j))))) :=
  (homologyFunctor Coefficients 12).mapIso
      (TopCat.isoOfHomeo (PathProductCoordinates.fibrePiHomeomorph a b)) ≪≫
    FiniteLoopModelHomology.coordinatesIso (fun j => fibreModel (e j) (a j) (b j))

theorem coordinatesIso_apply
    (x : ↥(homology Coefficients 12 (TopCat.of (Submission.PathFibre (∀ j, Y j) a b)))) (j : ι) :
    (coordinatesIso e a b).hom x j =
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (projection a b j)) x := by
  change (homologyFunctor Coefficients 12).map
      (TopCat.ofHom (FiniteLoopModelHomology.evaluation
        (Y := fun j => Submission.PathFibre (Y j) (a j) (b j)) j))
      (((homologyFunctor Coefficients 12).mapIso
        (TopCat.isoOfHomeo (PathProductCoordinates.fibrePiHomeomorph a b))).hom x) = _
  have h : ((homologyFunctor Coefficients 12).mapIso
      (TopCat.isoOfHomeo (PathProductCoordinates.fibrePiHomeomorph a b))).hom ≫
      (homologyFunctor Coefficients 12).map
        (TopCat.ofHom (FiniteLoopModelHomology.evaluation
          (Y := fun j => Submission.PathFibre (Y j) (a j) (b j)) j)) =
        (homologyFunctor Coefficients 12).map (TopCat.ofHom (projection a b j)) := by
    change (homologyFunctor Coefficients 12).map _ ≫ (homologyFunctor Coefficients 12).map _ = _
    rw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h x

def componentHomologyIso (j : ι) :
    homology Coefficients 12 (TopCat.of (Submission.PathFibre (Y j) (a j) (b j))) ≅
      AddCommGrpCat.of ℤ :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (fibreModel (e j) (a j) (b j)) Coefficients 12 ≪≫
    LoopSphereHomology.fibreDiagonalIso Coefficients 12 (by decide)

end AkopyanResearch.Sphere13FibreHomology
