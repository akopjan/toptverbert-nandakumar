module

public import AkopyanResearch.Completion.SphereConnectivity
public import AkopyanResearch.Completion.SphereHomology
public import AkopyanResearch.Completion.OriginalJoinBridge
public import AkopyanResearch.Completion.PairCofiberSection

/-!
# Homotopy and homology of the actual representation targets

The single target is the original unit sphere in `Rep10`. The pair target
is the original one-point compactification of the thirteen-dimensional
representation. Explicit homeomorphisms identify them with the ordinary
nine- and thirteen-spheres used by the homology calculation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.RepresentationSphereInvariants

open CategoryTheory CategoryTheory.Limits
open scoped Topology.Homotopy

def singleHomeomorph : OriginalJoinBridge.Target ≃ₜ TopCat.sphere.{0} 9 :=
  Homeomorph.ulift.symm

set_option synthInstance.maxHeartbeats 200000 in
def pairEuclideanHomeomorph :
    OnePoint PairTarget ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 14)) 1 := by
  let e : PairTarget ≃L[ℝ] EuclideanSpace ℝ (Fin 13) :=
    (LinearEquiv.ofFinrankEq PairTarget (EuclideanSpace ℝ (Fin 13))
      (by rw [finrank_PairTarget, finrank_euclideanSpace_fin])).toContinuousLinearEquiv
  exact e.toHomeomorph.onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]))

def pairHomeomorph : OnePoint PairTarget ≃ₜ TopCat.sphere.{0} 13 :=
  pairEuclideanHomeomorph.trans Homeomorph.ulift.symm

theorem single_pi_vanish (n : ℕ) (hn : n ≤ 8) (b : OriginalJoinBridge.Target) :
    Subsingleton (HomotopyGroup.Pi n OriginalJoinBridge.Target b) :=
  SphereConnectivity.sphere_pi_vanish Rep10 n (by
    rw [finrank_euclideanSpace_fin]
    omega) b

theorem single_pathConnected : PathConnectedSpace OriginalJoinBridge.Target :=
  SphereConnectivity.sphere_pathConnected Rep10 (by rw [finrank_euclideanSpace_fin]; decide)

theorem pair_pi_vanish (n : ℕ) (hn : n ≤ 12) (b : OnePoint PairTarget) :
    Subsingleton (HomotopyGroup.Pi n (OnePoint PairTarget) b) := by
  let e := pairEuclideanHomeomorph
  apply SphereConnectivity.pi_subsingleton_of_retract
    (⟨e, e.continuous⟩ : C(OnePoint PairTarget, _))
    (⟨e.symm, e.symm.continuous⟩ : C(_, OnePoint PairTarget))
    (by ext x; exact e.symm_apply_apply x) n b
  exact SphereConnectivity.sphere_pi_vanish (EuclideanSpace ℝ (Fin 14)) n
    (by rw [finrank_euclideanSpace_fin]; omega) (e b)

theorem pair_pathConnected : PathConnectedSpace (OnePoint PairTarget) := by
  let : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 14)) 1) :=
    SphereConnectivity.sphere_pathConnected (EuclideanSpace ℝ (Fin 14))
      (by rw [finrank_euclideanSpace_fin]; decide)
  exact pairEuclideanHomeomorph.symm.surjective.pathConnectedSpace
    pairEuclideanHomeomorph.symm.continuous

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
variable (R : C)

def singleHomologyIso :
    ProductSphereKernel.homology R 9 (TopCat.of OriginalJoinBridge.Target) ≅ R :=
  (ProductSphereKernel.homologyFunctor R 9).mapIso (TopCat.isoOfHomeo singleHomeomorph) ≪≫
    SphereHomology.diagonalIso R 9 (by decide)

def pairHomologyIso :
    ProductSphereKernel.homology R 13 (TopCat.of (OnePoint PairTarget)) ≅ R :=
  (ProductSphereKernel.homologyFunctor R 13).mapIso (TopCat.isoOfHomeo pairHomeomorph) ≪≫
    SphereHomology.diagonalIso R 13 (by decide)

def pairReducedHomologyIso :
    (Hatcher.Reduced.homologyFunctor R 13).obj (TopCat.of (OnePoint PairTarget)) ≅ R :=
  (Hatcher.Reduced.homologyFunctor R 13).mapIso (TopCat.isoOfHomeo pairHomeomorph) ≪≫
    SphereHomology.reducedDiagonalIso R 13 (by decide)

theorem single_homology_vanish (i : ℕ) (hi : 0 < i) (hne : i ≠ 9) :
    IsZero (ProductSphereKernel.homology R i (TopCat.of OriginalJoinBridge.Target)) :=
  (SphereHomology.isZero_offDiagonal R 9 i hi hne).of_iso
    ((ProductSphereKernel.homologyFunctor R i).mapIso (TopCat.isoOfHomeo singleHomeomorph))

theorem pair_homology_vanish (i : ℕ) (hi : 0 < i) (hne : i ≠ 13) :
    IsZero (ProductSphereKernel.homology R i (TopCat.of (OnePoint PairTarget))) :=
  (SphereHomology.isZero_offDiagonal R 13 i hi hne).of_iso
    ((ProductSphereKernel.homologyFunctor R i).mapIso (TopCat.isoOfHomeo pairHomeomorph))

end AkopyanResearch.RepresentationSphereInvariants
