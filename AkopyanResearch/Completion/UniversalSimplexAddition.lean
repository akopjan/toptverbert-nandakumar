module

public import AkopyanResearch.Completion.ContractibleSimplexAddition
public import AkopyanResearch.Completion.UniversalSimplexBoundary
public import AkopyanResearch.Completion.SimplexSkeletonConnectivity

/-!
# Homotopy addition for arbitrary simply connected pairs

First prove the relation in the universal pair consisting of a simplex
and its codimension-two skeleton. The ambient simplex is contractible
and the skeleton has the required connectivity, so its ordinary relative
Hurewicz map is injective. Naturality of free relative classes then
transports the relation to any pair with simply connected subspace.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.deprecated false
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

namespace AkopyanResearch.UniversalSimplexAddition

open Submission RelativeSimplexBoundary RelativeHurewiczDescent
open SimplexSkeletonRetraction

variable (n : ℕ)

theorem universal_relation (a : UniversalSkeleton n) :
    letI : PathConnectedSpace (UniversalSkeleton n) :=
      (SimplexSkeletonConnectivity.isNConnected_skeleton (n + 1)).pathConnected
    ∑ i : Fin (n + 5), ((-1 : ℤ) ^ (i : ℕ)) •
      Additive.ofMul (simplexClass a ((universalBoundary n).face i)) = 0 := by
  let : ContractibleSpace (I^Fin (n + 4)) := contractibleSpace_cube (n + 4)
  let : ContractibleSpace (UniversalSpace n) :=
    (cubeHomeoSimplex (n + 4)).symm.contractibleSpace
  exact alternating_class_eq_zero_of_contractible
    (n := n) (X := TopCat.of (UniversalSpace n)) (A := UniversalSkeleton n) a
    (SimplexSkeletonConnectivity.isNConnected_skeleton (n + 1)) (universalBoundary n)

variable {X : Type} [TopologicalSpace X] {A : Set X}
variable (a : A) [PathConnectedSpace A]
variable (hπ : Subsingleton (HomotopyGroup.Pi 1 A a))
include hπ

theorem all_pi1_subsingleton (b : A) : Subsingleton (HomotopyGroup.Pi 1 A b) := by
  let e := (Submission.nonempty_mulEquiv_of_pathConnectedSpace (N := Fin 1) a b).some
  let : Subsingleton (HomotopyGroup.Pi 1 A a) := hπ
  exact e.symm.injective.subsingleton

/-- The full alternating face relation for a map of a simplex whose
codimension-two skeleton lies in a simply connected subspace. -/
theorem alternating_class_eq_zero (s : Boundary (n + 1) (TopCat.of X) A) :
    ∑ i : Fin (n + 5), ((-1 : ℤ) ^ (i : ℕ)) •
      Additive.ofMul (simplexClass a (s.face i)) = 0 := by
  let hK := SimplexSkeletonConnectivity.isNConnected_skeleton (n + 1)
  let : PathConnectedSpace (UniversalSkeleton n) := hK.pathConnected
  let b : UniversalSkeleton n := Classical.choice hK.nonempty
  let F := sngEquiv (TopCat.of X) (n + 4) s.simplex
  let G := FreeRelativeOperations.postcomposeHom (n := n + 1) b F (maps_skeleton s) a
    (all_pi1_subsingleton a hπ)
  have hface (i : Fin (n + 5)) :
      G (simplexClass b ((universalBoundary n).face i)) =
        simplexClass a (s.face i) := by
    have he : F.comp ((universalBoundary n).face i).cubeMap = (s.face i).cubeMap := by
      apply ContinuousMap.ext
      intro y
      change sngEquiv (TopCat.of X) (n + 4) s.simplex
          (faceMap i (cubeHomeoSimplex (n + 3) y)) =
        sngEquiv (TopCat.of X) (n + 3) (s.face i).simplex
          (cubeHomeoSimplex (n + 3) y)
      rw [← apply_δ, ← s.face_simplex i]
    have h := FreeRelativeOperations.postcomposeHom_classOf b F (maps_skeleton s) a
      (all_pi1_subsingleton a hπ) ((universalBoundary n).face i).cubeMap
      ((universalBoundary n).face i).cubeMap_isMapOfPairs
    simpa only [G, simplexClass, he] using h
  have h := congrArg G.toAdditive (universal_relation n b)
  rw [map_sum, map_zero] at h
  have hface' (i : Fin (n + 5)) :
      G.toAdditive (Additive.ofMul (simplexClass b ((universalBoundary n).face i))) =
        Additive.ofMul (simplexClass a (s.face i)) :=
    congrArg Additive.ofMul (hface i)
  simpa only [map_zsmul, hface'] using h

/-- Coherent relative normalization satisfies the geometric relation
needed for descent from chains to relative homotopy. -/
theorem normalized_boundary_relation (h : IsNConnectedPair (n + 2) X A) :
    RelativeHurewiczDescent.BoundaryRelation a h := by
  intro s
  let c := h.normalization ⟨a, a.property⟩
  let b : Boundary (n + 1) (TopCat.of X) A := {
    simplex := c.ρ (n + 4) s
    face := fun i => c.normalizeRelativeTopSimplex ((Sng (TopCat.of X)).δ i s)
    face_simplex := fun i => c.ρ_δ i s }
  exact alternating_class_eq_zero n a hπ b

/-- The first relative Hurewicz map is injective for a simply connected
subspace and an appropriately connected pair. -/
theorem relativeHurewicz_injective (h : IsNConnectedPair (n + 2) X A) :
    Function.Injective (simplexRelativeHurewicz (n + 1) A a) :=
  simplexRelativeHurewicz_injective_of_boundaryRelation a hπ h
    (normalized_boundary_relation n a hπ h)

/-- The homology-to-homotopy step used in the mapping-cylinder induction. -/
theorem subsingleton_relativeHomotopy (h : IsNConnectedPair (n + 2) X A)
    (hz : IsZero (HrelSet (Y := TopCat.of X) (n + 3) A)) :
    Subsingleton (π_rel (n + 3) X A a) :=
  subsingleton_relativeHomotopy_of_boundaryRelation a hπ h
    (normalized_boundary_relation n a hπ h) hz

end AkopyanResearch.UniversalSimplexAddition
