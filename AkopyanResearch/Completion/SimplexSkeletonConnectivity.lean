module

public import AkopyanResearch.Completion.SimplexSkeletonRetraction
public import AkopyanResearch.Completion.PuncturedSphereHomeomorphism
public import AkopyanResearch.Completion.FinitePointConnectivity
public import AkopyanResearch.Completion.ConnectivityTransport
public import Submission.Hurewicz.SimplexHEP

/-!
# Connectivity of the codimension-two skeleton of a simplex

The simplex boundary with its finitely many facet barycentres deleted is
homeomorphic, by a boundary chart and stereographic projection, to a finite
point complement in Euclidean space. The explicit barycentric retraction
onto the codimension-two skeleton therefore gives its actual connectivity.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.deprecated false
noncomputable section

namespace AkopyanResearch.SimplexSkeletonConnectivity
open SimplexSkeletonRetraction
open scoped Topology
open Metric

/-- The actual simplex boundary, with the facet barycentres viewed in it. -/
def boundaryCenters (n : ℕ) (i : Index n) : boundary n :=
  ⟨faceCenter n i, ⟨i, faceCenter_same n i⟩⟩

/-- Removing these points in the boundary is the already constructed domain
of the skeleton retraction. -/
def puncturedBoundaryHomeomorph (n : ℕ) :
    puncturedBoundary n ≃ₜ
      PuncturedSphereHomeomorphism.PointComplement (boundaryCenters n) where
  toFun x := ⟨⟨x.val, x.property.1⟩, fun i hi =>
    x.property.2 i (congrArg Subtype.val hi)⟩
  invFun x := ⟨x.val.val, x.val.property, fun i hi => x.property i (Subtype.ext hi)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The radial simplex chart identifies its boundary with the ordinary sphere. -/
def boundarySphereHomeomorph (n : ℕ) :
    boundary n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (Submission.bdryHomeoDiskBoundary (n + 1)).trans Homeomorph.ulift

/-- The finitely many chart images of the facet barycentres. -/
def sphereCenters (n : ℕ) (i : Index n) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  boundarySphereHomeomorph n (boundaryCenters n i)

/-- After deleting one chart pole, all remaining punctures are literal points
of an `n`-dimensional Euclidean space. -/
def puncturedBoundaryEuclideanHomeomorph (n : ℕ) :
    puncturedBoundary n ≃ₜ
      PuncturedSphereHomeomorphism.PointComplement
        (PuncturedSphereHomeomorphism.projectedPoints (sphereCenters n) 0) :=
  (puncturedBoundaryHomeomorph n).trans
    ((PuncturedSphereHomeomorphism.transport (boundarySphereHomeomorph n)
      (boundaryCenters n)).trans
        (PuncturedSphereHomeomorphism.sphereComplementHomeomorph (sphereCenters n) 0))

/-- The punctured boundary of an `(n+3)`-simplex is `n`-connected. -/
theorem isNConnected_puncturedBoundary (n : ℕ) :
    Submission.IsNConnected n (puncturedBoundary (n + 2)) := by
  let p := PuncturedSphereHomeomorphism.projectedPoints (sphereCenters (n + 2)) 0
  have hp : Submission.IsNConnected n (FinitePointConnectivity.PointComplement p) := by
    let : PathConnectedSpace (FinitePointConnectivity.PointComplement p) :=
      FinitePointConnectivity.pathConnectedSpace_pointComplement p (by
        rw [finrank_euclideanSpace_fin]
        omega)
    refine ⟨inferInstance, inferInstance, fun k hk b => ?_⟩
    exact FinitePointConnectivity.subsingleton_homotopyGroup p (k + 1) (by
      rw [finrank_euclideanSpace_fin]
      omega) b
  exact ConnectivityTransport.homeomorph
    (puncturedBoundaryEuclideanHomeomorph (n + 2)).symm hp

/-- The codimension-two skeleton of an `(n+3)`-simplex is `n`-connected. -/
theorem isNConnected_skeleton (n : ℕ) :
    Submission.IsNConnected n (skeleton (n + 2)) :=
  ConnectivityTransport.retract (inclusionMap (n + 2)) (retractionMap (n + 2))
    (retraction_identity (n + 2)) (isNConnected_puncturedBoundary n)

end AkopyanResearch.SimplexSkeletonConnectivity
