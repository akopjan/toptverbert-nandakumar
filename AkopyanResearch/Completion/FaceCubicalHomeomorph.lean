module

public import AkopyanResearch.QuadraticArrangement
public import AkopyanResearch.Completion.CubicalHomotopyRectification

/-!
# A boundary-preserving cubical model for every simplex face

The already verified radial ball homeomorphisms identify the actual face
simplex with a cube of dimension `card S - 1`, including singleton faces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FaceCubicalHomeomorph

open AkopyanQuadratic CubicalHomotopyRectification
open scoped unitInterval Topology

def intervalCube (n : ℕ) : Domain n ≃ₜ UnitCube n where
  toFun x := ⟨fun i => (x i : ℝ), fun i => (x i).property⟩
  invFun x i := ⟨x.val i, x.property i⟩
  left_inv x := by rfl
  right_inv x := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_pi fun i =>
    Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _

def cubeBall (n : ℕ) : Domain n ≃ₜ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  (intervalCube n).trans (cubeHomeoBall n)

theorem cube_boundary_iff (n : ℕ) (x : Domain n) :
    x ∈ Cube.boundary (Fin n) ↔ ‖(cubeBall n x).val‖ = 1 := by
  rw [show cubeBall n x = cubeHomeoBall n (intervalCube n x) from rfl,
    cubeHomeoBall_norm_eq_one_iff]
  change (∃ j : Fin n, x j = 0 ∨ x j = 1) ↔ ∃ j : Fin n, (x j : ℝ) = 0 ∨ (x j : ℝ) = 1
  simp only [← Subtype.coe_inj, Set.Icc.coe_zero, Set.Icc.coe_one]

def faceCube (S : Finset (Fin 15)) (hS : S.Nonempty) :
    FaceSimplex S ≃ₜ Domain (S.card - 1) :=
  (faceSimplexHomeoBall S hS).trans (cubeBall (S.card - 1)).symm

theorem face_boundary_iff (S : Finset (Fin 15)) (hS : S.Nonempty) (z : FaceSimplex S) :
    faceCube S hS z ∈ Cube.boundary (Fin (S.card - 1)) ↔ ∃ i ∈ S, z.1.val i = 0 := by
  rw [cube_boundary_iff]
  change ‖((cubeBall (S.card - 1)) ((cubeBall (S.card - 1)).symm
    (faceSimplexHomeoBall S hS z))).val‖ = 1 ↔ _
  rw [Homeomorph.apply_symm_apply, faceSimplexHomeoBall_norm_eq_one_iff]

def faceBoundaryCube (S : Finset (Fin 15)) (hS : S.Nonempty) :
    FaceBoundary S ≃ₜ Boundary (S.card - 1) where
  toFun z := ⟨faceCube S hS z.val, (face_boundary_iff S hS z.val).mpr z.property⟩
  invFun z := ⟨(faceCube S hS).symm z.val, by
    apply (face_boundary_iff S hS _).mp
    simpa only [Homeomorph.apply_symm_apply] using z.property⟩
  left_inv z := by apply Subtype.ext; exact (faceCube S hS).symm_apply_apply z.val
  right_inv z := by apply Subtype.ext; exact (faceCube S hS).apply_symm_apply z.val
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem faceBoundaryCube_val (S : Finset (Fin 15)) (hS : S.Nonempty)
    (z : FaceBoundary S) :
    (faceBoundaryCube S hS z).val = faceCube S hS z.val := rfl

@[simp] theorem faceBoundaryCube_symm_val (S : Finset (Fin 15)) (hS : S.Nonempty)
    (z : Boundary (S.card - 1)) :
    ((faceBoundaryCube S hS).symm z).val = (faceCube S hS).symm z.val := rfl

end AkopyanResearch.FaceCubicalHomeomorph
