module

public import Submission.Homotopy.DiscTrivialisation
public import AkopyanResearch.Completion.ProductHemisphereCover

/-!
# An actual Mayer--Vietoris cover of the based path space of a sphere

The inverse images of the two deleted-pole charts form an open cover of
the contractible path space. Trivialisation over either chart identifies
its inverse image with the loop fibre. The intersection is equivalent to
the product of that fibre with the equator sphere. The northern inclusion
is identified with the first product projection.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.LoopSphereCover

open ContinuousMap Hatcher.MayerVietoris

universe w v

def affineContraction {T : Type w} [TopologicalSpace T]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : T ≃ₜ V) (a : T) : Submission.ContractionData T a where
  path b := {
    toFun t := e.symm ((1 - (t : ℝ)) • e a + (t : ℝ) • e b)
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp }
  continuous_uncurry := by
    change Continuous (fun p : T × unitInterval =>
      e.symm ((1 - (p.2 : ℝ)) • e a + (p.2 : ℝ) • e p.1))
    fun_prop
  path_base := by
    ext t
    change e.symm ((1 - (t : ℝ)) • e a + (t : ℝ) • e a) = a
    rw [← add_smul, sub_add_cancel, one_smul, e.symm_apply_apply]

abbrev Sphere (n : ℕ) : Type w := TopCat.sphere.{w} (n + 1)
abbrev basepoint (n : ℕ) : Sphere.{w} n := ProductHemisphereCover.commonPoint.{w} n
abbrev Total (n : ℕ) : Type w := Submission.PathSpace (Sphere.{w} n) (basepoint.{w} n)
abbrev Fibre (n : ℕ) : Type w :=
  Submission.PathFibre (Sphere.{w} n) (basepoint.{w} n) (basepoint.{w} n)

def northBase (n : ℕ) : Hatcher.Sphere.northNeighborhood.{w} n :=
  ⟨basepoint.{w} n, Hatcher.Sphere.northHemisphere_subset_northNeighborhood.{w} n
    (ProductHemisphereCover.northPoint.{w} n).property⟩

def southBase (n : ℕ) : Hatcher.Sphere.southNeighborhood.{w} n :=
  ⟨basepoint.{w} n, Hatcher.Sphere.southHemisphere_subset_southNeighborhood.{w} n
    (ProductHemisphereCover.southPoint.{w} n).property⟩

def northContraction (n : ℕ) :
    Submission.ContractionData (Hatcher.Sphere.northNeighborhood.{w} n) (northBase n) :=
  affineContraction (Hatcher.Sphere.northStereographicHomeomorph n) (northBase n)

def southContraction (n : ℕ) :
    Submission.ContractionData (Hatcher.Sphere.southNeighborhood.{w} n) (southBase n) :=
  affineContraction (Hatcher.Sphere.southStereographicHomeomorph n) (southBase n)

abbrev North (n : ℕ) : Set (Total.{w} n) :=
  Submission.ev₁ (Sphere n) (basepoint n) ⁻¹' Hatcher.Sphere.northNeighborhood n

abbrev South (n : ℕ) : Set (Total.{w} n) :=
  Submission.ev₁ (Sphere n) (basepoint n) ⁻¹' Hatcher.Sphere.southNeighborhood n

theorem base_cover (n : ℕ) :
    Hatcher.Sphere.northNeighborhood.{w} n ∪ Hatcher.Sphere.southNeighborhood n = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ Hatcher.Sphere.northHemisphere n ∪ Hatcher.Sphere.southHemisphere n := by
    rw [Hatcher.Sphere.hemisphere_union]
    trivial
  exact hx.elim
    (fun h => Or.inl (Hatcher.Sphere.northHemisphere_subset_northNeighborhood n h))
    (fun h => Or.inr (Hatcher.Sphere.southHemisphere_subset_southNeighborhood n h))

theorem isOpen_north (n : ℕ) : IsOpen (North.{w} n) :=
  (Hatcher.Sphere.isOpen_northNeighborhood n).preimage
    (Submission.ev₁ (Sphere n) (basepoint n)).continuous

theorem isOpen_south (n : ℕ) : IsOpen (South.{w} n) :=
  (Hatcher.Sphere.isOpen_southNeighborhood n).preimage
    (Submission.ev₁ (Sphere n) (basepoint n)).continuous

theorem cover (n : ℕ) : Hatcher.Excision.CoverCondition
    (X := TopCat.of (Total.{w} n)) (North n) (South n) where
  union_interior := by
    rw [(isOpen_north n).interior_eq, (isOpen_south n).interior_eq]
    change _ ⁻¹' _ ∪ _ ⁻¹' _ = Set.univ
    rw [← Set.preimage_union, base_cover, Set.preimage_univ]

def northEquiv (n : ℕ) : North.{w} n ≃ₕ Fibre n := by
  let : ContractibleSpace (Hatcher.Sphere.northNeighborhood.{w} n) :=
    (northContraction n).contractibleSpace
  exact (Submission.homotopyEquivOverDisc (x₀ := basepoint n)
    (northContraction n) (Set.Subset.refl _)).trans
      (ProductHemisphereCover.projectionHomotopyEquiv (Fibre n) (northBase n))

def southEquiv (n : ℕ) : South.{w} n ≃ₕ Fibre n := by
  let : ContractibleSpace (Hatcher.Sphere.southNeighborhood.{w} n) :=
    (southContraction n).contractibleSpace
  exact (Submission.homotopyEquivOverDisc (x₀ := basepoint n)
    (southContraction n) (Set.Subset.refl _)).trans
      (ProductHemisphereCover.projectionHomotopyEquiv (Fibre n) (southBase n))

def intersectionOverHomeomorph (n : ℕ) :
    ↑(North.{w} n ∩ South n) ≃ₜ
      Submission.PathSpaceOver (Sphere n) (basepoint n) (Hatcher.Sphere.neighborhoodOverlap n) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def overlapSphereEquiv (n : ℕ) :
    Hatcher.Sphere.neighborhoodOverlap.{w} n ≃ₕ (TopCat.sphere.{w} n : Type w) :=
  (Hatcher.Sphere.equatorStrongDeformationRetract n).toHomotopyEquiv.trans
    (Hatcher.Sphere.equatorSphereHomeomorph n).toHomotopyEquiv

def intersectionEquiv (n : ℕ) :
    ↑(North.{w} n ∩ South n) ≃ₕ (Fibre n × (TopCat.sphere.{w} n : Type w)) :=
  (intersectionOverHomeomorph n).toHomotopyEquiv.trans
    ((Submission.homotopyEquivOverDisc (x₀ := basepoint n)
      (northContraction n) Set.inter_subset_left).trans
        ((ContinuousMap.HomotopyEquiv.refl (Fibre n)).prodCongr (overlapSphereEquiv n)))

/-- The northern overlap inclusion is the product projection under the
actual trivialisation, before passing to homology. -/
theorem north_intersection_projection (n : ℕ) (x : ↑(North.{w} n ∩ South n)) :
    northEquiv n ⟨x.val, x.property.1⟩ = (intersectionEquiv n x).1 := rfl

/-- The fibre used in the calculation is homeomorphic to the usual
space of based loops with its compact-open topology. -/
def loopHomeomorph (n : ℕ) :
    Fibre.{w} n ≃ₜ Path (basepoint n) (basepoint n) :=
  Submission.fibreEv₁Homeomorph (Sphere n) (basepoint n)

end AkopyanResearch.LoopSphereCover
