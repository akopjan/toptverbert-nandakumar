module

public import AkopyanResearch.Completion.ContractibleSourcePullback
public import AkopyanResearch.Completion.LoopSphereCover

/-!
# A sphere-factor cover of an actual homotopy-fibre total space

For an arbitrary map `f : X × S^(n+1) → Y`, lift the two deleted-pole
charts to its path-fibration pullback. Both pieces are equivalent to the
pullback over the common equator point, and their overlap is equivalent
to its product with `S^n`. The equivalences preserve the common inclusion
up to specified homotopies.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.SphereSourceCover

open ContinuousMap HomotopyPullback
open LoopSphereCover (Sphere basepoint)

universe w
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {n : ℕ} (f : C(X × Sphere.{w} n, Y)) (y₀ : Y)

abbrev Total := Space f y₀
abbrev BaseSpace := Space (ContractibleSourcePullback.baseMap f (basepoint n)) y₀

abbrev Lifted (A : Set (Sphere.{w} n)) : Set (Total f y₀) :=
  {q | q.val.1.2 ∈ A}

def chartMap (A : Set (Sphere.{w} n)) : C(X × A, Y) :=
  f.comp ((ContinuousMap.id X).prodMap ⟨Subtype.val, continuous_subtype_val⟩)

def subsetHomeomorph (A : Set (Sphere.{w} n)) :
    Lifted f y₀ A ≃ₜ Space (chartMap f A) y₀ where
  toFun q := ⟨((q.val.val.1.1, ⟨q.val.val.1.2, q.property⟩), q.val.val.2), q.val.property⟩
  invFun q := ⟨⟨((q.val.1.1, q.val.1.2.val), q.val.2), q.property⟩, q.val.1.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

abbrev North : Set (Total f y₀) := Lifted f y₀ (Hatcher.Sphere.northNeighborhood n)
abbrev South : Set (Total f y₀) := Lifted f y₀ (Hatcher.Sphere.southNeighborhood n)

theorem isOpen_north : IsOpen (North f y₀) :=
  (Hatcher.Sphere.isOpen_northNeighborhood n).preimage
    (continuous_snd.comp (Submission.Pullback.fst f (Submission.ev₁ Y y₀)).continuous)

theorem isOpen_south : IsOpen (South f y₀) :=
  (Hatcher.Sphere.isOpen_southNeighborhood n).preimage
    (continuous_snd.comp (Submission.Pullback.fst f (Submission.ev₁ Y y₀)).continuous)

theorem cover : Hatcher.Excision.CoverCondition
    (X := TopCat.of (Total f y₀)) (North f y₀) (South f y₀) where
  union_interior := by
    rw [(isOpen_north f y₀).interior_eq, (isOpen_south f y₀).interior_eq]
    apply Set.eq_univ_iff_forall.mpr
    intro q
    exact Set.eq_univ_iff_forall.mp (LoopSphereCover.base_cover n) q.val.1.2

def unitEquiv : BaseSpace f y₀ ≃ₕ BaseSpace f y₀ :=
  HomotopyPullback.homotopyEquiv y₀
    (ContinuousMap.Homotopy.refl (ContractibleSourcePullback.baseMap f (basepoint n)))

def northRawEquiv : North f y₀ ≃ₕ BaseSpace f y₀ := by
  let : ContractibleSpace (Hatcher.Sphere.northNeighborhood.{w} n) :=
    (LoopSphereCover.northContraction n).contractibleSpace
  exact (subsetHomeomorph f y₀ (Hatcher.Sphere.northNeighborhood n)).toHomotopyEquiv.trans
    ((ContractibleSourcePullback.trivialisation
      (chartMap f (Hatcher.Sphere.northNeighborhood n))
      (LoopSphereCover.northBase n) (LoopSphereCover.northContraction n)
      (ContinuousMap.id _) y₀).trans
      (ProductHemisphereCover.projectionHomotopyEquiv (BaseSpace f y₀) (LoopSphereCover.northBase n)))

def southRawEquiv : South f y₀ ≃ₕ BaseSpace f y₀ := by
  let : ContractibleSpace (Hatcher.Sphere.southNeighborhood.{w} n) :=
    (LoopSphereCover.southContraction n).contractibleSpace
  exact (subsetHomeomorph f y₀ (Hatcher.Sphere.southNeighborhood n)).toHomotopyEquiv.trans
    ((ContractibleSourcePullback.trivialisation
      (chartMap f (Hatcher.Sphere.southNeighborhood n))
      (LoopSphereCover.southBase n) (LoopSphereCover.southContraction n)
      (ContinuousMap.id _) y₀).trans
      (ProductHemisphereCover.projectionHomotopyEquiv (BaseSpace f y₀) (LoopSphereCover.southBase n)))

def northEquiv : North f y₀ ≃ₕ BaseSpace f y₀ :=
  (northRawEquiv f y₀).trans (unitEquiv f y₀).symm

def southEquiv : South f y₀ ≃ₕ BaseSpace f y₀ :=
  (southRawEquiv f y₀).trans (unitEquiv f y₀).symm

def overlapRawEquiv :
    ↑(North f y₀ ∩ South f y₀) ≃ₕ (BaseSpace f y₀ × (TopCat.sphere.{w} n : Type w)) :=
  (subsetHomeomorph f y₀ (Hatcher.Sphere.neighborhoodOverlap n)).toHomotopyEquiv.trans
    ((ContractibleSourcePullback.trivialisation
      (chartMap f (Hatcher.Sphere.northNeighborhood n))
      (LoopSphereCover.northBase n) (LoopSphereCover.northContraction n)
      (ContinuousMap.inclusion Set.inter_subset_left) y₀).trans
      ((ContinuousMap.HomotopyEquiv.refl (BaseSpace f y₀)).prodCongr
        (LoopSphereCover.overlapSphereEquiv n)))

def overlapEquiv :
    ↑(North f y₀ ∩ South f y₀) ≃ₕ (BaseSpace f y₀ × (TopCat.sphere.{w} n : Type w)) :=
  (overlapRawEquiv f y₀).trans
    ((unitEquiv f y₀).symm.prodCongr (ContinuousMap.HomotopyEquiv.refl _))

theorem north_overlap_projection (q : ↑(North f y₀ ∩ South f y₀)) :
    northEquiv f y₀ ⟨q.val, q.property.1⟩ = (overlapEquiv f y₀ q).1 := rfl

def baseInclusion : C(BaseSpace f y₀, Total f y₀) where
  toFun q := ⟨((q.val.1, basepoint n), q.val.2), q.property⟩
  continuous_toFun := by fun_prop

def subsetBaseInclusion (A : Set (Sphere.{w} n)) (ha : basepoint n ∈ A) :
    C(BaseSpace f y₀, Lifted f y₀ A) :=
  ⟨fun q => ⟨baseInclusion f y₀ q, ha⟩, (baseInclusion f y₀).continuous.subtype_mk _⟩

abbrev northInclusion : C(BaseSpace f y₀, North f y₀) :=
  subsetBaseInclusion f y₀ _ (LoopSphereCover.northBase n).property

abbrev southInclusion : C(BaseSpace f y₀, South f y₀) :=
  subsetBaseInclusion f y₀ _ (LoopSphereCover.southBase n).property

abbrev overlapInclusion : C(BaseSpace f y₀, ↑(North f y₀ ∩ South f y₀)) :=
  subsetBaseInclusion f y₀ (Hatcher.Sphere.neighborhoodOverlap n)
    ⟨(LoopSphereCover.northBase n).property, (LoopSphereCover.southBase n).property⟩

theorem northRawEquiv_inclusion :
    (northRawEquiv f y₀).toFun.comp (northInclusion f y₀) = (unitEquiv f y₀).toFun := by
  ext q
  exact DFunLike.congr_fun
    (ContractibleSourcePullback.projection_baseInclusion
      (chartMap f (Hatcher.Sphere.northNeighborhood n))
      (LoopSphereCover.northBase n) (LoopSphereCover.northContraction n) y₀) q

theorem southRawEquiv_inclusion :
    (southRawEquiv f y₀).toFun.comp (southInclusion f y₀) = (unitEquiv f y₀).toFun := by
  ext q
  exact DFunLike.congr_fun
    (ContractibleSourcePullback.projection_baseInclusion
      (chartMap f (Hatcher.Sphere.southNeighborhood n))
      (LoopSphereCover.southBase n) (LoopSphereCover.southContraction n) y₀) q

theorem northEquiv_inclusion :
    ((northEquiv f y₀).toFun.comp (northInclusion f y₀)).Homotopic
      (ContinuousMap.id (BaseSpace f y₀)) := by
  change ((unitEquiv f y₀).invFun.comp
    ((northRawEquiv f y₀).toFun.comp (northInclusion f y₀))).Homotopic _
  rw [northRawEquiv_inclusion]
  exact (unitEquiv f y₀).left_inv

theorem southEquiv_inclusion :
    ((southEquiv f y₀).toFun.comp (southInclusion f y₀)).Homotopic
      (ContinuousMap.id (BaseSpace f y₀)) := by
  change ((unitEquiv f y₀).invFun.comp
    ((southRawEquiv f y₀).toFun.comp (southInclusion f y₀))).Homotopic _
  rw [southRawEquiv_inclusion]
  exact (unitEquiv f y₀).left_inv

end AkopyanResearch.SphereSourceCover
