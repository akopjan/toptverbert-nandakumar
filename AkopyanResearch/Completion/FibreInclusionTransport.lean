module

public import AkopyanResearch.Completion.HomotopyPullbackCoordinates
public import AkopyanResearch.Completion.ProductSphereProjection
public import Hatcher.Singular.Homology

/-!
# Independence of the source point for actual fibre-inclusion homology

A path in the source transports path fibres by concatenation. An explicit
homotopy moves the source coordinate along this path while appending its
initial segment. Thus the actual fibre inclusion induces an isomorphism
at one source point if and only if it does at every point of its path component.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FibreInclusionTransport

open ContinuousMap CategoryTheory CategoryTheory.Limits ProductSphereKernel
open HomotopyPullbackCoordinates

universe w v u
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y₀ : Y)

def constantMap (x : X) : C(PUnit.{w + 1}, Y) := ContinuousMap.const _ (f x)

def constantFibreHomeomorph (x : X) :
    HomotopyPullback.Space (constantMap f x) y₀ ≃ₜ Submission.PathFibre Y y₀ (f x) :=
  sourceSubsingletonHomeomorph (constantMap f x) PUnit.unit y₀

def pathHomotopy {a b : X} (p : Path a b) :
    (constantMap f a).Homotopy (constantMap f b) where
  toFun z := f (p z.1)
  continuous_toFun := f.continuous.comp (p.continuous.comp continuous_fst)
  map_zero_left _ := congrArg f p.source
  map_one_left _ := congrArg f p.target

def transportEquiv {a b : X} (p : Path a b) :
    Submission.PathFibre Y y₀ (f a) ≃ₕ Submission.PathFibre Y y₀ (f b) :=
  (constantFibreHomeomorph f y₀ a).symm.toHomotopyEquiv.trans
    ((HomotopyPullback.homotopyEquiv y₀ (pathHomotopy f p)).trans
      (constantFibreHomeomorph f y₀ b).toHomotopyEquiv)

def firstLeg (a : X) : C((unitInterval × Submission.PathFibre Y y₀ (f a)) × unitInterval, Y) where
  toFun z := z.1.2.val.val z.2
  continuous_toFun := Continuous.eval
    ((continuous_subtype_val.comp continuous_subtype_val).comp
      (continuous_snd.comp continuous_fst)) continuous_snd

def movingLeg {a b : X} (p : Path a b) :
    C((unitInterval × Submission.PathFibre Y y₀ (f a)) × unitInterval, Y) where
  toFun z := f (p (z.1.1 * z.2))
  continuous_toFun := by fun_prop

theorem legs_match {a b : X} (p : Path a b)
    (z : unitInterval × Submission.PathFibre Y y₀ (f a)) :
    firstLeg f y₀ a (z, 1) = movingLeg f y₀ p (z, 0) := by
  change z.2.val.val 1 = f (p (z.1 * 0))
  rw [mul_zero, p.source]
  exact z.2.property

def movingCurve {a b : X} (p : Path a b) :
    C((unitInterval × Submission.PathFibre Y y₀ (f a)) × unitInterval, Y) :=
  Submission.fconcat (firstLeg f y₀ a) (movingLeg f y₀ p) (legs_match f y₀ p)

theorem movingCurve_source {a b : X} (p : Path a b)
    (z : unitInterval × Submission.PathFibre Y y₀ (f a)) : movingCurve f y₀ p (z, 0) = y₀ := by
  rw [movingCurve, Submission.fconcat_zero]
  exact z.2.val.property

theorem movingCurve_target {a b : X} (p : Path a b)
    (z : unitInterval × Submission.PathFibre Y y₀ (f a)) :
    movingCurve f y₀ p (z, 1) = f (p z.1) := by
  rw [movingCurve, Submission.fconcat_one]
  change f (p (z.1 * 1)) = f (p z.1)
  rw [mul_one]

def movingMap {a b : X} (p : Path a b) :
    C(unitInterval × Submission.PathFibre Y y₀ (f a), HomotopyPullback.Space f y₀) where
  toFun z := ⟨(p z.1, ⟨(movingCurve f y₀ p).curry z, movingCurve_source f y₀ p z⟩),
    (movingCurve_target f y₀ p z).symm⟩
  continuous_toFun :=
    ((p.continuous.comp continuous_fst).prodMk
      ((movingCurve f y₀ p).curry.continuous.subtype_mk _)).subtype_mk _

theorem movingMap_zero {a b : X} (p : Path a b) (γ : Submission.PathFibre Y y₀ (f a)) :
    movingMap f y₀ p (0, γ) =
      fibreInclusion f a y₀ (transportEquiv f y₀ (Path.refl a) γ) := by
  apply Subtype.ext
  refine Prod.ext p.source ?_
  apply Subtype.ext
  ext t
  change movingCurve f y₀ p ((0, γ), t) =
    HomotopyPullback.appendCurve y₀ (pathHomotopy f (Path.refl a))
      ((constantFibreHomeomorph f y₀ a).symm γ, t)
  rw [movingCurve, HomotopyPullback.appendCurve]
  apply Submission.fconcat_congr
  · intro s; rfl
  · intro s
    change f (p (0 * s)) = f a
    rw [zero_mul, p.source]

theorem movingMap_one {a b : X} (p : Path a b) (γ : Submission.PathFibre Y y₀ (f a)) :
    movingMap f y₀ p (1, γ) = fibreInclusion f b y₀ (transportEquiv f y₀ p γ) := by
  apply Subtype.ext
  refine Prod.ext p.target ?_
  apply Subtype.ext
  ext t
  change movingCurve f y₀ p ((1, γ), t) =
    HomotopyPullback.appendCurve y₀ (pathHomotopy f p)
      ((constantFibreHomeomorph f y₀ a).symm γ, t)
  rw [movingCurve, HomotopyPullback.appendCurve]
  apply Submission.fconcat_congr
  · intro s; rfl
  · intro s
    change f (p (1 * s)) = f (p s)
    rw [one_mul]

def movingHomotopy {a b : X} (p : Path a b) :
    ((fibreInclusion f a y₀).comp (transportEquiv f y₀ (Path.refl a)).toFun).Homotopy
      ((fibreInclusion f b y₀).comp (transportEquiv f y₀ p).toFun) where
  toContinuousMap := movingMap f y₀ p
  map_zero_left := movingMap_zero f y₀ p
  map_one_left := movingMap_one f y₀ p

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (R : C) (i : ℕ)

theorem fibreInclusion_isIso_of_path {a b : X} (p : Path a b)
    (h : IsIso ((homologyFunctor R i).map (TopCat.ofHom (fibreInclusion f a y₀)))) :
    IsIso ((homologyFunctor R i).map (TopCat.ofHom (fibreInclusion f b y₀))) := by
  let e₀ := Hatcher.Singular.homologyIsoOfHomotopyEquiv (transportEquiv f y₀ (Path.refl a)) R i
  let e₁ := Hatcher.Singular.homologyIsoOfHomotopyEquiv (transportEquiv f y₀ p) R i
  have heq : e₀.hom ≫ (homologyFunctor R i).map (TopCat.ofHom (fibreInclusion f a y₀)) =
      e₁.hom ≫ (homologyFunctor R i).map (TopCat.ofHom (fibreInclusion f b y₀)) := by
    change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ =
      (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (movingHomotopy f y₀ p) R i
  apply (isIso_comp_left_iff e₁.hom _).mp
  rw [← heq]
  infer_instance

theorem fibreInclusion_isIso_of_pathConnected [PathConnectedSpace X] (a b : X)
    (h : IsIso ((homologyFunctor R i).map (TopCat.ofHom (fibreInclusion f a y₀)))) :
    IsIso ((homologyFunctor R i).map (TopCat.ofHom (fibreInclusion f b y₀))) :=
  fibreInclusion_isIso_of_path f y₀ R i (Joined.somePath (PathConnectedSpace.joined a b)) h

end AkopyanResearch.FibreInclusionTransport
