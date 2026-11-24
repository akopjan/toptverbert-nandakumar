module

public import AkopyanResearch.Completion.SphereNineSourceHomology
public import AkopyanResearch.Completion.FiniteProductTopology
public import AkopyanResearch.Completion.HomotopyPullbackCoordinates

/-!
# The actual fiber inclusion over a finite product of nine-spheres

In degrees ten through fourteen, the literal inclusion of the path fiber
over a chosen product point induces an integral homology isomorphism.
This is finite induction using the proved lifted hemisphere cover.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace AkopyanResearch.FiniteSphereSourceHomology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel
open HomotopyPullback HomotopyPullbackCoordinates

abbrev Sphere := LoopSphereCover.Sphere.{0} 8
abbrev Source (n : ℕ) := Fin n → Sphere
abbrev Coefficients := AddCommGrpCat.of ℤ

def sourcePoint : (n : ℕ) → Source n
  | 0 => Fin.elim0
  | n + 1 => (FiniteProductTopology.finSucc Sphere n).symm
      (sourcePoint n, ProductHemisphereCover.commonPoint 8)

theorem source_isNConnected (n : ℕ) : Submission.IsNConnected 8 (Source n) :=
  ConnectivityTransport.pi fun _ => ConnectivityTransport.sphere 8

variable {Y : Type} [TopologicalSpace Y]

def splitMap {n : ℕ} (f : C(Source (n + 1), Y)) : C(Source n × Sphere, Y) :=
  f.comp ⟨(FiniteProductTopology.finSucc Sphere n).symm,
    (FiniteProductTopology.finSucc Sphere n).symm.continuous⟩

def baseMap {n : ℕ} (f : C(Source (n + 1), Y)) : C(Source n, Y) :=
  ContractibleSourcePullback.baseMap (splitMap f) (ProductHemisphereCover.commonPoint 8)

theorem fibreInclusion_factor {n : ℕ} (f : C(Source (n + 1), Y)) (y₀ : Y) :
    fibreInclusion f (sourcePoint (n + 1)) y₀ =
      (⟨sourceHomeomorph (FiniteProductTopology.finSucc Sphere n).symm f y₀,
        (sourceHomeomorph (FiniteProductTopology.finSucc Sphere n).symm f y₀).continuous⟩ : C(_, _)).comp
        ((SphereSourceCover.baseInclusion (splitMap f) y₀).comp
          (fibreInclusion (baseMap f) (sourcePoint n) y₀)) := rfl

theorem fibreInclusion_isIso (n : ℕ) (f : C(Source n, Y)) (y₀ : Y)
    (hY : Submission.IsNConnected 9 Y) (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    IsIso ((homologyFunctor Coefficients i).map
      (TopCat.ofHom (fibreInclusion f (sourcePoint n) y₀))) := by
  induction n with
  | zero =>
      let e := sourceSubsingletonHomeomorph f (sourcePoint 0) y₀
      have heq : TopCat.ofHom (fibreInclusion f (sourcePoint 0) y₀) =
          (TopCat.isoOfHomeo e).inv := rfl
      rw [heq]
      infer_instance
  | succ n ih =>
      have h₁ := ih (baseMap f)
      have h₂ := SphereNineSourceHomology.baseInclusion_isIso
        (splitMap f) y₀ (source_isNConnected n) hY i hi hi'
      let e := sourceHomeomorph (FiniteProductTopology.finSucc Sphere n).symm f y₀
      let eT : TopCat.of (Space (splitMap f) y₀) ≅ TopCat.of (Space f y₀) := TopCat.isoOfHomeo e
      have h₃ : IsIso ((homologyFunctor Coefficients i).map
          eT.hom) := inferInstance
      have heq : (homologyFunctor Coefficients i).map
          (TopCat.ofHom (fibreInclusion f (sourcePoint (n + 1)) y₀)) =
        (homologyFunctor Coefficients i).map
            (TopCat.ofHom (fibreInclusion (baseMap f) (sourcePoint n) y₀)) ≫
          SphereSourceHomology.baseInclusionMap (splitMap f) y₀ Coefficients i ≫
          (homologyFunctor Coefficients i).map eT.hom := by
        change (homologyFunctor Coefficients i).map _ =
          (homologyFunctor Coefficients i).map _ ≫
            (homologyFunctor Coefficients i).map _ ≫ (homologyFunctor Coefficients i).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
      rw [heq]
      infer_instance

def fibreInclusionIso (n : ℕ) (f : C(Source n, Y)) (y₀ : Y)
    (hY : Submission.IsNConnected 9 Y) (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    homology Coefficients i (TopCat.of (Submission.PathFibre Y y₀ (f (sourcePoint n)))) ≅
      homology Coefficients i (TopCat.of (Space f y₀)) := by
  letI := fibreInclusion_isIso n f y₀ hY i hi hi'
  exact asIso ((homologyFunctor Coefficients i).map
    (TopCat.ofHom (fibreInclusion f (sourcePoint n) y₀)))

theorem fibreInclusion_isIso_of_homeomorph {X : Type} [TopologicalSpace X]
    (n : ℕ) (e : X ≃ₜ Source n) (f : C(X, Y)) (y₀ : Y)
    (hY : Submission.IsNConnected 9 Y) (i : ℕ) (hi : 10 ≤ i) (hi' : i ≤ 14) :
    IsIso ((homologyFunctor Coefficients i).map
      (TopCat.ofHom (fibreInclusion f (e.symm (sourcePoint n)) y₀))) := by
  let g : C(Source n, Y) := f.comp ⟨e.symm, e.symm.continuous⟩
  have h := fibreInclusion_isIso n g y₀ hY i hi hi'
  let eP := sourceHomeomorph e.symm f y₀
  let eT : TopCat.of (Space g y₀) ≅ TopCat.of (Space f y₀) := TopCat.isoOfHomeo eP
  have heq : (homologyFunctor Coefficients i).map
        (TopCat.ofHom (fibreInclusion f (e.symm (sourcePoint n)) y₀)) =
      (homologyFunctor Coefficients i).map
        (TopCat.ofHom (fibreInclusion g (sourcePoint n) y₀)) ≫
      (homologyFunctor Coefficients i).map eT.hom := by
    rw [← Functor.map_comp]
    rfl
  rw [heq]
  infer_instance

end AkopyanResearch.FiniteSphereSourceHomology
