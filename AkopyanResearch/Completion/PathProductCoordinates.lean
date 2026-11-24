module

public import AkopyanResearch.Completion.PathFibreEquivalences

/-! # Compact-open path spaces and products -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PathProductCoordinates

open ContinuousMap

universe u v w

def pathHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a b : X) : Path a b ≃ₜ Path (e a) (e b) where
  toFun p := p.map e.continuous
  invFun p := {
    toFun t := e.symm (p t)
    continuous_toFun := e.symm.continuous.comp p.continuous
    source' := by rw [p.source, e.symm_apply_apply]
    target' := by rw [p.target, e.symm_apply_apply] }
  left_inv p := Path.ext (funext fun t => e.symm_apply_apply (p t))
  right_inv p := Path.ext (funext fun t => e.apply_symm_apply (p t))
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (e.continuous.comp (Continuous.eval continuous_fst continuous_snd))
  continuous_invFun := Path.continuous_uncurry_iff.mp
    (e.symm.continuous.comp (Continuous.eval continuous_fst continuous_snd))

def pathPiHomeomorph {ι : Type u} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    (a b : ∀ i, Y i) : Path a b ≃ₜ (∀ i, Path (a i) (b i)) where
  toFun p i := p.map (continuous_apply i)
  invFun p := {
    toFun t i := p i t
    continuous_toFun := continuous_pi fun i => (p i).continuous
    source' := funext fun i => (p i).source
    target' := funext fun i => (p i).target }
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i => Path.continuous_uncurry_iff.mp
    ((continuous_apply i).comp (Continuous.eval continuous_fst continuous_snd))
  continuous_invFun := Path.continuous_uncurry_iff.mp
    (continuous_pi fun i => Continuous.eval ((continuous_apply i).comp continuous_fst) continuous_snd)

def fibrePiHomeomorph {ι : Type u} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    (a b : ∀ i, Y i) :
    Submission.PathFibre (∀ i, Y i) a b ≃ₜ (∀ i, Submission.PathFibre (Y i) (a i) (b i)) :=
  (PathFibreEquivalences.pathFibreHomeomorph a b).trans
    ((pathPiHomeomorph a b).trans
      (Homeomorph.piCongrRight fun i => (PathFibreEquivalences.pathFibreHomeomorph (a i) (b i)).symm))

end AkopyanResearch.PathProductCoordinates
