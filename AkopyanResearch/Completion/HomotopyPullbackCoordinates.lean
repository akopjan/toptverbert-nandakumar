module

public import AkopyanResearch.Completion.HomotopyPullback
public import AkopyanResearch.Completion.PathFibreEquivalences

/-! # Source coordinates and literal fibers in a path-fibration pullback -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.HomotopyPullbackCoordinates

open ContinuousMap HomotopyPullback

universe u v w
variable {X : Type u} {X' : Type v} {Y : Type w}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

def sourceHomeomorph (e : X ≃ₜ X') (f : C(X', Y)) (y₀ : Y) :
    Space (f.comp ⟨e, e.continuous⟩) y₀ ≃ₜ Space f y₀ where
  toFun q := ⟨(e q.val.1, q.val.2), q.property⟩
  invFun q := ⟨(e.symm q.val.1, q.val.2), by
    change f (e (e.symm q.val.1)) = Submission.ev₁ Y y₀ q.val.2
    simpa only [e.apply_symm_apply] using q.property⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext (e.symm_apply_apply _) rfl
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply _) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def fibreInclusion (f : C(X, Y)) (x : X) (y₀ : Y) :
    C(Submission.PathFibre Y y₀ (f x), Space f y₀) :=
  ⟨fun γ => ⟨(x, γ.val), γ.property.symm⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

def sourceSubsingletonHomeomorph [Subsingleton X] (f : C(X, Y)) (x : X) (y₀ : Y) :
    Space f y₀ ≃ₜ Submission.PathFibre Y y₀ (f x) where
  toFun q := ⟨q.val.2, q.property.symm.trans (congrArg f (Subsingleton.elim _ _))⟩
  invFun := fibreInclusion f x y₀
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  continuous_toFun :=
    (Submission.Pullback.snd f (Submission.ev₁ Y y₀)).continuous.subtype_mk _
  continuous_invFun := (fibreInclusion f x y₀).continuous

end AkopyanResearch.HomotopyPullbackCoordinates
