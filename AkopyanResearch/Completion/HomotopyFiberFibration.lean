module

public import Submission.Homotopy.PathFibration

/-!
# The actual path-space homotopy fiber is a fibration over its source

The paths run from the value of the map to the chosen basepoint, as in the
concrete comparison target. Reversing them identifies this construction
with the pullback of the ordinary based path fibration. Consequently the
projection has homotopy lifting for every parameter space.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.HomotopyFiberFibration

open ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

abbrev Time := unitInterval

def reverseTime : C(Time, Time) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩

def reversePath (p : C(Time, Y)) : C(Time, Y) := p.comp reverseTime

theorem reversePath_zero (p : C(Time, Y)) : reversePath p 0 = p 1 := by
  change p (unitInterval.symm 0) = p 1
  rw [unitInterval.symm_zero]

theorem reversePath_one (p : C(Time, Y)) : reversePath p 1 = p 0 := by
  change p (unitInterval.symm 1) = p 0
  rw [unitInterval.symm_one]

theorem reversePath_reversePath (p : C(Time, Y)) : reversePath (reversePath p) = p := by
  ext t
  exact congrArg p (unitInterval.symm_symm t)

theorem continuous_reversePath : Continuous (reversePath (Y := Y)) :=
  ContinuousMap.continuous_precomp reverseTime

abbrev Space (f : C(X, Y)) (y₀ : Y) :=
  {p : X × C(Time, Y) // p.2 0 = f p.1 ∧ p.2 1 = y₀}

variable (f : C(X, Y)) (y₀ : Y)

def projection : C(Space f y₀, X) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

def toPullback (p : Space f y₀) : Submission.Pullback f (Submission.ev₁ Y y₀) :=
  ⟨(p.val.1, ⟨reversePath p.val.2, (reversePath_zero _).trans p.property.2⟩),
    by
      change f p.val.1 = reversePath p.val.2 1
      rw [reversePath_one]
      exact p.property.1.symm⟩

def fromPullback (p : Submission.Pullback f (Submission.ev₁ Y y₀)) : Space f y₀ :=
  ⟨(p.val.1, reversePath p.val.2.val),
    by
      rw [reversePath_zero]
      exact p.property.symm,
    (reversePath_one _).trans p.val.2.property⟩

def pullbackHomeomorph : Space f y₀ ≃ₜ Submission.Pullback f (Submission.ev₁ Y y₀) where
  toFun := toPullback f y₀
  invFun := fromPullback f y₀
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (reversePath_reversePath p.val.2)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Subtype.ext (reversePath_reversePath p.val.2.val))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_reversePath.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_reversePath.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)))

/-- The actual projection has homotopy lifting with arbitrary parameters. -/
theorem hasHLP_projection (A : Type*) [TopologicalSpace A] :
    Submission.HasHLP (projection f y₀) A := by
  have hp : Submission.HasHLP (Submission.Pullback.fst f (Submission.ev₁ Y y₀)) A :=
    (Submission.hasHLP_ev₁ Y y₀ A).pullback
  exact ((Submission.HasHLP.of_homeomorph (pullbackHomeomorph f y₀)).comp hp).congr
    (fun _ => rfl)

theorem isSerreFibration_projection : Submission.IsSerreFibration (projection f y₀) :=
  fun _ => hasHLP_projection f y₀ _

end AkopyanResearch.HomotopyFiberFibration
