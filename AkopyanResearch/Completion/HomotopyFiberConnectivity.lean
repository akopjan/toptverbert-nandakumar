module

public import AkopyanResearch.Completion.FibrationConnectivity
public import AkopyanResearch.Completion.HomotopyFiberFibration
public import AkopyanResearch.Completion.SphereConnectivity

/-!
# Connectivity of the genuine path-space homotopy fiber

Reversal identifies each fibre of the source projection with a fibre of the
based path fibration. Exactness for that contractible total space computes
its connectivity. Exactness for the source projection then computes the
connectivity of the homotopy fiber itself.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.HomotopyFiberConnectivity

open HomotopyFiberFibration

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y₀ : Y)

def fibreHomeomorph (x : X) :
    (⇑(projection f y₀) ⁻¹' {x} : Set (Space f y₀)) ≃ₜ
      (⇑(Submission.ev₁ Y y₀) ⁻¹' {f x} : Set (Submission.PathSpace Y y₀)) where
  toFun p :=
    ⟨⟨reversePath p.val.val.2, (reversePath_zero _).trans p.val.property.2⟩, by
      change reversePath p.val.val.2 1 = f x
      rw [reversePath_one]
      exact p.val.property.1.trans (congrArg f p.property)⟩
  invFun p := ⟨fromPullback f y₀ ⟨(x, p.val), p.property.symm⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext p.property.symm (reversePath_reversePath p.val.val.2)
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact reversePath_reversePath p.val.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_reversePath.comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_const.prodMk
      (continuous_reversePath.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem fibre_pi_vanish (n : ℕ) (x : X)
    (b : (⇑(projection f y₀) ⁻¹' {x} : Set (Space f y₀)))
    (hY : Subsingleton (HomotopyGroup.Pi (n + 1) Y (f x))) :
    Subsingleton (HomotopyGroup.Pi n
      (⇑(projection f y₀) ⁻¹' {x} : Set (Space f y₀)) b) := by
  let e := fibreHomeomorph f y₀ x
  apply SphereConnectivity.pi_subsingleton_of_retract
    (⟨e, e.continuous⟩ : C(_, _)) (⟨e.symm, e.symm.continuous⟩ : C(_, _))
    (by apply ContinuousMap.ext; intro z; exact e.symm_apply_apply z)
  have hE : Subsingleton (HomotopyGroup.Pi n (Submission.PathSpace Y y₀) (e b).val) := by
    cases n with
    | zero => exact FibrationConnectivity.piZero_vanish _
    | succ k => exact Submission.subsingleton_homotopyGroup_of_contractible _
  exact FibrationConnectivity.fibre_pi_vanish (Submission.ev₁ Y y₀) (e b)
    (Submission.isSerreFibration_ev₁ Y y₀) n hE hY

theorem nonempty_space [Nonempty X] [PathConnectedSpace Y] : Nonempty (Space f y₀) := by
  let x : X := Classical.choice ‹Nonempty X›
  let γ := PathConnectedSpace.somePath (f x) y₀
  exact ⟨⟨(x, γ.toContinuousMap), γ.source, γ.target⟩⟩

theorem pathConnected_space [PathConnectedSpace X] [PathConnectedSpace Y]
    (hY : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 1 Y y)) :
    PathConnectedSpace (Space f y₀) := by
  let : Nonempty X := PathConnectedSpace.nonempty
  let : Nonempty (Space f y₀) := nonempty_space f y₀
  apply FibrationConnectivity.pathConnected_total (projection f y₀)
    (hasHLP_projection f y₀ PUnit.{1})
  intro p
  let b : (⇑(projection f y₀) ⁻¹' {projection f y₀ p} : Set (Space f y₀)) := ⟨p, rfl⟩
  exact FibrationConnectivity.pathConnectedSpace_of_piZero b
    (fibre_pi_vanish f y₀ 0 _ b (hY _))

theorem pi_vanish (n : ℕ) (b : Space f y₀)
    (hX : Subsingleton (HomotopyGroup.Pi (n + 1) X b.val.1))
    (hY : Subsingleton (HomotopyGroup.Pi (n + 2) Y (f b.val.1))) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (Space f y₀) b) := by
  let e : (⇑(projection f y₀) ⁻¹' {b.val.1} : Set (Space f y₀)) := ⟨b, rfl⟩
  exact FibrationConnectivity.total_pi_vanish (projection f y₀) e
    (isSerreFibration_projection f y₀) n
    (fibre_pi_vanish f y₀ (n + 1) b.val.1 e hY) hX

end AkopyanResearch.HomotopyFiberConnectivity
