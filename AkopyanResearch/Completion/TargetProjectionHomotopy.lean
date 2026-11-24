module

public import AkopyanResearch.Completion.TargetConnectivity

/-!
# Homotopy groups of the actual target projection

The fibre of the original projection to the matching spheres is the
actual path fibre in a product of thirteen-spheres. It has trivial
homotopy groups through degree eleven. The fibration exact sequence
therefore identifies the actual projection on homotopy groups in that
range.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.TargetProjectionHomotopy

open TargetFiberModel TargetFibration

variable {S : Finset (Fin 15)} (hS : S.Nonempty)

def fibreHomeomorph (x : SingleProduct S) :
    (⇑(projection hS) ⁻¹' {x} : Set (ConcreteComparisonTarget.Space S)) ≃ₜ
      (⇑(HomotopyFiberFibration.projection (collapse hS) (fun _ => OnePoint.infty)) ⁻¹' {x} :
        Set (HomotopyFiberFibration.Space (collapse hS) (fun _ => OnePoint.infty))) :=
  (homotopyFiberHomeomorph hS).subtype (fun _ => Iff.rfl)

theorem fibre_pi_vanish (x : SingleProduct S)
    (b : (⇑(projection hS) ⁻¹' {x} : Set (ConcreteComparisonTarget.Space S)))
    (n : ℕ) (hn : n ≤ 11) :
    Subsingleton (HomotopyGroup.Pi n
      (⇑(projection hS) ⁻¹' {x} : Set (ConcreteComparisonTarget.Space S)) b) := by
  let e := fibreHomeomorph hS x
  apply SphereConnectivity.pi_subsingleton_of_retract
    (⟨e, e.continuous⟩ : C(_, _)) (⟨e.symm, e.symm.continuous⟩ : C(_, _))
    (by apply ContinuousMap.ext; intro z; exact e.symm_apply_apply z)
  exact HomotopyFiberConnectivity.fibre_pi_vanish (collapse hS)
    (fun _ => OnePoint.infty) n x (e b)
    (ProductConnectivity.pairProduct_pi_vanish S (n + 1) (by omega) _)

theorem projection_pi_bijective (p : ConcreteComparisonTarget.Space S)
    (n : ℕ) (hn : n ≤ 10) :
    Function.Bijective (Submission.HomotopyGroup.map (N := Fin (n + 1))
      (x := p) (y := projection hS p) (projection hS) rfl) := by
  let e : (⇑(projection hS) ⁻¹' {projection hS p} :
      Set (ConcreteComparisonTarget.Space S)) := ⟨p, rfl⟩
  have h := Submission.bijective_pStarAbs_of_subsingleton_fibre e
    (isSerreFibration_projection hS) n
    (fibre_pi_vanish hS _ e (n + 1) (by omega))
    (fibre_pi_vanish hS _ e n (by omega))
  rw [Submission.pStarAbs_eq_map] at h
  exact h

end AkopyanResearch.TargetProjectionHomotopy
