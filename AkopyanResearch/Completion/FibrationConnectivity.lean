module

public import Submission.Homotopy.FibrationLES
public import Submission.ForMathlib.HomotopyGroup.Contractible

/-!
# Connectivity consequences of the actual fibration long exact sequence

The positive-degree conclusions use exactness of actual homotopy groups.
The degree-zero conclusion is proved by lifting a path in the base and
joining its endpoint inside a fibre.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.FibrationConnectivity

open scoped Topology.Homotopy

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) {b : B} (e : (⇑p ⁻¹' {b} : Set E))

theorem fibre_pi_vanish (hp : Submission.IsSerreFibration p) (n : ℕ)
    (hE : Subsingleton (HomotopyGroup.Pi n E e.val))
    (hB : Subsingleton (HomotopyGroup.Pi (n + 1) B b)) :
    Subsingleton (HomotopyGroup.Pi n (⇑p ⁻¹' {b} : Set E) e) := by
  have hz : ∀ z : HomotopyGroup.Pi n (⇑p ⁻¹' {b} : Set E) e, z = default := by
    intro z
    have hi : z ∈ Submission.iStarFib e n ⁻¹' {default} := hE.elim _ _
    rw [Submission.isExactAt_fibDelta_iStarFib e hp n] at hi
    obtain ⟨y, rfl⟩ := hi
    rw [hB.elim y default, Submission.fibDelta_default]
  exact ⟨fun a c => (hz a).trans (hz c).symm⟩

theorem total_pi_vanish (hp : Submission.IsSerreFibration p) (n : ℕ)
    (hF : Subsingleton (HomotopyGroup.Pi (n + 1) (⇑p ⁻¹' {b} : Set E) e))
    (hB : Subsingleton (HomotopyGroup.Pi (n + 1) B b)) :
    Subsingleton (HomotopyGroup.Pi (n + 1) E e.val) := by
  have hz : ∀ z : HomotopyGroup.Pi (n + 1) E e.val, z = default := by
    intro z
    have hi : z ∈ Submission.pStarAbs e (n + 1) ⁻¹' {default} := hB.elim _ _
    rw [Submission.isExactAt_iStarFib_pStarAbs e hp n] at hi
    obtain ⟨y, rfl⟩ := hi
    rw [hF.elim y default, Submission.iStarFib_default]
  exact ⟨fun a c => (hz a).trans (hz c).symm⟩

theorem pathConnectedSpace_of_piZero {X : Type*} [TopologicalSpace X] (x : X)
    (h : Subsingleton (HomotopyGroup.Pi 0 X x)) : PathConnectedSpace X := by
  let : Subsingleton (HomotopyGroup.Pi 0 X x) := h
  apply pathConnectedSpace_iff_zerothHomotopy.mpr
  exact ⟨⟨⟦x⟧⟩, (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm.subsingleton⟩

theorem piZero_vanish {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 0 X x) := by
  let : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp ‹PathConnectedSpace X›).2
  exact (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).subsingleton

omit e in
theorem pathConnected_total [Nonempty E] [PathConnectedSpace B]
    (hp : Submission.HasHLP p PUnit.{1})
    (hF : ∀ y : E, PathConnectedSpace (⇑p ⁻¹' {p y} : Set E)) :
    PathConnectedSpace E := by
  refine ⟨inferInstance, fun x y => ?_⟩
  let γ := PathConnectedSpace.somePath (p x) (p y)
  let H : C(unitInterval × PUnit, B) := ⟨fun z => γ z.1, γ.continuous.comp continuous_fst⟩
  obtain ⟨L, hL₀, hL⟩ := hp (ContinuousMap.const PUnit x) H (fun _ => γ.source)
  let δ : Path x (L (1, PUnit.unit)) :=
    { toFun := fun t => L (t, PUnit.unit)
      continuous_toFun := L.continuous.comp (continuous_id.prodMk continuous_const)
      source' := hL₀ PUnit.unit
      target' := rfl }
  let z : (⇑p ⁻¹' {p y} : Set E) :=
    ⟨L (1, PUnit.unit), (hL (1, PUnit.unit)).trans γ.target⟩
  let y' : (⇑p ⁻¹' {p y} : Set E) := ⟨y, rfl⟩
  let : PathConnectedSpace (⇑p ⁻¹' {p y} : Set E) := hF y
  exact ⟨δ.trans ((PathConnectedSpace.somePath z y').map continuous_subtype_val)⟩

end AkopyanResearch.FibrationConnectivity
