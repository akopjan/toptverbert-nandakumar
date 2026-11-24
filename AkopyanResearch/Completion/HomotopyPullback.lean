module

public import Submission.Homotopy.DiscTrivialisation

/-!
# Homotopic maps have equivalent actual path-fibration pullbacks

For a homotopy `H : f ∼ g`, append the path `H(-,x)` to the path over `x`.
Appending the reversed path gives an inverse up to the explicit
cancellation homotopy. All maps and both homotopies preserve the source
coordinate. This supplies trivialisation over a contractible source
factor without a separate bundle-triviality assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.HomotopyPullback

open ContinuousMap

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

abbrev Space (f : C(X, Y)) (y₀ : Y) := Submission.Pullback f (Submission.ev₁ Y y₀)

variable {f g : C(X, Y)} (y₀ : Y)

def legPath : C(Space f y₀ × unitInterval, Y) where
  toFun z := z.1.val.2.val z.2
  continuous_toFun := Continuous.eval
    (Submission.PathSpace.continuous_val.comp
      ((Submission.Pullback.snd f (Submission.ev₁ Y y₀)).continuous.comp continuous_fst))
    continuous_snd

def legHomotopy (H : f.Homotopy g) : C(Space f y₀ × unitInterval, Y) :=
  ⟨fun z => H (z.2, z.1.val.1), H.continuous.comp
    (continuous_snd.prodMk
      ((Submission.Pullback.fst f (Submission.ev₁ Y y₀)).continuous.comp continuous_fst))⟩

theorem legs_match (H : f.Homotopy g) (q : Space f y₀) :
    legPath y₀ (q, 1) = legHomotopy y₀ H (q, 0) :=
  q.property.symm.trans (H.apply_zero q.val.1).symm

def appendCurve (H : f.Homotopy g) : C(Space f y₀ × unitInterval, Y) :=
  Submission.fconcat (legPath y₀) (legHomotopy y₀ H) (legs_match y₀ H)

theorem appendCurve_source (H : f.Homotopy g) (q : Space f y₀) :
    appendCurve y₀ H (q, 0) = y₀ := by
  rw [appendCurve, Submission.fconcat_zero]
  exact q.val.2.property

theorem appendCurve_target (H : f.Homotopy g) (q : Space f y₀) :
    appendCurve y₀ H (q, 1) = g q.val.1 := by
  rw [appendCurve, Submission.fconcat_one]
  exact H.apply_one q.val.1

def map (H : f.Homotopy g) : C(Space f y₀, Space g y₀) where
  toFun q := ⟨(q.val.1, ⟨(appendCurve y₀ H).curry q, appendCurve_source y₀ H q⟩),
    (appendCurve_target y₀ H q).symm⟩
  continuous_toFun :=
    ((Submission.Pullback.fst f (Submission.ev₁ Y y₀)).continuous.prodMk
      ((appendCurve y₀ H).curry.continuous.subtype_mk _)).subtype_mk _

@[simp]
theorem map_fst (H : f.Homotopy g) (q : Space f y₀) : (map y₀ H q).val.1 = q.val.1 := rfl

theorem map_curve_apply (H : f.Homotopy g) (q : Space f y₀) (t : unitInterval) :
    (map y₀ H q).val.2.val t =
      Submission.fconcat (legPath y₀) (legHomotopy y₀ H) (legs_match y₀ H) (q, t) := rfl

theorem map_symm_map_curve (H : f.Homotopy g) (q : Space f y₀) (t : unitInterval) :
    (map y₀ H.symm (map y₀ H q)).val.2.val t =
      Submission.fconcat
        (Submission.fconcat (legPath y₀) (legHomotopy y₀ H) (legs_match y₀ H))
        (Submission.fsymm (legHomotopy y₀ H))
        (Submission.fconcat_one_eq_fsymm_zero
          (legPath y₀) (legHomotopy y₀ H) (legs_match y₀ H)) (q, t) := by
  rw [map_curve_apply]
  apply Submission.fconcat_congr
  · intro s
    exact map_curve_apply y₀ H q s
  · intro s
    rfl

def cancellationCurve (H : f.Homotopy g) :
    C((unitInterval × Space f y₀) × unitInterval, Y) :=
  Submission.cancelHomotopyMap (legPath y₀) (legHomotopy y₀ H) (legs_match y₀ H)

theorem cancellationCurve_source (H : f.Homotopy g) (z : unitInterval × Space f y₀) :
    cancellationCurve y₀ H (z, 0) = y₀ := by
  change Submission.cancelAux _ _ ((z.1, z.2), 0) = _
  rw [Submission.cancelAux_zero_right]
  exact z.2.val.2.property

theorem cancellationCurve_target (H : f.Homotopy g) (z : unitInterval × Space f y₀) :
    cancellationCurve y₀ H (z, 1) = f z.2.val.1 := by
  change Submission.cancelAux _ _ ((z.1, z.2), 1) = _
  rw [Submission.cancelAux_one_right _ _ (legs_match y₀ H)]
  exact z.2.property.symm

def cancellationMap (H : f.Homotopy g) : C(unitInterval × Space f y₀, Space f y₀) where
  toFun z := ⟨(z.2.val.1,
    ⟨(cancellationCurve y₀ H).curry z, cancellationCurve_source y₀ H z⟩),
    (cancellationCurve_target y₀ H z).symm⟩
  continuous_toFun :=
    (((Submission.Pullback.fst f (Submission.ev₁ Y y₀)).continuous.comp continuous_snd).prodMk
      ((cancellationCurve y₀ H).curry.continuous.subtype_mk _)).subtype_mk _

theorem cancellationMap_zero (H : f.Homotopy g) (q : Space f y₀) :
    cancellationMap y₀ H (0, q) = map y₀ H.symm (map y₀ H q) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  ext t
  change Submission.cancelAux _ _ ((0, q), t) = _
  rw [Submission.cancelAux_zero _ _ (legs_match y₀ H)]
  exact (map_symm_map_curve y₀ H q t).symm

theorem cancellationMap_one (H : f.Homotopy g) (q : Space f y₀) :
    cancellationMap y₀ H (1, q) = q := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  ext t
  exact Submission.cancelAux_one _ _ q t

def cancellationHomotopy (H : f.Homotopy g) :
    ((map y₀ H.symm).comp (map y₀ H)).Homotopy (ContinuousMap.id (Space f y₀)) where
  toContinuousMap := cancellationMap y₀ H
  map_zero_left := cancellationMap_zero y₀ H
  map_one_left := cancellationMap_one y₀ H

@[simp]
theorem cancellationHomotopy_fst (H : f.Homotopy g) (z : unitInterval × Space f y₀) :
    (cancellationHomotopy y₀ H z).val.1 = z.2.val.1 := rfl

/-- The actual path-fibration pullbacks of homotopic maps are homotopy
equivalent by an equivalence over their common source. -/
def homotopyEquiv (H : f.Homotopy g) : Space f y₀ ≃ₕ Space g y₀ where
  toFun := map y₀ H
  invFun := map y₀ H.symm
  left_inv := ⟨cancellationHomotopy y₀ H⟩
  right_inv := by
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      (show ((map y₀ H.symm.symm).comp (map y₀ H.symm)).Homotopic
          (ContinuousMap.id (Space g y₀)) from ⟨cancellationHomotopy y₀ H.symm⟩)

@[simp]
theorem homotopyEquiv_fst (H : f.Homotopy g) (q : Space f y₀) :
    (homotopyEquiv y₀ H q).val.1 = q.val.1 := rfl

@[simp]
theorem homotopyEquiv_symm_fst (H : f.Homotopy g) (q : Space g y₀) :
    ((homotopyEquiv y₀ H).symm q).val.1 = q.val.1 := rfl

end AkopyanResearch.HomotopyPullback
