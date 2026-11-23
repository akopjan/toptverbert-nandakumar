module

public import AkopyanResearch.PairNormalChart
public import AkopyanResearch.PairNormalFrame
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions


@[expose] public section

/-!
# Explicit trivialization of the pair normal bundle

The bundle `U × TS(W)` becomes a product after exchanging one fixed unit
line in `U` with the radial line in `W`. All maps below are actual
homeomorphisms given by the checked Euclidean formulas.
-/

noncomputable section

namespace AkopyanResearch.NormalBundleTrivialization

open PairNormalChart
open scoped InnerProductSpace

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

abbrev UnitDirections (W : Type*) [NormedAddCommGroup W] := {w : W // ‖w‖ = 1}

abbrev NormalFiber (f : U) := W × (ℝ ∙ f)ᗮ

def toProduct (f : U) (hf : ‖f‖ = 1) (x : UnitTangent W × U) :
    UnitDirections W × NormalFiber (W := W) f :=
  (⟨x.1.val.1, x.1.property.1⟩,
    (PairNormalFrame.forward f x.1.val.1 x.2 x.1.val.2).1,
    ⟨(PairNormalFrame.forward f x.1.val.1 x.2 x.1.val.2).2,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (PairNormalFrame.forward_perpendicular hf _ _ _)⟩)

def fromProduct (f : U) (x : UnitDirections W × NormalFiber (W := W) f) :
    UnitTangent W × U :=
  (⟨(x.1.val, (PairNormalFrame.backward f x.1.val x.2.1 x.2.2.val).2),
      x.1.property,
      PairNormalFrame.backward_perpendicular f x.1.property x.2.1 x.2.2.val⟩,
    (PairNormalFrame.backward f x.1.val x.2.1 x.2.2.val).1)

theorem fromProduct_toProduct (f : U) (hf : ‖f‖ = 1) (x : UnitTangent W × U) :
    fromProduct f (toProduct f hf x) = x := by
  have h := PairNormalFrame.backward_forward (f := f) x.1.property.1 x.1.property.2 x.2
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg (fun z : U × W => z.2) h
  · exact congrArg (fun z : U × W => z.1) h

theorem toProduct_fromProduct (f : U) (hf : ‖f‖ = 1)
    (x : UnitDirections W × NormalFiber (W := W) f) :
    toProduct f hf (fromProduct f x) = x := by
  have hu : ⟪f, x.2.2.val⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.2.2.property
  have h := PairNormalFrame.forward_backward (w := x.1.val) hf hu x.2.1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrArg (fun z : W × U => z.1) h
    · apply Subtype.ext
      exact congrArg (fun z : W × U => z.2) h

theorem continuous_toProduct (f : U) (hf : ‖f‖ = 1) :
    Continuous (toProduct (W := W) f hf) := by
  have hw : Continuous (fun x : UnitTangent W × U => x.1.val.1) := by fun_prop
  have hy : Continuous (fun x : UnitTangent W × U =>
      (PairNormalFrame.forward f x.1.val.1 x.2 x.1.val.2).1) := by
    unfold PairNormalFrame.forward
    fun_prop
  have hu : Continuous (fun x : UnitTangent W × U =>
      (PairNormalFrame.forward f x.1.val.1 x.2 x.1.val.2).2) := by
    unfold PairNormalFrame.forward
    fun_prop
  exact (hw.subtype_mk _).prodMk (hy.prodMk (hu.subtype_mk _))

theorem continuous_fromProduct (f : U) :
    Continuous (fromProduct (W := W) f) := by
  have hw : Continuous (fun x : UnitDirections W × NormalFiber (W := W) f => x.1.val) := by
    fun_prop
  have hz : Continuous (fun x : UnitDirections W × NormalFiber (W := W) f =>
      (PairNormalFrame.backward f x.1.val x.2.1 x.2.2.val).2) := by
    unfold PairNormalFrame.backward
    fun_prop
  have hu : Continuous (fun x : UnitDirections W × NormalFiber (W := W) f =>
      (PairNormalFrame.backward f x.1.val x.2.1 x.2.2.val).1) := by
    unfold PairNormalFrame.backward
    fun_prop
  exact ((hw.prodMk hz).subtype_mk _).prodMk hu

def normalBundleHomeomorph (f : U) (hf : ‖f‖ = 1) :
    (UnitTangent W × U) ≃ₜ (UnitDirections W × NormalFiber (W := W) f) where
  toFun := toProduct f hf
  invFun := fromProduct f
  left_inv := fromProduct_toProduct f hf
  right_inv := toProduct_fromProduct f hf
  continuous_toFun := continuous_toProduct f hf
  continuous_invFun := continuous_fromProduct f

theorem normalFiber_finrank [FiniteDimensional ℝ U] [FiniteDimensional ℝ W]
    {f : U} (hf : f ≠ 0) :
    Module.finrank ℝ (NormalFiber (W := W) f) + 1 =
      Module.finrank ℝ W + Module.finrank ℝ U := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ f)
  rw [finrank_span_singleton hf] at h
  rw [Module.finrank_prod]
  omega

theorem normalFiber_finrank_thirteen [FiniteDimensional ℝ U] [FiniteDimensional ℝ W]
    {f : U} (hf : f ≠ 0) (hU : Module.finrank ℝ U = 8) (hW : Module.finrank ℝ W = 6) :
    Module.finrank ℝ (NormalFiber (W := W) f) = 13 := by
  have h := normalFiber_finrank (W := W) hf
  omega

end AkopyanResearch.NormalBundleTrivialization
