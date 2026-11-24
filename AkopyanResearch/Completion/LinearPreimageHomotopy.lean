module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# A split linear map is a homotopy equivalence over every subset

If a continuous real linear map has a continuous linear right inverse,
its restriction over an arbitrary subset is a homotopy equivalence. The
straight homotopy between the identity and the chosen section preserves the
linear image at every time. No convexity of the subset is needed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.LinearPreimageHomotopy

open ContinuousMap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def restriction (f : E →L[ℝ] F) (s : Set F) : C(f ⁻¹' s, s) :=
  ⟨fun x => ⟨f x.val, x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

def sectionMap (f : E →L[ℝ] F) (g : F →L[ℝ] E)
    (hfg : f.comp g = ContinuousLinearMap.id ℝ F) (s : Set F) : C(s, f ⁻¹' s) where
  toFun y := ⟨g y.val, by
    change f (g y.val) ∈ s
    have he : f (g y.val) = y.val := congrArg (fun u : F →L[ℝ] F => u y.val) hfg
    rw [he]
    exact y.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact g.continuous.comp continuous_subtype_val

theorem restriction_section (f : E →L[ℝ] F) (g : F →L[ℝ] E)
    (hfg : f.comp g = ContinuousLinearMap.id ℝ F) (s : Set F) :
    (restriction f s).comp (sectionMap f g hfg s) = ContinuousMap.id s := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  exact congrArg (fun u : F →L[ℝ] F => u y.val) hfg

def straightHomotopy (f : E →L[ℝ] F) (g : F →L[ℝ] E)
    (hfg : f.comp g = ContinuousLinearMap.id ℝ F) (s : Set F) :
    (ContinuousMap.id (f ⁻¹' s)).Homotopy ((sectionMap f g hfg s).comp (restriction f s)) where
  toFun p := ⟨(1 - p.1.val) • p.2.val + p.1.val • g (f p.2.val), by
    change f ((1 - p.1.val) • p.2.val + p.1.val • g (f p.2.val)) ∈ s
    have he : f (g (f p.2.val)) = f p.2.val :=
      congrArg (fun u : F →L[ℝ] F => u (f p.2.val)) hfg
    rw [map_add, map_smul, map_smul, he, ← add_smul, sub_add_cancel, one_smul]
    exact p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have ht : Continuous (fun p : unitInterval × (f ⁻¹' s) => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : unitInterval × (f ⁻¹' s) => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub ht).smul hx).add (ht.smul (g.continuous.comp (f.continuous.comp hx)))
  map_zero_left x := by
    apply Subtype.ext
    simp
  map_one_left x := by
    apply Subtype.ext
    simp [sectionMap, restriction]

/-- The restriction's forward map is exactly the given linear map. -/
def splitPreimageEquiv (f : E →L[ℝ] F) (g : F →L[ℝ] E)
    (hfg : f.comp g = ContinuousLinearMap.id ℝ F) (s : Set F) : (f ⁻¹' s) ≃ₕ s where
  toFun := restriction f s
  invFun := sectionMap f g hfg s
  left_inv := ⟨(straightHomotopy f g hfg s).symm⟩
  right_inv := by rw [restriction_section f g hfg s]

/-- A finite-dimensional surjective target supplies the required continuous
linear section; no additional section hypothesis remains. -/
def surjectivePreimageEquiv [FiniteDimensional ℝ F]
    (f : E →L[ℝ] F) (hf : Function.Surjective f) (s : Set F) : (f ⁻¹' s) ≃ₕ s :=
  let h := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  splitPreimageEquiv f (Classical.choose h) (Classical.choose_spec h) s

theorem surjectivePreimageEquiv_apply [FiniteDimensional ℝ F]
    (f : E →L[ℝ] F) (hf : Function.Surjective f) (s : Set F) (x : f ⁻¹' s) :
    (surjectivePreimageEquiv f hf s x).val = f x.val := rfl

end AkopyanResearch.LinearPreimageHomotopy
