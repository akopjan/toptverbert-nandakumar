module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.FunProp


@[expose] public section

/-!
Elementary algebra for an explicit framed annulus.

This file verifies injectivity of the two-coordinate interpolation, injectivity
of its graph in space-time, flattening through a projection, and the formula
that turns curve-normal vectors into graph-annulus-normal vectors. It does not
assert the existence of a generic projection, a framed tubular neighborhood,
or a Pontryagin--Thom correspondence.
-/

namespace FramedAnnulus

section Interpolation

variable {A E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def interpolate (c : A → E) (r : A → F) (t : ℝ) (a : A) : E × F :=
  ((1 - t) • c a, t • r a)

@[simp] lemma interpolate_zero (c : A → E) (r : A → F) (a : A) :
    interpolate c r 0 a = (c a, 0) := by
  simp [interpolate]

@[simp] lemma interpolate_one (c : A → E) (r : A → F) (a : A) :
    interpolate c r 1 a = (0, r a) := by
  simp [interpolate]

/-- No restriction on the real parameter is required for injectivity. -/
lemma interpolate_injective (c : A → E) (r : A → F)
    (hc : Function.Injective c) (hr : Function.Injective r) (t : ℝ) :
    Function.Injective (interpolate c r t) := by
  intro a b hab
  by_cases ht : t = 1
  · apply hr
    simpa [interpolate, ht] using congrArg Prod.snd hab
  · apply hc
    have hne : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    exact (smul_right_inj hne).mp (congrArg Prod.fst hab)

/-- Recording time prevents intersections between distinct time slices. -/
def annulus (c : A → E) (r : A → F) (p : A × ℝ) : (E × F) × ℝ :=
  (interpolate c r p.2 p.1, p.2)

lemma annulus_injective (c : A → E) (r : A → F)
    (hc : Function.Injective c) (hr : Function.Injective r) :
    Function.Injective (annulus c r) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ hab
  have hst : s = t := congrArg Prod.snd hab
  subst t
  have hab' : interpolate c r s a = interpolate c r s b := congrArg Prod.fst hab
  have hab'' := interpolate_injective c r hc hr s hab'
  simp [hab'']

end Interpolation

section InterpolationContinuity

variable {A E F : Type*} [TopologicalSpace A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma continuous_interpolate (c : A → E) (r : A → F)
    (hc : Continuous c) (hr : Continuous r) :
    Continuous (fun p : A × ℝ => interpolate c r p.2 p.1) := by
  unfold interpolate
  fun_prop

lemma continuous_annulus (c : A → E) (r : A → F)
    (hc : Continuous c) (hr : Continuous r) : Continuous (annulus c r) := by
  exact (continuous_interpolate c r hc hr).prodMk continuous_snd

/-- On a compact parameter circle and the closed time interval, the graph is
an actual closed topological embedding. -/
lemma annulus_isClosedEmbedding [CompactSpace A]
    (c : A → E) (r : A → F) (hc : Continuous c) (hr : Continuous r)
    (hci : Function.Injective c) (hri : Function.Injective r) :
    Topology.IsClosedEmbedding (fun p : A × Set.Icc (0 : ℝ) 1 =>
      annulus c r (p.1, (p.2 : ℝ))) := by
  have hcont : Continuous (fun p : A × Set.Icc (0 : ℝ) 1 =>
      annulus c r (p.1, (p.2 : ℝ))) := by
    exact (continuous_annulus c r hc hr).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply hcont.isClosedEmbedding
  intro a b hab
  have heq := annulus_injective c r hci hri hab
  apply Prod.ext
  · exact congrArg (fun p : A × ℝ => p.1) heq
  · apply Subtype.ext
    exact congrArg (fun p : A × ℝ => p.2) heq

end InterpolationContinuity

section Flattening

variable {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def flatten (P : E →L[ℝ] E) (c : A → E) (t : ℝ) (a : A) : E :=
  P (c a) + (1 - t) • (c a - P (c a))

lemma projection_flatten (P : E →L[ℝ] E) (hP : ∀ x, P (P x) = P x)
    (c : A → E) (t : ℝ) (a : A) : P (flatten P c t a) = P (c a) := by
  simp [flatten, hP]

lemma flatten_injective (P : E →L[ℝ] E) (hP : ∀ x, P (P x) = P x)
    (c : A → E) (hc : Function.Injective (fun a => P (c a))) (t : ℝ) :
    Function.Injective (flatten P c t) := by
  intro a b hab
  apply hc
  simpa only [projection_flatten P hP] using congrArg P hab

@[simp] lemma flatten_zero (P : E →L[ℝ] E) (c : A → E) (a : A) :
    flatten P c 0 a = c a := by
  simp [flatten]

@[simp] lemma flatten_one (P : E →L[ℝ] E) (c : A → E) (a : A) :
    flatten P c 1 a = P (c a) := by
  simp [flatten]

lemma continuous_flatten [TopologicalSpace A] (P : E →L[ℝ] E)
    (c : A → E) (hc : Continuous c) :
    Continuous (fun p : A × ℝ => flatten P c p.2 p.1) := by
  unfold flatten
  fun_prop

end Flattening

section NormalFrame

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard Euclidean bilinear form on space-time, spelled out to avoid
imposing a noncanonical norm instance on a plain product. -/
def spaceTimeInner (x y : E × ℝ) : ℝ := inner ℝ x.1 y.1 + x.2 * y.2

def graphNormal (velocity normal : E) : E × ℝ :=
  (normal, -inner ℝ normal velocity)

lemma graphNormal_orthogonal_curve (velocity normal tangent : E)
    (hn : inner ℝ normal tangent = 0) :
    spaceTimeInner (graphNormal velocity normal) (tangent, 0) = 0 := by
  simp [spaceTimeInner, graphNormal, hn]

lemma graphNormal_orthogonal_time (velocity normal : E) :
    spaceTimeInner (graphNormal velocity normal) (velocity, 1) = 0 := by
  simp [spaceTimeInner, graphNormal]

@[simp] lemma graphNormal_zero_velocity (normal : E) :
    graphNormal (0 : E) normal = (normal, 0) := by
  simp [graphNormal]

noncomputable def graphNormalLinear (velocity : E) : E →ₗ[ℝ] E × ℝ where
  toFun := graphNormal velocity
  map_add' x y := by
    ext <;> simp [graphNormal, inner_add_left, add_comm]
  map_smul' r x := by
    ext <;> simp [graphNormal, real_inner_smul_left]

lemma graphNormal_injective (velocity : E) :
    Function.Injective (graphNormal velocity) := by
  intro x y h
  exact congrArg Prod.fst h

lemma graphNormal_linearIndependent (velocity : E) (frame : I → E)
    (hframe : LinearIndependent ℝ frame) :
    LinearIndependent ℝ (fun i => graphNormal velocity (frame i)) := by
  exact hframe.map' (graphNormalLinear velocity)
    (LinearMap.ker_eq_bot.mpr (graphNormal_injective velocity))

lemma continuous_graphNormal :
    Continuous (fun p : E × E => graphNormal p.1 p.2) := by
  unfold graphNormal
  fun_prop

end NormalFrame

end FramedAnnulus
