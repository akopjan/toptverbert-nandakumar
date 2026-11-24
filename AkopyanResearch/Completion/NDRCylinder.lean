module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.SplitIfs

/-!
# The cylinder retraction of a metric NDR pair

The construction here uses the actual interval, product and subspace
topologies. Its purpose is to derive the homotopy-extension property from
explicit neighborhood deformation data, without a triangulation theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.NDRCylinder

open Set Filter Topology ContinuousMap
open scoped Classical

abbrev Time := Set.Icc (0 : ℝ) 1

variable {X : Type*} [MetricSpace X]

/-- Standard neighborhood deformation retract data. -/
structure Data (A : Set X) where
  u : C(X, ℝ)
  nonneg : ∀ x, 0 ≤ u x
  le_one : ∀ x, u x ≤ 1
  zero_iff : ∀ x, u x = 0 ↔ x ∈ A
  h : C(Time × X, X)
  start : ∀ x, h (0, x) = x
  fixed : ∀ x ∈ A, ∀ t, h (t, x) = x
  finish : ∀ x, u x < 1 → h (1, x) ∈ A

/-- Evaluation at an arbitrary time remains continuous at a point where
the entire path is constant. Compactness of the time interval is essential. -/
theorem continuousAt_arbitrary_time {Z : Type*} [TopologicalSpace Z]
    (H : C(Time × X, X)) (a : Z → Time) (b : Z → X) (z₀ : Z)
    (hb : ContinuousAt b z₀) (hc : ∀ t, H (t, b z₀) = b z₀) :
    ContinuousAt (fun z => H (a z, b z)) z₀ := by
  let F : C(X, C(Time, X)) :=
    (H.comp ⟨Prod.swap, continuous_swap⟩).curry
  have hF : ContinuousAt (fun z => F (b z)) z₀ :=
    F.continuous.continuousAt.comp hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hF ε hε] with z hz
  calc
    dist (H (a z, b z)) (H (a z₀, b z₀)) =
        dist (F (b z) (a z)) (F (b z₀) (a z)) := by
      change dist (H (a z, b z)) (H (a z₀, b z₀)) =
        dist (H (a z, b z)) (H (a z, b z₀))
      rw [hc, hc]
    _ ≤ dist (F (b z)) (F (b z₀)) := ContinuousMap.dist_apply_le_dist _
    _ < ε := hz

namespace Data

variable {A : Set X} (N : Data A)

def usedTime (p : Time × X) : Time :=
  ⟨min 1 (p.1.val / N.u p.2),
    le_min zero_le_one (div_nonneg p.1.property.1 (N.nonneg p.2)), min_le_left _ _⟩

def remainingTime (p : Time × X) : Time :=
  ⟨max 0 (p.1.val - N.u p.2), le_max_left _ _,
    max_le zero_le_one (by have := p.1.property.2; have := N.nonneg p.2; linarith)⟩

def movedPoint (p : Time × X) : X := N.h (N.usedTime p, p.2)

theorem continuous_remainingTime : Continuous N.remainingTime := by
  unfold remainingTime
  fun_prop

theorem continuous_movedPoint : Continuous N.movedPoint := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hu : N.u p.2 = 0
  · exact continuousAt_arbitrary_time N.h N.usedTime Prod.snd p
      continuous_snd.continuousAt (N.fixed p.2 ((N.zero_iff p.2).mp hu))
  · have ht : ContinuousAt N.usedTime p := by
      apply tendsto_subtype_rng.mpr
      exact continuous_const.continuousAt.min
        ((continuous_subtype_val.comp continuous_fst).continuousAt.div
          (N.u.continuous.comp continuous_snd).continuousAt hu)
    exact N.h.continuous.continuousAt.comp
      (ht.prodMk continuous_snd.continuousAt)

theorem remaining_eq_zero_or_moved_mem (p : Time × X) :
    N.remainingTime p = 0 ∨ N.movedPoint p ∈ A := by
  by_cases hle : p.1.val ≤ N.u p.2
  · left
    apply Subtype.ext
    exact max_eq_left (sub_nonpos.mpr hle)
  · right
    have hlt : N.u p.2 < p.1.val := lt_of_not_ge hle
    by_cases hu : N.u p.2 = 0
    · have hx : p.2 ∈ A := (N.zero_iff p.2).mp hu
      simpa only [movedPoint, N.fixed p.2 hx] using hx
    · have hpos : 0 < N.u p.2 := lt_of_le_of_ne (N.nonneg p.2) (Ne.symm hu)
      have ht : N.usedTime p = 1 := by
        apply Subtype.ext
        change min 1 (p.1.val / N.u p.2) = 1
        exact min_eq_left ((le_div_iff₀ hpos).mpr (by simpa using hlt.le))
      change N.h (N.usedTime p, p.2) ∈ A
      rw [ht]
      exact N.finish p.2 (hlt.trans_le p.1.property.2)

/-- The bottom and side of the ordinary cylinder. -/
abbrev Boundary (A : Set X) := {p : Time × X // p.1 = 0 ∨ p.2 ∈ A}

def retraction (p : Time × X) : Boundary A :=
  ⟨(N.remainingTime p, N.movedPoint p), N.remaining_eq_zero_or_moved_mem p⟩

theorem continuous_retraction : Continuous N.retraction :=
  (N.continuous_remainingTime.prodMk N.continuous_movedPoint).subtype_mk _

theorem retraction_bottom (x : X) : N.retraction (0, x) = ⟨(0, x), Or.inl rfl⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change max 0 (0 - N.u x) = 0
    exact max_eq_left (by have := N.nonneg x; linarith)
  · have ht : N.usedTime (0, x) = 0 := by apply Subtype.ext; simp [usedTime]
    change N.h (N.usedTime (0, x), x) = x
    rw [ht, N.start]

theorem retraction_side (x : X) (hx : x ∈ A) (t : Time) :
    N.retraction (t, x) = ⟨(t, x), Or.inr hx⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change max 0 (t.val - N.u x) = t.val
    rw [(N.zero_iff x).mpr hx, sub_zero]
    exact max_eq_right t.property.1
  · exact N.fixed x hx _

theorem retraction_on_boundary (p : Boundary A) : N.retraction p.val = p := by
  rcases p.property with ht | hx
  · obtain ⟨⟨t, x⟩, hp⟩ := p
    change t = 0 at ht
    subst t
    exact N.retraction_bottom x
  · exact N.retraction_side p.val.2 hx p.val.1

include N in
theorem isClosed : IsClosed A := by
  have hA : A = N.u ⁻¹' {0} := by
    ext x
    exact (N.zero_iff x).symm
  rw [hA]
  exact isClosed_singleton.preimage N.u.continuous

section Extension

variable {Y : Type*} [TopologicalSpace Y]

def boundaryMap (f : C(X, Y)) (g : C(Time × A, Y)) (p : Boundary A) : Y :=
  if hx : p.val.2 ∈ A then g (p.val.1, ⟨p.val.2, hx⟩) else f p.val.2

theorem boundaryMap_bottom (f : C(X, Y)) (g : C(Time × A, Y))
    (hg : ∀ a : A, g (0, a) = f a.val) (x : X) :
    boundaryMap f g ⟨(0, x), Or.inl rfl⟩ = f x := by
  unfold boundaryMap
  split_ifs with hx
  · exact hg ⟨x, hx⟩
  · rfl

theorem boundaryMap_side (f : C(X, Y)) (g : C(Time × A, Y)) (t : Time) (a : A) :
    boundaryMap f g ⟨(t, a.val), Or.inr a.property⟩ = g (t, a) := by
  simp only [boundaryMap, dite_eq_left a.property]

include N in
theorem continuous_boundaryMap (f : C(X, Y)) (g : C(Time × A, Y))
    (hg : ∀ a : A, g (0, a) = f a.val) : Continuous (boundaryMap f g) := by
  let bottom : Set (Boundary A) := {p | p.val.1 = 0}
  let side : Set (Boundary A) := {p | p.val.2 ∈ A}
  have hb : IsClosed bottom := isClosed_eq (by fun_prop) continuous_const
  have hs : IsClosed side := N.isClosed.preimage (by fun_prop)
  have hcov : bottom ∪ side = Set.univ := by
    ext p
    exact iff_of_true p.property (Set.mem_univ p)
  have hbottom : ContinuousOn (boundaryMap f g) bottom := by
    apply (f.continuous.comp (show Continuous (fun p : Boundary A => p.val.2) by
      fun_prop)).continuousOn.congr
    intro p hp
    obtain ⟨⟨t, x⟩, hpx⟩ := p
    change t = 0 at hp
    subst t
    exact boundaryMap_bottom f g hg x
  have hside : ContinuousOn (boundaryMap f g) side := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun p : side =>
        g (p.val.val.1, ⟨p.val.val.2, p.property⟩)) := by fun_prop
    apply hc.congr
    intro p
    have hp : p.val.val.2 ∈ A := p.property
    simp only [Set.domRestrict_apply, boundaryMap, dite_eq_left hp]
  rw [← continuousOn_univ, ← hcov]
  exact hbottom.union_of_isClosed hside hb hs

include N in
/-- Actual homotopy extension into every topological target, with both
boundary equations preserved exactly. -/
theorem homotopyExtension (f : C(X, Y)) (g : C(Time × A, Y))
    (hg : ∀ a : A, g (0, a) = f a.val) :
    ∃ H : C(Time × X, Y),
      (∀ x, H (0, x) = f x) ∧ (∀ t a, H (t, a.val) = g (t, a)) := by
  let b : C(Boundary A, Y) := ⟨boundaryMap f g, N.continuous_boundaryMap f g hg⟩
  let H : C(Time × X, Y) := b.comp ⟨N.retraction, N.continuous_retraction⟩
  refine ⟨H, ?_, ?_⟩
  · intro x
    change boundaryMap f g (N.retraction (0, x)) = f x
    rw [N.retraction_bottom]
    exact boundaryMap_bottom f g hg x
  · intro t a
    change boundaryMap f g (N.retraction (t, a.val)) = g (t, a)
    rw [N.retraction_side a.val a.property t]
    exact boundaryMap_side f g t a

end Extension

end Data

end AkopyanResearch.NDRCylinder
