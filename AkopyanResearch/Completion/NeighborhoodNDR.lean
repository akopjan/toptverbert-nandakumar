module

public import AkopyanResearch.Completion.NDRCylinder
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# From a neighborhood deformation to explicit NDR data

A continuous cutoff extends a strong deformation of an open neighborhood
to the entire metric space. The control function is constructed from actual
distances to the closed retract and to the complement of its neighborhood.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.NeighborhoodNDR

open Set Metric ContinuousMap
open scoped Classical
open NDRCylinder

variable {X : Type*} [MetricSpace X] {A U : Set X}

structure Control (A U : Set X) where
  value : C(X, ℝ)
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  zero_iff : ∀ x, value x = 0 ↔ x ∈ A
  mem_of_lt_one : ∀ x, value x < 1 → x ∈ U

structure LocalDeformation (A U : Set X) where
  h : C(Time × U, X)
  start : ∀ x, h (0, x) = x.val
  fixed : ∀ x : U, x.val ∈ A → ∀ t, h (t, x) = x.val
  finish : ∀ x, h (1, x) ∈ A

theorem distance_sum_pos (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (hneA : A.Nonempty) (hneC : Uᶜ.Nonempty) (x : X) :
    0 < infDist x A + infDist x Uᶜ := by
  by_cases hx : x ∈ A
  · have hc : x ∉ Uᶜ := fun h => h (hAU hx)
    have hp := (hU.isClosed_compl.notMem_iff_infDist_pos hneC).mp hc
    exact add_pos_of_nonneg_of_pos infDist_nonneg hp
  · have hp := (hA.notMem_iff_infDist_pos hneA).mp hx
    exact add_pos_of_pos_of_nonneg hp infDist_nonneg

/-- The usual metric separator, with its zero set and strict sublevel
property proved for the specified closed set and open neighborhood. -/
def metricControl (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (hneA : A.Nonempty) (hneC : Uᶜ.Nonempty) : Control A U where
  value := ⟨fun x => infDist x A / (infDist x A + infDist x Uᶜ),
    (continuous_infDist_pt A).div
      ((continuous_infDist_pt A).add (continuous_infDist_pt Uᶜ))
      (fun x => (distance_sum_pos hA hU hAU hneA hneC x).ne')⟩
  nonneg x := div_nonneg infDist_nonneg (distance_sum_pos hA hU hAU hneA hneC x).le
  le_one x := (div_le_one (distance_sum_pos hA hU hAU hneA hneC x)).mpr
    (le_add_of_nonneg_right infDist_nonneg)
  zero_iff x := by
    change infDist x A / (infDist x A + infDist x Uᶜ) = 0 ↔ x ∈ A
    rw [div_eq_zero_iff, or_iff_left (distance_sum_pos hA hU hAU hneA hneC x).ne']
    exact (hA.mem_iff_infDist_zero hneA).symm
  mem_of_lt_one x hx := by
    by_contra hxu
    have hz : infDist x Uᶜ = 0 := infDist_zero_of_mem hxu
    have hp := distance_sum_pos hA hU hAU hneA hneC x
    simp only [hz, add_zero] at hp
    change infDist x A / (infDist x A + infDist x Uᶜ) < 1 at hx
    rw [hz, add_zero, div_self hp.ne'] at hx
    exact lt_irrefl _ hx

def cutoff (r : ℝ) : ℝ := max 0 (min 1 (2 - 4 * r))

theorem continuous_cutoff : Continuous cutoff := by unfold cutoff; fun_prop

theorem cutoff_nonneg (r : ℝ) : 0 ≤ cutoff r := le_max_left _ _

theorem cutoff_le_one (r : ℝ) : cutoff r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem cutoff_eq_one {r : ℝ} (hr : r ≤ 1 / 4) : cutoff r = 1 := by
  rw [cutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem cutoff_eq_zero {r : ℝ} (hr : 1 / 2 ≤ r) : cutoff r = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

namespace Control

variable (C : Control A U) (L : LocalDeformation A U)

def slowTime (p : Time × X) : Time :=
  ⟨p.1.val * cutoff (C.value p.2),
    mul_nonneg p.1.property.1 (cutoff_nonneg _),
    (mul_le_mul_of_nonneg_left (cutoff_le_one _) p.1.property.1).trans
      (by simpa only [mul_one] using p.1.property.2)⟩

theorem continuous_slowTime : Continuous C.slowTime := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_cutoff.comp (C.value.continuous.comp continuous_snd))

abbrev Active := {p : Time × X // C.value p.2 ≤ 1 / 2}

def active (p : C.Active) : X :=
  L.h (C.slowTime p.val, ⟨p.val.2, C.mem_of_lt_one _ (by linarith [p.property])⟩)

theorem continuous_active : Continuous (C.active L) := by
  apply L.h.continuous.comp
  exact (C.continuous_slowTime.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

theorem active_boundary (p : C.Active) (hp : 1 / 2 ≤ C.value p.val.2) :
    C.active L p = p.val.2 := by
  have ht : C.slowTime p.val = 0 := by
    apply Subtype.ext
    change p.val.1.val * cutoff (C.value p.val.2) = 0
    rw [cutoff_eq_zero hp, mul_zero]
  unfold active
  rw [ht, L.start]

def global (p : Time × X) : X :=
  if hp : C.value p.2 ≤ 1 / 2 then C.active L ⟨p, hp⟩ else p.2

theorem continuous_global : Continuous (C.global L) := by
  let left : Set (Time × X) := {p | C.value p.2 ≤ 1 / 2}
  let right : Set (Time × X) := {p | 1 / 2 ≤ C.value p.2}
  have hl : IsClosed left := isClosed_le (C.value.continuous.comp continuous_snd) continuous_const
  have hr : IsClosed right := isClosed_le continuous_const (C.value.continuous.comp continuous_snd)
  have hcov : left ∪ right = Set.univ := by
    ext p
    change (C.value p.2 ≤ 1 / 2 ∨ 1 / 2 ≤ C.value p.2) ↔ True
    exact iff_of_true (le_total _ _) (Set.mem_univ p)
  have hleft : ContinuousOn (C.global L) left := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (C.continuous_active L).congr
    intro p
    have hp : C.value p.val.2 ≤ 1 / 2 := p.property
    simp only [Set.domRestrict_apply, global, dite_eq_left hp]
  have hright : ContinuousOn (C.global L) right := by
    apply continuous_snd.continuousOn.congr
    intro p hp
    change 1 / 2 ≤ C.value p.2 at hp
    unfold global
    split_ifs with hp'
    · exact C.active_boundary L ⟨p, hp'⟩ hp
    · rfl
  rw [← continuousOn_univ, ← hcov]
  exact hleft.union_of_isClosed hright hl hr

theorem global_start (x : X) : C.global L (0, x) = x := by
  unfold global
  split_ifs with hx
  · have ht : C.slowTime (0, x) = 0 := by
      apply Subtype.ext
      simp [slowTime]
    unfold active
    rw [ht, L.start]
  · rfl

theorem global_fixed (x : X) (hx : x ∈ A) (t : Time) : C.global L (t, x) = x := by
  have hz := (C.zero_iff x).mpr hx
  have hhalf : C.value x ≤ 1 / 2 := by rw [hz]; norm_num
  rw [global, dite_eq_left hhalf]
  exact L.fixed _ hx _

theorem global_finish (x : X) (hx : C.value x < 1 / 4) :
    C.global L (1, x) ∈ A := by
  have hhalf : C.value x ≤ 1 / 2 := by linarith
  rw [global, dite_eq_left hhalf]
  have ht : C.slowTime (1, x) = 1 := by
    apply Subtype.ext
    change 1 * cutoff (C.value x) = 1
    rw [cutoff_eq_one hx.le, mul_one]
  unfold active
  rw [ht]
  exact L.finish _

/-- A neighborhood deformation gives actual NDR data on the whole space. -/
def ndrData : NDRCylinder.Data A where
  u := ⟨fun x => min 1 (4 * C.value x), by fun_prop⟩
  nonneg x := le_min zero_le_one (mul_nonneg (by norm_num) (C.nonneg x))
  le_one x := min_le_left _ _
  zero_iff x := by
    change min 1 (4 * C.value x) = 0 ↔ x ∈ A
    rw [← C.zero_iff x]
    constructor
    · intro hx
      by_cases hle : 1 ≤ 4 * C.value x
      · rw [min_eq_left hle] at hx
        norm_num at hx
      · rw [min_eq_right (le_of_not_ge hle)] at hx
        linarith
    · intro hx
      simp only [hx, mul_zero, min_eq_right zero_le_one]
  h := ⟨C.global L, C.continuous_global L⟩
  start := C.global_start L
  fixed := C.global_fixed L
  finish x hx := by
    apply C.global_finish L x
    change min 1 (4 * C.value x) < 1 at hx
    by_contra hn
    have hle : 1 ≤ 4 * C.value x := by linarith
    rw [min_eq_left hle] at hx
    exact lt_irrefl _ hx

end Control

end AkopyanResearch.NeighborhoodNDR
