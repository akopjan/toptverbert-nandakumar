module

public import AkopyanResearch.Completion.EquivariantJoinIteration
public import AkopyanResearch.Completion.JoinNullhomotopy

/-!
# Finite free joins with a subgroup-equivariant nullhomotopy

The only substantive topological inputs are an equivariant self-map `phi`,
an ordinary nullhomotopy of `phi`, and a point fixed by the specified subgroup.
The initial map on `G`, its subgroup nullhomotopy, and all finite join steps
are constructed. No subgroup nullhomotopy is assumed in the final theorem.
Existence of `phi` and of the fixed point remains explicit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.JoinNullIteration

open EquivariantJoinStep EquivariantJoinIteration JoinNullhomotopy

universe u v
variable {G X : Type u} {Y : Type v}
  [Group G] [TopologicalSpace G] [TopologicalSpace Y] [MulAction G Y]

/-- A self-map with an ordinary nullhomotopy. The homotopy need not be
equivariant; the self-map must be equivariant for all of `G`. -/
structure SelfNullData (G : Type u) (Y : Type v) [Group G]
    [TopologicalSpace Y] [MulAction G Y] where
  phi : Y → Y
  h : Y × Time → Y
  c : Y
  continuous_phi : Continuous phi
  continuous_h : Continuous h
  equivariant_phi : ∀ (a : G) (y : Y), phi (a • y) = a • phi y
  start : ∀ y, h (y, timeZero) = phi y
  finish : ∀ y, h (y, timeOne) = c

variable [IsTopologicalGroup G] [ContinuousSMul G Y]

variable (d : SelfNullData G Y)

/-- The seed is the actual free `G`-space `G` with its regular left action. -/
def seedData : ExtensionData G G Y where
  F := fun g => g • d.c
  phi := d.phi
  h := d.h
  c := d.c
  continuous_F := continuous_id.smul continuous_const
  continuous_phi := d.continuous_phi
  continuous_h := d.continuous_h
  equivariant_F := fun a g => mul_smul a g d.c
  equivariant_phi := d.equivariant_phi
  start := d.start
  finish := d.finish

def seedHomotopy (v : Y) (p : G × Time) : Y :=
  p.1 • d.h (p.1⁻¹ • v, unitInterval.symm p.2)

theorem continuous_seedHomotopy (v : Y) : Continuous (seedHomotopy d v) :=
  continuous_fst.smul
    (d.continuous_h.comp
      ((continuous_fst.inv.smul continuous_const).prodMk
        (unitInterval.continuous_symm.comp continuous_snd)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G Y] in
theorem seedHomotopy_start (v : Y) (g : G) :
    seedHomotopy d v (g, timeZero) = g • d.c := by
  change g • d.h (g⁻¹ • v, unitInterval.symm (0 : unitInterval)) = _
  rw [unitInterval.symm_zero]
  change g • d.h (g⁻¹ • v, timeOne) = _
  rw [d.finish]

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G Y] in
theorem seedHomotopy_finish (v : Y) (g : G) :
    seedHomotopy d v (g, timeOne) = d.phi v := by
  change g • d.h (g⁻¹ • v, unitInterval.symm (1 : unitInterval)) = _
  rw [unitInterval.symm_one]
  change g • d.h (g⁻¹ • v, timeZero) = _
  rw [d.start, d.equivariant_phi, smul_inv_smul]

variable (H : Subgroup G) (v : Y) (hv : ∀ a : G, a ∈ H → a • v = v)

include hv in
omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G Y] in
theorem seedHomotopy_equivariant (a : G) (ha : a ∈ H) (g : G) (s : Time) :
    seedHomotopy d v (a * g, s) = a • seedHomotopy d v (g, s) := by
  have hi : a⁻¹ • v = v := hv a⁻¹ (H.inv_mem ha)
  change (a * g) • d.h ((a * g)⁻¹ • v, unitInterval.symm s) =
    a • (g • d.h (g⁻¹ • v, unitInterval.symm s))
  simp only [mul_inv_rev, mul_smul, hi]

/-- The initial subgroup nullhomotopy is constructed from a fixed point. -/
def seedNullData : NullData (seedData d) H where
  N := seedHomotopy d v
  c₀ := d.phi v
  continuous_N := continuous_seedHomotopy d v
  start := seedHomotopy_start d v
  finish := seedHomotopy_finish d v
  equivariant := seedHomotopy_equivariant d H v hv
  fixed := fun a ha => by rw [← d.equivariant_phi, hv a ha]

section GeneralIteration

variable [TopologicalSpace X] [MulAction G X]

/-- Propagate an actual subgroup nullhomotopy through the iterated quotient
joins already defined in `EquivariantJoinIteration`. -/
def iterateNull (e : ExtensionData G X Y) (H : Subgroup G) (n₀ : NullData e H) :
    (k : ℕ) → NullData (iteratedData e k) H
  | 0 => n₀
  | k + 1 =>
      { N := fun p => nullhomotopy (iteratedData e k) H (iterateNull e H n₀ k) (p.2, p.1)
        c₀ := (iteratedData e k).phi (iterateNull e H n₀ k).c₀
        continuous_N :=
          (nullhomotopy (iteratedData e k) H (iterateNull e H n₀ k)).continuous_toFun.comp
            continuous_swap
        start := (nullhomotopy (iteratedData e k) H (iterateNull e H n₀ k)).map_zero_left
        finish := (nullhomotopy (iteratedData e k) H (iterateNull e H n₀ k)).map_one_left
        equivariant := fun a ha x s =>
          (nullhomotopy (iteratedData e k) H (iterateNull e H n₀ k)).prop' s a ha x
        fixed := endpoint_fixed (iteratedData e k) H (iterateNull e H n₀ k) }

theorem iterateNull_endpoint (e : ExtensionData G X Y) (H : Subgroup G)
    (n₀ : NullData e H) (k : ℕ) :
    (iterateNull e H n₀ k).c₀ = (e.phi^[k]) n₀.c₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (iteratedData e k).phi (iterateNull e H n₀ k).c₀ = _
      rw [iteratedData_phi, ih, Function.iterate_succ_apply']

end GeneralIteration

theorem iterated_seed_endpoint (k : ℕ) :
    (iterateNull (seedData d) H (seedNullData d H v hv) k).c₀ =
      (d.phi^[k + 1]) v := by
  rw [iterateNull_endpoint]
  change (d.phi^[k]) (d.phi v) = (d.phi^[k + 1]) v
  rw [Function.iterate_succ_apply]

include hv in
/-- With `k = 14` the source is the fifteen-fold free join of `G`.
Both the map and its subgroup nullhomotopy are constructed from the stated
self-map, ordinary nullhomotopy and subgroup-fixed point. -/
theorem exists_finite_join_map_with_subgroup_nullhomotopy (k : ℕ) :
    ∃ F : IteratedJoin G G k → Y, ∃ N : IteratedJoin G G k × Time → Y,
      Continuous F ∧
      (∀ (a : G) (x : IteratedJoin G G k), F (a • x) = a • F x) ∧
      Continuous N ∧
      (∀ x, N (x, timeZero) = F x) ∧
      (∀ x, N (x, timeOne) = (d.phi^[k + 1]) v) ∧
      (∀ (a : G), a ∈ H → ∀ (x : IteratedJoin G G k) (s : Time),
        N (a • x, s) = a • N (x, s)) ∧
      (∀ (a : G), a ∈ H → a • (d.phi^[k + 1]) v = (d.phi^[k + 1]) v) := by
  let e := iteratedData (seedData d) k
  let n := iterateNull (seedData d) H (seedNullData d H v hv) k
  have hend : n.c₀ = (d.phi^[k + 1]) v := iterated_seed_endpoint d H v hv k
  refine ⟨e.F, n.N, e.continuous_F, e.equivariant_F, n.continuous_N,
    n.start, ?_, n.equivariant, ?_⟩
  · intro x
    exact (n.finish x).trans hend
  · intro a ha
    rw [← hend]
    exact n.fixed a ha

end AkopyanResearch.JoinNullIteration
