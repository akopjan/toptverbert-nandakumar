module

public import AkopyanResearch.Completion.EquivariantJoinStep
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic

/-!
# Subgroup nullhomotopies through an explicit join step

An equivariant ordinary-null self-map is still an explicit input. If the
seed map has an `H`-equivariant nullhomotopy to an `H`-fixed point, the
constructed map on the actual quotient join has such a nullhomotopy too.
Two explicit homotopies are descended through the quotient and concatenated.
The homotopy of the self-map need not itself be equivariant.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.JoinNullhomotopy

open EquivariantJoinStep

variable {G X Y : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X] [MulAction G Y]

/-- The subgroup nullhomotopy on the seed, with all hypotheses explicit. -/
structure NullData (d : ExtensionData G X Y) (H : Subgroup G) where
  N : X × Time → Y
  c₀ : Y
  continuous_N : Continuous N
  start : ∀ x, N (x, timeZero) = d.F x
  finish : ∀ x, N (x, timeOne) = c₀
  equivariant : ∀ (a : G), a ∈ H → ∀ (x : X) (s : Time),
    N (a • x, s) = a • N (x, s)
  fixed : ∀ (a : G), a ∈ H → a • c₀ = c₀

variable (d : ExtensionData G X Y) (H : Subgroup G) (n : NullData d H)

/-- Shrink the join coordinate to zero. -/
def contractTime (s t : Time) : Time :=
  ⟨(1 - s.val) * t.val, by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr s.property.2) t.property.1
    · nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]⟩

@[simp] theorem contractTime_zero_left (t : Time) : contractTime timeZero t = t := by
  apply Subtype.ext
  simp [contractTime, timeZero]

@[simp] theorem contractTime_one_left (t : Time) : contractTime timeOne t = timeZero := by
  apply Subtype.ext
  simp [contractTime, timeOne, timeZero]

@[simp] theorem contractTime_zero_right (s : Time) : contractTime s timeZero = timeZero := by
  apply Subtype.ext
  simp [contractTime, timeZero]

theorem continuous_contractTime : Continuous (fun p : Time × Time => contractTime p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

def firstRaw (s : Time) (p : Raw X G) : Y :=
  p.2.2 • d.h (p.2.2⁻¹ • n.N (p.2.1, s), p.1)

def secondRaw (s : Time) (p : Raw X G) : Y :=
  p.2.2 • d.h (p.2.2⁻¹ • n.c₀, contractTime s p.1)

theorem firstRaw_zero (s : Time) (x : X) (g : G) :
    firstRaw d H n s (timeZero, x, g) = d.phi (n.N (x, s)) := by
  change g • d.h (g⁻¹ • n.N (x, s), timeZero) = _
  rw [d.start, d.equivariant_phi, smul_inv_smul]

theorem firstRaw_one (s : Time) (x : X) (g : G) :
    firstRaw d H n s (timeOne, x, g) = g • d.c := by
  change g • d.h (g⁻¹ • n.N (x, s), timeOne) = _
  rw [d.finish]

theorem secondRaw_zero (s : Time) (x : X) (g : G) :
    secondRaw d H n s (timeZero, x, g) = d.phi n.c₀ := by
  change g • d.h (g⁻¹ • n.c₀, contractTime s timeZero) = _
  rw [contractTime_zero_right, d.start, d.equivariant_phi, smul_inv_smul]

theorem firstRaw_respects (s : Time) (p q : Raw X G) (hpq : EndpointRel p q) :
    firstRaw d H n s p = firstRaw d H n s q := by
  rcases p with ⟨t, x, g⟩
  rcases q with ⟨u, y, k⟩
  rcases hpq with ⟨ht, hu, hxy⟩ | ⟨ht, hu, hgk⟩
  · change t = timeZero at ht
    change u = timeZero at hu
    change x = y at hxy
    subst t
    subst u
    subst y
    rw [firstRaw_zero, firstRaw_zero]
  · change t = timeOne at ht
    change u = timeOne at hu
    change g = k at hgk
    subst t
    subst u
    subst k
    rw [firstRaw_one, firstRaw_one]

theorem secondRaw_respects (s : Time) (p q : Raw X G) (hpq : EndpointRel p q) :
    secondRaw d H n s p = secondRaw d H n s q := by
  rcases p with ⟨t, x, g⟩
  rcases q with ⟨u, y, k⟩
  rcases hpq with ⟨ht, hu, _⟩ | ⟨ht, hu, hgk⟩
  · change t = timeZero at ht
    change u = timeZero at hu
    subst t
    subst u
    rw [secondRaw_zero, secondRaw_zero]
  · change t = timeOne at ht
    change u = timeOne at hu
    change g = k at hgk
    subst t
    subst u
    subst k
    rfl

def first (p : Time × Join X G) : Y :=
  Quot.lift (firstRaw d H n p.1) (firstRaw_respects d H n p.1) p.2

def second (p : Time × Join X G) : Y :=
  Quot.lift (secondRaw d H n p.1) (secondRaw_respects d H n p.1) p.2

theorem first_start (z : Join X G) : first d H n (timeZero, z) = step d z := by
  induction z using Quot.inductionOn with
  | h p =>
      rcases p with ⟨t, x, g⟩
      change g • d.h (g⁻¹ • n.N (x, timeZero), t) = g • d.h (g⁻¹ • d.F x, t)
      rw [n.start]

theorem stages_match (z : Join X G) :
    second d H n (timeZero, z) = first d H n (timeOne, z) := by
  induction z using Quot.inductionOn with
  | h p =>
      rcases p with ⟨t, x, g⟩
      change g • d.h (g⁻¹ • n.c₀, contractTime timeZero t) =
        g • d.h (g⁻¹ • n.N (x, timeOne), t)
      rw [contractTime_zero_left, n.finish]

theorem second_finish (z : Join X G) :
    second d H n (timeOne, z) = d.phi n.c₀ := by
  induction z using Quot.inductionOn with
  | h p =>
      rcases p with ⟨t, x, g⟩
      change g • d.h (g⁻¹ • n.c₀, contractTime timeOne t) = _
      rw [contractTime_one_left, d.start, d.equivariant_phi, smul_inv_smul]

theorem first_equivariant (a : G) (ha : a ∈ H) (s : Time) (z : Join X G) :
    first d H n (s, a • z) = a • first d H n (s, z) := by
  induction z using Quot.inductionOn with
  | h p =>
      rcases p with ⟨t, x, g⟩
      change (a * g) • d.h ((a * g)⁻¹ • n.N (a • x, s), t) =
        a • (g • d.h (g⁻¹ • n.N (x, s), t))
      rw [n.equivariant a ha]
      simp only [mul_inv_rev, mul_smul, inv_smul_smul]

theorem second_equivariant (a : G) (ha : a ∈ H) (s : Time) (z : Join X G) :
    second d H n (s, a • z) = a • second d H n (s, z) := by
  induction z using Quot.inductionOn with
  | h p =>
      rcases p with ⟨t, x, g⟩
      change (a * g) • d.h ((a * g)⁻¹ • n.c₀, contractTime s t) =
        a • (g • d.h (g⁻¹ • n.c₀, contractTime s t))
      have hc : a⁻¹ • n.c₀ = n.c₀ := n.fixed a⁻¹ (H.inv_mem ha)
      simp only [mul_inv_rev, mul_smul, hc]

theorem endpoint_fixed (a : G) (ha : a ∈ H) : a • d.phi n.c₀ = d.phi n.c₀ := by
  rw [← d.equivariant_phi, n.fixed a ha]

section Continuity

variable [IsTopologicalGroup G] [ContinuousSMul G Y]

theorem continuous_first : Continuous (first d H n) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_right
  change Continuous (fun p : Time × Raw X G =>
    p.2.2.2 • d.h (p.2.2.2⁻¹ • n.N (p.2.2.1, p.1), p.2.1))
  exact continuous_snd.snd.snd.smul
    (d.continuous_h.comp
      (((continuous_snd.snd.snd.inv).smul
        (n.continuous_N.comp (continuous_snd.snd.fst.prodMk continuous_fst))).prodMk
          continuous_snd.fst))

theorem continuous_second : Continuous (second d H n) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_right
  change Continuous (fun p : Time × Raw X G =>
    p.2.2.2 • d.h (p.2.2.2⁻¹ • n.c₀, contractTime p.1 p.2.1))
  exact continuous_snd.snd.snd.smul
    (d.continuous_h.comp
      (((continuous_snd.snd.snd.inv).smul continuous_const).prodMk
        (continuous_contractTime.comp (continuous_fst.prodMk continuous_snd.fst))))

def Equivariant (H : Subgroup G) (f : C(Join X G, Y)) : Prop :=
  ∀ (a : G), a ∈ H → ∀ z : Join X G, f (a • z) = a • f z

def initialMap : C(Join X G, Y) := ⟨step d, continuous_step d⟩

def middleMap : C(Join X G, Y) :=
  ⟨fun z => first d H n (timeOne, z),
    (continuous_first d H n).comp (continuous_const.prodMk continuous_id)⟩

def finalMap : C(Join X G, Y) := ContinuousMap.const _ (d.phi n.c₀)

def firstHomotopy : ContinuousMap.HomotopyWith (initialMap d) (middleMap d H n)
    (Equivariant H) where
  toFun := first d H n
  continuous_toFun := continuous_first d H n
  map_zero_left := first_start d H n
  map_one_left := fun _ => rfl
  prop' := fun s a ha z => first_equivariant d H n a ha s z

def secondHomotopy : ContinuousMap.HomotopyWith (middleMap d H n) (finalMap d H n)
    (Equivariant H) where
  toFun := second d H n
  continuous_toFun := continuous_second d H n
  map_zero_left := stages_match d H n
  map_one_left := second_finish d H n
  prop' := fun s a ha z => second_equivariant d H n a ha s z

/-- The two displayed stages are concatenated by the standard interval
rescaling; every intermediate map is `H`-equivariant. -/
def nullhomotopy : ContinuousMap.HomotopyWith (initialMap d) (finalMap d H n)
    (Equivariant H) := (firstHomotopy d H n).trans (secondHomotopy d H n)

theorem exists_equivariant_nullhomotopy :
    ∃ K : Time × Join X G → Y, Continuous K ∧
      (∀ z, K (timeZero, z) = step d z) ∧
      (∀ z, K (timeOne, z) = d.phi n.c₀) ∧
      (∀ (a : G), a ∈ H → ∀ (s : Time) (z : Join X G),
        K (s, a • z) = a • K (s, z)) := by
  let K := nullhomotopy d H n
  refine ⟨K, K.continuous_toFun, K.map_zero_left, K.map_one_left, ?_⟩
  intro a ha s z
  exact K.prop' s a ha z

end Continuity

end AkopyanResearch.JoinNullhomotopy
