module
public import AkopyanResearch.Completion.PhaseExtension
public import AkopyanResearch.Completion.EquivariantJoinStep
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# Coordinate colored joins and the binary quotient join

The map `(t,x,y) ↦ ((1-t)x,t y)` is constructed on actual colored-join
coordinates. It descends through the actual endpoint quotient. Splitting
coordinates by their colors gives surjectivity, while recovering the total
right mass and cancelling positive weights gives injectivity. Compactness
then upgrades the continuous bijection to a homeomorphism.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AkopyanResearch.JoinCoordinates


universe u v w
variable {C : Type u} {D : Type v} {V : Type w}
variable [Fintype C] [Fintype D] [Fintype V]

/-- Coordinate joins are closed, including their one-vertex-per-color condition. -/
theorem isClosed_join : IsClosed {x : C × V → ℝ | PhaseExtension.IsJoin x} := by
  have heq : {x : C × V → ℝ | PhaseExtension.IsJoin x} =
      ((⋂ i : C × V, {x | (0 : ℝ) ≤ x i}) ∩ {x | ∑ i, x i = (1 : ℝ)}) ∩
        ⋂ c : C, ⋂ a : V, ⋂ b : V, ⋂ (_ : a ≠ b), {x | x (c, a) * x (c, b) = 0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hn, hs, hu⟩
      refine ⟨⟨hn, hs⟩, ?_⟩
      intro c a b hab
      by_cases ha : x (c, a) = 0
      · simp [ha]
      · by_cases hb : x (c, b) = 0
        · simp [hb]
        · exact False.elim (hab (hu c a b ha hb))
    · rintro ⟨⟨hn, hs⟩, hp⟩
      refine ⟨hn, hs, ?_⟩
      intro c a b ha hb
      by_contra hab
      exact mul_ne_zero ha hb (hp c a b hab)
  rw [heq]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter (fun c => isClosed_iInter (fun a => isClosed_iInter (fun b =>
      isClosed_iInter (fun _ => isClosed_eq
        ((continuous_apply (c, a)).mul (continuous_apply (c, b))) continuous_const))))

theorem isCompact_join : IsCompact {x : C × V → ℝ | PhaseExtension.IsJoin x} := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc :
    IsCompact (Set.Icc (0 : C × V → ℝ) 1)) isClosed_join
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro i
  have hi : x i ≤ ∑ j : C × V, x j :=
    Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  simpa only [hx.2.1, Pi.one_apply] using hi

instance compactSpaceCoordinate : CompactSpace (PhaseExtension.Join C V) :=
  isCompact_iff_compactSpace.mp isCompact_join

def leftMass (x : PhaseExtension.Join (C ⊕ D) V) : ℝ :=
  ∑ i : C × V, x.val (Sum.inl i.1, i.2)

def rightMass (x : PhaseExtension.Join (C ⊕ D) V) : ℝ :=
  ∑ i : D × V, x.val (Sum.inr i.1, i.2)

theorem mass_add (x : PhaseExtension.Join (C ⊕ D) V) : leftMass x + rightMass x = 1 := by
  simpa only [leftMass, rightMass, Fintype.sum_prod_type, Fintype.sum_sum_type]
    using x.property.2.1

theorem left_nonneg (x : PhaseExtension.Join (C ⊕ D) V) : 0 ≤ leftMass x :=
  Finset.sum_nonneg (fun i _ => x.property.1 (Sum.inl i.1, i.2))

theorem right_nonneg (x : PhaseExtension.Join (C ⊕ D) V) : 0 ≤ rightMass x :=
  Finset.sum_nonneg (fun i _ => x.property.1 (Sum.inr i.1, i.2))

def mixWeight (p : EquivariantJoinStep.Raw (PhaseExtension.Join C V) (PhaseExtension.Join D V)) (i : (C ⊕ D) × V) : ℝ :=
  match i.1 with
  | Sum.inl c => (1 - p.1.val) * p.2.1.val (c, i.2)
  | Sum.inr d => p.1.val * p.2.2.val (d, i.2)

def mix (p : EquivariantJoinStep.Raw (PhaseExtension.Join C V) (PhaseExtension.Join D V)) : PhaseExtension.Join (C ⊕ D) V :=
  ⟨mixWeight p, by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, v⟩
      cases c with
      | inl c => exact mul_nonneg (sub_nonneg.mpr p.1.property.2) (p.2.1.property.1 _)
      | inr d => exact mul_nonneg p.1.property.1 (p.2.2.property.1 _)
    · rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp only [mixWeight, ← Finset.mul_sum]
      rw [← Fintype.sum_prod_type, ← Fintype.sum_prod_type,
        p.2.1.property.2.1, p.2.2.property.2.1]
      ring
    · intro c a b ha hb
      cases c with
      | inl c =>
        exact p.2.1.property.2.2 c a b (mul_ne_zero_iff.mp ha).2 (mul_ne_zero_iff.mp hb).2
      | inr d =>
        exact p.2.2.property.2.2 d a b (mul_ne_zero_iff.mp ha).2 (mul_ne_zero_iff.mp hb).2⟩

theorem continuous_mix : Continuous (mix (C := C) (D := D) (V := V)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  rintro ⟨c, v⟩
  cases c with
  | inl c =>
      exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply (c, v)).comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  | inr d =>
      exact (continuous_subtype_val.comp continuous_fst).mul
        ((continuous_apply (d, v)).comp
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))

theorem rightMass_mix (p : EquivariantJoinStep.Raw (PhaseExtension.Join C V) (PhaseExtension.Join D V)) :
    rightMass (mix p) = p.1.val := by
  change (∑ i : D × V, p.1.val * p.2.2.val i) = p.1.val
  rw [← Finset.mul_sum, p.2.2.property.2.1, mul_one]

theorem mix_zero (x : PhaseExtension.Join C V) (y z : PhaseExtension.Join D V) :
    mix (EquivariantJoinStep.timeZero, x, y) = mix (EquivariantJoinStep.timeZero, x, z) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨c, v⟩
  cases c <;> simp [mix, mixWeight, EquivariantJoinStep.timeZero]

theorem mix_one (x z : PhaseExtension.Join C V) (y : PhaseExtension.Join D V) :
    mix (EquivariantJoinStep.timeOne, x, y) = mix (EquivariantJoinStep.timeOne, z, y) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨c, v⟩
  cases c <;> simp [mix, mixWeight, EquivariantJoinStep.timeOne]

theorem mix_respects (p q : EquivariantJoinStep.Raw (PhaseExtension.Join C V) (PhaseExtension.Join D V))
    (h : EquivariantJoinStep.EndpointRel p q) : mix p = mix q := by
  rcases p with ⟨t, x, y⟩
  rcases q with ⟨s, x', y'⟩
  rcases h with ⟨ht, hs, hx⟩ | ⟨ht, hs, hy⟩
  · change t = EquivariantJoinStep.timeZero at ht
    change s = EquivariantJoinStep.timeZero at hs
    change x = x' at hx
    subst t
    subst s
    subst x'
    exact mix_zero x y y'
  · change t = EquivariantJoinStep.timeOne at ht
    change s = EquivariantJoinStep.timeOne at hs
    change y = y' at hy
    subst t
    subst s
    subst y'
    exact mix_one x x' y

def toCoordinates : EquivariantJoinStep.Join (PhaseExtension.Join C V) (PhaseExtension.Join D V) → PhaseExtension.Join (C ⊕ D) V :=
  Quot.lift mix mix_respects

theorem continuous_toCoordinates : Continuous (toCoordinates (C := C) (D := D) (V := V)) :=
  continuous_quot_lift _ continuous_mix

@[simp] theorem toCoordinates_mk (t : EquivariantJoinStep.Time) (x : PhaseExtension.Join C V) (y : PhaseExtension.Join D V) :
    toCoordinates (EquivariantJoinStep.joinMk t x y) = mix (t, x, y) := rfl

theorem toCoordinates_zero_left (x : PhaseExtension.Join C V) (y : PhaseExtension.Join D V) (c : C) (v : V) :
    (toCoordinates (EquivariantJoinStep.joinMk EquivariantJoinStep.timeZero x y)).val (Sum.inl c, v) = x.val (c, v) := by
  simp [toCoordinates_mk, mix, mixWeight, EquivariantJoinStep.timeZero]

theorem toCoordinates_one_right (x : PhaseExtension.Join C V) (y : PhaseExtension.Join D V) (d : D) (v : V) :
    (toCoordinates (EquivariantJoinStep.joinMk EquivariantJoinStep.timeOne x y)).val (Sum.inr d, v) = y.val (d, v) := by
  simp [toCoordinates_mk, mix, mixWeight, EquivariantJoinStep.timeOne]

theorem toCoordinates_zero_right (x : PhaseExtension.Join C V) (y : PhaseExtension.Join D V)
    (d : D) (v : V) :
    (toCoordinates (EquivariantJoinStep.joinMk EquivariantJoinStep.timeZero x y)).val
      (Sum.inr d, v) = 0 := by
  simp [toCoordinates_mk, mix, mixWeight, EquivariantJoinStep.timeZero]

theorem toCoordinates_one_left (x : PhaseExtension.Join C V) (y : PhaseExtension.Join D V)
    (c : C) (v : V) :
    (toCoordinates (EquivariantJoinStep.joinMk EquivariantJoinStep.timeOne x y)).val
      (Sum.inl c, v) = 0 := by
  simp [toCoordinates_mk, mix, mixWeight, EquivariantJoinStep.timeOne]

/-- Simultaneous vertex relabeling on both factors of the binary quotient. -/
def binaryRelabel (e : Equiv.Perm V) :
    EquivariantJoinStep.Join (PhaseExtension.Join C V) (PhaseExtension.Join D V) →
      EquivariantJoinStep.Join (PhaseExtension.Join C V) (PhaseExtension.Join D V) :=
  Quot.map (fun p => (p.1, PhaseExtension.relabel e p.2.1, PhaseExtension.relabel e p.2.2))
    (by
      intro p q h
      rcases h with ⟨ht, hs, hx⟩ | ⟨ht, hs, hy⟩
      · exact Or.inl ⟨ht, hs, congrArg (PhaseExtension.relabel e) hx⟩
      · exact Or.inr ⟨ht, hs, congrArg (PhaseExtension.relabel e) hy⟩)

theorem continuous_binaryRelabel (e : Equiv.Perm V) :
    Continuous (binaryRelabel (C := C) (D := D) e) := by
  apply continuous_quot_map
  exact continuous_fst.prodMk
    (((PhaseExtension.continuous_relabel e).comp continuous_snd.fst).prodMk
      ((PhaseExtension.continuous_relabel e).comp continuous_snd.snd))

theorem toCoordinates_relabel (e : Equiv.Perm V)
    (z : EquivariantJoinStep.Join (PhaseExtension.Join C V) (PhaseExtension.Join D V)) :
    toCoordinates (binaryRelabel e z) = PhaseExtension.relabel e (toCoordinates z) := by
  induction z using Quot.inductionOn with
  | h p =>
    apply Subtype.ext
    funext i
    rcases i with ⟨c, v⟩
    cases c <;> rfl

/-- A vertex supplies the harmless conditional distribution at a zero mass. -/
def vertex (c : C) (v : V) : PhaseExtension.Join C V := by
  classical
  refine ⟨fun i => if i = (c, v) then 1 else 0, ?_⟩
  refine ⟨?_, by simp, ?_⟩
  · intro i
    change 0 ≤ (if i = (c, v) then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · intro d a b ha hb
    have hda : (d, a) = (c, v) := by by_contra h; simp [h] at ha
    have hdb : (d, b) = (c, v) := by by_contra h; simp [h] at hb
    exact congrArg Prod.snd (hda.trans hdb.symm)

theorem vertex_unit_injective : Function.Injective (fun v : V => vertex () v) := by
  intro v w h
  have hv := congrArg (fun x : PhaseExtension.Join Unit V => x.val ((), v)) h
  by_contra hne
  simp [vertex, hne] at hv

theorem vertex_unit_surjective : Function.Surjective (fun v : V => vertex () v) := by
  intro x
  have hs : (∑ v : V, x.val ((), v)) = 1 := by
    simpa only [Fintype.sum_prod_type, Fintype.sum_unique] using x.property.2.1
  have hex : ∃ v : V, x.val ((), v) ≠ 0 := by
    by_contra hn
    push Not at hn
    simp only [hn, Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨v, hv⟩ := hex
  have hother : ∀ w : V, w ≠ v → x.val ((), w) = 0 := by
    intro w hw
    by_contra hn
    exact hw (x.property.2.2 () w v hn hv)
  have hsum : (∑ w : V, x.val ((), w)) = x.val ((), v) := by
    classical
    exact Finset.sum_eq_single v (fun w _ hw => hother w hw) (by simp)
  have hvone : x.val ((), v) = 1 := hsum.symm.trans hs
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext i
  rcases i with ⟨c, w⟩
  cases c
  by_cases hw : w = v
  · subst w
    simp [vertex, hvone]
  · simp [vertex, hw, hother w hw]

/-- A one-color coordinate join is the finite discrete vertex set itself. -/
def unitHomeomorph [TopologicalSpace V] [DiscreteTopology V] :
    V ≃ₜ PhaseExtension.Join Unit V :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (fun v : V => vertex () v)
    ⟨vertex_unit_injective, vertex_unit_surjective⟩) continuous_of_discreteTopology

variable [Nonempty C] [Nonempty D] [Nonempty V]

def defaultPoint : PhaseExtension.Join C V := vertex (Classical.choice inferInstance) (Classical.choice inferInstance)

def leftConditional (x : PhaseExtension.Join (C ⊕ D) V) : PhaseExtension.Join C V :=
  if h : leftMass x = 0 then defaultPoint
  else ⟨fun i => x.val (Sum.inl i.1, i.2) / leftMass x, by
    refine ⟨fun i => div_nonneg (x.property.1 _) (left_nonneg x), ?_, ?_⟩
    · rw [← Finset.sum_div]
      exact div_self h
    · intro c a b ha hb
      apply x.property.2.2 (Sum.inl c) a b
      · intro hzero; apply ha; simp [hzero]
      · intro hzero; apply hb; simp [hzero]⟩

def rightConditional (x : PhaseExtension.Join (C ⊕ D) V) : PhaseExtension.Join D V :=
  if h : rightMass x = 0 then defaultPoint
  else ⟨fun i => x.val (Sum.inr i.1, i.2) / rightMass x, by
    refine ⟨fun i => div_nonneg (x.property.1 _) (right_nonneg x), ?_, ?_⟩
    · rw [← Finset.sum_div]
      exact div_self h
    · intro d a b ha hb
      apply x.property.2.2 (Sum.inr d) a b
      · intro hzero; apply ha; simp [hzero]
      · intro hzero; apply hb; simp [hzero]⟩

def parameters (x : PhaseExtension.Join (C ⊕ D) V) : EquivariantJoinStep.Raw (PhaseExtension.Join C V) (PhaseExtension.Join D V) :=
  (⟨rightMass x, right_nonneg x, by have h := mass_add x; have hn := left_nonneg x; linarith⟩,
    leftConditional x, rightConditional x)

theorem mix_parameters (x : PhaseExtension.Join (C ⊕ D) V) : mix (parameters x) = x := by
  apply Subtype.ext
  funext i
  rcases i with ⟨c, v⟩
  cases c with
  | inl c =>
      change (1 - rightMass x) * (leftConditional x).val (c, v) = x.val (Sum.inl c, v)
      have hl : 1 - rightMass x = leftMass x := by have h := mass_add x; linarith
      rw [hl]
      by_cases h : leftMass x = 0
      · have hlow := x.property.1 (Sum.inl c, v)
        have hhigh : x.val (Sum.inl c, v) ≤ leftMass x :=
          Finset.single_le_sum (fun i _ => x.property.1 (Sum.inl i.1, i.2)) (Finset.mem_univ (c, v))
        simp only [h, zero_mul]
        linarith
      · simp only [leftConditional, dite_eq_right h]
        field_simp
  | inr d =>
      change rightMass x * (rightConditional x).val (d, v) = x.val (Sum.inr d, v)
      by_cases h : rightMass x = 0
      · have hlow := x.property.1 (Sum.inr d, v)
        have hhigh : x.val (Sum.inr d, v) ≤ rightMass x :=
          Finset.single_le_sum (fun i _ => x.property.1 (Sum.inr i.1, i.2)) (Finset.mem_univ (d, v))
        simp only [h, zero_mul]
        linarith
      · simp only [rightConditional, dite_eq_right h]
        field_simp

theorem toCoordinates_surjective :
    Function.Surjective (toCoordinates (C := C) (D := D) (V := V)) := by
  intro x
  exact ⟨Quot.mk _ (parameters x), mix_parameters x⟩

omit [Nonempty C] [Nonempty D] [Nonempty V] in
theorem toCoordinates_injective :
    Function.Injective (toCoordinates (C := C) (D := D) (V := V)) := by
  intro z w hzw
  induction z using Quot.inductionOn with
  | h p =>
    induction w using Quot.inductionOn with
    | h q =>
      change mix p = mix q at hzw
      have ht : p.1 = q.1 := Subtype.ext (by
        have h := congrArg rightMass hzw
        simpa only [rightMass_mix] using h)
      rcases p with ⟨t, x, y⟩
      rcases q with ⟨s, x', y'⟩
      change t = s at ht
      subst s
      have hx : t.val ≠ 1 → x = x' := by
        intro hn
        apply Subtype.ext
        funext i
        apply mul_left_cancel₀ (show (1 - t.val) ≠ 0 by intro h; apply hn; linarith)
        exact congrArg (fun w : PhaseExtension.Join (C ⊕ D) V => w.val (Sum.inl i.1, i.2)) hzw
      have hy : t.val ≠ 0 → y = y' := by
        intro hn
        apply Subtype.ext
        funext i
        apply mul_left_cancel₀ hn
        exact congrArg (fun w : PhaseExtension.Join (C ⊕ D) V => w.val (Sum.inr i.1, i.2)) hzw
      by_cases hzero : t.val = 0
      · apply Quot.sound
        exact Or.inl ⟨Subtype.ext hzero, Subtype.ext hzero, hx (by rw [hzero]; norm_num)⟩
      · by_cases hone : t.val = 1
        · apply Quot.sound
          exact Or.inr ⟨Subtype.ext hone, Subtype.ext hone, hy hzero⟩
        · have hxx := hx hone
          have hyy := hy hzero
          subst x'
          subst y'
          rfl

/-- The actual homeomorphism from the binary quotient join to coordinate join. -/
def homeomorph : EquivariantJoinStep.Join (PhaseExtension.Join C V) (PhaseExtension.Join D V) ≃ₜ PhaseExtension.Join (C ⊕ D) V :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective toCoordinates
    ⟨toCoordinates_injective, toCoordinates_surjective⟩) continuous_toCoordinates

theorem homeomorph_mk (t : EquivariantJoinStep.Time)
    (x : PhaseExtension.Join C V) (y : PhaseExtension.Join D V) :
    homeomorph (EquivariantJoinStep.joinMk t x y) = mix (t, x, y) := rfl

end AkopyanResearch.JoinCoordinates

#print axioms AkopyanResearch.JoinCoordinates.continuous_toCoordinates
#print axioms AkopyanResearch.JoinCoordinates.toCoordinates_surjective
#print axioms AkopyanResearch.JoinCoordinates.toCoordinates_injective
#print axioms AkopyanResearch.JoinCoordinates.homeomorph
#print axioms AkopyanResearch.JoinCoordinates.toCoordinates_relabel
#print axioms AkopyanResearch.JoinCoordinates.unitHomeomorph

end
