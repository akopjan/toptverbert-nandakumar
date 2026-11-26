module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# Explicit extension from the two pure phases of a finite colored join

The source is the actual coordinate colored join: nonnegative weights on
`C × V`, total mass one, with at most one active vertex of each color.
Normalization after discarding one phase is constructed and proved continuous
on the corresponding closed half. Two nullhomotopies with a common endpoint
then extend by a literal two-branch formula. No projections, CW structures,
or homotopy extension properties are assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AkopyanResearch.PhaseExtension

universe u v w
variable {C : Type u} {V : Type v} [Fintype C] [Fintype V]

def IsJoin (x : C × V → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧
    ∀ c a b, x (c, a) ≠ 0 → x (c, b) ≠ 0 → a = b

abbrev Join (C : Type u) (V : Type v) [Fintype C] [Fintype V] :=
  {x : C × V → ℝ // IsJoin x}

variable (phase : V → Bool)

def mass (b : Bool) (x : Join C V) : ℝ :=
  ∑ i : C × V, if phase i.2 = b then x.val i else 0

abbrev Pure (b : Bool) :=
  {x : Join C V // ∀ i : C × V, phase i.2 ≠ b → x.val i = 0}

abbrev Half (b : Bool) := {x : Join C V // (1 / 2 : ℝ) ≤ mass phase b x}

theorem mass_nonneg (b : Bool) (x : Join C V) : 0 ≤ mass phase b x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact x.property.1 i
  · exact le_rfl

theorem mass_add (x : Join C V) : mass phase false x + mass phase true x = 1 := by
  rw [mass, mass, ← Finset.sum_add_distrib]
  convert x.property.2.1 using 1
  apply Finset.sum_congr rfl
  intro i _
  cases phase i.2 <;> simp

theorem mass_le_one (b : Bool) (x : Join C V) : mass phase b x ≤ 1 := by
  have h := mass_add phase x
  have hf := mass_nonneg phase false x
  have ht := mass_nonneg phase true x
  cases b <;> linarith

theorem mass_pure (b : Bool) (x : Pure (C := C) phase b) : mass phase b x.val = 1 := by
  unfold mass
  convert x.val.property.2.1 using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : phase i.2 = b
  · simp [hi]
  · simp [hi, x.property i hi]

theorem continuous_mass (b : Bool) : Continuous (mass phase b : Join C V → ℝ) := by
  unfold mass
  apply continuous_finsetSum
  intro i _
  exact continuous_if_const _ (fun _ => (continuous_apply i).comp continuous_subtype_val)
    (fun _ => continuous_const)

theorem isClosed_half (b : Bool) :
    IsClosed {x : Join C V | (1 / 2 : ℝ) ≤ mass phase b x} :=
  isClosed_le continuous_const (continuous_mass phase b)

/-- Actual normalized coordinate projection; zero-mass vertex choices never occur. -/
def normalize (b : Bool) (x : Join C V) (hx : 0 < mass phase b x) : Pure (C := C) phase b :=
  ⟨⟨fun i => (if phase i.2 = b then x.val i else 0) / mass phase b x, by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      apply div_nonneg _ hx.le
      split_ifs
      · exact x.property.1 i
      · exact le_rfl
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hx)
    · intro c a d ha hd
      apply x.property.2.2 c a d
      · intro h
        apply ha
        simp [h]
      · intro h
        apply hd
        simp [h]⟩, by
    intro i hi
    simp [hi]⟩

def projection (b : Bool) (x : Half (C := C) phase b) : Pure (C := C) phase b :=
  normalize phase b x.val (by have h := x.property; linarith)

theorem continuous_projection (b : Bool) : Continuous (projection (C := C) phase b) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : Half (C := C) phase b =>
    (if phase i.2 = b then x.val.val i else 0) / mass phase b x.val)
  apply Continuous.div
  · exact continuous_if_const _
      (fun _ => (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
      (fun _ => continuous_const)
  · exact (continuous_mass phase b).comp continuous_subtype_val
  · intro x
    have h := x.property
    linarith

def pureHalf (b : Bool) (x : Pure (C := C) phase b) : Half (C := C) phase b :=
  ⟨x.val, by rw [mass_pure phase b x]; norm_num⟩

theorem projection_pure (b : Bool) (x : Pure (C := C) phase b) :
    projection phase b (pureHalf (C := C) phase b x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (if phase i.2 = b then x.val.val i else 0) / mass phase b x.val = x.val.val i
  rw [mass_pure, div_one]
  by_cases hi : phase i.2 = b
  · simp [hi]
  · simp [hi, x.property i hi]

/-- Time zero at the pure phase and time one at the midpoint of the two phases. -/
def time (b : Bool) (x : Half (C := C) phase b) : Set.Icc (0 : ℝ) 1 :=
  ⟨2 * (1 - mass phase b x.val), by
    constructor
    · have h := mass_le_one phase b x.val; linarith
    · have h := x.property; linarith⟩

theorem continuous_time (b : Bool) : Continuous (time (C := C) phase b) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul (continuous_const.sub
    ((continuous_mass phase b).comp continuous_subtype_val))

theorem time_pure (b : Bool) (x : Pure (C := C) phase b) :
    time phase b (pureHalf (C := C) phase b x) = 0 := by
  apply Subtype.ext
  change 2 * (1 - mass phase b x.val) = 0
  rw [mass_pure]
  ring

theorem time_midpoint (b : Bool) (x : Half (C := C) phase b)
    (hx : mass phase b x.val = 1 / 2) : time phase b x = 1 := by
  apply Subtype.ext
  change 2 * (1 - mass phase b x.val) = 1
  rw [hx]
  norm_num

/-- Permuting the finite vertex set acts on actual join coordinates. -/
def relabel (e : Equiv.Perm V) (x : Join C V) : Join C V :=
  ⟨fun i => x.val (i.1, e.symm i.2), by
    refine ⟨fun i => x.property.1 _, ?_, ?_⟩
    · exact (Equiv.sum_comp (Equiv.prodCongr (Equiv.refl C) e.symm) x.val).trans
        x.property.2.1
    · intro c a d ha hd
      exact e.symm.injective (x.property.2.2 c (e.symm a) (e.symm d) ha hd)⟩

theorem continuous_relabel (e : Equiv.Perm V) :
    Continuous (relabel (C := C) e) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (i.1, e.symm i.2)).comp continuous_subtype_val

variable (e : Equiv.Perm V) (ε : Equiv.Perm Bool)
variable (he : ∀ v : V, phase (e v) = ε (phase v))

omit [Fintype V] in
theorem phase_preimage (he : ∀ v : V, phase (e v) = ε (phase v)) (v : V) : phase v = ε (phase (e.symm v)) := by
  simpa using he (e.symm v)

include he in
theorem mass_relabel (b : Bool) (x : Join C V) :
    mass phase (ε b) (relabel e x) = mass phase b x := by
  unfold mass
  calc
    (∑ i : C × V, if phase i.2 = ε b then (relabel e x).val i else 0) =
        ∑ i : C × V, if phase (e i.2) = ε b then x.val i else 0 := by
      simpa [relabel] using
        (Equiv.sum_comp (Equiv.prodCongr (Equiv.refl C) e)
          (fun i : C × V => if phase i.2 = ε b then (relabel e x).val i else 0)).symm
    _ = ∑ i : C × V, if phase i.2 = b then x.val i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he]
      simp only [ε.injective.eq_iff]

def relabelPure (b : Bool) (x : Pure (C := C) phase b) : Pure (C := C) phase (ε b) :=
  ⟨relabel e x.val, by
    intro i hi
    apply x.property (i.1, e.symm i.2)
    intro hb
    apply hi
    have h := phase_preimage phase e ε he i.2
    simpa [hb] using h⟩

def relabelHalf (b : Bool) (x : Half (C := C) phase b) : Half (C := C) phase (ε b) :=
  ⟨relabel e x.val, by rw [mass_relabel phase e ε he]; exact x.property⟩

theorem projection_relabel (b : Bool) (x : Half (C := C) phase b) :
    projection phase (ε b) (relabelHalf phase e ε he b x) =
      relabelPure phase e ε he b (projection phase b x) := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (if phase i.2 = ε b then x.val.val (i.1, e.symm i.2) else 0) /
      mass phase (ε b) (relabel e x.val) =
    (if phase (e.symm i.2) = b then x.val.val (i.1, e.symm i.2) else 0) /
      mass phase b x.val
  rw [mass_relabel phase e ε he]
  have hiff : phase i.2 = ε b ↔ phase (e.symm i.2) = b := by
    rw [phase_preimage phase e ε he i.2]
    exact ε.injective.eq_iff
  simp only [hiff]

theorem time_relabel (b : Bool) (x : Half (C := C) phase b) :
    time phase (ε b) (relabelHalf phase e ε he b x) = time phase b x := by
  apply Subtype.ext
  change 2 * (1 - mass phase (ε b) (relabel e x.val)) = 2 * (1 - mass phase b x.val)
  rw [mass_relabel phase e ε he]

variable {Y : Type w} [TopologicalSpace Y]
variable (N : ∀ b : Bool, Pure (C := C) phase b × Set.Icc (0 : ℝ) 1 → Y)

def branch (b : Bool) (x : Half (C := C) phase b) : Y :=
  N b (projection phase b x, time phase b x)

theorem continuous_branch (b : Bool) (hN : Continuous (N b)) :
    Continuous (branch phase N b) :=
  hN.comp ((continuous_projection phase b).prodMk (continuous_time phase b))

def extension (x : Join C V) : Y :=
  if hx : (1 / 2 : ℝ) ≤ mass phase false x then
    branch phase N false ⟨x, hx⟩
  else branch phase N true ⟨x, by
    have h := mass_add phase x
    have hx' := lt_of_not_ge hx
    linarith⟩

variable (endpoint : Y)
variable (hNend : ∀ b (x : Pure (C := C) phase b), N b (x, 1) = endpoint)

include endpoint hNend

omit [TopologicalSpace Y] in
theorem branch_midpoint (b : Bool) (x : Half (C := C) phase b)
    (hx : mass phase b x.val = 1 / 2) : branch phase N b x = endpoint := by
  unfold branch
  rw [time_midpoint phase b x hx]
  exact hNend b (projection phase b x)

omit [TopologicalSpace Y] in
theorem extension_eq_branch (b : Bool) (x : Half (C := C) phase b) :
    extension phase N x.val = branch phase N b x := by
  cases b with
  | false => simp only [extension, dite_eq_left x.property]
  | true =>
    unfold extension
    by_cases hf : (1 / 2 : ℝ) ≤ mass phase false x.val
    · rw [dite_eq_left hf]
      have hs := mass_add phase x.val
      have ht := x.property
      have hfm : mass phase false x.val = 1 / 2 := by linarith
      have htm : mass phase true x.val = 1 / 2 := by linarith
      rw [branch_midpoint phase N endpoint hNend false ⟨x.val, hf⟩ hfm,
        branch_midpoint phase N endpoint hNend true x htm]
    · rw [dite_eq_right hf]

theorem continuous_extension (hN : ∀ b, Continuous (N b)) :
    Continuous (extension phase N) := by
  have hcover : {x : Join C V | (1 / 2 : ℝ) ≤ mass phase false x} ∪
      {x : Join C V | (1 / 2 : ℝ) ≤ mass phase true x} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hs := mass_add phase x
    change (1 / 2 : ℝ) ≤ mass phase false x ∨ (1 / 2 : ℝ) ≤ mass phase true x
    by_cases h : (1 / 2 : ℝ) ≤ mass phase false x
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [← continuousOn_univ, ← hcover,
    continuousOn_union_iff_of_isClosed (isClosed_half phase false) (isClosed_half phase true)]
  constructor
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_branch phase N false (hN false)).congr
      (fun x => (extension_eq_branch phase N endpoint hNend false x).symm)
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_branch phase N true (hN true)).congr
      (fun x => (extension_eq_branch phase N endpoint hNend true x).symm)

omit [TopologicalSpace Y] in
theorem extension_pure (b : Bool) (x : Pure (C := C) phase b) :
    extension phase N x.val = N b (x, 0) := by
  have h := extension_eq_branch phase N endpoint hNend b (pureHalf (C := C) phase b x)
  change extension phase N x.val = branch phase N b (pureHalf (C := C) phase b x) at h
  rw [h]
  unfold branch
  rw [projection_pure, time_pure]

/-- Two actual pure-phase nullhomotopies with a common endpoint extend over the
finite colored join, with exact prescribed values on both pure subjoins. -/
theorem exists_continuous_extension
    (g : ∀ b : Bool, Pure (C := C) phase b → Y)
    (hN : ∀ b, Continuous (N b))
    (hNstart : ∀ b (x : Pure (C := C) phase b), N b (x, 0) = g b x) :
    ∃ F : Join C V → Y, Continuous F ∧ ∀ b (x : Pure (C := C) phase b), F x.val = g b x := by
  refine ⟨extension phase N, continuous_extension phase N endpoint hNend hN, ?_⟩
  intro b x
  rw [extension_pure phase N endpoint hNend, hNstart]


omit [TopologicalSpace Y] in
/-- Naturality for every vertex permutation preserving or exchanging the two
phases. Only the stated naturality of the supplied homotopies is assumed;
all coordinate-projection identities are proved above. -/
theorem extension_relabel (T : Y → Y)
    (hcompat : ∀ b (z : Pure (C := C) phase b) (t : Set.Icc (0 : ℝ) 1),
      N (ε b) (relabelPure phase e ε he b z, t) = T (N b (z, t)))
    (x : Join C V) :
    extension phase N (relabel e x) = T (extension phase N x) := by
  have half_exists : ∃ b : Bool, (1 / 2 : ℝ) ≤ mass phase b x := by
    have hs := mass_add phase x
    by_cases hf : (1 / 2 : ℝ) ≤ mass phase false x
    · exact ⟨false, hf⟩
    · exact ⟨true, by linarith⟩
  obtain ⟨b, hb⟩ := half_exists
  let xb : Half (C := C) phase b := ⟨x, hb⟩
  have hleft := extension_eq_branch phase N endpoint hNend (ε b)
    (relabelHalf phase e ε he b xb)
  have hright := extension_eq_branch phase N endpoint hNend b xb
  change extension phase N (relabel e x) =
    branch phase N (ε b) (relabelHalf phase e ε he b xb) at hleft
  change extension phase N x = branch phase N b xb at hright
  rw [hleft, hright]
  unfold branch
  rw [projection_relabel phase e ε he, time_relabel phase e ε he]
  exact hcompat b (projection phase b xb) (time phase b xb)

end AkopyanResearch.PhaseExtension

#print axioms AkopyanResearch.PhaseExtension.continuous_projection
#print axioms AkopyanResearch.PhaseExtension.continuous_extension
#print axioms AkopyanResearch.PhaseExtension.exists_continuous_extension
#print axioms AkopyanResearch.PhaseExtension.extension_relabel

end
