module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic


@[expose] public section

/-!
# Explicit contraction of augmented colored chains below the top degree

A word records either an absent color (`none`) or a vertex in that color.
All degrees are kept in one free abelian group. The boundary and contraction
are defined recursively in the first color, so the alternating signs are
part of the definitions rather than hypotheses.
-/

noncomputable section

namespace AkopyanColoredChains

open scoped BigOperators Classical

universe u

variable (A : Type u)

abbrev Word : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Option A × Word n

abbrev Chain (n : ℕ) := Word A n →₀ ℤ

def basis {n : ℕ} (w : Word A n) : Chain A n := Finsupp.single w 1

def prepend {n : ℕ} (a : Option A) : Chain A n →ₗ[ℤ] Chain A (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun w => (a, w))

@[simp] lemma prepend_basis {n : ℕ} (a : Option A) (w : Word A n) :
    prepend A a (basis A w) = basis A (n := n + 1) (a, w) := by
  simp [prepend, basis]

lemma chainMap_ext {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    {f g : Chain A n →ₗ[ℤ] M}
    (h : ∀ w, f (basis A w) = g (basis A w)) : f = g := by
  apply Finsupp.lhom_ext
  intro w r
  have hs : (Finsupp.single w r : Chain A n) = r • basis A w := by simp [basis]
  rw [hs, f.map_smul, g.map_smul, h]

def boundary : (n : ℕ) → Chain A n →ₗ[ℤ] Chain A n
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ (fun w =>
      match w with
      | (none, v) => prepend A none (boundary n (basis A v))
      | (some a, v) => prepend A none (basis A v) -
          prepend A (some a) (boundary n (basis A v)))

def contraction (o : A) : (n : ℕ) → Chain A n →ₗ[ℤ] Chain A n
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ (fun w =>
      match w with
      | (none, v) => prepend A (some o) (basis A v)
      | (some a, v) => -prepend A (some a) (contraction o n (basis A v)) +
          prepend A (some o) (contraction o n (basis A v)))

def topProjection (o : A) : (n : ℕ) → Chain A n →ₗ[ℤ] Chain A n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ (fun w =>
      match w with
      | (none, _) => 0
      | (some a, v) => prepend A (some a) (topProjection o n (basis A v)) -
          prepend A (some o) (topProjection o n (basis A v)))

@[simp] lemma boundary_basis_none (n : ℕ) (w : Word A n) :
    boundary A (n + 1) (basis A (none, w)) = prepend A none (boundary A n (basis A w)) := by
  simp [boundary, basis]

@[simp] lemma boundary_basis_some (n : ℕ) (a : A) (w : Word A n) :
    boundary A (n + 1) (basis A (some a, w)) = prepend A none (basis A w) -
      prepend A (some a) (boundary A n (basis A w)) := by
  simp [boundary, basis]

@[simp] lemma contraction_basis_none (o : A) (n : ℕ) (w : Word A n) :
    contraction A o (n + 1) (basis A (none, w)) = prepend A (some o) (basis A w) := by
  simp [contraction, basis]

@[simp] lemma contraction_basis_some (o : A) (n : ℕ) (a : A) (w : Word A n) :
    contraction A o (n + 1) (basis A (some a, w)) =
      -prepend A (some a) (contraction A o n (basis A w)) +
        prepend A (some o) (contraction A o n (basis A w)) := by
  simp [contraction, basis]

@[simp] lemma topProjection_basis_none (o : A) (n : ℕ) (w : Word A n) :
    topProjection A o (n + 1) (basis A (none, w)) = 0 := by
  simp [topProjection, basis]

@[simp] lemma topProjection_basis_some (o : A) (n : ℕ) (a : A) (w : Word A n) :
    topProjection A o (n + 1) (basis A (some a, w)) =
      prepend A (some a) (topProjection A o n (basis A w)) -
        prepend A (some o) (topProjection A o n (basis A w)) := by
  simp [topProjection, basis]

@[simp] lemma boundary_prepend_none (n : ℕ) (c : Chain A n) :
    boundary A (n + 1) (prepend A none c) = prepend A none (boundary A n c) := by
  have h : (boundary A (n + 1)).comp (prepend A none) =
      (prepend A none).comp (boundary A n) := by
    apply chainMap_ext
    intro w
    simp only [LinearMap.comp_apply]
    rw [prepend_basis A (n := n) _ w]
    exact boundary_basis_none A n w
  exact LinearMap.congr_fun h c

@[simp] lemma boundary_prepend_some (n : ℕ) (a : A) (c : Chain A n) :
    boundary A (n + 1) (prepend A (some a) c) =
      prepend A none c - prepend A (some a) (boundary A n c) := by
  have h : (boundary A (n + 1)).comp (prepend A (some a)) =
      prepend A none - (prepend A (some a)).comp (boundary A n) := by
    apply chainMap_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    rw [prepend_basis A (n := n) _ w]
    exact boundary_basis_some A n a w
  exact LinearMap.congr_fun h c

@[simp] lemma contraction_prepend_none (o : A) (n : ℕ) (c : Chain A n) :
    contraction A o (n + 1) (prepend A none c) = prepend A (some o) c := by
  have h : (contraction A o (n + 1)).comp (prepend A none) = prepend A (some o) := by
    apply chainMap_ext
    intro w
    simp only [LinearMap.comp_apply]
    rw [prepend_basis A (n := n) _ w]
    exact contraction_basis_none A o n w
  exact LinearMap.congr_fun h c

@[simp] lemma contraction_prepend_some (o : A) (n : ℕ) (a : A) (c : Chain A n) :
    contraction A o (n + 1) (prepend A (some a) c) =
      -prepend A (some a) (contraction A o n c) +
        prepend A (some o) (contraction A o n c) := by
  have h : (contraction A o (n + 1)).comp (prepend A (some a)) =
      -(prepend A (some a)).comp (contraction A o n) +
        (prepend A (some o)).comp (contraction A o n) := by
    apply chainMap_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply]
    rw [prepend_basis A (n := n) _ w]
    exact contraction_basis_some A o n a w
  exact LinearMap.congr_fun h c

@[simp] lemma topProjection_prepend_none (o : A) (n : ℕ) (c : Chain A n) :
    topProjection A o (n + 1) (prepend A none c) = 0 := by
  have h : (topProjection A o (n + 1)).comp (prepend A none) = 0 := by
    apply chainMap_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [prepend_basis A (n := n) _ w]
    exact topProjection_basis_none A o n w
  exact LinearMap.congr_fun h c

@[simp] lemma topProjection_prepend_some (o : A) (n : ℕ) (a : A) (c : Chain A n) :
    topProjection A o (n + 1) (prepend A (some a) c) =
      prepend A (some a) (topProjection A o n c) -
        prepend A (some o) (topProjection A o n c) := by
  have h : (topProjection A o (n + 1)).comp (prepend A (some a)) =
      (prepend A (some a)).comp (topProjection A o n) -
        (prepend A (some o)).comp (topProjection A o n) := by
    apply chainMap_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    rw [prepend_basis A (n := n) _ w]
    exact topProjection_basis_some A o n a w
  exact LinearMap.congr_fun h c

/-- The alternating deletion operator is genuinely a differential. -/
theorem boundary_squared (n : ℕ) :
    (boundary A n).comp (boundary A n) = 0 := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
    apply chainMap_ext
    rintro ⟨a, w⟩
    have hi : boundary A n (boundary A n (basis A w)) = 0 := LinearMap.congr_fun ih _
    cases a with
    | none =>
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      rw [boundary_basis_none A n w, boundary_prepend_none A n _, hi, map_zero]
    | some a =>
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      rw [boundary_basis_some A n a w, map_sub,
        boundary_prepend_none A n _, boundary_prepend_some A n a _, hi, map_zero]
      abel

/-- Explicit chain homotopy; the only remainder is the top-degree projection. -/
theorem contraction_identity (o : A) (n : ℕ) :
    (boundary A n).comp (contraction A o n) +
      (contraction A o n).comp (boundary A n) = LinearMap.id - topProjection A o n := by
  induction n with
  | zero => simp [boundary, contraction, topProjection]
  | succ n ih =>
    apply chainMap_ext
    rintro ⟨a, w⟩
    have hi : boundary A n (contraction A o n (basis A w)) +
        contraction A o n (boundary A n (basis A w)) = basis A w - topProjection A o n (basis A w) :=
      LinearMap.congr_fun ih (basis A w)
    change boundary A (n + 1) (contraction A o (n + 1) (basis A (a, w))) +
      contraction A o (n + 1) (boundary A (n + 1) (basis A (a, w))) =
        basis A (a, w) - topProjection A o (n + 1) (basis A (a, w))
    cases a with
    | none =>
      rw [contraction_basis_none A o n w, boundary_basis_none A n w,
        topProjection_basis_none A o n w, boundary_prepend_some A n o,
        contraction_prepend_none A o n, ← prepend_basis A (n := n) none w]
      abel
    | some a =>
      calc
        _ = prepend A (some a) (boundary A n (contraction A o n (basis A w)) +
              contraction A o n (boundary A n (basis A w))) -
            prepend A (some o) (boundary A n (contraction A o n (basis A w)) +
              contraction A o n (boundary A n (basis A w))) + prepend A (some o) (basis A w) := by
          rw [contraction_basis_some A o n a w, boundary_basis_some A n a w]
          simp only [map_add, map_sub, map_neg,
            boundary_prepend_some A n, contraction_prepend_none A o n,
            contraction_prepend_some A o n]
          abel
        _ = prepend A (some a) (basis A w - topProjection A o n (basis A w)) -
            prepend A (some o) (basis A w - topProjection A o n (basis A w)) +
              prepend A (some o) (basis A w) := by rw [hi]
        _ = _ := by
          rw [topProjection_basis_some A o n a w, ← prepend_basis A (n := n) (some a) w]
          simp only [map_sub]
          abel

def HasMissing : {n : ℕ} → Word A n → Prop
  | 0, _ => False
  | _ + 1, (none, _) => True
  | _ + 1, (some _, w) => HasMissing w

/-- The remainder vanishes on every word which omits at least one color. -/
theorem topProjection_basis_eq_zero_of_missing (o : A) (n : ℕ) (w : Word A n)
    (hw : HasMissing A w) : topProjection A o n (basis A w) = 0 := by
  induction n with
  | zero => exact False.elim hw
  | succ n ih =>
    rcases w with ⟨a, w⟩
    cases a with
    | none => exact topProjection_basis_none A o n w
    | some a =>
      rw [topProjection_basis_some A o n a w, ih w hw]
      simp

lemma chain_expansion (n : ℕ) (c : Chain A n) :
    c = ∑ w ∈ c.support, c w • basis A w := by
  simpa [Finsupp.sum, basis] using c.sum_single.symm

theorem topProjection_eq_zero_of_missing (o : A) (n : ℕ) (c : Chain A n)
    (hc : ∀ w ∈ c.support, HasMissing A w) : topProjection A o n c = 0 := by
  calc
    topProjection A o n c =
        topProjection A o n (∑ w ∈ c.support, c w • basis A w) :=
      congrArg (topProjection A o n) (chain_expansion A n c)
    _ = ∑ w ∈ c.support, c w • topProjection A o n (basis A w) := by simp
    _ = 0 := Finset.sum_eq_zero (fun w hw => by
      rw [topProjection_basis_eq_zero_of_missing A o n w (hc w hw), smul_zero])

/-- Every cycle supported on words missing a color has the explicit primitive `h c`. -/
theorem fill_cycle_of_missing (o : A) (n : ℕ) (c : Chain A n)
    (hc : ∀ w ∈ c.support, HasMissing A w) (hcycle : boundary A n c = 0) :
    boundary A n (contraction A o n c) = c := by
  have h := LinearMap.congr_fun (contraction_identity A o n) c
  change boundary A n (contraction A o n c) + contraction A o n (boundary A n c) =
    c - topProjection A o n c at h
  rw [hcycle, map_zero, add_zero, topProjection_eq_zero_of_missing A o n c hc, sub_zero] at h
  exact h

def degree : {n : ℕ} → Word A n → ℤ
  | 0, _ => 0
  | _ + 1, (none, w) => degree w
  | _ + 1, (some _, w) => degree w + 1

lemma degree_le_colors (n : ℕ) (w : Word A n) : degree A w ≤ (n : ℤ) := by
  induction n with
  | zero => simp [degree]
  | succ n ih =>
    rcases w with ⟨a, w⟩
    have h := ih w
    cases a <;> simp only [degree] <;> omega

lemma hasMissing_iff_degree_lt (n : ℕ) (w : Word A n) :
    HasMissing A w ↔ degree A w < (n : ℤ) := by
  induction n with
  | zero => simp [HasMissing, degree]
  | succ n ih =>
    rcases w with ⟨a, w⟩
    have hle := degree_le_colors A n w
    cases a with
    | none =>
      change True ↔ degree A w < ((n + 1 : ℕ) : ℤ)
      constructor
      · intro _
        omega
      · intro _
        trivial
    | some a =>
      change HasMissing A w ↔ degree A w + 1 < ((n + 1 : ℕ) : ℤ)
      rw [ih w]
      omega

def Homogeneous {n : ℕ} (k : ℤ) (c : Chain A n) : Prop :=
  ∀ w ∈ c.support, degree A w = k

lemma homogeneous_zero (n : ℕ) (k : ℤ) : Homogeneous A k (0 : Chain A n) := by
  simp [Homogeneous]

lemma homogeneous_basis (n : ℕ) (w : Word A n) :
    Homogeneous A (degree A w) (basis A w) := by
  intro v hv
  have h : v = w := by simpa [basis] using hv
  rw [h]

lemma support_prepend (n : ℕ) (a : Option A) (c : Chain A n) :
    (prepend A a c).support = c.support.image (fun w => (a, w)) := by
  let e : Word A n ↪ Word A (n + 1) := ⟨fun w => (a, w), fun _ _ h => (Prod.mk.inj h).2⟩
  have he : (e : Word A n → Word A (n + 1)) = (fun w => (a, w)) := rfl
  have h := Finsupp.support_mapDomain_embedding e c
  rw [Finset.map_eq_image, he] at h
  exact h


lemma homogeneous_add {n : ℕ} {k : ℤ} {c d : Chain A n}
    (hc : Homogeneous A k c) (hd : Homogeneous A k d) : Homogeneous A k (c + d) := by
  intro w hw
  have hn : (c + d) w ≠ 0 := Finsupp.mem_support_iff.mp hw
  by_cases hz : c w = 0
  · have hdn : d w ≠ 0 := by
      intro hdz
      apply hn
      simp [hz, hdz]
    exact hd w (Finsupp.mem_support_iff.mpr hdn)
  · exact hc w (Finsupp.mem_support_iff.mpr hz)

lemma homogeneous_smul {n : ℕ} {k : ℤ} {c : Chain A n}
    (r : ℤ) (hc : Homogeneous A k c) : Homogeneous A k (r • c) := by
  intro w hw
  have hn : (r • c) w ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hcn : c w ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  exact hc w (Finsupp.mem_support_iff.mpr hcn)

lemma homogeneous_neg {n : ℕ} {k : ℤ} {c : Chain A n}
    (hc : Homogeneous A k c) : Homogeneous A k (-c) := by
  simpa only [neg_one_zsmul] using homogeneous_smul A (-1) hc

lemma homogeneous_sub {n : ℕ} {k : ℤ} {c d : Chain A n}
    (hc : Homogeneous A k c) (hd : Homogeneous A k d) : Homogeneous A k (c - d) := by
  simpa only [sub_eq_add_neg] using homogeneous_add A hc (homogeneous_neg A hd)

lemma homogeneous_sum {n : ℕ} {k : ℤ} {T : Type*} (s : Finset T)
    (f : T → Chain A n) (hf : ∀ i ∈ s, Homogeneous A k (f i)) :
    Homogeneous A k (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using homogeneous_zero A n k
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact homogeneous_add A (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma homogeneous_prepend_none {n : ℕ} {k : ℤ} {c : Chain A n}
    (hc : Homogeneous A k c) : Homogeneous A k (prepend A none c) := by
  intro w hw
  rw [support_prepend] at hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  exact hc v hv

lemma homogeneous_prepend_some {n : ℕ} {k : ℤ} {c : Chain A n}
    (a : A) (hc : Homogeneous A k c) : Homogeneous A (k + 1) (prepend A (some a) c) := by
  intro w hw
  rw [support_prepend] at hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  change degree A v + 1 = k + 1
  rw [hc v hv]

/-- The explicit contraction raises the number of occupied colors by one. -/
theorem contraction_basis_homogeneous (o : A) (n : ℕ) (w : Word A n) :
    Homogeneous A (degree A w + 1) (contraction A o n (basis A w)) := by
  induction n with
  | zero => simpa only [contraction, LinearMap.zero_apply] using homogeneous_zero A 0 (degree A w + 1)
  | succ n ih =>
    rcases w with ⟨a, w⟩
    cases a with
    | none =>
      rw [contraction_basis_none A o n w]
      exact homogeneous_prepend_some A o (homogeneous_basis A n w)
    | some a =>
      rw [contraction_basis_some A o n a w]
      exact homogeneous_add A
        (homogeneous_neg A (homogeneous_prepend_some A a (ih w)))
        (homogeneous_prepend_some A o (ih w))

lemma homogeneous_map_of_basis {n m : ℕ} {k l : ℤ}
    (f : Chain A n →ₗ[ℤ] Chain A m) (c : Chain A n)
    (hc : Homogeneous A k c)
    (hf : ∀ w, degree A w = k → Homogeneous A l (f (basis A w))) :
    Homogeneous A l (f c) := by
  rw [chain_expansion A n c, map_sum]
  apply homogeneous_sum
  intro w hw
  rw [f.map_smul]
  exact homogeneous_smul A (c w) (hf w (hc w hw))

theorem contraction_homogeneous (o : A) (n : ℕ) {k : ℤ} (c : Chain A n)
    (hc : Homogeneous A k c) : Homogeneous A (k + 1) (contraction A o n c) := by
  apply homogeneous_map_of_basis A (contraction A o n) c hc
  intro w hw
  simpa only [hw] using contraction_basis_homogeneous A o n w

/-- A homogeneous cycle below the top number of colors has an explicit
homogeneous primitive in the next degree. -/
theorem fill_homogeneous_cycle_below_top (o : A) (n : ℕ) {k : ℤ} (c : Chain A n)
    (hk : k < (n : ℤ)) (hc : Homogeneous A k c) (hcycle : boundary A n c = 0) :
    Homogeneous A (k + 1) (contraction A o n c) ∧
      boundary A n (contraction A o n c) = c := by
  refine ⟨contraction_homogeneous A o n c hc, fill_cycle_of_missing A o n c ?_ hcycle⟩
  intro w hw
  apply (hasMissing_iff_degree_lt A n w).mpr
  rw [hc w hw]
  exact hk

/-- Fifteen colors supply primitives for augmented simplicial cycles of
all dimensions at most thirteen (`k` counts vertices, so dimension is `k-1`). -/
theorem fill_fifteen_colors_through_thirteen (o : A) {k : ℤ} (c : Chain A 15)
    (hk : k ≤ 14) (hc : Homogeneous A k c) (hcycle : boundary A 15 c = 0) :
    Homogeneous A (k + 1) (contraction A o 15 c) ∧
      boundary A 15 (contraction A o 15 c) = c :=
  fill_homogeneous_cycle_below_top A o 15 c (by omega) hc hcycle

end AkopyanColoredChains
