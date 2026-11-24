module

public import Mathlib
public import AkopyanResearch.Completion.ProductExpectation
public import AkopyanResearch.Completion.MatchingExtraction

/-!
# Realization of continuous compatible height tables

The construction separates the continuous realization step from the existence
of a safe table. In particular, no polynomial-degree condition is imposed on
the table. The latter existence problem is not solved in this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Topology

namespace AkopyanResearch.TableRealization

/-- The simplex with vertices indexed by a finite type. -/
abbrev Simplex (I : Type*) [Fintype I] :=
  {x : I → ℝ // (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1}

instance simplex_compactSpace (I : Type*) [Fintype I] : CompactSpace (Simplex I) := by
  apply isCompact_iff_compactSpace.mp
  have hclosed : IsClosed {x : I → ℝ | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1} := by
    have hnonneg := isClosed_iInter (fun i : I =>
      isClosed_le (continuous_const : Continuous (fun _ : I → ℝ => (0 : ℝ)))
        (continuous_apply i))
    have htotal := isClosed_eq
      (continuous_finsetSum Finset.univ (fun i _ => continuous_apply i))
      (continuous_const : Continuous (fun _ : I → ℝ => (1 : ℝ)))
    convert hnonneg.inter htotal using 1
    ext x
    simp
  refine IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : I → ℝ) 1)) hclosed ?_
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  change x i ≤ (1 : ℝ)
  rw [← hx.2]
  exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)

variable {C L : Type*} [Fintype C] [Fintype L]

/-- Masses of the colours, together with one conditional distribution per colour. -/
abbrev ParameterSpace (C L : Type*) [Fintype C] [Fintype L] :=
  Simplex C × (C → Simplex L)

/-- Recover the mass of each colour from barycentric coordinates. -/
def colourMass (x : Simplex (C × L)) : Simplex C :=
  ⟨fun c => ∑ l, x.val (c, l),
    fun c => Finset.sum_nonneg (fun l _ => x.property.1 (c, l)), by
      rw [← Fintype.sum_prod_type]
      exact x.property.2⟩

/-- Multiply a colour mass by its conditional label distribution. -/
def project (p : ParameterSpace C L) : Simplex (C × L) :=
  ⟨fun v => p.1.val v.1 * (p.2 v.1).val v.2,
    fun v => mul_nonneg (p.1.property.1 v.1) ((p.2 v.1).property.1 v.2), by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, (p.2 _).property.2, mul_one]
      exact p.1.property.2⟩

theorem continuous_colourMass : Continuous (colourMass (C := C) (L := L)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro c
  exact continuous_finsetSum _ (fun l _ => (continuous_apply (c, l)).comp continuous_subtype_val)

theorem continuous_project : Continuous (project (C := C) (L := L)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact ((continuous_apply v.1).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply v.2).comp
      (continuous_subtype_val.comp ((continuous_apply v.1).comp continuous_snd)))

theorem colourMass_project (p : ParameterSpace C L) : colourMass (project p) = p.1 := by
  apply Subtype.ext
  funext c
  change (∑ l, p.1.val c * (p.2 c).val l) = p.1.val c
  rw [← Finset.mul_sum, (p.2 c).property.2, mul_one]

theorem coordinate_le_mass (x : Simplex (C × L)) (c : C) (l : L) :
    x.val (c, l) ≤ (colourMass x).val c := by
  exact Finset.single_le_sum (fun j _ => x.property.1 (c, j)) (Finset.mem_univ l)

theorem coordinate_eq_zero_of_mass_eq_zero (x : Simplex (C × L))
    (c : C) (h : (colourMass x).val c = 0) (l : L) : x.val (c, l) = 0 := by
  have hlo := x.property.1 (c, l)
  have hhi := coordinate_le_mass x c l
  linarith

variable [DecidableEq L] [Nonempty L]

/-- A harmless arbitrary distribution used on colours of zero mass. -/
def defaultDistribution : Simplex L :=
  ⟨fun l => if l = Classical.arbitrary L then 1 else 0,
    by intro l; dsimp; split_ifs <;> norm_num,
    by simp⟩

/-- Conditional distributions are used only algebraically; they need not be
continuous when a colour mass tends to zero. -/
def conditionals (x : Simplex (C × L)) (c : C) : Simplex L :=
  if h : (colourMass x).val c = 0 then defaultDistribution
  else ⟨fun l => x.val (c, l) / (colourMass x).val c,
    fun l => div_nonneg (x.property.1 (c, l)) ((colourMass x).property.1 c), by
      rw [← Finset.sum_div]
      exact div_self h⟩

theorem project_conditionals (x : Simplex (C × L)) :
    project (colourMass x, conditionals x) = x := by
  apply Subtype.ext
  funext v
  change (colourMass x).val v.1 * (conditionals x v.1).val v.2 = x.val v
  by_cases h : (colourMass x).val v.1 = 0
  · simp only [h, zero_mul]
    exact (coordinate_eq_zero_of_mass_eq_zero x v.1 h v.2).symm
  · simp only [conditionals, dite_eq_right h]
    field_simp

theorem project_surjective : Function.Surjective (project (C := C) (L := L)) := by
  intro x
  exact ⟨(colourMass x, conditionals x), project_conditionals x⟩

/-- A compact parametrization of the simplex is a quotient map. This avoids
claiming continuity of the normalized coordinates at a zero mass. -/
theorem project_isQuotientMap : IsQuotientMap (project (C := C) (L := L)) :=
  IsQuotientMap.of_surjective_continuous project_surjective continuous_project

omit [DecidableEq L] [Nonempty L] in
theorem same_project_same_mass {p q : ParameterSpace C L}
    (h : project p = project q) : p.1 = q.1 := by
  simpa only [colourMass_project] using congrArg colourMass h

omit [DecidableEq L] [Nonempty L] in
theorem same_project_same_active_distribution {p q : ParameterSpace C L}
    (h : project p = project q) (c : C) (hc : p.1.val c ≠ 0) : p.2 c = q.2 c := by
  have hz := same_project_same_mass h
  apply Subtype.ext
  funext l
  have hv := congrArg (fun x : Simplex (C × L) => x.val (c, l)) h
  change p.1.val c * (p.2 c).val l = q.1.val c * (q.2 c).val l at hv
  rw [← hz] at hv
  exact mul_left_cancel₀ hc hv

/-- A continuous height on the compact parameter space descends whenever it is
constant on the fibres of `project`. -/
theorem exists_continuous_descent {E : Type*} [TopologicalSpace E]
    (F : ParameterSpace C L → E) (hF : Continuous F)
    (hfibre : ∀ p q, project p = project q → F p = F q) :
    ∃ h : Simplex (C × L) → E, Continuous h ∧ ∀ p, h (project p) = F p := by
  let π : C(ParameterSpace C L, Simplex (C × L)) := ⟨project, continuous_project⟩
  have hπ : IsQuotientMap π := project_isQuotientMap
  let F' : C(ParameterSpace C L, E) := ⟨F, hF⟩
  have hfactor : Function.FactorsThrough F' π := fun _ _ hpq => hfibre _ _ hpq
  refine ⟨hπ.lift F' hfactor, (hπ.lift F' hfactor).continuous, ?_⟩
  intro p
  exact congrArg (fun f : C(ParameterSpace C L, E) => f p) (hπ.lift_comp F' hfactor)

variable {T : Type*} [DecidableEq C]

/-- A table may have any number of real output coordinates. -/
abbrev HeightTable (C L T : Type*) [Fintype C] :=
  Simplex C → (C → L) → (T → ℝ)

/-- At a fixed mass vector, only positive-mass colours may affect the value. -/
def Compatible (H : HeightTable C L T) : Prop :=
  ∀ z : Simplex C,
    ProductExpectation.DependsOn (fun c => z.val c ≠ 0) (H z)

/-- Multilinear averaging over the conditional label distributions. -/
def parameterHeight (H : HeightTable C L T) (p : ParameterSpace C L) (t : T) : ℝ :=
  ProductExpectation.expectation (fun c l => (p.2 c).val l) (fun w => H p.1 w t)

omit [DecidableEq L] [Nonempty L] in
theorem continuous_parameterHeight (H : HeightTable C L T) (hH : Continuous H) :
    Continuous (parameterHeight H) := by
  apply continuous_pi
  intro t
  unfold parameterHeight ProductExpectation.expectation
  apply continuous_finsetSum
  intro w _
  apply Continuous.mul
  · apply continuous_finsetProd
    intro c _
    exact (continuous_apply (w c)).comp
      (continuous_subtype_val.comp ((continuous_apply c).comp continuous_snd))
  · exact (continuous_apply t).comp
      ((continuous_apply w).comp (hH.comp continuous_fst))

omit [DecidableEq L] [Nonempty L] in
theorem parameterHeight_constant_on_fibres (H : HeightTable C L T)
    (hcompat : Compatible H) {p q : ParameterSpace C L}
    (hpq : project p = project q) : parameterHeight H p = parameterHeight H q := by
  have hz := same_project_same_mass hpq
  funext t
  unfold parameterHeight
  rw [← hz]
  apply ProductExpectation.expectation_congr_of_dependsOn
    (fun c l => (p.2 c).val l) (fun c l => (q.2 c).val l)
    (fun c => (p.2 c).property.2) (fun c => (q.2 c).property.2)
    (fun c => p.1.val c ≠ 0)
  · intro w w' hw
    exact congrFun (hcompat p.1 w w' hw) t
  · intro c hc
    exact congrArg Subtype.val (same_project_same_active_distribution hpq c hc)

/-- Every continuous compatible height table has a continuous realization on
the entire simplex. Polynomial or quadratic dependence is not required. -/
theorem exists_continuous_height (H : HeightTable C L T)
    (hH : Continuous H) (hcompat : Compatible H) :
    ∃ h : Simplex (C × L) → (T → ℝ), Continuous h ∧
      ∀ p : ParameterSpace C L, h (project p) = parameterHeight H p := by
  exact exists_continuous_descent (parameterHeight H)
    (continuous_parameterHeight H hH)
    (fun _ _ hpq => parameterHeight_constant_on_fibres H hcompat hpq)

omit [Nonempty L] in
theorem parameterHeight_of_active_dirac (H : HeightTable C L T)
    (hcompat : Compatible H) (p : ParameterSpace C L) (w : C → L)
    (hdirac : ∀ c, p.1.val c ≠ 0 → ∀ l,
      (p.2 c).val l = if l = w c then 1 else 0) :
    parameterHeight H p = H p.1 w := by
  funext t
  apply ProductExpectation.expectation_eq_of_dirac_on
    (fun c l => (p.2 c).val l) (fun c => (p.2 c).property.2)
    (fun c => p.1.val c ≠ 0) (fun w => H p.1 w t)
  · intro u v huv
    exact congrFun (hcompat p.1 u v huv) t
  · exact hdirac

/-- Safety requires independent label permutations in every colour and holds
also on the boundary of the mass simplex. -/
def Safe (base : L) (H : HeightTable C L T) : Prop :=
  ∀ z : Simplex C, ∀ M : C → Equiv.Perm L,
    ∃ j : L, H z (fun c => M c j) ≠ H z (fun c => M c base)

/-- Pairwise disjoint supports for the rows of a family of simplex points. -/
def DisjointSupports (x : L → Simplex (C × L)) : Prop :=
  ∀ i j, i ≠ j → ∀ v, (x i).val v = 0 ∨ (x j).val v = 0

/-- The realized height separates disjoint rows having the same colour masses. -/
theorem realized_height_separates (H : HeightTable C L T)
    (hcompat : Compatible H) (base : L) (hsafe : Safe base H)
    (h : Simplex (C × L) → (T → ℝ))
    (hreal : ∀ p : ParameterSpace C L, h (project p) = parameterHeight H p)
    (x : L → Simplex (C × L)) (hdisjoint : DisjointSupports x)
    (hmass : ∀ j, colourMass (x j) = colourMass (x base)) :
    ∃ j : L, h (x j) ≠ h (x base) := by
  let z := colourMass (x base)
  obtain ⟨M, _, hnormalized, _⟩ := MatchingExtraction.exists_colored_matching
    (fun r c l => (x r).val (c, l)) z.val
    (fun r c l => (x r).property.1 (c, l))
    (fun r c => congrArg (fun s : Simplex C => s.val c) (hmass r))
    (fun r s hrs c l => hdisjoint r s hrs (c, l))
  have heval (j : L) : h (x j) = H z (fun c => M c j) := by
    rw [← project_conditionals (x j), hreal]
    have hdirac : ∀ c, (colourMass (x j)).val c ≠ 0 → ∀ l,
        (conditionals (x j) c).val l = if l = M c j then 1 else 0 := by
      intro c hc l
      have hcz : z.val c ≠ 0 := by simpa only [hmass j] using hc
      have hpos : 0 < z.val c := lt_of_le_of_ne (z.property.1 c) (Ne.symm hcz)
      simp only [conditionals, dite_eq_right hc]
      rw [hmass j]
      exact hnormalized c hpos j l
    rw [parameterHeight_of_active_dirac H hcompat _ (fun c => M c j) hdirac]
    rw [hmass j]
  obtain ⟨j, hj⟩ := hsafe z M
  refine ⟨j, ?_⟩
  rw [heval j, heval base]
  exact hj

/-- This is a conditional realization theorem: the existence of the safe table
remains an explicit hypothesis. -/
theorem exists_height_separating_equal_mass (H : HeightTable C L T)
    (hH : Continuous H) (hcompat : Compatible H) (base : L) (hsafe : Safe base H) :
    ∃ h : Simplex (C × L) → (T → ℝ), Continuous h ∧
      ∀ x : L → Simplex (C × L), DisjointSupports x →
        (∀ j, colourMass (x j) = colourMass (x base)) →
          ∃ j : L, h (x j) ≠ h (x base) := by
  obtain ⟨h, hh, hreal⟩ := exists_continuous_height H hH hcompat
  exact ⟨h, hh, fun x hd hm =>
    realized_height_separates H hcompat base hsafe h hreal x hd hm⟩

end AkopyanResearch.TableRealization

