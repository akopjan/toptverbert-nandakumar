module
public import Mathlib

@[expose] public section

/-!
# From a planar height function to a 90-vertex almost-six map

The only topological hypothesis in this module is a continuous two-dimensional
height function on the colored simplex. It must separate every six disjoint
simplex points that have equal masses in all fifteen colors. Fourteen color
mass coordinates together with the two height coordinates then give a map to
sixteen-dimensional space. Equality of the missing color mass follows from
the equation saying that the total mass is one.

The construction is conditional on that height function. It does not establish
the existence of a safe fifteen-color table.
-/

set_option autoImplicit false

namespace AkopyanResearch.SimplexEmbedding

universe u

/-- The standard simplex in the coordinate space indexed by `V`. -/
def simplexSet (V : Type u) [Fintype V] : Set (V → ℝ) :=
  {x | (∀ v : V, 0 ≤ x v) ∧ ∑ v : V, x v = 1}

theorem isClosed_simplexSet (V : Type u) [Fintype V] : IsClosed (simplexSet V) := by
  have hnonneg := isClosed_iInter (fun v : V =>
    isClosed_le (continuous_const : Continuous (fun _ : V → ℝ => (0 : ℝ)))
      (continuous_apply v))
  have hsum := isClosed_eq
    (continuous_finsetSum Finset.univ (fun v _ => continuous_apply v))
    (continuous_const : Continuous (fun _ : V → ℝ => (1 : ℝ)))
  convert hnonneg.inter hsum using 1
  ext x
  simp [simplexSet]

abbrev Vertex := Fin 15 × Fin 6
abbrev Simplex := {x : Vertex → ℝ // x ∈ simplexSet Vertex}
abbrev Simplex90 := {x : Fin 90 → ℝ // x ∈ simplexSet (Fin 90)}

/-- Pairwise disjoint supports of the six coordinate vectors. -/
def DisjointSupports {V : Type u} (x : Fin 6 → V → ℝ) : Prop :=
  ∀ r s : Fin 6, r ≠ s → ∀ v : V, x r v = 0 ∨ x s v = 0

/-- The mass in a specified color. -/
def mass (x : Simplex) (c : Fin 15) : ℝ := ∑ l : Fin 6, x.val (c, l)

theorem total_mass (x : Simplex) : ∑ c : Fin 15, mass x c = 1 := by
  simpa only [Fintype.sum_prod_type, mass] using x.property.2

/-- Retain colors one through fourteen and append the two height coordinates. -/
def massAndHeight (h : Simplex → Fin 2 → ℝ) (x : Simplex) : Fin 16 → ℝ :=
  fun i => Fin.addCases (m := 14) (n := 2) (motive := fun _ => ℝ)
    (fun j : Fin 14 => mass x j.succ) (h x) i

theorem continuous_massAndHeight (h : Simplex → Fin 2 → ℝ) (hh : Continuous h) :
    Continuous (massAndHeight h) := by
  apply continuous_pi
  intro i
  refine Fin.addCases (m := 14) (n := 2) ?_ ?_ i
  · intro i
    simp only [massAndHeight, Fin.addCases_left]
    unfold mass
    exact continuous_finsetSum _
      (fun l _ => (continuous_apply (i.succ, l)).comp continuous_subtype_val)
  · intro i
    simp only [massAndHeight, Fin.addCases_right]
    exact (continuous_apply i).comp hh

theorem mass_eq_of_massAndHeight_eq
    (h : Simplex → Fin 2 → ℝ) {x y : Simplex}
    (heq : massAndHeight h x = massAndHeight h y) :
    ∀ c : Fin 15, mass x c = mass y c := by
  have htail : ∀ i : Fin 14, mass x i.succ = mass y i.succ := by
    intro i
    have hi := congrArg (fun v : Fin 16 → ℝ => v (Fin.castAdd 2 i)) heq
    simpa only [massAndHeight, Fin.addCases_left] using hi
  intro c
  refine Fin.cases ?_ htail c
  have hx := total_mass x
  have hy := total_mass y
  rw [Fin.sum_univ_succ] at hx hy
  have hsum : (∑ i : Fin 14, mass x i.succ) = ∑ i : Fin 14, mass y i.succ :=
    Finset.sum_congr rfl (fun i _ => htail i)
  linarith

theorem height_eq_of_massAndHeight_eq
    (h : Simplex → Fin 2 → ℝ) {x y : Simplex}
    (heq : massAndHeight h x = massAndHeight h y) : h x = h y := by
  funext i
  have hi := congrArg (fun v : Fin 16 → ℝ => v (Fin.natAdd 14 i)) heq
  simpa only [massAndHeight, Fin.addCases_right] using hi

/-- The precise separation property required of the planar height function. -/
def SeparatesEqualMass (h : Simplex → Fin 2 → ℝ) : Prop :=
  ∀ x : Fin 6 → Simplex,
    DisjointSupports (fun r => (x r).val) →
    (∀ (r : Fin 6) (c : Fin 15), mass (x r) c = mass (x 0) c) →
    ∃ r : Fin 6, h (x r) ≠ h (x 0)

theorem massAndHeight_separates_disjoint
    (h : Simplex → Fin 2 → ℝ) (hs : SeparatesEqualMass h)
    (x : Fin 6 → Simplex) (hx : DisjointSupports (fun r => (x r).val)) :
    ∃ r : Fin 6, massAndHeight h (x r) ≠ massAndHeight h (x 0) := by
  by_contra hn
  push Not at hn
  obtain ⟨r, hr⟩ := hs x hx (fun r => mass_eq_of_massAndHeight_eq h (hn r))
  exact hr (height_eq_of_massAndHeight_eq h (hn r))

/-- Reindex the ninety vertices by fifteen colors with six labels each. -/
def vertexEquiv : Vertex ≃ Fin 90 := finProdFinEquiv

def toColoredSimplex (x : Simplex90) : Simplex :=
  ⟨fun v => x.val (vertexEquiv v), fun v => x.property.1 (vertexEquiv v), by
    rw [Equiv.sum_comp]
    exact x.property.2⟩

theorem continuous_toColoredSimplex : Continuous toColoredSimplex := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact (continuous_apply (vertexEquiv v)).comp continuous_subtype_val

/-- A continuous height function separating equal-mass disjoint points gives the
required almost-six map on the standard simplex with ninety vertices. -/
theorem exists_almostSix_of_height_separates_equal_mass
    (h : Simplex → Fin 2 → ℝ) (hh : Continuous h) (hs : SeparatesEqualMass h) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ,
      ContinuousOn g (simplexSet (Fin 90)) ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ r : Fin 6, x r ∈ simplexSet (Fin 90)) →
        DisjointSupports x →
        ∃ r : Fin 6, g (x r) ≠ g (x 0) := by
  classical
  let f : Simplex90 → Fin 16 → ℝ := fun x => massAndHeight h (toColoredSimplex x)
  have hf : Continuous f := (continuous_massAndHeight h hh).comp continuous_toColoredSimplex
  let g : (Fin 90 → ℝ) → Fin 16 → ℝ := fun x =>
    if hx : x ∈ simplexSet (Fin 90) then f ⟨x, hx⟩ else 0
  have hg : ContinuousOn g (simplexSet (Fin 90)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : Simplex90 => g x.val)
    have heq : (fun x : Simplex90 => g x.val) = f := by
      funext x
      simp [g, x.property]
    rw [heq]
    exact hf
  refine ⟨g, hg, ?_⟩
  intro x hx hdisjoint
  let y : Fin 6 → Simplex := fun r => toColoredSimplex ⟨x r, hx r⟩
  have hy : DisjointSupports (fun r => (y r).val) := by
    intro r s hrs v
    exact hdisjoint r s hrs (vertexEquiv v)
  obtain ⟨r, hr⟩ := massAndHeight_separates_disjoint h hs y hy
  refine ⟨r, ?_⟩
  simpa only [g, dite_eq_left (hx r), dite_eq_left (hx 0), f, y] using hr

/-- A continuous map on the closed simplex extends to the ambient coordinate space. -/
theorem exists_continuous_extension_of_simplex
    (f : Simplex90 → Fin 16 → ℝ) (hf : Continuous f) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ,
      Continuous g ∧ ∀ x : Simplex90, g x.val = f x := by
  let F : C(Simplex90, Fin 16 → ℝ) := ⟨f, hf⟩
  obtain ⟨G, hG⟩ := F.exists_restrict_eq (isClosed_simplexSet (Fin 90))
  refine ⟨G, G.continuous, ?_⟩
  intro x
  exact congrArg (fun k : C(Simplex90, Fin 16 → ℝ) => k x) hG

/-- Global ambient continuity follows from the Tietze extension theorem, without
altering any value on the simplex or imposing a degree condition on the height. -/
theorem exists_continuous_almostSix_of_height_separates_equal_mass
    (h : Simplex → Fin 2 → ℝ) (hh : Continuous h) (hs : SeparatesEqualMass h) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ,
      Continuous g ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ r : Fin 6, x r ∈ simplexSet (Fin 90)) →
        DisjointSupports x →
        ∃ r : Fin 6, g (x r) ≠ g (x 0) := by
  obtain ⟨f, hf, hseparate⟩ :=
    exists_almostSix_of_height_separates_equal_mass h hh hs
  have hrestrict : Continuous (fun x : Simplex90 => f x.val) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  obtain ⟨g, hg, heq⟩ :=
    exists_continuous_extension_of_simplex (fun x : Simplex90 => f x.val) hrestrict
  refine ⟨g, hg, ?_⟩
  intro x hx hdisjoint
  obtain ⟨r, hr⟩ := hseparate x hx hdisjoint
  refine ⟨r, ?_⟩
  intro he
  apply hr
  calc
    f (x r) = g (x r) := (heq ⟨x r, hx r⟩).symm
    _ = g (x 0) := he
    _ = f (x 0) := heq ⟨x 0, hx 0⟩

end AkopyanResearch.SimplexEmbedding


end
