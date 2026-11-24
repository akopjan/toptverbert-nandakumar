module

public import AkopyanResearch.Completion.JoinVertexMap

/-!
# Masses and vertex labels as actual colored-join coordinates

There is one fixed finite color set. A zero-mass color contributes no
coordinate, so changing its label has literally no effect. In particular,
restriction to a face uses the same ambient colored join and does not
choose a new iterated-join map depending on the number of active colors.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.JoinMassCoordinates

open scoped BigOperators Classical
open PhaseExtension JoinVertexMap

universe u v w
variable {C : Type u} {V : Type v} {W : Type w}
  [Fintype C] [Fintype V] [Fintype W]

/-- The finite simplex of color masses. -/
abbrev Mass (C : Type u) [Fintype C] :=
  {x : C → ℝ // (∀ c, 0 ≤ x c) ∧ (∑ c, x c) = 1}

/-- The weight of color `c` is placed at its chosen vertex `σ c`. -/
def fromMass (z : Mass C) (σ : C → V) : Join C V :=
  ⟨fun i => if i.2 = σ i.1 then z.val i.1 else 0, by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ite_nonneg (z.property.1 i.1) le_rfl
    · rw [Fintype.sum_prod_type]
      simpa using z.property.2
    · intro c a b ha hb
      have he : a = σ c := by
        by_contra hn
        exact ha (ite_eq_right hn)
      have hf : b = σ c := by
        by_contra hn
        exact hb (ite_eq_right hn)
      exact he.trans hf.symm⟩

@[simp] theorem fromMass_val (z : Mass C) (σ : C → V) (c : C) (v : V) :
    (fromMass z σ).val (c, v) = if v = σ c then z.val c else 0 := rfl

@[simp] theorem fromMass_color_mass (z : Mass C) (σ : C → V) (c : C) :
    ∑ v : V, (fromMass z σ).val (c, v) = z.val c := by
  simp

theorem continuous_fromMass (σ : C → V) : Continuous (fun z : Mass C => fromMass z σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact continuous_if_const (i.2 = σ i.1)
    (fun _ => (continuous_apply i.1).comp continuous_subtype_val)
    (fun _ => continuous_const)

/-- With discrete labels the parametrization is jointly continuous. -/
theorem continuous_fromMass_joint [TopologicalSpace V] [DiscreteTopology V] :
    Continuous (fun p : Mass C × (C → V) => fromMass p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr continuous_fromMass

theorem mapVertices_fromMass (f : V → W) (z : Mass C) (σ : C → V) :
    mapVertices f (fromMass z σ) = fromMass z (f ∘ σ) := by
  apply Subtype.ext
  funext i
  rw [mapVertices_val, Finset.sum_eq_single (σ i.1)]
  · simp [fromMass, eq_comm]
  · intro v _ hv
    simp [hv]
  · simp

theorem relabel_fromMass (e : Equiv.Perm V) (z : Mass C) (σ : C → V) :
    relabel e (fromMass z σ) = fromMass z (e ∘ σ) := by
  rw [← mapVertices_perm, mapVertices_fromMass]

/-- Only labels at nonzero-mass colors enter the coordinate point. -/
theorem fromMass_congr_of_support (z : Mass C) (σ τ : C → V)
    (h : ∀ c, z.val c ≠ 0 → σ c = τ c) :
    fromMass z σ = fromMass z τ := by
  apply Subtype.ext
  funext i
  by_cases hi : z.val i.1 = 0
  · simp [fromMass, hi]
  · simp [fromMass, h i.1 hi]

theorem fromMass_eq_iff (z : Mass C) (σ τ : C → V) :
    fromMass z σ = fromMass z τ ↔ ∀ c, z.val c ≠ 0 → σ c = τ c := by
  refine ⟨?_, fromMass_congr_of_support z σ τ⟩
  intro he c hc
  have hv := congrArg (fun x : Join C V => x.val (c, σ c)) he
  by_contra hn
  exact hc (by simpa [hn] using hv)

/-- The labels of zero-mass colors may lie in either phase. -/
theorem fromMass_pure (phase : V → Bool) (b : Bool) (z : Mass C) (σ : C → V)
    (h : ∀ c, z.val c ≠ 0 → phase (σ c) = b) :
    ∀ i : C × V, phase i.2 ≠ b → (fromMass z σ).val i = 0 := by
  rintro ⟨c, v⟩ hv
  by_cases hz : z.val c = 0
  · simp [hz]
  · have he : v ≠ σ c := by
      intro he
      exact hv ((congrArg phase he).trans (h c hz))
    simp [he]

def fromMassPure (phase : V → Bool) (b : Bool) (z : Mass C) (σ : C → V)
    (h : ∀ c, z.val c ≠ 0 → phase (σ c) = b) : Pure (C := C) phase b :=
  ⟨fromMass z σ, fromMass_pure phase b z σ h⟩

end AkopyanResearch.JoinMassCoordinates
