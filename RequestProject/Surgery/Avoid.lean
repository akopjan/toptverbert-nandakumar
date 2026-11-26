module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# General position: avoiding finitely many linear subspaces

* `Surgery.exists_not_mem_finset_submodule`: a real vector space is not a finite union of proper
  submodules (also inside a given submodule);
* `Surgery.exists_arc_apex`: two points of `ker Q` which avoid the subspaces `ker Q j`
  (`ker Q j ≠ ker Q`) can be joined inside `ker Q` by a two-segment path avoiding them, provided
  every `Q j` has rank at least two on `ker Q`;
* `Surgery.exists_cone_apex`: finitely many segments avoiding subspaces of codimension at least
  three can be coned off from a common apex, avoiding the subspaces.
-/

open Set

namespace Surgery

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A real vector space is not a finite union of proper submodules. -/
lemma exists_not_mem_finset_submodule {ι : Type*} (s : Finset ι) (p : ι → Submodule ℝ M)
    (h : ∀ i ∈ s, p i ≠ ⊤) : ∃ v : M, ∀ i ∈ s, v ∉ p i := by
  classical
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (K := ℝ)
    (Finset.univ : Finset s) (fun i => p i) (fun i => h i i.2)
    (by rw [ENat.card_eq_top_of_infinite]; exact ENat.coe_lt_top _)
  obtain ⟨v, -, hv⟩ := exists_of_ssubset hss
  refine ⟨v, fun i hi hvi => hv ?_⟩
  exact mem_iUnion₂.2 ⟨⟨i, hi⟩, Finset.mem_univ _, hvi⟩

/-- Version inside a submodule `W`. -/
lemma exists_mem_not_mem_finset_submodule {ι : Type*} (W : Submodule ℝ M) (s : Finset ι)
    (p : ι → Submodule ℝ M) (h : ∀ i ∈ s, ¬ (W : Set M) ⊆ p i) :
    ∃ v ∈ W, ∀ i ∈ s, v ∉ p i := by
  obtain ⟨v, hv⟩ := exists_not_mem_finset_submodule (M := W) s (fun i => (p i).comap W.subtype)
    (by
      intro i hi htop
      apply h i hi
      intro x hx
      have : (⟨x, hx⟩ : W) ∈ (p i).comap W.subtype := by
        have h' : (p i).comap W.subtype = ⊤ := htop
        rw [h']; exact Submodule.mem_top
      simpa using this)
  exact ⟨v, v.2, fun i hi hvi => hv i hi (by simpa using hvi)⟩

/-- If `z` lies outside `S ⊔ span {a}`, `a ∉ S` and `S` is a submodule, then the segment
`[a, z]` misses `S`. -/
lemma segment_disjoint_of_not_mem_sup {S : Submodule ℝ M} {a z : M} (ha : a ∉ S)
    (hz : z ∉ S ⊔ Submodule.span ℝ {a}) : ∀ x ∈ segment ℝ a z, x ∉ S := by
  rintro x ⟨μa, μz, hμa, hμz, hsum, rfl⟩ hx
  rcases eq_or_lt_of_le hμz with h0 | hpos
  · subst h0
    simp only [zero_smul, add_zero] at hx
    have : μa = 1 := by linarith
    subst this
    simp at hx
    exact ha hx
  · apply hz
    have hz' : z = μz⁻¹ • (μa • a + μz • z) + (-(μz⁻¹ * μa)) • a := by
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      rw [neg_smul]; abel
    rw [hz']
    exact Submodule.add_mem _ (Submodule.mem_sup_left (S.smul_mem _ hx))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)))

/-- If `z` lies outside `S ⊔ span {a, b}` and the segment `[a, b]` misses the submodule `S`,
then the triangle with vertices `a, b, z` misses `S`. -/
lemma triangle_disjoint_of_not_mem_sup {S : Submodule ℝ M} {a b z : M}
    (hab : ∀ y ∈ segment ℝ a b, y ∉ S) (hz : z ∉ S ⊔ Submodule.span ℝ {a, b}) :
    ∀ y ∈ segment ℝ a b, ∀ x ∈ segment ℝ y z, x ∉ S := by
  intro y hy
  have hyspan : y ∈ Submodule.span ℝ {a, b} := by
    obtain ⟨μa, μb, -, -, -, rfl⟩ := hy
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  refine segment_disjoint_of_not_mem_sup (hab y hy) ?_
  intro hz'
  apply hz
  refine (sup_le_sup_left ?_ S) hz'
  rw [Submodule.span_le]
  simpa using hyspan

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- **Arcs inside a level set.** Let `Q`, `Q j` be linear maps such that each `Q j` with a
different kernel has rank at least two on `ker Q`.  Two points `a, b ∈ ker Q` lying in no other
kernel can be joined inside `ker Q` by the broken line `a → z → b` avoiding all other kernels. -/
lemma exists_arc_apex {ι : Type*} [Fintype ι] (Q : V →ₗ[ℝ] (Fin n → ℝ))
    (Qs : ι → V →ₗ[ℝ] (Fin n → ℝ))
    (hrank : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q →
      ∃ u ∈ LinearMap.ker Q, ∃ w ∈ LinearMap.ker Q, LinearIndependent ℝ ![Qs j u, Qs j w])
    {a b : V} (ha : Q a = 0) (hb : Q b = 0)
    (haj : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j a ≠ 0)
    (hbj : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j b ≠ 0) :
    ∃ z, Q z = 0 ∧ ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q →
      (∀ x ∈ segment ℝ a z, Qs j x ≠ 0) ∧ (∀ x ∈ segment ℝ z b, Qs j x ≠ 0) := by
  classical
  let B : Finset ι := Finset.univ.filter fun j => LinearMap.ker (Qs j) ≠ LinearMap.ker Q
  let S : ι → Submodule ℝ V := fun j => LinearMap.ker (Qs j) ⊓ LinearMap.ker Q
  -- the bad submodules
  let p : ι ⊕ ι → Submodule ℝ V := fun c => match c with
    | .inl j => S j ⊔ Submodule.span ℝ {a}
    | .inr j => S j ⊔ Submodule.span ℝ {b}
  let s : Finset (ι ⊕ ι) := B.disjSum B
  have key : ∀ (j : ι) (c : V), j ∈ B →
      ¬ (LinearMap.ker Q ≤ S j ⊔ Submodule.span ℝ {c}) := by
    intro j c hj hsub
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨u, hu, w, hw, hind⟩ := hrank j hj
    have himg : ∀ x ∈ LinearMap.ker Q, ∃ t : ℝ, Qs j x = t • Qs j c := by
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsub hx)
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
      refine ⟨t, ?_⟩
      have : Qs j y = 0 := (Submodule.mem_inf.1 hy).1
      simp [this]
    obtain ⟨t1, ht1⟩ := himg u hu
    obtain ⟨t2, ht2⟩ := himg w hw
    rw [ht1, ht2] at hind
    -- two multiples of the same vector are linearly dependent
    by_cases h1 : t1 = 0
    · have h := LinearIndependent.ne_zero 0 hind
      simp [h1] at h
    · have := LinearIndependent.pair_iff.1 hind t2 (-t1) (by
        simp only [smul_smul, ← add_smul]; ring_nf; simp)
      exact h1 (by simpa using this.2)
  obtain ⟨z, hzQ, hz⟩ := exists_mem_not_mem_finset_submodule (LinearMap.ker Q) s p (by
    intro c hc
    rcases c with j | j
    · exact fun h => key j a (Finset.inl_mem_disjSum.1 hc) h
    · exact fun h => key j b (Finset.inr_mem_disjSum.1 hc) h)
  refine ⟨z, hzQ, fun j hj => ⟨?_, ?_⟩⟩
  · have hjB : j ∈ B := by simp [B, hj]
    have hz1 := hz (.inl j) (Finset.inl_mem_disjSum.2 hjB)
    have haS : a ∉ S j := fun h => haj j hj (Submodule.mem_inf.1 h).1
    intro x hx hxj
    have hxQ : x ∈ LinearMap.ker Q := by
      obtain ⟨μa, μz, -, -, -, rfl⟩ := hx
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hzQ)
    exact segment_disjoint_of_not_mem_sup haS hz1 x hx (Submodule.mem_inf.2 ⟨hxj, hxQ⟩)
  · have hjB : j ∈ B := by simp [B, hj]
    have hz1 := hz (.inr j) (Finset.inr_mem_disjSum.2 hjB)
    have hbS : b ∉ S j := fun h => hbj j hj (Submodule.mem_inf.1 h).1
    intro x hx hxj
    rw [segment_symm] at hx
    have hxQ : x ∈ LinearMap.ker Q := by
      obtain ⟨μa, μz, -, -, -, rfl⟩ := hx
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hzQ)
    exact segment_disjoint_of_not_mem_sup hbS hz1 x hx (Submodule.mem_inf.2 ⟨hxj, hxQ⟩)

/-- **Cone apexes.** Finitely many segments avoiding finitely many submodules of codimension at
least three can be coned to a common apex avoiding the submodules. -/
lemma exists_cone_apex [FiniteDimensional ℝ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : ι → Submodule ℝ V) (hS : ∀ j, Module.finrank ℝ (S j) + 3 ≤ Module.finrank ℝ V)
    (a b : κ → V) (hab : ∀ i j, ∀ y ∈ segment ℝ (a i) (b i), y ∉ S j) :
    ∃ z : V, ∀ i j, ∀ y ∈ segment ℝ (a i) (b i), ∀ x ∈ segment ℝ y z, x ∉ S j := by
  classical
  let p : κ × ι → Submodule ℝ V := fun c => S c.2 ⊔ Submodule.span ℝ {a c.1, b c.1}
  obtain ⟨z, hz⟩ := exists_not_mem_finset_submodule (Finset.univ : Finset (κ × ι)) p (by
    intro c _ htop
    have h1 : Module.finrank ℝ (p c) ≤ Module.finrank ℝ (S c.2) + 2 := by
      calc Module.finrank ℝ (p c)
          ≤ Module.finrank ℝ (S c.2) + Module.finrank ℝ (Submodule.span ℝ {a c.1, b c.1}) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ Module.finrank ℝ (S c.2) + 2 := by
            gcongr
            calc Module.finrank ℝ (Submodule.span ℝ ({a c.1, b c.1} : Set V))
                ≤ ({a c.1, b c.1} : Finset V).card := by
                  have h := finrank_span_finset_le_card (R := ℝ) ({a c.1, b c.1} : Finset V)
                  have hcoe : (({a c.1, b c.1} : Finset V) : Set V) = {a c.1, b c.1} := by simp
                  rw [Set.finrank, hcoe] at h
                  exact h
              _ ≤ 2 := Finset.card_le_two
    have h2 : Module.finrank ℝ (p c) = Module.finrank ℝ V := by
      rw [htop, finrank_top]
    have := hS c.2
    omega)
  exact ⟨z, fun i j => triangle_disjoint_of_not_mem_sup (hab i j) (hz (i, j) (Finset.mem_univ _))⟩

end Surgery
