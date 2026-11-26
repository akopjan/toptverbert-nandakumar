module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import RequestProject.Surgery.Avoid

@[expose] public section

/-!
# Simple connectivity of complements of high-codimension subspaces

* `Surgery.homotopic_of_segment`: straight-line homotopy of paths inside a set;
* `Surgery.homotopic_of_cone`: two paths whose points can all be joined to a common apex inside
  the set are homotopic;
* `Surgery.exists_polygonal`: every path in an open set is homotopic to a polygonal path;
* `Surgery.simplyConnected_compl`: the complement of finitely many subspaces of codimension at
  least three in a finite-dimensional real normed space is simply connected.
-/

open Set

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Straight-line homotopy of paths inside a set. -/
lemma homotopic_of_segment {X : Set V} {x y : X} (p q : Path x y)
    (h : ∀ t, segment ℝ (p t : V) (q t) ⊆ X) : p.Homotopic q := by
  refine ⟨{ toFun := fun st => ⟨AffineMap.lineMap (p st.2 : V) (q st.2) (st.1 : ℝ),
              h st.2 (segment_eq_image_lineMap ℝ (p st.2 : V) (q st.2) ▸ ⟨st.1, st.1.2, rfl⟩)⟩
            continuous_toFun := by
              apply Continuous.subtype_mk
              simp only [AffineMap.lineMap_apply_module]
              fun_prop
            map_zero_left := by intro t; ext; simp
            map_one_left := by intro t; ext; simp
            prop' := ?_ }⟩
  intro t z hz
  rcases hz with rfl | rfl <;> ext <;> simp

/-- Two paths in `X` all of whose points can be joined to a common apex `z` inside `X` are
homotopic. -/
lemma homotopic_of_cone {X : Set V} {x y : X} (p q : Path x y) (z : V)
    (hp : ∀ t, segment ℝ (p t : V) z ⊆ X) (hq : ∀ t, segment ℝ (q t : V) z ⊆ X) :
    p.Homotopic q := by
  let C : Set V := {w | ∃ t, w ∈ segment ℝ (p t : V) z} ∪ {w | ∃ t, w ∈ segment ℝ (q t : V) z}
  have hstar : StarConvex ℝ z C := by
    intro w hw a b ha hb hab
    rcases hw with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, convex_segment _ _ (right_mem_segment _ _ _) ht ha hb hab⟩
    · exact Or.inr ⟨t, convex_segment _ _ (right_mem_segment _ _ _) ht ha hb hab⟩
  have hne : C.Nonempty := ⟨z, Or.inl ⟨0, right_mem_segment _ _ _⟩⟩
  haveI := hstar.contractibleSpace hne
  haveI := SimplyConnectedSpace.ofContractible C
  have hC : C ⊆ X := by
    rintro w (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact hp t ht
    · exact hq t ht
  have hx : (x : V) ∈ C := Or.inl ⟨0, by simpa using left_mem_segment ℝ (p 0 : V) z⟩
  have hy : (y : V) ∈ C := Or.inl ⟨1, by simpa using left_mem_segment ℝ (p 1 : V) z⟩
  let p' : Path (⟨x, hx⟩ : C) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, Or.inl ⟨t, left_mem_segment _ _ _⟩⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp
      target' := by ext; simp }
  let q' : Path (⟨x, hx⟩ : C) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, Or.inr ⟨t, left_mem_segment _ _ _⟩⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp
      target' := by ext; simp }
  have h := (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Set.inclusion hC, continuous_inclusion hC⟩
  convert h using 1 <;> rfl

/-- The hat function. -/
noncomputable def hat (u : ℝ) : ℝ := max 0 (1 - |u|)

lemma continuous_hat : Continuous hat := by unfold hat; fun_prop

lemma sum_hat_smul (b : ℕ → V) {s : ℝ} (hs : 0 ≤ s) {M : ℕ} (hM : ⌊s⌋₊ + 1 < M) :
    ∑ j ∈ Finset.range M, hat (s - j) • b j =
      (1 - (s - ⌊s⌋₊)) • b ⌊s⌋₊ + (s - ⌊s⌋₊) • b (⌊s⌋₊ + 1) := by
  set k := ⌊s⌋₊
  have h1 : (k : ℝ) ≤ s := Nat.floor_le hs
  have h2 : s < k + 1 := Nat.lt_floor_add_one s
  rw [Finset.sum_eq_add k (k+1) (by omega)]
  · congr 1
    · congr 1; unfold hat; rw [abs_of_nonneg (by linarith)]; rw [max_eq_right (by linarith)]
    · congr 1; unfold hat; push_cast; rw [abs_of_neg (by linarith)]
      rw [max_eq_right (by linarith)]; ring
  · intro j _ ⟨hjk, hjk1⟩
    have : hat (s - j) = 0 := by
      unfold hat
      apply max_eq_left
      rcases lt_or_gt_of_ne hjk with h | h
      · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (k : ℝ) + 2 ≤ j := by
          have : k + 2 ≤ j := by omega
          exact_mod_cast this
        rw [abs_of_neg (by linarith)]; linarith
    simp [this]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · intro h; exact absurd (Finset.mem_range.2 hM) h

/-- Every path in an open set is homotopic (inside the set) to a polygonal path. -/
lemma exists_polygonal {X : Set V} (hX : IsOpen X) {x y : X} (p : Path x y) :
    ∃ (N : ℕ) (a : ℕ → V), (∀ k, segment ℝ (a k) (a (k+1)) ⊆ X) ∧
      ∃ P : Path x y, p.Homotopic P ∧ ∀ t, ∃ k ≤ N, (P t : V) ∈ segment ℝ (a k) (a (k+1)) := by
  set f : unitInterval → V := fun t => (p t : V) with hf
  have hfc : Continuous f := by fun_prop
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_range hfc).exists_cthickening_subset_open hX
    (by rintro _ ⟨t, rfl⟩; exact (p t).2)
  have hball : ∀ t, Metric.closedBall (f t) δ ⊆ X := fun t =>
    (Metric.closedBall_subset_cthickening (mem_range_self t) δ).trans hsub
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hfc) δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNpos : (0:ℝ) < N := lt_trans (by positivity) hN
  have hN1 : 1 / (N:ℝ) < η := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hη] at hN; linarith
  let g : ℝ → unitInterval := fun s => projIcc 0 1 zero_le_one s
  let a : ℕ → V := fun k => f (g (k / N))
  have hclose : ∀ s s' : ℝ, |s - s'| ≤ 1 / N → dist (f (g s)) (f (g s')) < δ := by
    intro s s' h
    apply hu
    rw [Subtype.dist_eq, Real.dist_eq]
    exact lt_of_le_of_lt ((abs_projIcc_sub_projIcc _).trans h) hN1
  have hseg : ∀ k, segment ℝ (a k) (a (k+1)) ⊆ X := by
    intro k
    refine ((convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self hδ.le) ?_).trans
      (hball _)
    rw [Metric.mem_closedBall, dist_comm]
    refine (hclose _ _ ?_).le
    rw [show ((k:ℝ)/N - ((k+1:ℕ):ℝ)/N) = -(1/N) by push_cast; ring, abs_neg,
      abs_of_pos (by positivity)]
  let Pf : ℝ → V := fun s => ∑ j ∈ Finset.range (N+2), hat (N * s - j) • a j
  have hPf : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      Pf s = (1 - (N * s - ⌊(N:ℝ) * s⌋₊)) • a ⌊(N:ℝ) * s⌋₊ +
        (N * s - ⌊(N:ℝ) * s⌋₊) • a (⌊(N:ℝ) * s⌋₊ + 1) := by
    intro s hs0 hs1
    have hs : 0 ≤ (N:ℝ) * s := mul_nonneg hNpos.le hs0
    have hk : ⌊(N:ℝ) * s⌋₊ ≤ N := Nat.floor_le_of_le (by nlinarith)
    exact sum_hat_smul a hs (by omega)
  have hPseg : ∀ t : unitInterval,
      Pf t ∈ segment ℝ (a ⌊(N:ℝ) * t⌋₊) (a (⌊(N:ℝ) * t⌋₊ + 1)) := by
    intro t
    have hs : 0 ≤ (N:ℝ) * t := mul_nonneg hNpos.le t.2.1
    have h1 := Nat.floor_le hs
    have h2 := Nat.lt_floor_add_one ((N:ℝ) * t)
    rw [hPf t t.2.1 t.2.2]
    exact ⟨_, _, by linarith, by linarith, by ring, rfl⟩
  have hPX : ∀ t : unitInterval, Pf t ∈ X := fun t => hseg _ (hPseg t)
  have hgt : ∀ t : unitInterval, g t = t := fun t => projIcc_val zero_le_one t
  let P : Path x y :=
    { toFun := fun t => ⟨Pf t, hPX t⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        simp only [Pf]
        have := continuous_hat
        fun_prop
      source' := by
        ext
        show Pf 0 = x
        rw [hPf 0 le_rfl zero_le_one]
        simp only [mul_zero, Nat.floor_zero, CharP.cast_eq_zero, sub_self, zero_smul, add_zero,
          a, zero_div]
        rw [show g 0 = 0 from hgt 0]
        simp [f]
      target' := by
        ext
        show Pf 1 = y
        rw [hPf 1 zero_le_one le_rfl]
        simp only [mul_one, Nat.floor_natCast, sub_self, zero_smul, add_zero, a,
          div_self hNpos.ne']
        rw [show g 1 = 1 from hgt 1]
        simp [f] }
  refine ⟨N, a, hseg, P, homotopic_of_segment p P (fun t => ?_), fun t => ⟨_, ?_, hPseg t⟩⟩
  swap
  · exact Nat.floor_le_of_le (by nlinarith [t.2.1, t.2.2])
  have hs : 0 ≤ (N:ℝ) * t := mul_nonneg hNpos.le t.2.1
  have h1 := Nat.floor_le hs
  have h2 := Nat.lt_floor_add_one ((N:ℝ) * t)
  have hconv := convex_closedBall (f t) δ
  refine (hconv.segment_subset (Metric.mem_closedBall_self hδ.le) ?_).trans (hball t)
  have key : ∀ u : ℝ, |u - N * t| ≤ 1 → |u / N - t| ≤ 1 / N := by
    intro u hu
    rw [show u / N - t = (u - N * t) / N by field_simp, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hu hNpos.le
  refine hconv.segment_subset ?_ ?_ (hPseg t)
  · rw [Metric.mem_closedBall]
    have := hclose (⌊(N:ℝ) * t⌋₊ / N) t (key _ (by rw [abs_le]; constructor <;> linarith))
    rw [hgt] at this; exact this.le
  · rw [Metric.mem_closedBall]
    have := hclose ((⌊(N:ℝ) * t⌋₊ + 1 : ℕ) / N) t
      (key _ (by push_cast; rw [abs_le]; constructor <;> linarith))
    rw [hgt] at this; exact this.le



/-- **Simple connectivity.** The complement of finitely many linear subspaces of codimension at
least three in a finite-dimensional real normed space is simply connected. -/
theorem simplyConnected_compl [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] (S : ι → Submodule ℝ V)
    (hS : ∀ j, Module.finrank ℝ (S j) + 3 ≤ Module.finrank ℝ V) :
    SimplyConnectedSpace ((⋃ j, (S j : Set V))ᶜ : Set V) := by
  classical
  set X : Set V := (⋃ j, (S j : Set V))ᶜ with hXdef
  have hmemX : ∀ v, v ∈ X ↔ ∀ j, v ∉ S j := by
    intro v; simp [X]
  have hXopen : IsOpen X := by
    rw [hXdef, isOpen_compl_iff]
    exact isClosed_iUnion_of_finite fun j => Submodule.closed_of_finiteDimensional _
  have hproper : ∀ (j : ι) (c : V), S j ⊔ Submodule.span ℝ {c} ≠ ⊤ := by
    intro j c htop
    have h1 : Module.finrank ℝ ↥(S j ⊔ Submodule.span ℝ {c}) ≤ Module.finrank ℝ (S j) + 1 :=
      (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
        (by gcongr; simpa using finrank_span_le_card (R := ℝ) ({c} : Set V))
    rw [htop, finrank_top] at h1
    have := hS j
    omega
  rw [simply_connected_iff_paths_homotopic']
  refine ⟨?_, ?_⟩
  · rw [← isPathConnected_iff_pathConnectedSpace, isPathConnected_iff]
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv⟩ := exists_not_mem_finset_submodule (Finset.univ : Finset ι) S (by
        intro j _ htop
        have := hS j
        rw [htop, finrank_top] at this
        omega)
      exact ⟨v, (hmemX v).2 fun j => hv j (Finset.mem_univ _)⟩
    · intro a ha b hb
      obtain ⟨z, hz⟩ := exists_not_mem_finset_submodule (Finset.univ : Finset (ι ⊕ ι))
        (fun c => match c with
          | .inl j => S j ⊔ Submodule.span ℝ {a}
          | .inr j => S j ⊔ Submodule.span ℝ {b})
        (by rintro (j | j) _ <;> exact hproper _ _)
      refine (JoinedIn.of_segment_subset (y := z) ?_).trans (JoinedIn.of_segment_subset ?_)
      · intro w hw
        exact (hmemX w).2 fun j => segment_disjoint_of_not_mem_sup (((hmemX a).1 ha) j)
          (hz (.inl j) (Finset.mem_univ _)) w hw
      · intro w hw
        rw [segment_symm] at hw
        exact (hmemX w).2 fun j => segment_disjoint_of_not_mem_sup (((hmemX b).1 hb) j)
          (hz (.inr j) (Finset.mem_univ _)) w hw
  · intro x y p q
    obtain ⟨N, a, hsega, P, hpP, hP⟩ := exists_polygonal hXopen p
    obtain ⟨M, b, hsegb, Q, hqQ, hQ⟩ := exists_polygonal hXopen q
    let A : Fin (N+1) ⊕ Fin (M+1) → V := fun c => match c with
      | .inl k => a k
      | .inr k => b k
    let B : Fin (N+1) ⊕ Fin (M+1) → V := fun c => match c with
      | .inl k => a (k+1)
      | .inr k => b (k+1)
    obtain ⟨z, hz⟩ := exists_cone_apex S hS A B (by
      rintro (k | k) j w hw
      · exact (hmemX w).1 (hsega k hw) j
      · exact (hmemX w).1 (hsegb k hw) j)
    refine hpP.trans (Path.Homotopic.trans ?_ hqQ.symm)
    refine homotopic_of_cone P Q z (fun t w hw => ?_) (fun t w hw => ?_)
    · obtain ⟨k, hk, hkt⟩ := hP t
      exact (hmemX w).2 fun j => hz (.inl ⟨k, Nat.lt_succ_of_le hk⟩) j _ hkt w hw
    · obtain ⟨k, hk, hkt⟩ := hQ t
      exact (hmemX w).2 fun j => hz (.inr ⟨k, Nat.lt_succ_of_le hk⟩) j _ hkt w hw

end Surgery
