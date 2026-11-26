module

public import RequestProject.Surgery.PathHomotopy

@[expose] public section

/-!
# Auxiliary constructions for zero-pair cancellation

* `Surgery.exists_margin`: a compact set inside an open set has a uniform margin;
* `Surgery.exists_core_arc`: a continuous arc inside a level set avoiding other kernels;
* `Surgery.exists_homotopy_fun`: homotopies rel endpoints in a simply connected open set, as
  plain functions `ℝ × ℝ → V`, with a uniform margin.
-/

open Set

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The clamp of a real number to `[0, 1]`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

lemma clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clamp01_of_mem {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : clamp01 x = x := by
  simp [clamp01, min_eq_left hx.2, max_eq_right hx.1]

lemma clamp01_of_nonpos {x : ℝ} (hx : x ≤ 0) : clamp01 x = 0 := by
  simp [clamp01, min_eq_left (hx.trans zero_le_one), hx]

lemma clamp01_of_one_le {x : ℝ} (hx : 1 ≤ x) : clamp01 x = 1 := by
  simp [clamp01, min_eq_right hx]

lemma continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

/-- A compact subset of an open set has a uniform margin. -/
lemma exists_margin {K X : Set V} (hK : IsCompact K) (hX : IsOpen X) (hKX : K ⊆ X) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ y : V, ‖y‖ < ρ → x + y ∈ X := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hX hKX
  refine ⟨δ, hδ, fun x hx y hy => hsub ?_⟩
  apply Metric.closedBall_subset_cthickening hx
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  exact hy.le

/-- **Core arcs.** Two points of `ker Q` outside the other kernels are joined by a continuous
arc in `ker Q` outside the other kernels (constant outside `[0, 1]`). -/
lemma exists_core_arc {ι : Type*} [Fintype ι] {n : ℕ} (Q : V →ₗ[ℝ] (Fin n → ℝ))
    (Qs : ι → V →ₗ[ℝ] (Fin n → ℝ))
    (hrank : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q →
      ∃ u ∈ LinearMap.ker Q, ∃ w ∈ LinearMap.ker Q, LinearIndependent ℝ ![Qs j u, Qs j w])
    {a b : V} (ha : Q a = 0) (hb : Q b = 0)
    (haj : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j a ≠ 0)
    (hbj : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j b ≠ 0) :
    ∃ Γ : ℝ → V, Continuous Γ ∧ (∀ u ≤ 0, Γ u = a) ∧ (∀ u, 1 ≤ u → Γ u = b) ∧
      (∀ u, Q (Γ u) = 0) ∧ ∀ u j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j (Γ u) ≠ 0 := by
  obtain ⟨z, hz, hseg⟩ := exists_arc_apex Q Qs hrank ha hb haj hbj
  let Γ : ℝ → V := fun u => a + clamp01 (2 * u) • (z - a) + clamp01 (2 * u - 1) • (b - z)
  refine ⟨Γ, by unfold Γ; have := continuous_clamp01; fun_prop, ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp [Γ, clamp01_of_nonpos (show 2 * u ≤ 0 by linarith),
      clamp01_of_nonpos (show 2 * u - 1 ≤ 0 by linarith)]
  · intro u hu
    simp only [Γ, clamp01_of_one_le (show 1 ≤ 2 * u by linarith),
      clamp01_of_one_le (show 1 ≤ 2 * u - 1 by linarith), one_smul]
    abel
  · intro u
    simp [Γ, ha, hb, hz]
  · intro u j hj
    rcases le_or_gt u (1/2) with hu | hu
    · have h0 : clamp01 (2 * u - 1) = 0 := clamp01_of_nonpos (by linarith)
      have hmem : Γ u ∈ segment ℝ a z := by
        rw [segment_eq_image']
        exact ⟨_, clamp01_mem (2 * u), by simp [Γ, h0]⟩
      exact (hseg j hj).1 _ hmem
    · have h1 : clamp01 (2 * u) = 1 := clamp01_of_one_le (by linarith)
      have hmem : Γ u ∈ segment ℝ z b := by
        rw [segment_eq_image']
        refine ⟨_, clamp01_mem (2 * u - 1), ?_⟩
        simp only [Γ, h1, one_smul]
        abel
      exact (hseg j hj).2 _ hmem

/-- **Homotopies as functions.** In a simply connected open set `X`, two arcs `α, c : ℝ → V`
mapping `[0,1]` into `X` with common endpoints are homotopic rel endpoints, by a continuous
`K : ℝ × ℝ → V` which has a uniform margin inside `X`. -/
lemma exists_homotopy_fun {X : Set V} (hX : IsOpen X) [SimplyConnectedSpace X]
    (α c : ℝ → V) (hα : Continuous α) (hc : Continuous c)
    (hαX : ∀ u ∈ Icc (0:ℝ) 1, α u ∈ X) (hcX : ∀ u ∈ Icc (0:ℝ) 1, c u ∈ X)
    (h0 : α 0 = c 0) (h1 : α 1 = c 1) :
    ∃ K : ℝ × ℝ → V, Continuous K ∧ (∀ u ∈ Icc (0:ℝ) 1, K (0, u) = α u) ∧
      (∀ u ∈ Icc (0:ℝ) 1, K (1, u) = c u) ∧ (∀ s, K (s, 0) = α 0) ∧ (∀ s, K (s, 1) = α 1) ∧
      ∃ ρ > 0, ∀ s u, ∀ y : V, ‖y‖ < ρ → K (s, u) + y ∈ X := by
  let x0 : X := ⟨α 0, hαX 0 ⟨le_rfl, zero_le_one⟩⟩
  let x1 : X := ⟨α 1, hαX 1 ⟨zero_le_one, le_rfl⟩⟩
  let p : Path x0 x1 :=
    { toFun := fun t => ⟨α t, hαX t t.2⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let q : Path x0 x1 :=
    { toFun := fun t => ⟨c t, hcX t t.2⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp [x0, h0]
      target' := by ext; simp [x1, h1] }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic p q
  let g : ℝ → unitInterval := fun s => projIcc 0 1 zero_le_one s
  have hg : Continuous g := continuous_projIcc
  let K : ℝ × ℝ → V := fun su => (F (g su.1, g su.2) : V)
  have hK : Continuous K := by
    unfold K
    exact continuous_subtype_val.comp (F.continuous.comp
      ((hg.comp continuous_fst).prodMk (hg.comp continuous_snd)))
  have hgval : ∀ (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1), g u = ⟨u, hu⟩ :=
    fun u hu => projIcc_of_mem _ hu
  obtain ⟨ρ, hρ, hmar⟩ := exists_margin (K := range K)
    (by
      have : range K = (fun st : unitInterval × unitInterval => (F st : V)) '' univ := by
        ext v; constructor
        · rintro ⟨su, rfl⟩; exact ⟨_, mem_univ _, rfl⟩
        · rintro ⟨st, -, rfl⟩
          refine ⟨((st.1 : ℝ), (st.2 : ℝ)), ?_⟩
          simp [K, g, projIcc_val]
      rw [this]
      exact isCompact_univ.image (continuous_subtype_val.comp F.continuous))
    hX (by rintro _ ⟨su, rfl⟩; exact (F _).2)
  refine ⟨K, hK, ?_, ?_, ?_, ?_, ρ, hρ, fun s u y hy => hmar _ ⟨_, rfl⟩ y hy⟩
  · intro u hu
    simp only [K, hgval u hu, show g 0 = 0 from projIcc_left _]
    simp [p]
  · intro u hu
    simp only [K, hgval u hu, show g 1 = 1 from projIcc_right _]
    simp [q]
  · intro s
    simp only [K, show g 0 = 0 from projIcc_left _]
    simp [x0]
  · intro s
    simp only [K, show g 1 = 1 from projIcc_right _]
    simp [x1]

end Surgery
