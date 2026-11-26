module

public import Mathlib.Tactic.Continuity
public import RequestProject.Surgery.Frame
public import RequestProject.Surgery.Cutoff

@[expose] public section

/-!
# Zero-pair cancellation in standard position

The domain is `ℝ × ℝ^k`; the two zeros sit at `0` and at `(1, 0)`.  The obstacle is a finite
union of kernels `ker (Qs j)` of codimension at least three, and the two zeros are zeros of a
map `Q` whose kernel is one of them (or not; the statement does not need this).  Near the zeros
`f` is affine, with linear parts `lin a0`, `lin a1` such that `Q ∘ lin a0` and `Q ∘ lin a1`
have determinants of opposite signs.  Then `f` can be modified inside an arbitrarily thin tube
around the segment so that the modified map has no zero in the tube.
-/

open Set

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}

/-- The open tube of length parameter `ζ` and radius `ε`. -/
def tube (ζ ε : ℝ) : Set (ℝ × (Fin k → ℝ)) :=
  {x | x.1 ∈ Ioo (-2 * ζ) (1 + 2 * ζ) ∧ ‖x.2‖ < ε}

lemma norm_mk_lt {t : ℝ} {v : Fin k → ℝ} {c : ℝ} (ht : |t| < c) (hv : ‖v‖ < c) :
    ‖((t, v) : ℝ × (Fin k → ℝ))‖ < c := by
  rw [Prod.norm_def]; exact max_lt (by rwa [Real.norm_eq_abs]) hv

lemma norm_mk_le {t : ℝ} {v : Fin k → ℝ} {c : ℝ} (ht : |t| ≤ c) (hv : ‖v‖ ≤ c) :
    ‖((t, v) : ℝ × (Fin k → ℝ))‖ ≤ c := by
  rw [Prod.norm_def]; exact max_le (by rwa [Real.norm_eq_abs]) hv

set_option maxHeartbeats 4000000 in
/-- **Zero-pair cancellation in standard position.** -/
theorem pair_cancel {ι : Type*} [Fintype ι]
    (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ))
    (hcodim : ∀ j, Module.finrank ℝ (LinearMap.ker (Qs j)) + 3 ≤ Module.finrank ℝ V)
    (hrank : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q →
      ∃ u ∈ LinearMap.ker Q, ∃ w ∈ LinearMap.ker Q, LinearIndependent ℝ ![Qs j u, Qs j w])
    (f : ℝ × (Fin k → ℝ) → V) (hf : Continuous f) (a0 a1 : Fin (k+1) → V) {r : ℝ} (hr : 0 < r)
    (h0 : ∀ x, ‖x‖ < r → f x = f 0 + lin a0 x)
    (h1 : ∀ x, ‖x‖ < r → f ((1, 0) + x) = f (1, 0) + lin a1 x)
    (hQ0 : Q (f 0) = 0) (hQ1 : Q (f (1, 0)) = 0)
    (hdet : (frameMat Q a0).det * (frameMat Q a1).det < 0)
    (hsep0 : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j (f 0) ≠ 0)
    (hsep1 : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j (f (1, 0)) ≠ 0)
    (hseg : ∀ t ∈ Ioo (0:ℝ) 1, ∀ j, Qs j (f (t, 0)) ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ g : ℝ × (Fin k → ℝ) → V, Continuous g ∧ ∃ T : Set (ℝ × (Fin k → ℝ)),
      T ⊆ {x | x.1 ∈ Ioo (-η) (1 + η) ∧ ‖x.2‖ < η} ∧ (0 : ℝ × (Fin k → ℝ)) ∈ T ∧
      ((1, 0) : ℝ × (Fin k → ℝ)) ∈ T ∧ (∀ x ∉ T, g x = f x) ∧
      ∀ x ∈ T, ∀ j, Qs j (g x) ≠ 0 := by
  classical
  -- obstacles
  set X : Set V := (⋃ j, ((LinearMap.ker (Qs j) : Submodule ℝ V) : Set V))ᶜ with hXdef
  have hmemX : ∀ v, v ∈ X ↔ ∀ j, Qs j v ≠ 0 := by
    intro v; simp [X]
  have hXopen : IsOpen X := by
    rw [hXdef, isOpen_compl_iff]
    exact isClosed_iUnion_of_finite fun j => Submodule.closed_of_finiteDimensional _
  haveI : SimplyConnectedSpace X := simplyConnected_compl _ hcodim
  set Xb : Set V := {v | ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j v ≠ 0} with hXbdef
  have hXbopen : IsOpen Xb := by
    have : Xb = (⋃ j ∈ {j | LinearMap.ker (Qs j) ≠ LinearMap.ker Q},
        ((LinearMap.ker (Qs j) : Submodule ℝ V) : Set V))ᶜ := by
      ext v; simp [Xb]
    rw [this, isOpen_compl_iff]
    exact (Set.toFinite _).isClosed_biUnion fun j _ => Submodule.closed_of_finiteDimensional _
  -- zeros of the kernels equal to `ker Q`
  have hsame : ∀ j v, LinearMap.ker (Qs j) = LinearMap.ker Q → Qs j v = 0 → Q v = 0 := by
    intro j v hj hv
    have : v ∈ LinearMap.ker (Qs j) := hv
    rw [hj] at this; exact this
  -- frames
  obtain ⟨J0, hJ0⟩ : ∃ J0, J0 = Function.update a0 0 (-a0 0) := ⟨_, rfl⟩
  have hJ0lin : ∀ w v, lin J0 (w, v) = lin a0 (-w, v) := fun w v => by rw [hJ0]; exact lin_update_neg a0 w v
  have hdetJ : 0 < (frameMat Q J0).det * (frameMat Q a1).det := by
    rw [hJ0, frameMat_update_neg]; linarith
  obtain ⟨J, hJc, hJ0', hJ1', hJdet⟩ := exists_frame_path Q J0 a1 hdetJ
  obtain ⟨Γ, hΓc, hΓ0, hΓ1, hΓQ, hΓb⟩ :=
    exists_core_arc Q Qs hrank hQ0 hQ1 hsep0 hsep1
  -- uniform bound on the frames
  have hJclamp : ∀ u, J u = J (clamp01 u) := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · rw [hJ0' u hu, clamp01_of_nonpos hu, hJ0' 0 le_rfl]
    rcases le_or_gt 1 u with hu' | hu'
    · rw [hJ1' u hu', clamp01_of_one_le hu', hJ1' 1 le_rfl]
    · rw [clamp01_of_mem ⟨hu.le, hu'.le⟩]
  have hJn : Continuous fun u => ∑ i, ‖J u i‖ :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hJc).norm
  obtain ⟨CJ0, hCJ0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hJn.continuousOn
  obtain ⟨CJ, hCJdef⟩ : ∃ CJ, CJ = max CJ0 1 := ⟨_, rfl⟩
  have hCJ : ∀ u, ∑ i, ‖J u i‖ ≤ CJ := by
    intro u
    rw [hJclamp u]
    have := hCJ0 _ (clamp01_mem u)
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (hCJdef ▸ le_max_left _ _)
  have hCJpos : 0 < CJ := lt_of_lt_of_le one_pos (hCJdef ▸ le_max_right _ _)
  have hlinJ : ∀ u x, ‖lin (J u) x‖ ≤ CJ * ‖x‖ := fun u x =>
    (norm_lin_le _ _).trans (mul_le_mul_of_nonneg_right (hCJ u) (norm_nonneg _))
  -- margin of the core arc
  have hΓclamp : ∀ u, Γ u = Γ (clamp01 u) := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · rw [hΓ0 u hu, clamp01_of_nonpos hu, hΓ0 0 le_rfl]
    rcases le_or_gt 1 u with hu' | hu'
    · rw [hΓ1 u hu', clamp01_of_one_le hu', hΓ1 1 le_rfl]
    · rw [clamp01_of_mem ⟨hu.le, hu'.le⟩]
  obtain ⟨ρΓ, hρΓ, hmarΓ⟩ := exists_margin (K := Γ '' Icc 0 1)
    (isCompact_Icc.image hΓc) hXbopen (by rintro _ ⟨u, -, rfl⟩; exact fun j hj => hΓb u j hj)
  have hmarΓ' : ∀ u y, ‖y‖ < ρΓ → Γ u + y ∈ Xb := by
    intro u y hy; rw [hΓclamp u]; exact hmarΓ _ ⟨_, clamp01_mem u, rfl⟩ y hy
  -- the length parameter
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = min (min (1/8 : ℝ) (η/2)) (min (r/4) (ρΓ/(16*CJ))) := ⟨_, rfl⟩
  have hζpos : 0 < ζ := by
    rw [hζdef]
    exact lt_min (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by positivity))
  have hζ8 : ζ ≤ 1/8 := by rw [hζdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hζη : ζ ≤ η/2 := by rw [hζdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hζr : ζ ≤ r/4 := by rw [hζdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hζΓ : ζ ≤ ρΓ/(16*CJ) := by rw [hζdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hCJζ : CJ * (4*ζ) ≤ ρΓ/4 := by
    rw [le_div_iff₀ (by positivity)] at hζΓ; nlinarith
  -- the two arcs
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ → V, α = fun u => f (ζ + u * (1 - 2*ζ), 0) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ → V, c = fun u => Γ u + lin (J u) (-ζ, 0) := ⟨_, rfl⟩
  have hαc : Continuous α := by rw [hαdef]; exact hf.comp (by fun_prop)
  have hcc : Continuous c := by
    rw [hcdef]; exact hΓc.add (continuous_lin.comp (hJc.prodMk continuous_const))
  have hαX : ∀ u ∈ Icc (0:ℝ) 1, α u ∈ X := by
    intro u hu
    rw [hmemX, hαdef]
    apply hseg
    constructor <;> nlinarith [hu.1, hu.2]
  have hnormζ : ‖((-ζ, 0) : ℝ × (Fin k → ℝ))‖ ≤ ζ :=
    norm_mk_le (by rw [abs_neg, abs_of_pos hζpos]) (by simp [hζpos.le])
  have hcX : ∀ u ∈ Icc (0:ℝ) 1, c u ∈ X := by
    intro u _
    rw [hmemX]
    intro j
    by_cases hj : LinearMap.ker (Qs j) = LinearMap.ker Q
    · intro h
      have h' := hsame j _ hj h
      simp only [hcdef, map_add, hΓQ, zero_add] at h'
      rw [Q_lin_eq_zero_iff Q (hJdet u)] at h'
      have := congrArg Prod.fst h'
      simp at this
      linarith
    · rw [hcdef]
      refine hmarΓ' u _ ?_ j hj
      calc ‖lin (J u) (-ζ, 0)‖ ≤ CJ * ζ := (hlinJ u _).trans
            (mul_le_mul_of_nonneg_left hnormζ hCJpos.le)
        _ < ρΓ := by nlinarith
  have hc0 : α 0 = c 0 := by
    simp only [hαdef, hcdef, zero_mul, add_zero, hΓ0 0 le_rfl, hJ0' 0 le_rfl, hJ0lin, neg_neg]
    exact h0 (ζ, 0) (lt_of_le_of_lt (norm_mk_le (by rw [abs_of_pos hζpos]) (by simp [hζpos.le]))
      (by linarith))
  have hc1 : α 1 = c 1 := by
    simp only [hαdef, hcdef, one_mul, hΓ1 1 le_rfl, hJ1' 1 le_rfl]
    have e : ((ζ + (1 - 2 * ζ), 0) : ℝ × (Fin k → ℝ)) = (1, 0) + (-ζ, 0) := by
      ext <;> simp; ring
    rw [e]
    exact h1 _ (lt_of_le_of_lt hnormζ (by linarith))
  obtain ⟨K, hKc, hK0, hK1, hKs0, hKs1, ρK, hρK, hmarK⟩ :=
    exists_homotopy_fun hXopen α c hαc hcc hαX hcX hc0 hc1
  -- uniform continuity of `f`
  obtain ⟨ε0, hε0, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (-1:ℝ)) (b := 2)).prod
      (isCompact_closedBall (0 : Fin k → ℝ) 1) |>.uniformContinuousOn_of_continuous
      hf.continuousOn) (ρK/2) (by positivity)
  -- the radius
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min (η/2) (r/2)) (min (1/2) (min (ε0/2) (min (ρΓ/(4*CJ)) (ρK/(4*CJ))))) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by norm_num) (lt_min (by linarith) (lt_min (by positivity) (by positivity))))
  have hεη : ε ≤ η/2 := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hεr : ε ≤ r/2 := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1/2 := by rw [hεdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hε0' : ε ≤ ε0/2 := by rw [hεdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεΓ : ε ≤ ρΓ/(4*CJ) := by rw [hεdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεK : ε ≤ ρK/(4*CJ) := by rw [hεdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hCJε : CJ * ε ≤ ρΓ/4 := by rw [le_div_iff₀ (by positivity)] at hεΓ; nlinarith
  have hCJεK : CJ * ε ≤ ρK/4 := by rw [le_div_iff₀ (by positivity)] at hεK; nlinarith
  -- the modified map
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ → ℝ, lam = fun t => clamp01 ((t - ζ) / (1 - 2*ζ)) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ × (Fin k → ℝ) → ℝ, s = fun x => cutChi ζ x.1 * cutRad ε ‖x.2‖ := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ × (Fin k → ℝ) → V, g = fun x =>
    K (s x, lam x.1) + (f (x.1, 0) - α (lam x.1)) + (1 - s x) • (f x - f (x.1, 0)) +
      s x • lin (J (lam x.1)) (bumpRad ε ‖x.2‖ * bump ζ x.1, x.2) := ⟨_, rfl⟩
  have hlamc : Continuous lam := by rw [hlamdef]; exact continuous_clamp01.comp (by fun_prop)
  have hsc : Continuous s := by
    rw [hsdef]
    exact ((continuous_cutChi ζ).comp continuous_fst).mul
      ((continuous_cutRad ε).comp continuous_snd.norm)
  have hs01 : ∀ x, s x ∈ Icc (0:ℝ) 1 := fun x => by
    rw [hsdef]
    exact ⟨mul_nonneg (cutChi_mem _ _).1 (cutRad_mem _ _).1,
      mul_le_one₀ (cutChi_mem _ _).2 (cutRad_mem _ _).1 (cutRad_mem _ _).2⟩
  have hlam01 : ∀ t, lam t ∈ Icc (0:ℝ) 1 := by intro t; rw [hlamdef]; exact clamp01_mem _
  have hgc : Continuous g := by
    have hf0 : Continuous fun x : ℝ × (Fin k → ℝ) => f (x.1, 0) :=
      hf.comp (continuous_fst.prodMk continuous_const)
    rw [hgdef]
    refine (((hKc.comp (hsc.prodMk (hlamc.comp continuous_fst))).add
      (hf0.sub (hαc.comp (hlamc.comp continuous_fst)))).add
      ((continuous_const.sub hsc).smul (hf.sub hf0))).add (hsc.smul ?_)
    exact continuous_lin.comp ((hJc.comp (hlamc.comp continuous_fst)).prodMk
      ((((continuous_bumpRad ε).comp continuous_snd.norm).mul
        ((continuous_bump ζ).comp continuous_fst)).prodMk continuous_snd))
  refine ⟨g, hgc, tube ζ ε, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, v⟩ ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · show (0:ℝ) ∈ Ioo (-2*ζ) (1+2*ζ) ∧ ‖(0 : Fin k → ℝ)‖ < ε
    exact ⟨⟨by linarith, by linarith⟩, by simpa using hεpos⟩
  · have hA : -2*ζ < (1:ℝ) := by linarith
    have hB : (1:ℝ) < 1 + 2*ζ := by linarith
    have hC : ‖(0 : Fin k → ℝ)‖ < ε := by simpa using hεpos
    exact ⟨⟨hA, hB⟩, hC⟩
  · rintro ⟨t, v⟩ hx
    have hs0 : s (t, v) = 0 := by
      simp only [tube, mem_setOf_eq, not_and_or, not_lt] at hx
      rcases hx with h | h
      · simp [hsdef, cutChi_eq_zero hζpos h]
      · simp [hsdef, cutRad_eq_zero hεpos h]
    simp only [hgdef, hs0, sub_zero, one_smul, zero_smul, add_zero]
    rw [hK0 _ (hlam01 t)]
    abel
  · rintro ⟨t, v⟩ ⟨⟨ht1, ht2⟩, hv⟩ j
    simp only at ht1 ht2 hv
    have hgx : g (t, v) = K (s (t, v), lam t) + (f (t, 0) - α (lam t)) +
        (1 - s (t, v)) • (f (t, v) - f (t, 0)) +
        s (t, v) • lin (J (lam t)) (bumpRad ε ‖v‖ * bump ζ t, v) := by
      rw [hgdef]
    have hsx : s (t, v) = cutChi ζ t * cutRad ε ‖v‖ := by rw [hsdef]
    obtain ⟨hs0', hs1'⟩ := hs01 (t, v)
    have hσ := bumpRad_mem ε ‖v‖
    have hβ0 := bump_nonneg hζpos t
    have hβ1 := bump_le hζpos t
    have hχ := cutChi_mem ζ t
    -- if `v = 0` then `s = χ` and `σ = 1`
    have hv0 : v = 0 → s (t, v) = cutChi ζ t ∧ bumpRad ε ‖v‖ = 1 := by
      rintro rfl
      rw [hsx, norm_zero, cutRad_zero hεpos, bumpRad_zero, mul_one]
      exact ⟨rfl, rfl⟩
    have hvr : ‖v‖ < r := by linarith
    have hJ0det : (frameMat Q J0).det ≠ 0 := by
      have := hJdet 0; rwa [hJ0' 0 le_rfl] at this
    have hJ1det : (frameMat Q a1).det ≠ 0 := by
      have := hJdet 1; rwa [hJ1' 1 le_rfl] at this
    set σ := bumpRad ε ‖v‖ with hσdef
    set β := bump ζ t with hβdef
    set S := s (t, v) with hSdef
    have hσβ0 : 0 ≤ σ * β := mul_nonneg hσ.1 hβ0
    have hσβ1 : σ * β ≤ 2 * ζ := (mul_le_of_le_one_left hβ0 hσ.2).trans hβ1
    have hSσβ0 : 0 ≤ S * (σ * β) := mul_nonneg hs0' hσβ0
    have hSσβ1 : S * (σ * β) ≤ 2 * ζ := (mul_le_of_le_one_left hσβ0 hs1').trans hσβ1
    have hbound : ∀ w : ℝ, |w| ≤ 4 * ζ → CJ * ‖((w, v) : ℝ × (Fin k → ℝ))‖ < ρΓ := by
      intro w hw
      calc CJ * ‖((w, v) : ℝ × (Fin k → ℝ))‖ ≤ CJ * (4 * ζ + ε) := by
            gcongr
            exact norm_mk_le (by linarith) (by linarith)
        _ < ρΓ := by rw [mul_add]; linarith
    rcases le_or_gt t ζ with htA | htA
    · -- left end
      have hlam : lam t = 0 := by
        rw [hlamdef]; exact clamp01_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
          (by linarith))
      have htr : |t| < r := by rw [abs_lt]; constructor <;> linarith
      have hfx : f (t, v) = f 0 + lin J0 (-t, v) := by
        rw [h0 (t, v) (norm_mk_lt htr hvr), hJ0lin, neg_neg]
      have hft : f (t, 0) = f 0 + lin J0 (-t, 0) := by
        rw [h0 (t, 0) (norm_mk_lt htr (by simpa using hr)), hJ0lin, neg_neg]
      have hdiff : f (t, v) - f (t, 0) = lin J0 (0, v) := by
        rw [hfx, hft, lin_mk J0 (-t) v]; abel
      have hg : g (t, v) = f 0 + lin J0 (-t + S * (σ * β), v) := by
        rw [hgx, hlam, hKs0, hJ0' 0 le_rfl, hdiff, hft]
        have e : ((-t + S * (σ * β), v) : ℝ × (Fin k → ℝ)) =
            (-t, 0) + (1 - S) • ((0:ℝ), v) + S • (σ * β, v) := by
          refine Prod.ext ?_ ?_
          · simp
          · show v = (0 : Fin k → ℝ) + (1 - S) • v + S • v
            rw [zero_add, ← add_smul]; simp
        rw [e, lin_add, lin_add, lin_smul, lin_smul]
        abel
      by_cases hj : LinearMap.ker (Qs j) = LinearMap.ker Q
      · intro hz
        have hQz := hsame j _ hj hz
        rw [hg, map_add, hQ0, zero_add, Q_lin_eq_zero_iff Q hJ0det] at hQz
        have hvz : v = 0 := congrArg Prod.snd hQz
        have htz : -t + S * (σ * β) = 0 := congrArg Prod.fst hQz
        obtain ⟨hS, hσ1⟩ := hv0 hvz
        rw [hS, hσ1, one_mul] at htz
        rcases lt_or_ge t 0 with ht0 | ht0
        · nlinarith [hχ.1]
        · have hb : β = 2 * ζ := bump_eq hζpos ht0 (by linarith)
          rw [cutChi_eq_one hζpos (by linarith) (by linarith), hb] at htz
          linarith
      · have hm := hmarΓ' 0 (lin J0 (-t + S * (σ * β), v)) ?_
        · rw [hΓ0 0 le_rfl, ← hg] at hm; exact hm j hj
        · refine lt_of_le_of_lt ?_ (hbound (-t + S * (σ * β)) ?_)
          · rw [← hJ0' 0 le_rfl]; exact hlinJ 0 _
          · rw [abs_le]; constructor <;> linarith
    rcases le_or_gt (1 - ζ) t with htB | htB
    · -- right end
      have hlam : lam t = 1 := by
        rw [hlamdef]; apply clamp01_of_one_le
        rw [le_div_iff₀ (by linarith)]; linarith
      have htr : |t - 1| < r := by rw [abs_lt]; constructor <;> linarith
      have e1 : ∀ w : Fin k → ℝ, ((t, w) : ℝ × (Fin k → ℝ)) = (1, 0) + (t - 1, w) := by
        intro w; refine Prod.ext ?_ ?_ <;> simp
      have hfx : f (t, v) = f (1, 0) + lin a1 (t - 1, v) := by
        rw [e1 v, h1 _ (norm_mk_lt htr hvr)]
      have hft : f (t, 0) = f (1, 0) + lin a1 (t - 1, 0) := by
        rw [e1 0, h1 _ (norm_mk_lt htr (by simpa using hr))]
      have hdiff : f (t, v) - f (t, 0) = lin a1 (0, v) := by
        rw [hfx, hft, lin_mk a1 (t - 1) v]; abel
      have hg : g (t, v) = f (1, 0) + lin a1 (t - 1 + S * (σ * β), v) := by
        rw [hgx, hlam, hKs1, hJ1' 1 le_rfl, hdiff, hft]
        have e : ((t - 1 + S * (σ * β), v) : ℝ × (Fin k → ℝ)) =
            (t - 1, 0) + (1 - S) • ((0:ℝ), v) + S • (σ * β, v) := by
          refine Prod.ext ?_ ?_
          · simp
          · show v = (0 : Fin k → ℝ) + (1 - S) • v + S • v
            rw [zero_add, ← add_smul]; simp
        rw [e, lin_add, lin_add, lin_smul, lin_smul]
        abel
      by_cases hj : LinearMap.ker (Qs j) = LinearMap.ker Q
      · intro hz
        have hQz := hsame j _ hj hz
        rw [hg, map_add, hQ1, zero_add, Q_lin_eq_zero_iff Q hJ1det] at hQz
        have hvz : v = 0 := congrArg Prod.snd hQz
        have htz : t - 1 + S * (σ * β) = 0 := congrArg Prod.fst hQz
        obtain ⟨hS, hσ1⟩ := hv0 hvz
        rw [hS, hσ1, one_mul] at htz
        rcases lt_or_ge 1 t with ht0 | ht0
        · nlinarith [hχ.1]
        · have hb : β = 2 * ζ := bump_eq hζpos (by linarith) ht0
          rw [cutChi_eq_one hζpos (by linarith) (by linarith), hb] at htz
          linarith
      · have hm := hmarΓ' 1 (lin a1 (t - 1 + S * (σ * β), v)) ?_
        · rw [hΓ1 1 le_rfl, ← hg] at hm; exact hm j hj
        · refine lt_of_le_of_lt ?_ (hbound (t - 1 + S * (σ * β)) ?_)
          · rw [← hJ1' 1 le_rfl]; exact hlinJ 1 _
          · rw [abs_le]; constructor <;> linarith
    -- middle
    set u := lam t with hudef
    have hne : (1 - 2 * ζ) ≠ 0 := (show (0:ℝ) < 1 - 2 * ζ by linarith).ne'
    have hu : ζ + u * (1 - 2 * ζ) = t := by
      have hu' : u = (t - ζ) / (1 - 2 * ζ) := by
        rw [hudef, hlamdef]
        exact clamp01_of_mem ⟨div_nonneg (by linarith) (by linarith),
          (div_le_one (by linarith)).2 (by linarith)⟩
      rw [hu', div_mul_cancel₀ _ hne]; ring
    have hαu : α u = f (t, 0) := by rw [hαdef]; simp only; rw [hu]
    have hχ1 : cutChi ζ t = 1 := cutChi_eq_one hζpos (by linarith) (by linarith)
    have hβ2 : β = 2 * ζ := bump_eq hζpos (by linarith) (by linarith)
    have hSv : S = cutRad ε ‖v‖ := by rw [hsx, hχ1, one_mul]
    rcases le_or_gt ‖v‖ (ε / 2) with hvs | hvs
    · have hS1 : S = 1 := by rw [hSv]; exact cutRad_eq_one hεpos hvs
      have hg : g (t, v) = Γ u + lin (J u) (σ * (2 * ζ) - ζ, v) := by
        rw [hgx, hS1, hK1 u (hlam01 t), hαu, hcdef, hβ2]
        simp only [sub_self, zero_smul, add_zero, one_smul]
        rw [add_assoc, ← lin_add]
        congr 2
        refine Prod.ext ?_ ?_
        · simp; ring
        · simp
      by_cases hj : LinearMap.ker (Qs j) = LinearMap.ker Q
      · intro hz
        have hQz := hsame j _ hj hz
        rw [hg, map_add, hΓQ, zero_add, Q_lin_eq_zero_iff Q (hJdet u)] at hQz
        have hvz : v = 0 := congrArg Prod.snd hQz
        have htz : σ * (2 * ζ) - ζ = 0 := congrArg Prod.fst hQz
        obtain ⟨-, hσ1⟩ := hv0 hvz
        rw [hσ1] at htz
        linarith
      · have hm := hmarΓ' u (lin (J u) (σ * (2 * ζ) - ζ, v)) ?_
        · rw [← hg] at hm; exact hm j hj
        · refine lt_of_le_of_lt (hlinJ u _) (hbound _ ?_)
          rw [abs_le]; constructor <;> nlinarith [hσ.1, hσ.2]
    · have hσ0 : σ = 0 := bumpRad_eq_zero hεpos hvs.le
      set y : V := (1 - S) • (f (t, v) - f (t, 0)) + S • lin (J u) (0, v) with hydef
      have hg : g (t, v) = K (S, u) + y := by
        rw [hgx, hαu, hσ0, zero_mul, hydef]
        abel
      have hdist : ‖f (t, v) - f (t, 0)‖ < ρK / 2 := by
        rw [← dist_eq_norm]
        apply hunif
        · exact ⟨⟨by linarith, by linarith⟩, by
            rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
        · exact ⟨⟨by linarith, by linarith⟩, by simp⟩
        · rw [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg _)]
          linarith
      have hy : ‖y‖ < ρK := by
        rw [hydef]
        calc ‖(1 - S) • (f (t, v) - f (t, 0)) + S • lin (J u) (0, v)‖
            ≤ ‖(1 - S) • (f (t, v) - f (t, 0))‖ + ‖S • lin (J u) (0, v)‖ := norm_add_le _ _
          _ ≤ ‖f (t, v) - f (t, 0)‖ + CJ * ε := by
            gcongr
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
              exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0']
              refine mul_le_of_le_one_left (norm_nonneg _) hs1' |>.trans ?_
              refine (hlinJ u _).trans ?_
              gcongr
              exact norm_mk_le (by simp [hεpos.le]) hv.le
          _ < ρK := by linarith
      rw [hg]
      exact (hmemX _).1 (hmarK S u y hy) j

end Surgery
