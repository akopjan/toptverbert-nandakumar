module

public import RequestProject.Construction.Map
public import RequestProject.Construction.Chart
public import RequestProject.Construction.Obstacles
public import RequestProject.Construction.DetLemmas
public import RequestProject.Surgery.Good

@[expose] public section

/-!
# The initial map in the chart, and its local frames

`Fmap q y = F0 q (toBary (ret y))`.  Where `F0` is locally affine (on the hyperplane) near
`toBary y`, `Fmap` has a frame at `y`; its matrix along `ell m` factors through the
barycentric description of `ell m ∘ F0`.
-/

open Set Surgery

namespace Tverberg6R

noncomputable section

/-- Matchings, as an index type. -/
abbrev Mtch := {m : Fin 6 → Word // IsMatching m}

noncomputable instance : Fintype Mtch := Fintype.ofFinite _

/-- The obstacles. -/
def Qs : Mtch → Table →ₗ[ℝ] (Fin 5 → ℝ) := fun m => ellLin m.1

/-- The initial map in the chart. -/
def Fmap (q : Fin 6 → Fin 6 → ℝ) (y : ℝ × (Fin 4 → ℝ)) : Table := F0 q (toBary (ret y))

lemma toBaryL_apply (v : ℝ × (Fin 4 → ℝ)) : toBaryL v = toBaryLin v := rfl

lemma sum_toBaryLin (v : ℝ × (Fin 4 → ℝ)) : ∑ i, toBaryLin v i = 0 := by
  have h1 := sum_toBary (0 + v)
  rw [toBary_add] at h1
  simp only [Pi.add_apply] at h1
  rw [Finset.sum_add_distrib, sum_toBary] at h1
  linarith

lemma ret_eq_self_of_mem {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ Uo) : ret y = y :=
  ret_eq_self fun i => (hy i).le

lemma Fmap_of_mem {q : Fin 6 → Fin 6 → ℝ} {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ Uo) :
    Fmap q y = F0 q (toBary y) := by
  rw [Fmap, ret_eq_self_of_mem hy]

/-- Local affinity of `F0` on the hyperplane gives a frame of `Fmap`. -/
lemma isFrameAt_Fmap {q : Fin 6 → Fin 6 → ℝ} {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ Uo)
    (FL : (Fin 6 → ℝ) →ₗ[ℝ] Table)
    (hloc : ∃ r > 0, ∀ w : Fin 6 → ℝ, ‖w‖ < r → ∑ i, w i = 0 →
      F0 q (toBary y + w) = F0 q (toBary y) + FL w) :
    IsFrameAt (Fmap q) y (fun i => FL (toBaryL (unitE i))) := by
  obtain ⟨r, hr, hF⟩ := hloc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_Uo y hy
  have hcont : Continuous toBaryL := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuous_iff.1 hcont 0 r hr
  refine ⟨min ε δ, lt_min hε hδ, fun v hv => ?_⟩
  have hyv : y + v ∈ Uo := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hv (min_le_left _ _))
  have hw : ‖toBaryL v‖ < r := by
    have := hδr v (by rw [dist_zero_right]; exact lt_of_lt_of_le hv (min_le_right _ _))
    simpa using this
  rw [Fmap_of_mem hyv, Fmap_of_mem hy, toBary_add]
  rw [← toBaryL_apply, hF _ hw (by rw [toBaryL_apply]; exact sum_toBaryLin v)]
  congr 1
  conv_lhs => rw [← sum_toVec_smul_unitE v]
  simp only [lin, map_sum, map_smul]

/-- **Frame matrix and its determinant.**  If `F0` is locally affine near `toBary y` with
linear part `FL`, and `ell m ∘ FL` factors as `w ↦ ∑ₛ (YL w)ₛ zₛ` with `YL` preserving
zero sums, then at a zero of `ell m` described by `ystar` the frame determinant is
`-det (affMat z) * det [YL (eᵢ) | ystar]`. -/
lemma frame_det {q : Fin 6 → Fin 6 → ℝ} {m : Fin 6 → Word} {y : ℝ × (Fin 4 → ℝ)} (hy : y ∈ Uo)
    (FL : (Fin 6 → ℝ) →ₗ[ℝ] Table)
    (hloc : ∃ r > 0, ∀ w : Fin 6 → ℝ, ‖w‖ < r → ∑ i, w i = 0 →
      F0 q (toBary y + w) = F0 q (toBary y) + FL w)
    (YL : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)) (z : Fin 6 → Fin 5 → ℝ)
    (hlin : ∀ w, ell m (FL w) = ∑ s, YL w s • z s)
    (hsum : ∀ w, ∑ i, w i = 0 → ∑ s, YL w s = 0)
    (ystar : Fin 6 → ℝ) (hy1 : ∑ s, ystar s = 1) (hy0 : ∑ s, ystar s • z s = 0) :
    (∃ a, IsFrameAt (Fmap q) y a) ∧
      (frameMat (ellLin m) (frameAt (Fmap q) y)).det =
        -(affMat z).det * (snocMat (fun i => YL (toBaryL (unitE i))) ystar).det := by
  have hfr := isFrameAt_Fmap hy FL hloc
  refine ⟨⟨_, hfr⟩, ?_⟩
  rw [frameAt_eq hfr]
  have : frameMat (ellLin m) (fun i => FL (toBaryL (unitE i))) =
      Matrix.of fun r i => ∑ s, YL (toBaryL (unitE i)) s * z s r := by
    ext r i
    simp only [frameMat, Matrix.of_apply]
    rw [ellLin_apply, hlin]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact det_frame_eq z _ ystar (fun i => hsum _ (sum_toBaryLin _)) hy1 hy0

end

end Tverberg6R
