module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import RequestProject.Surgery.PairCancel

@[expose] public section

/-!
# Zero-pair cancellation for two arbitrary zeros

`Surgery.pair_cancel_at` transports `Surgery.pair_cancel` along an affine change of coordinates
sending `0 ↦ z` and `(1, 0) ↦ z'`.
-/

open Set

namespace Surgery

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- `(y₀, …, y_k) ↦ (y₀, (y₁, …, y_k))`. -/
def fromVec (y : Fin (k+1) → ℝ) : ℝ × (Fin k → ℝ) := (y 0, Fin.tail y)

lemma toVec_fromVec (y : Fin (k+1) → ℝ) : toVec (fromVec y) = y := by
  simp [toVec, fromVec, Fin.cons_self_tail]

lemma fromVec_toVec (x : ℝ × (Fin k → ℝ)) : fromVec (toVec x) = x := by
  simp [toVec, fromVec]

lemma fromVec_add (y y' : Fin (k+1) → ℝ) : fromVec (y + y') = fromVec y + fromVec y' := by
  simp [fromVec, Fin.tail_def]; rfl

lemma fromVec_smul (c : ℝ) (y : Fin (k+1) → ℝ) : fromVec (c • y) = c • fromVec y := by
  simp [fromVec, Fin.tail_def]; rfl

lemma norm_fromVec_le (y : Fin (k+1) → ℝ) : ‖fromVec y‖ ≤ ‖y‖ := by
  rw [fromVec, Prod.norm_def]
  refine max_le (norm_le_pi_norm y 0) ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact norm_le_pi_norm y i.succ

/-- `toVec` as a linear map. -/
def toVecLin : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (Fin (k+1) → ℝ) where
  toFun := toVec
  map_add' := toVec_add
  map_smul' := toVec_smul

/-- `fromVec` as a linear map. -/
def fromVecLin : (Fin (k+1) → ℝ) →ₗ[ℝ] (ℝ × (Fin k → ℝ)) where
  toFun := fromVec
  map_add' := fromVec_add
  map_smul' := fromVec_smul

/-- The frame map as a linear map. -/
noncomputable def linMap (a : Fin (k+1) → V) : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] V where
  toFun := lin a
  map_add' := lin_add a
  map_smul' := lin_smul a

/-- The standard basis of `ℝ × ℝ^k`. -/
noncomputable def unitE (i : Fin (k+1)) : ℝ × (Fin k → ℝ) :=
  fromVec (Pi.single i 1 : Fin (k+1) → ℝ)

lemma sum_toVec_smul_unitE (x : ℝ × (Fin k → ℝ)) : ∑ i, toVec x i • unitE (k := k) i = x := by
  have : ∑ i, toVec x i • unitE (k := k) i =
      fromVec (∑ i, toVec x i • (Pi.single i 1 : Fin (k+1) → ℝ)) := by
    rw [show fromVec (k := k) = fromVecLin from rfl, map_sum]
    simp [unitE, fromVecLin, fromVec_smul]
  rw [this]
  have h2 : ∑ i, toVec x i • (Pi.single i 1 : Fin (k+1) → ℝ) = toVec x := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [h2, fromVec_toVec]

/-- A frame composed with a linear map. -/
noncomputable def compFrame (a : Fin (k+1) → V) (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ))) :
    Fin (k+1) → V := fun i => lin a (L (unitE i))

lemma lin_compFrame (a : Fin (k+1) → V) (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ)))
    (x : ℝ × (Fin k → ℝ)) : lin (compFrame a L) x = lin a (L x) := by
  conv_rhs => rw [← sum_toVec_smul_unitE x]
  rw [map_sum, show lin a = linMap a from rfl, map_sum]
  simp [lin, compFrame, linMap]

/-- The matrix of a linear map of `ℝ × ℝ^k`. -/
noncomputable def matE (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ))) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℝ := Matrix.of fun r i => toVec (L (unitE i)) r

lemma frameMat_compFrame (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (a : Fin (k+1) → V)
    (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ))) :
    frameMat Q (compFrame a L) = frameMat Q a * matE L := by
  ext r i
  simp only [frameMat, compFrame, matE, Matrix.of_apply, Matrix.mul_apply]
  rw [Q_lin]
  simp [Matrix.mulVec, dotProduct, frameMat]

lemma det_matE_ne_zero (L : (ℝ × (Fin k → ℝ)) ≃ₗ[ℝ] (ℝ × (Fin k → ℝ))) :
    (matE (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ)))).det ≠ 0 := by
  intro h
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hy0
  have : L (fromVec y) = 0 := by
    have e : (matE (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ)))).mulVec y =
        toVec (L (fromVec y)) := by
      conv_rhs => rw [← sum_toVec_smul_unitE (fromVec y)]
      rw [map_sum]
      ext r
      simp only [matE, Matrix.mulVec, dotProduct, Matrix.of_apply, toVec_fromVec, map_smul]
      have := congrFun (show toVec (∑ i, y i • L (unitE i)) = ∑ i, y i • toVec (L (unitE i)) from by
        rw [show toVec (k := k) = toVecLin from rfl, map_sum]
        simp [toVecLin, toVec_smul]) r
      rw [this]
      simp [Finset.sum_apply, mul_comm]
    rw [e] at hy
    exact (toVec_eq_zero_iff _).1 hy
  have h2 := L.injective (this.trans L.map_zero.symm)
  rw [← toVec_fromVec y, h2]
  exact (toVec_eq_zero_iff 0).2 rfl

/-- A linear automorphism of `ℝ × ℝ^k` sending `(1, 0)` to a given nonzero vector. -/
lemma exists_linearEquiv_one {d : ℝ × (Fin k → ℝ)} (hd : d ≠ 0) :
    ∃ L : (ℝ × (Fin k → ℝ)) ≃ₗ[ℝ] (ℝ × (Fin k → ℝ)), L (1, 0) = d := by
  classical
  set c : ℝ := if d.1 = 0 then 1 else 0 with hc
  let Lf : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ)) :=
    { toFun := fun x => (x.1 * d.1 + c * (d.2 ⬝ᵥ x.2), x.2 + x.1 • d.2)
      map_add' := by
        intro x y
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.snd_add, dotProduct_add]; ring
        · simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
      map_smul' := by
        intro a x
        refine Prod.ext ?_ ?_
        · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotProduct_smul,
            RingHom.id_apply]; ring
        · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, smul_add,
            mul_smul] }
  have hinj : Function.Injective Lf := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨t, v⟩ hx
    have h1 : t * d.1 + c * (d.2 ⬝ᵥ v) = 0 := congrArg Prod.fst hx
    have h2 : v + t • d.2 = 0 := congrArg Prod.snd hx
    have hv : v = -(t • d.2) := eq_neg_of_add_eq_zero_left h2
    rw [hv, dotProduct_neg, dotProduct_smul, smul_eq_mul] at h1
    have ht : t = 0 := by
      by_cases hd1 : d.1 = 0
      · have hc1 : c = 1 := by simp [hc, hd1]
        rw [hd1, hc1] at h1
        have hd2 : d.2 ≠ 0 := by
          intro h; apply hd; exact Prod.ext hd1 h
        have hpos : 0 < d.2 ⬝ᵥ d.2 :=
          lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
            (fun h => hd2 (dotProduct_self_eq_zero.1 h.symm))
        nlinarith
      · have hc0 : c = 0 := by simp [hc, hd1]
        rw [hc0] at h1
        have : t * d.1 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right hd1
    rw [ht, zero_smul, neg_zero] at hv
    rw [ht, hv]; rfl
  refine ⟨LinearEquiv.ofInjectiveEndo Lf hinj, ?_⟩
  show Lf (1, 0) = d
  refine Prod.ext ?_ ?_ <;> simp [Lf]

variable [FiniteDimensional ℝ V]

/-- **Zero-pair cancellation for two arbitrary zeros.** -/
theorem pair_cancel_at {ι : Type*} [Fintype ι]
    (Q : V →ₗ[ℝ] (Fin (k+1) → ℝ)) (Qs : ι → V →ₗ[ℝ] (Fin (k+1) → ℝ))
    (hcodim : ∀ j, Module.finrank ℝ (LinearMap.ker (Qs j)) + 3 ≤ Module.finrank ℝ V)
    (hrank : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q →
      ∃ u ∈ LinearMap.ker Q, ∃ w ∈ LinearMap.ker Q, LinearIndependent ℝ ![Qs j u, Qs j w])
    (F : ℝ × (Fin k → ℝ) → V) (hF : Continuous F) {z z' : ℝ × (Fin k → ℝ)} (hzz : z ≠ z')
    (a a' : Fin (k+1) → V) {r : ℝ} (hr : 0 < r)
    (ha : ∀ x, ‖x‖ < r → F (z + x) = F z + lin a x)
    (ha' : ∀ x, ‖x‖ < r → F (z' + x) = F z' + lin a' x)
    (hQ : Q (F z) = 0) (hQ' : Q (F z') = 0)
    (hdet : (frameMat Q a).det * (frameMat Q a').det < 0)
    (hsep : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j (F z) ≠ 0)
    (hsep' : ∀ j, LinearMap.ker (Qs j) ≠ LinearMap.ker Q → Qs j (F z') ≠ 0)
    (hseg : ∀ t ∈ Ioo (0:ℝ) 1, ∀ j, Qs j (F (z + t • (z' - z))) ≠ 0)
    {W : Set (ℝ × (Fin k → ℝ))} (hW : IsOpen W) (hWseg : segment ℝ z z' ⊆ W) :
    ∃ G : ℝ × (Fin k → ℝ) → V, Continuous G ∧ ∃ K T : Set (ℝ × (Fin k → ℝ)),
      IsCompact K ∧ K ⊆ W ∧ T ⊆ K ∧ z ∈ T ∧ z' ∈ T ∧ (∀ x ∉ T, G x = F x) ∧
      ∀ x ∈ T, ∀ j, Qs j (G x) ≠ 0 := by
  have hd : z' - z ≠ 0 := sub_ne_zero.2 hzz.symm
  obtain ⟨L, hL1⟩ := exists_linearEquiv_one hd
  let Lc : (ℝ × (Fin k → ℝ)) →L[ℝ] (ℝ × (Fin k → ℝ)) :=
    LinearMap.toContinuousLinearMap (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] (ℝ × (Fin k → ℝ)))
  have hLc : ∀ x, Lc x = L x := fun x => rfl
  set C := ‖Lc‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  have hLbound : ∀ x, ‖L x‖ ≤ C * ‖x‖ := fun x => by
    rw [← hLc]
    exact (Lc.le_opNorm x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  let Φ : ℝ × (Fin k → ℝ) → ℝ × (Fin k → ℝ) := fun x => z + L x
  have hΦc : Continuous Φ := continuous_const.add (L.toContinuousLinearEquiv.continuous)
  let f : ℝ × (Fin k → ℝ) → V := fun x => F (Φ x)
  have hfc : Continuous f := hF.comp hΦc
  have hΦ0 : Φ 0 = z := by simp [Φ]
  have hΦ1 : Φ (1, 0) = z' := by simp [Φ, hL1]
  have hf0 : f 0 = F z := by simp [f, hΦ0]
  have hf1 : f (1, 0) = F z' := by simp [f, hΦ1]
  -- local affinity
  have hr' : 0 < r / C := div_pos hr hCpos
  have hsmall : ∀ x, ‖x‖ < r / C → ‖L x‖ < r := fun x hx =>
    lt_of_le_of_lt (hLbound x) (by rw [lt_div_iff₀ hCpos] at hx; linarith)
  have h0 : ∀ x, ‖x‖ < r / C → f x = f 0 + lin (compFrame a L) x := by
    intro x hx
    simp only [f, Φ, hf0, lin_compFrame]
    exact ha _ (hsmall x hx)
  have h1 : ∀ x, ‖x‖ < r / C → f ((1, 0) + x) = f (1, 0) + lin (compFrame a' L) x := by
    intro x hx
    simp only [f, Φ, map_add, hL1, hf1, lin_compFrame]
    rw [show z + (z' - z + L x) = z' + L x by abel]
    exact ha' _ (hsmall x hx)
  have hdet' : (frameMat Q (compFrame a L)).det * (frameMat Q (compFrame a' L)).det < 0 := by
    rw [frameMat_compFrame, frameMat_compFrame, Matrix.det_mul, Matrix.det_mul]
    have hm := det_matE_ne_zero L
    have : 0 < (matE (L : (ℝ × (Fin k → ℝ)) →ₗ[ℝ] _)).det ^ 2 := by positivity
    nlinarith
  have hseg' : ∀ t ∈ Ioo (0:ℝ) 1, ∀ j, Qs j (f (t, 0)) ≠ 0 := by
    intro t ht j
    have : Φ (t, 0) = z + t • (z' - z) := by
      simp only [Φ]
      rw [show ((t, 0) : ℝ × (Fin k → ℝ)) = t • (1, 0) by simp, map_smul, hL1]
    simp only [f, this]
    exact hseg t ht j
  -- the width of the tube
  have hsegc : IsCompact (segment ℝ z z') := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hδW⟩ := hsegc.exists_cthickening_subset_open hW hWseg
  set η : ℝ := min (δ / (2 * (‖z' - z‖ + C))) 1 with hηdef
  have hη : 0 < η := lt_min (by positivity) one_pos
  have hηle : η * (‖z' - z‖ + C) < δ := by
    have := min_le_left (δ / (2 * (‖z' - z‖ + C))) 1
    rw [← hηdef, le_div_iff₀ (by positivity)] at this
    nlinarith
  let Kt : Set (ℝ × (Fin k → ℝ)) := Icc (-η) (1 + η) ×ˢ Metric.closedBall 0 η
  have hKt : IsCompact Kt := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hΦK : Φ '' Kt ⊆ W := by
    rintro _ ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
    apply hδW
    set t' := max 0 (min t 1)
    have ht' : t' ∈ Icc (0:ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    have hmem : z + t' • (z' - z) ∈ segment ℝ z z' := by
      rw [segment_eq_image']; exact ⟨t', ht', rfl⟩
    apply Metric.mem_cthickening_of_dist_le _ _ _ _ hmem
    have hΦtv : Φ (t, v) = z + t • (z' - z) + L (0, v) := by
      simp only [Φ]
      rw [show ((t, v) : ℝ × (Fin k → ℝ)) = t • (1, 0) + (0, v) by simp, map_add, map_smul, hL1]
      abel
    rw [hΦtv, dist_eq_norm]
    rw [show z + t • (z' - z) + L (0, v) - (z + t' • (z' - z)) =
      (t - t') • (z' - z) + L (0, v) by rw [sub_smul]; abel]
    have htt : |t - t'| ≤ η := by
      simp only [mem_Icc] at ht
      rw [abs_le]
      constructor
      · simp only [t']
        rcases le_total t 1 with h | h
        · rw [min_eq_left h]
          rcases le_total 0 t with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_right h, max_eq_right zero_le_one]; linarith
      · simp only [t']
        rcases le_total t 1 with h | h
        · rw [min_eq_left h]
          rcases le_total 0 t with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_right h, max_eq_right zero_le_one]; linarith
    have hv' : ‖v‖ ≤ η := by simpa using hv
    have hLv : ‖L (0, v)‖ ≤ C * ‖v‖ := by
      refine (hLbound _).trans (le_of_eq ?_)
      rw [Prod.norm_def]; simp
    calc ‖(t - t') • (z' - z) + L (0, v)‖ ≤ |t - t'| * ‖z' - z‖ + C * ‖v‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ hLv)
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ η * ‖z' - z‖ + C * η := by gcongr
      _ ≤ δ := by nlinarith
  -- cancel in standard position
  obtain ⟨g, hgc, T0, hT0, h0T, h1T, hgf, hgz⟩ := pair_cancel Q Qs hcodim hrank f hfc
    (compFrame a L) (compFrame a' L) hr' h0 h1 (by rwa [hf0]) (by rwa [hf1]) hdet'
    (by rwa [hf0]) (by rwa [hf1]) hseg' hη
  let Ψ : ℝ × (Fin k → ℝ) → ℝ × (Fin k → ℝ) := fun y => L.symm (y - z)
  have hΨc : Continuous Ψ :=
    L.symm.toContinuousLinearEquiv.continuous.comp (continuous_id.sub continuous_const)
  have hΦΨ : ∀ y, Φ (Ψ y) = y := fun y => by simp [Φ, Ψ]
  have hΨΦ : ∀ x, Ψ (Φ x) = x := fun x => by simp [Φ, Ψ]
  refine ⟨fun y => g (Ψ y), hgc.comp hΨc, Φ '' Kt, Φ '' T0, hKt.image hΦc, hΦK, ?_, ?_, ?_, ?_,
    ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hT0 hx
    exact ⟨x, ⟨⟨h1.le, h2.le⟩, by simpa using h3.le⟩, rfl⟩
  · exact ⟨0, h0T, hΦ0⟩
  · exact ⟨(1, 0), h1T, hΦ1⟩
  · intro y hy
    have : Ψ y ∉ T0 := fun h => hy ⟨Ψ y, h, hΦΨ y⟩
    simp only
    rw [hgf _ this]
    simp [f, hΦΨ]
  · rintro _ ⟨x, hx, rfl⟩ j
    simp only [hΨΦ]
    exact hgz x hx j

end Surgery
