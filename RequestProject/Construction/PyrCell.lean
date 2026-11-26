module

public import RequestProject.Construction.PyrDet

@[expose] public section

/-!
# The pyramid cells

On the zero cell of the pyramid `(k, A)`, `F0 x = cellT (alp x, gam x)` with `cellT` linear;
this is a cell (in the sense of `CellData`) with coordinates `yv k A`, simplex
`facetPts q m (rowSet m (k.succAbove 0) A) k` and orientation sign `-(-1)^k` (times `-1` if
`|A| = 3`).
-/

open Set Surgery Matrix

namespace Tverberg6R

noncomputable section

/-- The `H⁰`-argument of the cell formula. -/
def lamVec (k : Fin 6) (A : Finset (Fin 6)) (a : ℝ) (g : Fin 5 → ℝ) : Fin 6 → ℝ :=
  a • (Pi.single (k.succAbove 0) 1 : Fin 6 → ℝ) +
    ∑ t, g t • (Pi.single (sig k A (k.succAbove t)) 1 : Fin 6 → ℝ) - (5 * g 0) • bJ k

/-- The cell formula. -/
def cellT (q : Fin 6 → Fin 6 → ℝ) (k : Fin 6) (A : Finset (Fin 6)) (a : ℝ) (g : Fin 5 → ℝ) :
    Table :=
  (5 * g 0) • anc k A + H0 q (lamVec k A a g)

lemma lamVec_add (k : Fin 6) (A : Finset (Fin 6)) (a a' : ℝ) (g g' : Fin 5 → ℝ) :
    lamVec k A (a + a') (g + g') = lamVec k A a g + lamVec k A a' g' := by
  simp only [lamVec, add_smul, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  abel

lemma lamVec_smul (k : Fin 6) (A : Finset (Fin 6)) (c a : ℝ) (g : Fin 5 → ℝ) :
    lamVec k A (c * a) (c • g) = c • lamVec k A a g := by
  simp only [lamVec, smul_add, smul_sub, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  congr 2
  ring_nf

lemma cellT_add (q : Fin 6 → Fin 6 → ℝ) (k : Fin 6) (A : Finset (Fin 6)) (a a' : ℝ)
    (g g' : Fin 5 → ℝ) :
    cellT q k A (a + a') (g + g') = cellT q k A a g + cellT q k A a' g' := by
  simp only [cellT, lamVec_add, ← H0L_apply, map_add, Pi.add_apply, mul_add, add_smul]
  abel

lemma cellT_smul (q : Fin 6 → Fin 6 → ℝ) (k : Fin 6) (A : Finset (Fin 6)) (c a : ℝ)
    (g : Fin 5 → ℝ) : cellT q k A (c * a) (c • g) = c • cellT q k A a g := by
  simp only [cellT, lamVec_smul, ← H0L_apply, map_smul, Pi.smul_apply, smul_eq_mul, smul_add,
    smul_smul]
  ring_nf

lemma ell_cellT (q : Fin 6 → Fin 6 → ℝ) (m : Fin 6 → Word) (k : Fin 6) (A : Finset (Fin 6))
    (a : ℝ) (g : Fin 5 → ℝ) :
    ell m (cellT q k A a g) =
      ∑ s, ycoef A a g s • facetPts q m (rowSet m (k.succAbove 0) A) k s := by
  rw [cellT, ell_add, ell_smul, anc, ell_anchorTable, lamVec, bJ_eq_sum, smul_smul,
    show (5 * g 0 * (1 / 5)) = g 0 by ring, Finset.smul_sum]
  rw [← H0L_apply, map_sub, map_add, map_smul, ell_sub, ell_add, ell_smul, H0L_apply,
    ell_H0_single, H0L_apply, H0L_apply, ell_H0_sum, ell_H0_sum]
  have hre : ∑ t, g t • vvec q m (sig k A (k.succAbove t)) =
      ∑ t, g (tau A t) • vvec q m (k.succAbove t) := by
    rw [← Equiv.sum_comp (tau A)]
    simp only [sig_succAbove_tau]
  rw [hre]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [ycoef, facetPts, Fin.cons_zero, Fin.cons_succ]
  simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

lemma F0_eq_cellT (q : Fin 6 → Fin 6 → ℝ) {x : Fin 6 → ℝ} (hx : x ∈ massSimplex)
    {k : Fin 6} {A : Finset (Fin 6)} (hp : (k, A) ∈ Pyr) (h : InPyr k A x)
    (hmin : ∀ t, gam k A 0 x ≤ gam k A t x) :
    F0 q x = cellT q k A (alp k x) (fun t => gam k A t x) := by
  have hm0 : mhat k A x = gam k A 0 x := by
    unfold mhat
    have : (mn5 fun t => gam k A t x) = gam k A 0 x :=
      le_antisymm (mn5_le _ 0) (le_mn5 hmin)
    rw [this, pp_of_nonneg (h.2 0)]
  rw [F0_inPyr q hx hp h]
  simp only at hm0 ⊢
  rw [cellT, lam, hm0, zetaT_of_inPyr hx.2 h, lamVec]

/-- The linear part of `F0` on the zero cell. -/
def FLp (q : Fin 6 → Fin 6 → ℝ) (k : Fin 6) (A : Finset (Fin 6)) :
    (Fin 6 → ℝ) →ₗ[ℝ] Table where
  toFun w := cellT q k A (alpL k w) (fun t => gamL k t w)
  map_add' w w' := by
    rw [← cellT_add]
    congr 1
    · simp only [alpL, Pi.add_apply]; ring
    · funext t; simp only [gamL, Pi.add_apply]; ring
  map_smul' c w := by
    rw [RingHom.id_apply, ← cellT_smul]
    congr 1
    · simp only [alpL, Pi.smul_apply, smul_eq_mul]; ring
    · funext t; simp only [gamL, Pi.smul_apply, smul_eq_mul]; ring

/-! ### The open zero cell -/

lemma open_cell {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : ∀ s, 0 < yv k A x s) :
    0 < alp k x ∧ 0 < gam k A 0 x ∧ ∀ t, t ≠ 0 → gam k A 0 x < gam k A t x := by
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · have := h (Fin.succ 0)
    simpa [yv, tau_zero] using this
  · have := h 0
    simp only [yv, Fin.cons_zero] at this
    linarith
  · set t' := (tau A).symm t
    have ht' : t' ≠ 0 := by
      intro h0
      apply ht
      have : tau A t' = t := Equiv.apply_symm_apply _ _
      rw [← this, h0, tau_zero]
    have := h (Fin.succ t')
    simp only [yv, Fin.cons_succ, if_neg ht', add_zero, t', Equiv.apply_symm_apply] at this
    linarith

lemma inPyr_of_pos {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : ∀ s, 0 < yv k A x s) :
    InPyr k A x ∧ ∀ t, gam k A 0 x ≤ gam k A t x := by
  obtain ⟨ha, hg, hlt⟩ := open_cell h
  have hmin : ∀ t, gam k A 0 x ≤ gam k A t x := fun t => by
    by_cases ht : t = 0
    · rw [ht]
    · exact (hlt t ht).le
  exact ⟨⟨ha.le, fun t => hg.le.trans (hmin t)⟩, hmin⟩

lemma pos_of_yv_pos {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1)
    (h : ∀ s, 0 < yv k A x s) : ∀ i, 0 < x i := by
  intro i
  by_cases hik : i = k
  · rw [hik, x_self_eq k x]
    have := (open_cell h).1
    have := dl_pos
    positivity
  · have hnear := near_of_inPyr hx (inPyr_of_pos h).1
    linarith [(near_lt hnear hik).2]

/-- The pyramid cell `(k, A)` along `m`. -/
def pyrCell {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word} (hm : IsMatching m)
    {k : Fin 6} {A : Finset (Fin 6)} (hp : (k, A) ∈ Pyr) : CellData q m where
  Y := yv k A
  YL := yvL k A
  hY := yv_add k A
  hYL w hw := by
    have h1 := sum_yv k A (x := ehat + w) (by
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_ehat, hw, add_zero])
    rw [yv_add] at h1
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_yv k A sum_ehat] at h1
    linarith
  x0 := apex k A
  hx0 := sum_apex k A
  hYx0 := sum_yv k A (sum_apex k A)
  hdet := by
    rw [yv_apex]
    simp only [yvL_unitE, det_snocMat_smul, det_D1]
    have := dl_pos
    split_ifs <;> simp [this.ne'] <;> positivity
  z := facetPts q m (rowSet m (k.succAbove 0) A) k
  hz := by
    have hc := card_rowSet hm (k.succAbove 0) A
    have hA := mem_Pyr hp
    refine indep5_facetPts hq hm ?_ ?_ k
    · rw [← Finset.card_pos, hc]; exact hA.1
    · intro h
      have := congrArg Finset.card h
      rw [hc, Finset.card_univ, Fintype.card_fin] at this
      simp only at hA
      omega
  FL := FLp q k A
  hlin w := ell_cellT q m k A (alpL k w) (fun t => gamL k t w)
  hpos x hx h := pos_of_yv_pos hx h
  hell x hx h := by
    have hmem : x ∈ massSimplex := ⟨fun i => (pos_of_yv_pos hx h i).le, hx⟩
    rw [F0_eq_cellT q hmem hp (inPyr_of_pos h).1 (inPyr_of_pos h).2, ell_cellT]
    rfl
  hloc x hx h := by
    have hS : IsOpen {w : Fin 6 → ℝ | ∀ s, 0 < yv k A (x + w) s} := by
      have : {w : Fin 6 → ℝ | ∀ s, 0 < yv k A (x + w) s} =
          ⋂ s, {w | 0 < yv k A (x + w) s} := by ext w; simp
      rw [this]
      exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const
        ((continuous_apply s).comp ((continuous_yv k A).comp (continuous_const.add continuous_id)))
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS 0 (by simpa using h)
    refine ⟨r, hr, fun w hw hw0 => ?_⟩
    have hw' : ∀ s, 0 < yv k A (x + w) s := hball (by simpa using hw)
    have hsum : ∑ i, (x + w) i = 1 := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hw0, add_zero]
    have hmem : x ∈ massSimplex := ⟨fun i => (pos_of_yv_pos hx h i).le, hx⟩
    have hmem' : x + w ∈ massSimplex := ⟨fun i => (pos_of_yv_pos hsum hw' i).le, hsum⟩
    rw [F0_eq_cellT q hmem' hp (inPyr_of_pos hw').1 (inPyr_of_pos hw').2,
      F0_eq_cellT q hmem hp (inPyr_of_pos h).1 (inPyr_of_pos h).2]
    have e1 : alp k (x + w) = alp k x + alpL k w := alp_add k x w
    have e2 : (fun t => gam k A t (x + w)) = (fun t => gam k A t x) + (fun t => gamL k t w) := by
      funext t; exact gam_add k A t x w
    rw [e1, e2, cellT_add]
    rfl

lemma pyrCell_eps {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) {m : Fin 6 → Word}
    (hm : IsMatching m) {k : Fin 6} {A : Finset (Fin 6)} (hp : (k, A) ∈ Pyr) :
    (pyrCell hq hm hp).eps = -(-1) ^ (k : ℕ) * (if A.card = 3 then -1 else 1) := by
  simp only [CellData.eps, pyrCell]
  rw [yv_apex]
  simp only [yvL_unitE, det_snocMat_smul, det_D1]
  have hpos : (0 : ℝ) < (1 / dl) ^ 5 := by have := dl_pos; positivity
  rw [sign_mul, sign_pos hpos, one_mul]
  rcases Nat.even_or_odd (k : ℕ) with h | h <;> split_ifs <;>
    simp [h.neg_one_pow]

end

end Tverberg6R
