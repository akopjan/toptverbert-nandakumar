module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import RequestProject.Reduction

@[expose] public section

/-!
# Layout of the anchor pyramids

For every facet `k` (the face `x k = 0` of the mass simplex) and every anchor label set `A`
with `1 ≤ |A| ≤ 3` there is a tiny pyramid with apex `apex k A` (inside the simplex) and base
vertices `vert k A t` (on the facet).  `alp k` and `gam k A t` are the barycentric coordinates
with respect to these six points (for points of the hyperplane `∑ x = 1`).
-/

open Set

namespace Tverberg6R

noncomputable section

/-- Size of the pyramids. -/
def dl : ℝ := 1 / 100000

lemma dl_pos : 0 < dl := by norm_num [dl]

/-- The barycentre of the mass simplex. -/
def ehat : Fin 6 → ℝ := fun _ => 1 / 6

/-- The barycentre of the facet `x k = 0`. -/
def bJ (k : Fin 6) : Fin 6 → ℝ := fun i => if i = k then 0 else 1 / 5

/-- Anchor label sets. -/
def anchors : Finset (Finset (Fin 6)) :=
  Finset.univ.filter fun A => 1 ≤ A.card ∧ A.card ≤ 3

/-- An injective code of label sets. -/
def code (A : Finset (Fin 6)) : ℕ := (Fintype.equivFin (Finset (Fin 6)) A : ℕ)

lemma code_lt (A : Finset (Fin 6)) : code A < 64 := by
  have := (Fintype.equivFin (Finset (Fin 6)) A).isLt
  simpa [code] using this

lemma code_inj {A A' : Finset (Fin 6)} (h : code A = code A') : A = A' :=
  (Fintype.equivFin _).injective (Fin.ext h)

/-- The centre of the base of the pyramid `(k, A)`. -/
def ctr (k : Fin 6) (A : Finset (Fin 6)) : Fin 6 → ℝ := fun i =>
  bJ k i + (code A : ℝ) / 1000 *
    ((if i = k.succAbove 3 then 1 else 0) - (if i = k.succAbove 4 then 1 else 0))

/-- The apex. -/
def apex (k : Fin 6) (A : Finset (Fin 6)) : Fin 6 → ℝ := ctr k A + dl • (ehat - bJ k)

/-- The base vertices. -/
def vert (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) : Fin 6 → ℝ :=
  ctr k A + dl • (Pi.single (k.succAbove t) 1 - bJ k)

/-- Barycentric coordinate of the apex. -/
def alp (k : Fin 6) (x : Fin 6 → ℝ) : ℝ := 6 * x k / dl

/-- Barycentric coordinates of the base vertices. -/
def gam (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) (x : Fin 6 → ℝ) : ℝ :=
  (x (k.succAbove t) - ctr k A (k.succAbove t) + alp k x * dl / 30) / dl + (1 - alp k x) / 5

/-! ### Basic values -/

lemma bJ_self (k : Fin 6) : bJ k k = 0 := by simp [bJ]

lemma bJ_succAbove (k : Fin 6) (t : Fin 5) : bJ k (k.succAbove t) = 1 / 5 := by
  simp [bJ, Fin.succAbove_ne]

lemma ctr_self (k : Fin 6) (A : Finset (Fin 6)) : ctr k A k = 0 := by
  have h3 : k ≠ k.succAbove 3 := (Fin.succAbove_ne k 3).symm
  have h4 : k ≠ k.succAbove 4 := (Fin.succAbove_ne k 4).symm
  simp [ctr, bJ_self, h3, h4]

lemma ctr_succAbove (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) :
    ctr k A (k.succAbove t) = 1 / 5 + (code A : ℝ) / 1000 *
      ((if t = 3 then 1 else 0) - (if t = 4 then 1 else 0)) := by
  simp [ctr, bJ_succAbove, Fin.succAbove_right_inj]

lemma code_div_bound (A : Finset (Fin 6)) : 0 ≤ (code A : ℝ) / 1000 ∧ (code A : ℝ) / 1000 ≤ 63 / 1000 := by
  have := code_lt A
  have h : (code A : ℝ) ≤ 63 := by exact_mod_cast Nat.lt_succ_iff.1 this
  constructor <;> [positivity; linarith]

lemma ctr_succAbove_bounds (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) :
    13 / 100 ≤ ctr k A (k.succAbove t) ∧ ctr k A (k.succAbove t) ≤ 27 / 100 := by
  rw [ctr_succAbove]
  obtain ⟨h0, h1⟩ := code_div_bound A
  split_ifs <;> constructor <;> nlinarith

lemma sum_succAbove (k : Fin 6) (x : Fin 6 → ℝ) : ∑ t, x (k.succAbove t) = ∑ i, x i - x k := by
  rw [Fin.sum_univ_succAbove x k]; ring

lemma sum_ctr_succAbove (k : Fin 6) (A : Finset (Fin 6)) : ∑ t, ctr k A (k.succAbove t) = 1 := by
  simp only [ctr_succAbove, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Fin.sum_univ_five]

lemma sum_alp_gam (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) :
    alp k x + ∑ t, gam k A t x = 1 := by
  have hs := sum_succAbove k x
  have hc := sum_ctr_succAbove k A
  have hd := dl_pos
  simp only [gam, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs, hc, hx]
  unfold alp
  field_simp
  ring

/-- **Reconstruction**: barycentric coordinates. -/
lemma recon (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1) :
    x = alp k x • apex k A + ∑ t, gam k A t x • vert k A t := by
  have hsum := sum_alp_gam k A hx
  have hd := dl_pos
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, apex, vert,
    Pi.sub_apply]
  rcases eq_or_ne i k with rfl | hik
  · have : ∀ t, (Pi.single (i.succAbove t) (1:ℝ) : Fin 6 → ℝ) i = 0 := fun t =>
      Pi.single_eq_of_ne (Fin.succAbove_ne i t).symm _
    simp only [this, ctr_self, bJ_self, ehat]
    simp only [sub_zero, zero_add, mul_zero, Finset.sum_const_zero, add_zero]
    unfold alp; field_simp
  · obtain ⟨t0, rfl⟩ := Fin.exists_succAbove_eq hik
    have hsg : ∑ t, gam k A t x = 1 - alp k x := by linarith
    have hsingle : ∀ t, (Pi.single (k.succAbove t) (1:ℝ) : Fin 6 → ℝ) (k.succAbove t0) =
        if t = t0 then 1 else 0 := by
      intro t
      by_cases h : t = t0
      · subst h; simp
      · rw [Pi.single_eq_of_ne (fun e => h (Fin.succAbove_right_injective e).symm), if_neg h]
    simp only [hsingle, bJ_succAbove, ehat]
    have : ∑ t, gam k A t x * (ctr k A (k.succAbove t0) + dl * ((if t = t0 then 1 else 0) - 1 / 5))
        = (∑ t, gam k A t x) * (ctr k A (k.succAbove t0) - dl / 5) + dl * gam k A t0 x := by
      have e : ∀ t, gam k A t x * (ctr k A (k.succAbove t0) + dl * ((if t = t0 then 1 else 0) - 1 / 5))
          = gam k A t x * (ctr k A (k.succAbove t0) - dl / 5) +
            dl * (if t = t0 then gam k A t x else 0) := by
        intro t; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ t0]
      simp
    rw [this, hsg]
    unfold gam
    field_simp
    ring

/-! ### Neighbourhoods of the pyramids -/

/-- Points close to the centre of the pyramid `(k, A)`. -/
def Near (k : Fin 6) (A : Finset (Fin 6)) (x : Fin 6 → ℝ) : Prop :=
  ∀ i, |x i - ctr k A i| ≤ 2 * dl

lemma x_self_eq (k : Fin 6) (x : Fin 6 → ℝ) : x k = alp k x * dl / 6 := by
  unfold alp; have := dl_pos; field_simp

lemma x_succAbove_eq (k : Fin 6) (A : Finset (Fin 6)) (t : Fin 5) (x : Fin 6 → ℝ) :
    x (k.succAbove t) - ctr k A (k.succAbove t) =
      dl * (gam k A t x - (1 - alp k x) / 5) - alp k x * dl / 30 := by
  unfold gam; have := dl_pos; field_simp; ring

lemma near_of_coords (k : Fin 6) (A : Finset (Fin 6)) {x : Fin 6 → ℝ} (hx : ∑ i, x i = 1)
    (ha : -1 / 10 ≤ alp k x) (hg : ∀ t, -1 / 10 ≤ gam k A t x) : Near k A x := by
  have hsum := sum_alp_gam k A hx
  rw [Fin.sum_univ_five] at hsum
  have h0 := hg 0; have h1 := hg 1; have h2 := hg 2; have h3 := hg 3; have h4 := hg 4
  have hd := dl_pos
  have hgu : ∀ t, gam k A t x ≤ 3 / 2 := by
    intro t; fin_cases t <;> simp <;> linarith
  have hau : alp k x ≤ 3 / 2 := by linarith
  intro i
  rcases eq_or_ne i k with rfl | hik
  · rw [ctr_self, sub_zero, x_self_eq i x, abs_le]
    constructor <;> nlinarith
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hik
    rw [x_succAbove_eq, abs_le]
    have := hgu t; have := hg t
    constructor <;> nlinarith

lemma near_self_le {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : Near k A x) :
    x k ≤ 2 * dl := by
  have := h k; rw [ctr_self, sub_zero, abs_le] at this; exact this.2

lemma near_succAbove_ge {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : Near k A x)
    (t : Fin 5) : 13 / 100 - 2 * dl ≤ x (k.succAbove t) := by
  have := h (k.succAbove t); rw [abs_le] at this
  have := (ctr_succAbove_bounds k A t).1
  linarith

lemma near_lt {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : Near k A x) {i : Fin 6}
    (hi : i ≠ k) : x k < x i ∧ 1 / 10 < x i := by
  obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hi
  have h1 := near_self_le h
  have h2 := near_succAbove_ge h t
  have : dl = 1 / 100000 := rfl
  constructor <;> linarith

lemma near_self_lt {k : Fin 6} {A : Finset (Fin 6)} {x : Fin 6 → ℝ} (h : Near k A x) :
    x k < 1 / 12 := by
  have := near_self_le h; have : dl = 1 / 100000 := rfl; linarith

lemma near_unique {k k' : Fin 6} {A A' : Finset (Fin 6)} {x : Fin 6 → ℝ}
    (h : Near k A x) (h' : Near k' A' x) : k = k' ∧ A = A' := by
  have hdl : dl = 1 / 100000 := rfl
  by_cases hk : k = k'
  · subst hk
    refine ⟨rfl, code_inj ?_⟩
    by_contra hne
    have e1 := h (k.succAbove 3)
    have e2 := h' (k.succAbove 3)
    rw [ctr_succAbove, abs_le] at e1 e2
    simp only [if_true, show (3 : Fin 5) ≠ 4 by decide, if_false, sub_zero, mul_one] at e1 e2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (code A : ℝ) + 1 ≤ code A' := by exact_mod_cast hlt
      linarith [e1.1, e1.2, e2.1, e2.2]
    · have : (code A' : ℝ) + 1 ≤ code A := by exact_mod_cast hlt
      linarith [e1.1, e1.2, e2.1, e2.2]
  · exfalso
    have h1 := near_self_le h
    have h2 := (near_lt h' hk).2
    linarith

end

end Tverberg6R
