module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

open scoped BigOperators

/-- The 35-dimensional simplex in `ℝ^36` (same as in `Challenge.lean`). -/
def Δ : Set (Fin 36 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1}

/-- The comparator statement (same as in `Challenge.lean`). -/
def TverbergCounterexample : Prop :=
  ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
    ContinuousOn f Δ ∧
    ∀ x : Fin 6 → (Fin 36 → ℝ),
      (∀ i, x i ∈ Δ) →
      (∀ i j, i ≠ j →
        ∀ k, x i k = 0 ∨ x j k = 0) →
      ∃ i, f (x i) ≠ f (x 0)

namespace Tverberg6R

/-- Words of length six over six letters: position `i` is a color, the letter a label. -/
abbrev Word := Fin 6 → Fin 6

/-- Height tables. -/
abbrev Table := Word → ℝ

/-- The vertex of `Δ^35` with color `i` and label `a`. -/
def vtx (i a : Fin 6) : Fin 36 := finProdFinEquiv (i, a)

/-- Color masses of a source point. -/
noncomputable def mass (x : Fin 36 → ℝ) (i : Fin 6) : ℝ := ∑ a, x (vtx i a)

/-- The mass simplex `Δ^5`. -/
def massSimplex : Set (Fin 6 → ℝ) := {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1}

/-- Boundary compatibility: if color `i` has zero mass, the table ignores letter `i`. -/
def Compatible (H : (Fin 6 → ℝ) → Table) : Prop :=
  ∀ l ∈ massSimplex, ∀ i, l i = 0 → ∀ u v : Word, (∀ j, j ≠ i → u j = v j) → H l u = H l v

/-- An (ordered) matching: six words whose letters in every position are distinct. -/
def IsMatching (m : Fin 6 → Word) : Prop := ∀ p, Function.Injective (fun j => m j p)

/-- Safety: along every matching, the heights are not all equal. -/
def Safe (H : (Fin 6 → ℝ) → Table) : Prop :=
  ∀ l ∈ massSimplex, ∀ m : Fin 6 → Word, IsMatching m → ∃ j, H l (m j) ≠ H l (m 0)

/-- Conditional weights (uniform on a zero-mass color). -/
noncomputable def cw (x : Fin 36 → ℝ) (i a : Fin 6) : ℝ :=
  if mass x i = 0 then 1 / 6 else x (vtx i a) / mass x i

/-- The averaged height. -/
noncomputable def avgHeight (H : (Fin 6 → ℝ) → Table) (x : Fin 36 → ℝ) : ℝ :=
  ∑ w : Word, H (mass x) w * ∏ i, cw x i (w i)

/-- The test map `x ↦ (λ₀,…,λ₄, g(x))`. -/
noncomputable def testMap (H : (Fin 6 → ℝ) → Table) (x : Fin 36 → ℝ) : Fin 6 → ℝ :=
  fun k => if k = 5 then avgHeight H x else mass x k

/-! ### Basic facts about masses -/

lemma sum_mass (x : Fin 36 → ℝ) : ∑ i, mass x i = ∑ k, x k := by
  unfold mass vtx
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp (finProdFinEquiv (m := 6) (n := 6)) x

lemma mass_nonneg {x : Fin 36 → ℝ} (hx : x ∈ Δ) (i : Fin 6) : 0 ≤ mass x i :=
  Finset.sum_nonneg fun _ _ => hx.1 _

lemma mass_mem {x : Fin 36 → ℝ} (hx : x ∈ Δ) : mass x ∈ massSimplex :=
  ⟨mass_nonneg hx, by rw [sum_mass]; exact hx.2⟩

lemma continuous_mass (i : Fin 6) : Continuous (fun x : Fin 36 → ℝ => mass x i) := by
  unfold mass
  fun_prop

lemma continuous_massVec : Continuous (fun x : Fin 36 → ℝ => mass x) :=
  continuous_pi continuous_mass

lemma cw_nonneg {x : Fin 36 → ℝ} (hx : x ∈ Δ) (i a : Fin 6) : 0 ≤ cw x i a := by
  unfold cw
  split_ifs
  · norm_num
  · exact div_nonneg (hx.1 _) (mass_nonneg hx i)

lemma cw_le_one {x : Fin 36 → ℝ} (hx : x ∈ Δ) (i a : Fin 6) : cw x i a ≤ 1 := by
  unfold cw
  split_ifs with h
  · norm_num
  · have hpos : 0 < mass x i := lt_of_le_of_ne (mass_nonneg hx i) (Ne.symm h)
    rw [div_le_one hpos]
    exact Finset.single_le_sum (f := fun a => x (vtx i a)) (fun b _ => hx.1 _)
      (Finset.mem_univ a)

lemma cw_sum {x : Fin 36 → ℝ} (i : Fin 6) : ∑ a, cw x i a = 1 := by
  unfold cw
  split_ifs with h
  · simp
  · rw [← Finset.sum_div]
    exact div_self h

/-! ### Averaging over letters a table ignores -/

lemma sum_row_shift (Ψ : Word → ℝ) (i : Fin 6)
    (hΨ : ∀ w b, Ψ (Function.update w i b) = Ψ w) (r : Fin 6 → ℝ) (hr : ∑ a, r a = 1) :
    ∑ w, Ψ w * r (w i) = (1 / 6) * ∑ w, Ψ w := by
  have key : ∀ c : Fin 6, ∑ w, Ψ w * r (w i) = ∑ w, Ψ w * r (w i + c) := by
    intro c
    let e : Word ≃ Word :=
      { toFun := fun w => Function.update w i (w i + c)
        invFun := fun w => Function.update w i (w i - c)
        left_inv := fun w => by simp
        right_inv := fun w => by simp }
    rw [← e.sum_comp]
    simp [e, hΨ]
  have h6 : 6 * ∑ w, Ψ w * r (w i) = ∑ w, Ψ w := by
    calc 6 * ∑ w, Ψ w * r (w i) = ∑ c : Fin 6, ∑ w, Ψ w * r (w i + c) := by
          rw [← Finset.sum_congr rfl (fun c _ => key c)]
          simp
      _ = ∑ w, Ψ w * ∑ c, r (w i + c) := by
          rw [Finset.sum_comm]
          simp [Finset.mul_sum]
      _ = ∑ w, Ψ w := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [show ∑ c, r (w i + c) = ∑ a, r a from
            Equiv.sum_comp (Equiv.addLeft (w i)) r, hr, mul_one]
  linarith

lemma prod_update_row (p : Fin 6 → Fin 6 → ℝ) (i : Fin 6) (r : Fin 6 → ℝ) (w : Word) :
    ∏ k, Function.update p i r k (w k) =
      r (w i) * ∏ k, Function.update p i (fun _ => 1) k (w k) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun k => Function.update p i (fun _ => 1) k (w k))
      (Finset.mem_univ i)]
  simp only [Function.update_self, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Finset.mem_erase] at hk
  simp [Function.update_of_ne hk.1]

lemma sum_update_row (F : Word → ℝ) (p : Fin 6 → Fin 6 → ℝ) (i : Fin 6)
    (hF : ∀ w b, F (Function.update w i b) = F w) (r : Fin 6 → ℝ) (hr : ∑ a, r a = 1) :
    ∑ w, F w * ∏ k, Function.update p i r k (w k) =
      (1 / 6) * ∑ w, F w * ∏ k, Function.update p i (fun _ => 1) k (w k) := by
  simp_rw [prod_update_row p i r]
  rw [← sum_row_shift (fun w => F w * ∏ k, Function.update p i (fun _ => 1) k (w k)) i _ r hr]
  · refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · intro w b
    simp only [hF]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]

lemma sum_replace_row (F : Word → ℝ) (p : Fin 6 → Fin 6 → ℝ) (i : Fin 6)
    (hF : ∀ w b, F (Function.update w i b) = F w) (hp : ∑ a, p i a = 1)
    (r : Fin 6 → ℝ) (hr : ∑ a, r a = 1) :
    ∑ w, F w * ∏ k, p k (w k) = ∑ w, F w * ∏ k, Function.update p i r k (w k) := by
  have h1 := sum_update_row F p i hF (p i) hp
  rw [Function.update_eq_self] at h1
  rw [h1, sum_update_row F p i hF r hr]

/-- Replacing probability rows on letters that the table ignores does not change the
average. -/
lemma sum_replace (F : Word → ℝ) (p q : Fin 6 → Fin 6 → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ i, ∑ a, q i a = 1)
    (hF : ∀ i, p i ≠ q i → ∀ w b, F (Function.update w i b) = F w) :
    ∑ w, F w * ∏ i, p i (w i) = ∑ w, F w * ∏ i, q i (w i) := by
  have main : ∀ S : Finset (Fin 6), ∑ w, F w * ∏ i, p i (w i) =
      ∑ w, F w * ∏ i, (fun k => if k ∈ S then q k else p k) i (w i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [ih]
      have hfun : (fun k => if k ∈ insert a S then q k else p k) =
          Function.update (fun k => if k ∈ S then q k else p k) a (q a) := by
        funext k
        by_cases hk : k = a
        · subst hk; simp
        · simp [hk]
      rw [hfun]
      by_cases hpq : p a = q a
      · have : Function.update (fun k => if k ∈ S then q k else p k) a (q a) =
            (fun k => if k ∈ S then q k else p k) := by
          rw [Function.update_eq_iff]
          refine ⟨by simp [ha, hpq], fun _ _ => rfl⟩
        rw [this]
      · refine sum_replace_row F _ a (hF a hpq) ?_ (q a) (hq a)
        simp [ha, hp a]
  have := main Finset.univ
  simpa using this

/-- Averaging a table against point masses evaluates it. -/
lemma sum_pointMass (F : Word → ℝ) (m : Word) :
    ∑ w, F w * ∏ i, (fun i a => if a = m i then (1 : ℝ) else 0) i (w i) = F m := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    have : ∃ i, b i ≠ m i := by
      by_contra h
      push_neg at h
      exact hb (funext h)
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · simp [hi]
  · simp

lemma compat_update {H : (Fin 6 → ℝ) → Table} (hC : Compatible H) {l : Fin 6 → ℝ}
    (hl : l ∈ massSimplex) {i : Fin 6} (hi : l i = 0) (w : Word) (b : Fin 6) :
    H l (Function.update w i b) = H l w :=
  hC l hl i hi _ _ fun j hj => by simp [Function.update_of_ne hj]

/-! ### Continuity of the averaged height -/

theorem avgHeight_continuousOn (H : (Fin 6 → ℝ) → Table) (hH : ContinuousOn H massSimplex)
    (hC : Compatible H) : ContinuousOn (avgHeight H) Δ := by
  intro x0 hx0
  set l0 := mass x0 with hl0
  have hl0m : l0 ∈ massSimplex := mass_mem hx0
  let q : (Fin 36 → ℝ) → Fin 6 → Fin 6 → ℝ := fun x i a => if l0 i = 0 then 1 / 6 else cw x i a
  let G : (Fin 36 → ℝ) → ℝ := fun x => ∑ w : Word, H l0 w * ∏ i, q x i (w i)
  -- Step A: replacing the rows of inactive colors
  have hA : ∀ x, ∑ w : Word, H l0 w * ∏ i, cw x i (w i) = G x := by
    intro x
    refine sum_replace _ _ _ (fun i => cw_sum i) (fun i => ?_) (fun i hi => ?_)
    · by_cases h : l0 i = 0
      · simp [q, h]
      · simp only [q, h, if_false]; exact cw_sum i
    · have h : l0 i = 0 := by
        by_contra h
        exact hi (by funext a; simp [q, h])
      exact compat_update hC hl0m h
  -- Step B: `G` is continuous at `x0`
  have hq : ∀ i a, ContinuousAt (fun x => q x i a) x0 := by
    intro i a
    by_cases h : l0 i = 0
    · simp only [q, h, if_true]; exact continuousAt_const
    · simp only [q, h, if_false]
      have hev : (fun x => x (vtx i a) / mass x i) =ᶠ[nhds x0] (fun x => cw x i a) := by
        have : ∀ᶠ x in nhds x0, mass x i ≠ 0 :=
          (continuous_mass i).continuousAt.eventually_ne h
        filter_upwards [this] with x hx
        simp [cw, hx]
      refine ContinuousAt.congr ?_ hev
      exact ContinuousAt.div (continuous_apply _).continuousAt
        (continuous_mass i).continuousAt h
  have hG : ContinuousAt G x0 := by
    simp only [G]
    fun_prop
  -- Step C: the error term
  let E : (Fin 36 → ℝ) → ℝ := fun x => ∑ w : Word, |H (mass x) w - H l0 w|
  have hHc : ContinuousOn (fun x => H (mass x)) Δ :=
    hH.comp continuous_massVec.continuousOn (fun x hx => mass_mem hx)
  have hE : Filter.Tendsto E (nhdsWithin x0 Δ) (nhds 0) := by
    have hcont : ContinuousWithinAt E Δ x0 := by
      simp only [E]
      exact tendsto_finsetSum _ fun w _ =>
        (((continuous_apply w).continuousWithinAt.comp (hHc x0 hx0)
          (Set.mapsTo_univ _ _)).sub continuousWithinAt_const).abs
    have h0 : E x0 = 0 := by simp [E, l0]
    rw [← h0]
    exact hcont
  -- Step D: the bound
  have hD : ∀ x ∈ Δ, ‖avgHeight H x - G x‖ ≤ E x := by
    intro x hx
    rw [← hA x]
    simp only [avgHeight, E, ← Finset.sum_sub_distrib, ← sub_mul, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    rw [abs_mul]
    have h1 : |∏ i, cw x i (w i)| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => cw_nonneg hx _ _)]
      exact (Finset.prod_induction (fun i => cw x i (w i)) (fun r => 0 ≤ r ∧ r ≤ 1)
        (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
        ⟨zero_le_one, le_rfl⟩ fun i _ => ⟨cw_nonneg hx _ _, cw_le_one hx _ _⟩).2
    calc |H (mass x) w - H l0 w| * |∏ i, cw x i (w i)| ≤ |H (mass x) w - H l0 w| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := mul_one _
  -- Step E: combine
  have hdiff : Filter.Tendsto (fun x => avgHeight H x - G x) (nhdsWithin x0 Δ) (nhds 0) :=
    squeeze_zero_norm' (eventually_nhdsWithin_of_forall hD) hE
  have hsum := hdiff.add hG.continuousWithinAt.tendsto
  have hval : avgHeight H x0 = 0 + G x0 := by rw [zero_add, ← hA x0]; rfl
  show Filter.Tendsto (avgHeight H) (nhdsWithin x0 Δ) (nhds (avgHeight H x0))
  rw [hval]
  convert hsum using 1
  funext x
  ring

/-! ### The height-table reduction -/

/-- **Height-table reduction.** A continuous, boundary-compatible, safe height table on the
mass simplex yields a counterexample of the comparator form. -/
theorem counterexample_of_height (H : (Fin 6 → ℝ) → Table) (hH : ContinuousOn H massSimplex)
    (hC : Compatible H) (hS : Safe H) : TverbergCounterexample := by
  refine ⟨testMap H, ?_, ?_⟩
  · refine continuousOn_pi.2 fun k => ?_
    show ContinuousOn (fun x => testMap H x k) Δ
    simp only [testMap]
    split_ifs
    · exact avgHeight_continuousOn H hH hC
    · exact (continuous_mass k).continuousOn
  · intro x hx hdisj
    by_contra hcon
    push_neg at hcon
    set l := mass (x 0) with hl_def
    have hl : l ∈ massSimplex := mass_mem (hx 0)
    -- all masses agree
    have hmass : ∀ j, mass (x j) = l := by
      intro j
      have e : ∀ k : Fin 6, k ≠ 5 → mass (x j) k = mass (x 0) k := by
        intro k hk
        have := congrFun (hcon j) k
        simpa [testMap, hk] using this
      have s1 : ∑ i, mass (x j) i = 1 := by rw [sum_mass]; exact (hx j).2
      have s0 : ∑ i, mass (x 0) i = 1 := by rw [sum_mass]; exact (hx 0).2
      rw [Fin.sum_univ_six] at s1 s0
      have e0 := e 0 (by decide)
      have e1 := e 1 (by decide)
      have e2 := e 2 (by decide)
      have e3 := e 3 (by decide)
      have e4 := e 4 (by decide)
      funext i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
      · exact e3
      · exact e4
      · show mass (x j) 5 = mass (x 0) 5
        linarith
    -- every point charges every active color
    have hpos : ∀ j i, l i ≠ 0 → ∃ a, 0 < x j (vtx i a) := by
      intro j i hi
      by_contra h
      push_neg at h
      have hle : mass (x j) i ≤ 0 := Finset.sum_nonpos fun a _ => h a
      have hge : 0 ≤ mass (x j) i := mass_nonneg (hx j) i
      rw [hmass j] at hle hge
      exact hi (le_antisymm hle hge)
    classical
    let m : Fin 6 → Word := fun j i =>
      if h : l i = 0 then j else Classical.choose (hpos j i h)
    have hm_pos : ∀ j i (h : l i ≠ 0), 0 < x j (vtx i (m j i)) := by
      intro j i h
      rw [show m j i = Classical.choose (hpos j i h) from dif_neg h]
      exact Classical.choose_spec (hpos j i h)
    have hmatch : IsMatching m := by
      intro p j j' hjj'
      simp only at hjj'
      by_cases hp : l p = 0
      · simpa [m, hp] using hjj'
      · by_contra hne
        have a := hm_pos j p hp
        have b := hm_pos j' p hp
        rw [hjj'] at a
        rcases hdisj j j' hne (vtx p (m j' p)) with h | h <;> linarith
    have hzero : ∀ j i, l i ≠ 0 → ∀ a, a ≠ m j i → x j (vtx i a) = 0 := by
      intro j i hi a ha
      have hsurj : Function.Surjective (fun j' => m j' i) :=
        Finite.injective_iff_surjective.mp (hmatch i)
      obtain ⟨j', rfl⟩ := hsurj a
      have hne : j' ≠ j := fun h => ha (by rw [h])
      rcases hdisj j j' (Ne.symm hne) (vtx i (m j' i)) with h | h
      · exact h
      · have := hm_pos j' i hi
        linarith
    have hval : ∀ j, avgHeight H (x j) = H l (m j) := by
      intro j
      unfold avgHeight
      rw [hmass j]
      rw [sum_replace (H l) (cw (x j)) (fun i a => if a = m j i then (1 : ℝ) else 0)
        (fun i => cw_sum i) (fun i => by simp) ?_]
      · exact sum_pointMass (H l) (m j)
      · intro i hi
        have h : l i = 0 := by
          by_contra h
          apply hi
          funext a
          have hmi : mass (x j) i = l i := by rw [hmass j]
          have htot : x j (vtx i (m j i)) = l i := by
            rw [← hmi]
            unfold mass
            rw [Finset.sum_eq_single (m j i)]
            · intro b _ hb; exact hzero j i h b hb
            · simp
          simp only [cw, hmi, h, if_false]
          by_cases ha : a = m j i
          · subst ha; rw [htot, div_self h]; simp
          · rw [hzero j i h a ha]; simp [ha]
        exact compat_update hC hl h
    obtain ⟨j, hj⟩ := hS l hl m hmatch
    apply hj
    rw [← hval j, ← hval 0]
    have := congrFun (hcon j) 5
    simpa [testMap] using this

end Tverberg6R
