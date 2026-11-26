module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import AkopyanResearch.ColoredChainContraction
public import AkopyanResearch.CochainAnnihilator

@[expose] public section

/-!
# Universal pair source `Ω^{*15}`, symmetry `H = S₄ × D₈`, and explicit 16-annihilator

1. Explicit group `D8` of order `8`, pair symmetry group `PairGroup := Equiv.Perm (Fin 4) × D8`
   of order `192`, index-3 subgroup `P_pair := Sylow₂(S₄) × D8`, and exchange character
   `exchangeChar : PairGroup →* ℤˣ`.
2. Universal pair column states `PairState` (`|PairState| = 1440`), free `PairGroup`-action on
   non-degenerate words `w : Word PairState 15`, and existence of a fixing exchange involution on
   every degenerate word.
3. Explicit `PairGroup`-equivariant averaged chain homotopy `Kbar` on `Chain PairState 15`,
   producing an explicit relative `16`-primitive for every `exchangeChar`-equivariant relative
   `13`-cocycle (both for `PairGroup` and for `P_pair`).
-/

noncomputable section

open scoped BigOperators Classical

namespace AkopyanResearch

/-! ### 1. The dihedral group `D8` and `PairGroup = S₄ × D₈` -/

section Groups

@[ext]
structure D8 where
  sa : Bool
  sb : Bool
  ex : Bool
  deriving DecidableEq, Fintype

instance : One D8 := ⟨⟨false, false, false⟩⟩

instance : Mul D8 where
  mul d₁ d₂ :=
    if d₂.ex then ⟨xor d₁.sb d₂.sa, xor d₁.sa d₂.sb, !d₁.ex⟩
    else ⟨xor d₁.sa d₂.sa, xor d₁.sb d₂.sb, d₁.ex⟩

instance : Inv D8 where
  inv d := if d.ex then ⟨d.sb, d.sa, true⟩ else ⟨d.sa, d.sb, false⟩

lemma d8_one_def : (1 : D8) = ⟨false, false, false⟩ := rfl
lemma d8_mul_def (a b : D8) : a * b =
    if b.ex then ⟨xor a.sb b.sa, xor a.sa b.sb, !a.ex⟩
    else ⟨xor a.sa b.sa, xor a.sb b.sb, a.ex⟩ := rfl
lemma d8_inv_def (a : D8) : a⁻¹ = if a.ex then ⟨a.sb, a.sa, true⟩ else ⟨a.sa, a.sb, false⟩ := rfl

instance : Group D8 where
  mul_assoc a b c := by
    rcases a with ⟨a1, a2, a3⟩
    rcases b with ⟨b1, b2, b3⟩
    rcases c with ⟨c1, c2, c3⟩
    cases a1 <;> cases a2 <;> cases a3 <;>
      cases b1 <;> cases b2 <;> cases b3 <;>
      cases c1 <;> cases c2 <;> cases c3 <;> rfl
  one_mul a := by
    rcases a with ⟨a1, a2, a3⟩
    cases a1 <;> cases a2 <;> cases a3 <;> rfl
  mul_one a := by
    rcases a with ⟨a1, a2, a3⟩
    cases a1 <;> cases a2 <;> cases a3 <;> rfl
  inv_mul_cancel a := by
    rcases a with ⟨a1, a2, a3⟩
    cases a1 <;> cases a2 <;> cases a3 <;> rfl

lemma card_D8 : Fintype.card D8 = 8 := by decide

abbrev PairGroup := Equiv.Perm (Fin 4) × D8

lemma card_PairGroup : Fintype.card PairGroup = 192 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, card_D8]
  norm_num [Nat.factorial]

def tau0 : D8 := ⟨false, false, true⟩
def tau1 : D8 := ⟨true, true, true⟩

def exchangeChar : PairGroup →* ℤˣ where
  toFun h := if h.2.ex then -1 else 1
  map_one' := rfl
  map_mul' a b := by
    rcases a with ⟨σ₁, ⟨sa₁, sb₁, ex₁⟩⟩
    rcases b with ⟨σ₂, ⟨sa₂, sb₂, ex₂⟩⟩
    cases ex₁ <;> cases ex₂ <;> rfl

lemma exchangeChar_conj_tau0 (d : D8) :
    exchangeChar ((1 : Equiv.Perm (Fin 4)), d * tau0 * d⁻¹) = -1 := by
  rcases d with ⟨sa, sb, ex⟩
  cases sa <;> cases sb <;> cases ex <;> rfl

lemma exchangeChar_tau0 : exchangeChar ((1 : Equiv.Perm (Fin 4)), tau0) = -1 := rfl
lemma exchangeChar_tau1 : exchangeChar ((1 : Equiv.Perm (Fin 4)), tau1) = -1 := rfl

def isSylow2Fin4 (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ i j : Fin 4, i.1 % 2 = j.1 % 2 ↔ (σ i).1 % 2 = (σ j).1 % 2

instance instDecidablePredIsSylow2Fin4 : DecidablePred isSylow2Fin4 :=
  fun σ => inferInstanceAs (Decidable (∀ i j : Fin 4,
    i.1 % 2 = j.1 % 2 ↔ (σ i).1 % 2 = (σ j).1 % 2))

def P_pair : Subgroup PairGroup where
  carrier := {h | isSylow2Fin4 h.1}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {a b} ha hb i j := (hb i j).trans (ha (b.1 i) (b.1 j))
  inv_mem' {a} ha i j := by
    have h := ha (a.1⁻¹ i) (a.1⁻¹ j)
    simpa using h.symm

instance instDecidablePredMemP_pair : DecidablePred (· ∈ P_pair) :=
  fun h => instDecidablePredIsSylow2Fin4 h.1

theorem card_P_pair : Fintype.card P_pair = 64 := by
  have heq : Fintype.card P_pair =
      Fintype.card {σ : Equiv.Perm (Fin 4) // isSylow2Fin4 σ} * Fintype.card D8 := by
    refine Fintype.card_congr
      { toFun := fun h => (⟨h.1.1, h.2⟩, h.1.2)
        invFun := fun (p : {σ : Equiv.Perm (Fin 4) // isSylow2Fin4 σ} × D8) =>
          ⟨(p.1.1, p.2), p.1.2⟩
        left_inv := fun h => Subtype.ext (Prod.ext rfl rfl)
        right_inv := fun p => Prod.ext (Subtype.ext rfl) rfl }
  have hS : Fintype.card {σ : Equiv.Perm (Fin 4) // isSylow2Fin4 σ} = 8 := by decide
  rw [heq, hS, card_D8]

theorem index_P_pair : P_pair.index = 3 := by
  have h := Subgroup.index_mul_card P_pair
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_P_pair, card_PairGroup] at h
  omega

end Groups

/-! ### 2. Universal pair column states `Ω` (`|Ω| = 1440`) and free action outside `A_X` -/

section UniversalSource

inductive PairSymbol
  | c (i : Fin 4)
  | a (j : Fin 2)
  | b (j : Fin 2)
  deriving DecidableEq, Fintype

abbrev PairState := Equiv.Perm (Fin 6) × Bool

theorem card_PairState : Fintype.card PairState = 1440 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_bool]
  norm_num [Nat.factorial]

def evalPairState (ω : PairState) : PairSymbol → Fin 6
  | .c i => ω.1 (i.castAdd 2)
  | .a j => ω.1 (Fin.natAdd 4 j)
  | .b j => ω.1 (Fin.natAdd 4 (if ω.2 then ⟨1 - j.1, by omega⟩ else j))

def actSymbol (h : PairGroup) : PairSymbol → PairSymbol
  | .c i => .c (h.1 i)
  | .a j =>
      let j' : Fin 2 := if h.2.sa then ⟨1 - j.1, by omega⟩ else j
      if h.2.ex then .b j' else .a j'
  | .b j =>
      let j' : Fin 2 := if h.2.sb then ⟨1 - j.1, by omega⟩ else j
      if h.2.ex then .a j' else .b j'

lemma actSymbol_one (s : PairSymbol) : actSymbol (1 : PairGroup) s = s := by
  cases s <;> rfl

lemma actSymbol_mul (h₁ h₂ : PairGroup) (s : PairSymbol) :
    actSymbol (h₁ * h₂) s = actSymbol h₁ (actSymbol h₂ s) := by
  rcases h₁ with ⟨σ₁, ⟨sa₁, sb₁, ex₁⟩⟩
  rcases h₂ with ⟨σ₂, ⟨sa₂, sb₂, ex₂⟩⟩
  cases s with
  | c i => rfl
  | a j =>
    fin_cases j <;> cases sa₁ <;> cases sb₁ <;> cases ex₁ <;>
      cases sa₂ <;> cases sb₂ <;> cases ex₂ <;> rfl
  | b j =>
    fin_cases j <;> cases sa₁ <;> cases sb₁ <;> cases ex₁ <;>
      cases sa₂ <;> cases sb₂ <;> cases ex₂ <;> rfl

instance : MulAction PairGroup PairSymbol where
  smul := actSymbol
  one_smul := actSymbol_one
  mul_smul := actSymbol_mul

lemma evalPairState_injective : Function.Injective evalPairState := by
  intro ω₁ ω₂ h
  have hc : ∀ i : Fin 4, ω₁.1 (i.castAdd 2) = ω₂.1 (i.castAdd 2) := fun i =>
    congrFun h (.c i)
  have ha : ∀ j : Fin 2, ω₁.1 (Fin.natAdd 4 j) = ω₂.1 (Fin.natAdd 4 j) := fun j =>
    congrFun h (.a j)
  have hperm : ω₁.1 = ω₂.1 := by
    apply Equiv.ext
    intro k
    fin_cases k
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact hc 3
    · exact ha 0
    · exact ha 1
  have hb0 := congrFun h (.b 0)
  dsimp [evalPairState] at hb0
  rw [hperm] at hb0
  have hb0' := ω₂.1.injective hb0
  have hbool : ω₁.2 = ω₂.2 := by
    cases h1 : ω₁.2 <;> cases h2 : ω₂.2
    · rfl
    · simp [h1, h2, Fin.ext_iff] at hb0'
    · simp [h1, h2, Fin.ext_iff] at hb0'
    · rfl
  exact Prod.ext hperm hbool

def sResPerm (d : D8) (exSwap : Bool) : Equiv.Perm (Fin 2) :=
  if d.ex then
    (if xor d.sa exSwap then Equiv.swap 0 1 else 1)
  else
    (if d.sa then Equiv.swap 0 1 else 1)

def colPerm4 (σ : Equiv.Perm (Fin 4)) (d : D8) (exSwap : Bool) : Equiv.Perm (Fin 6) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ (sResPerm d exSwap)).trans finSumFinEquiv)

def actPairStateFun (h : PairGroup) (ω : PairState) : PairState :=
  (ω.1 * colPerm4 h.1⁻¹ h.2⁻¹ ω.2, xor (xor h.2.sa h.2.sb) ω.2)

lemma colPerm4_castAdd (σ : Equiv.Perm (Fin 4)) (d : D8) (exSwap : Bool) (i : Fin 4) :
    colPerm4 σ d exSwap (i.castAdd 2) = (σ i).castAdd 2 := by
  change finSumFinEquiv
    (Equiv.sumCongr σ (sResPerm d exSwap) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma colPerm4_natAdd (σ : Equiv.Perm (Fin 4)) (d : D8) (exSwap : Bool) (j : Fin 2) :
    colPerm4 σ d exSwap (Fin.natAdd 4 j) = Fin.natAdd 4 (sResPerm d exSwap j) := by
  change finSumFinEquiv
    (Equiv.sumCongr σ (sResPerm d exSwap) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem evalPairState_actPairState (h : PairGroup) (ω : PairState) (s : PairSymbol) :
    evalPairState (actPairStateFun h ω) s = evalPairState ω (h⁻¹ • s) := by
  rcases h with ⟨σ, ⟨sa, sb, ex⟩⟩
  rcases ω with ⟨π, swap⟩
  cases s with
  | c i =>
    change (π * colPerm4 σ⁻¹ ⟨sa, sb, ex⟩⁻¹ swap) (i.castAdd 2) = π ((σ⁻¹ i).castAdd 2)
    simp [Equiv.Perm.mul_apply, colPerm4_castAdd]
  | a j =>
    change (π * colPerm4 σ⁻¹ ⟨sa, sb, ex⟩⁻¹ swap) (Fin.natAdd 4 j) =
      evalPairState (π, swap) (actSymbol (σ, ⟨sa, sb, ex⟩)⁻¹ (.a j))
    rw [Equiv.Perm.mul_apply, colPerm4_natAdd]
    cases sa <;> cases sb <;> cases ex <;> cases swap <;> fin_cases j <;>
      simp [Prod.inv_mk, d8_inv_def, sResPerm, evalPairState, actSymbol]
  | b j =>
    change (π * colPerm4 σ⁻¹ ⟨sa, sb, ex⟩⁻¹ swap)
        (Fin.natAdd 4 (if xor (xor sa sb) swap then ⟨1 - j.1, by omega⟩ else j)) =
      evalPairState (π, swap) (actSymbol (σ, ⟨sa, sb, ex⟩)⁻¹ (.b j))
    rw [Equiv.Perm.mul_apply, colPerm4_natAdd]
    cases sa <;> cases sb <;> cases ex <;> cases swap <;> fin_cases j <;>
      simp [Prod.inv_mk, d8_inv_def, sResPerm, evalPairState, actSymbol]

instance : SMul PairGroup PairState := ⟨actPairStateFun⟩

@[simp] lemma pairGroup_smul_pairState (h : PairGroup) (ω : PairState) :
    h • ω = actPairStateFun h ω := rfl

instance : MulAction PairGroup PairState where
  one_smul ω := evalPairState_injective (by
    funext s
    rw [pairGroup_smul_pairState, evalPairState_actPairState, inv_one, one_smul])
  mul_smul h₁ h₂ ω := evalPairState_injective (by
    funext s
    simp only [pairGroup_smul_pairState, evalPairState_actPairState, mul_inv_rev, mul_smul])

theorem stabilizer_PairState_iff (h : PairGroup) (ω : PairState) :
    h • ω = ω ↔ h.1 = 1 ∧
      ((ω.2 = false ∧ (h.2 = 1 ∨ h.2 = tau0)) ∨
       (ω.2 = true ∧ (h.2 = 1 ∨ h.2 = tau1))) := by
  rcases h with ⟨σ, d⟩
  rcases ω with ⟨π, swap⟩
  constructor
  · intro heq
    rcases d with ⟨sa, sb, ex⟩
    have hfun : ∀ s, evalPairState (π, swap) (((σ, (⟨sa, sb, ex⟩ : D8)) : PairGroup)⁻¹ • s) =
        evalPairState (π, swap) s :=
      fun s => by rw [← evalPairState_actPairState]; exact congrFun (congrArg evalPairState heq) s
    have hσ : σ = 1 := by
      apply Equiv.ext; intro i
      have hc := hfun (.c i)
      change π ((σ⁻¹ i).castAdd 2) = π (i.castAdd 2) at hc
      have h0 : σ⁻¹ i = i := by
        have := π.injective hc
        exact Fin.ext (by simpa [Fin.ext_iff] using this)
      have hσi : σ i = i := by
        have := congrArg σ h0
        simpa using this.symm
      exact hσi
    refine ⟨hσ, ?_⟩
    have hswap : xor (xor sa sb) swap = swap := congrArg Prod.snd heq
    have hcol : colPerm4 σ⁻¹ (⟨sa, sb, ex⟩ : D8)⁻¹ swap = 1 :=
      mul_left_cancel (congrArg Prod.fst heq)
    have h4 : colPerm4 σ⁻¹ (⟨sa, sb, ex⟩ : D8)⁻¹ swap (Fin.natAdd 4 (0 : Fin 2)) =
        Fin.natAdd 4 (0 : Fin 2) := by
      rw [hcol]; rfl
    rw [colPerm4_natAdd] at h4
    have hres0 : sResPerm (⟨sa, sb, ex⟩ : D8)⁻¹ swap 0 = 0 :=
      Fin.ext (by have := congrArg Fin.val h4; simp [Fin.natAdd] at this; omega)
    cases swap <;> cases sa <;> cases sb <;> cases ex <;>
      simp_all [d8_inv_def, sResPerm, d8_one_def, tau0, tau1, Fin.ext_iff]
  · rintro ⟨rfl, (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩)⟩
    · exact one_smul _ _
    · apply evalPairState_injective; funext s; rw [pairGroup_smul_pairState, evalPairState_actPairState]
      cases s with
      | c i => rfl
      | a j => fin_cases j <;> rfl
      | b j => fin_cases j <;> rfl
    · exact one_smul _ _
    · apply evalPairState_injective; funext s; rw [pairGroup_smul_pairState, evalPairState_actPairState]
      cases s with
      | c i => rfl
      | a j => fin_cases j <;> rfl
      | b j => fin_cases j <;> rfl

theorem S4_free_PairState (σ : Equiv.Perm (Fin 4)) (ω : PairState)
    (h : ((σ, (1 : D8)) : PairGroup) • ω = ω) : σ = 1 :=
  ((stabilizer_PairState_iff (σ, 1) ω).mp h).1

def actWord (h : PairGroup) : {n : ℕ} →
    AkopyanColoredChains.Word PairState n → AkopyanColoredChains.Word PairState n
  | 0, PUnit.unit => PUnit.unit
  | _ + 1, (none, w) => (none, actWord h w)
  | _ + 1, (some ω, w) => (some (h • ω), actWord h w)

lemma actWord_one : ∀ (n : ℕ) (w : AkopyanColoredChains.Word PairState n), actWord 1 w = w
  | 0, PUnit.unit => rfl
  | _ + 1, (none, w) => by simp [actWord, actWord_one _ w]
  | _ + 1, (some ω, w) => by simp [actWord, actWord_one _ w]

lemma actWord_mul : ∀ (n : ℕ) (h₁ h₂ : PairGroup) (w : AkopyanColoredChains.Word PairState n),
    actWord (h₁ * h₂) w = actWord h₁ (actWord h₂ w)
  | 0, _, _, PUnit.unit => rfl
  | _ + 1, h₁, h₂, (none, w) => by simp [actWord, actWord_mul _ h₁ h₂ w]
  | _ + 1, h₁, h₂, (some ω, w) => by simp [actWord, mul_smul, actWord_mul _ h₁ h₂ w]

lemma actWord_injective (n : ℕ) (h : PairGroup) :
    Function.Injective (actWord h : AkopyanColoredChains.Word PairState n → _) := by
  intro w₁ w₂ heq
  have h1 := congrArg (actWord h⁻¹) heq
  rwa [← actWord_mul, ← actWord_mul, inv_mul_cancel, actWord_one, actWord_one] at h1

lemma degree_actWord : ∀ (n : ℕ) (h : PairGroup) (w : AkopyanColoredChains.Word PairState n),
    AkopyanColoredChains.degree PairState (actWord h w) = AkopyanColoredChains.degree PairState w
  | 0, _, PUnit.unit => rfl
  | _ + 1, h, (none, w) => degree_actWord _ h w
  | _ + 1, h, (some _, w) => congrArg (· + 1) (degree_actWord _ h w)

def AllSwapFalse : {n : ℕ} → AkopyanColoredChains.Word PairState n → Prop
  | 0, PUnit.unit => True
  | _ + 1, (none, w) => AllSwapFalse w
  | _ + 1, (some ω, w) => ω.2 = false ∧ AllSwapFalse w

def AllSwapTrue : {n : ℕ} → AkopyanColoredChains.Word PairState n → Prop
  | 0, PUnit.unit => True
  | _ + 1, (none, w) => AllSwapTrue w
  | _ + 1, (some ω, w) => ω.2 = true ∧ AllSwapTrue w

def DegenerateWord {n : ℕ} (w : AkopyanColoredChains.Word PairState n) : Prop :=
  AllSwapFalse w ∨ AllSwapTrue w

lemma S4_free_actWord : ∀ {n : ℕ} (σ : Equiv.Perm (Fin 4))
    (w : AkopyanColoredChains.Word PairState n),
    0 < AkopyanColoredChains.degree PairState w →
    actWord (σ, (1 : D8)) w = w → σ = 1
  | 0, _, _, hdeg, _ => absurd hdeg (by simp [AkopyanColoredChains.degree])
  | _ + 1, σ, (none, w), hdeg, heq => by
    simp only [actWord, Prod.mk.injEq, true_and] at heq
    exact S4_free_actWord σ w hdeg heq
  | _ + 1, σ, (some ω, _), _, heq => by
    simp only [actWord, Prod.mk.injEq, Option.some.injEq] at heq
    exact S4_free_PairState σ ω heq.1

lemma allSwapFalse_of_degree_nonpos : ∀ {n : ℕ} (w : AkopyanColoredChains.Word PairState n),
    AkopyanColoredChains.degree PairState w ≤ 0 → AllSwapFalse w
  | 0, PUnit.unit, _ => trivial
  | _ + 1, (none, w), hle => allSwapFalse_of_degree_nonpos w hle
  | m + 1, (some ω, w), hle => by
    have h0 : (0 : ℤ) ≤ AkopyanColoredChains.degree PairState w := by
      clear hle
      induction m with
      | zero => cases w; simp [AkopyanColoredChains.degree]
      | succ m ih' =>
        rcases w with ⟨b, w⟩
        cases b <;> simp [AkopyanColoredChains.degree] <;> have := ih' w <;> omega
    simp [AkopyanColoredChains.degree] at hle
    omega

theorem pairGroup_free_of_not_degenerate {n : ℕ} (w : AkopyanColoredChains.Word PairState n)
    (hnot : ¬ DegenerateWord w) (h : PairGroup) (heq : actWord h w = w) : h = 1 := by
  have aux : ∀ {m : ℕ} (v : AkopyanColoredChains.Word PairState m),
      actWord h v = v → (¬ AllSwapFalse v → h.2 ≠ tau0) ∧ (¬ AllSwapTrue v → h.2 ≠ tau1) ∧
      (0 < AkopyanColoredChains.degree PairState v → h.1 = 1 ∧ (h.2 = 1 ∨ h.2 = tau0 ∨ h.2 = tau1)) := by
    intro m v hv
    induction m with
    | zero =>
      cases v
      refine ⟨fun h1 => absurd trivial h1, fun h1 => absurd trivial h1, fun hdeg => ?_⟩
      simp [AkopyanColoredChains.degree] at hdeg
    | succ m ih =>
      rcases v with ⟨a, v⟩
      cases a with
      | none =>
        simp only [actWord, Prod.mk.injEq, true_and] at hv
        exact ih v hv
      | some ω =>
        simp only [actWord, Prod.mk.injEq, Option.some.injEq] at hv
        obtain ⟨ihf, iht, ihd⟩ := ih v hv.2
        have hst := (stabilizer_PairState_iff h ω).mp hv.1
        refine ⟨fun hnf => ?_, fun hnt => ?_, fun _ => ?_⟩
        · simp only [AllSwapFalse, not_and] at hnf
          by_cases hω : ω.2 = false
          · exact ihf (hnf hω)
          · have hωt : ω.2 = true := Bool.eq_true_of_not_eq_false hω
            intro hbad
            rcases hst.2 with ⟨hf, _⟩ | ⟨_, h1 | h1⟩
            · exact absurd (hf ▸ hωt) (by decide)
            · exact absurd (h1.symm.trans hbad) (by decide)
            · exact absurd (h1.symm.trans hbad) (by decide)
        · simp only [AllSwapTrue, not_and] at hnt
          by_cases hω : ω.2 = true
          · exact iht (hnt hω)
          · have hωf : ω.2 = false := Bool.eq_false_of_not_eq_true hω
            intro hbad
            rcases hst.2 with ⟨_, h1 | h1⟩ | ⟨ht, _⟩
            · exact absurd (h1.symm.trans hbad) (by decide)
            · exact absurd (h1.symm.trans hbad) (by decide)
            · exact absurd (ht ▸ hωf) (by decide)
        · refine ⟨hst.1, ?_⟩
          rcases hst.2 with ⟨_, h1 | h1⟩ | ⟨_, h1 | h1⟩ <;> simp [h1]
  obtain ⟨hf, ht, hd⟩ := aux w heq
  have hnf : ¬ AllSwapFalse w := fun h1 => hnot (Or.inl h1)
  have hnt : ¬ AllSwapTrue w := fun h1 => hnot (Or.inr h1)
  have hdeg : 0 < AkopyanColoredChains.degree PairState w := by
    by_contra hle
    exact hnf (allSwapFalse_of_degree_nonpos w (not_lt.mp hle))
  obtain ⟨h1, h2⟩ := hd hdeg
  have h2' : h.2 = 1 := by
    rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd h2 (hf hnf)
    · exact absurd h2 (ht hnt)
  exact Prod.ext h1 h2'

theorem exists_fixing_exchange_of_degenerate {n : ℕ} (w : AkopyanColoredChains.Word PairState n)
    (hdeg : DegenerateWord w) :
    ∃ d : D8, exchangeChar ((1 : Equiv.Perm (Fin 4)), d) = -1 ∧
      actWord ((1 : Equiv.Perm (Fin 4)), d) w = w := by
  have hf_fix : ∀ {m : ℕ} (v : AkopyanColoredChains.Word PairState m),
      AllSwapFalse v → actWord ((1 : Equiv.Perm (Fin 4)), tau0) v = v := by
    intro m v hv
    induction m with
    | zero => cases v; rfl
    | succ m ih =>
      rcases v with ⟨a, v⟩
      cases a with
      | none => exact congrArg (none, ·) (ih v hv)
      | some ω =>
        have hst := (stabilizer_PairState_iff (1, tau0) ω).mpr ⟨rfl, Or.inl ⟨hv.1, Or.inr rfl⟩⟩
        simp [actWord, hst, ih v hv.2]
  have ht_fix : ∀ {m : ℕ} (v : AkopyanColoredChains.Word PairState m),
      AllSwapTrue v → actWord ((1 : Equiv.Perm (Fin 4)), tau1) v = v := by
    intro m v hv
    induction m with
    | zero => cases v; rfl
    | succ m ih =>
      rcases v with ⟨a, v⟩
      cases a with
      | none => exact congrArg (none, ·) (ih v hv)
      | some ω =>
        have hst := (stabilizer_PairState_iff (1, tau1) ω).mpr ⟨rfl, Or.inr ⟨hv.1, Or.inr rfl⟩⟩
        simp [actWord, hst, ih v hv.2]
  rcases hdeg with hf | ht
  · exact ⟨tau0, exchangeChar_tau0, hf_fix w hf⟩
  · exact ⟨tau1, exchangeChar_tau1, ht_fix w ht⟩

end UniversalSource

/-! ### 3. Unconditional `S₄`-equivariant chain homotopy & `D8`-averaged `16`-annihilator -/

section ChainAnnihilator

open AkopyanColoredChains

abbrev PairChain := Chain PairState 15
abbrev PairWord := Word PairState 15

def refState : PairState := (1, false)

lemma degWord_nonneg : ∀ {n : ℕ} (w : Word PairState n), 0 ≤ degree PairState w
  | 0, PUnit.unit => le_rfl
  | _ + 1, (none, w) => degWord_nonneg w
  | _ + 1, (some _, w) => by simp [degree]; linarith [degWord_nonneg w]

def actChain (h : PairGroup) : PairChain →ₗ[ℤ] PairChain :=
  Finsupp.lmapDomain ℤ ℤ (actWord h)

@[simp] lemma actChain_basis (h : PairGroup) (w : PairWord) :
    actChain h (basis PairState w) = basis PairState (actWord h w) := by
  simp [actChain, basis]

@[simp] lemma actWord_one_mk {n : ℕ} (w : Word PairState n) :
    actWord ((1 : Equiv.Perm (Fin 4)), (1 : D8)) w = w :=
  actWord_one n w

@[simp] lemma lmapDomain_basis {n : ℕ} (f : Word PairState n → Word PairState n) (w : Word PairState n) :
    Finsupp.lmapDomain ℤ ℤ f (basis PairState w) = basis PairState (f w) := by
  simp [basis]

lemma actChain_one : actChain (1 : PairGroup) = LinearMap.id := by
  apply chainMap_ext; intro w; rw [actChain_basis, actWord_one, LinearMap.id_apply]

lemma actChain_mul (h₁ h₂ : PairGroup) :
    actChain (h₁ * h₂) = (actChain h₁).comp (actChain h₂) := by
  apply chainMap_ext; intro w
  rw [LinearMap.comp_apply, actChain_basis, actChain_basis, actChain_basis, actWord_mul]

lemma actChain_apply_mul (h₁ h₂ : PairGroup) (c : PairChain) :
    actChain h₁ (actChain h₂ c) = actChain (h₁ * h₂) c :=
  congrArg (fun f => f c) (actChain_mul h₁ h₂).symm

lemma actChain_prepend_none (h : PairGroup) {n : ℕ} (c : Chain PairState n) :
    Finsupp.lmapDomain ℤ ℤ (actWord h) (prepend PairState none c) =
      prepend PairState none (Finsupp.lmapDomain ℤ ℤ (actWord h) c) := by
  have hl : (Finsupp.lmapDomain ℤ ℤ (actWord h : Word PairState (n + 1) → Word PairState (n + 1))).comp
        (prepend PairState none) =
      (prepend PairState none).comp (Finsupp.lmapDomain ℤ ℤ (actWord h)) := by
    apply chainMap_ext; intro w; simp [prepend, basis, actWord]
  exact LinearMap.congr_fun hl c

lemma actChain_prepend_some (h : PairGroup) {n : ℕ} (ω : PairState) (c : Chain PairState n) :
    Finsupp.lmapDomain ℤ ℤ (actWord h) (prepend PairState (some ω) c) =
      prepend PairState (some (h • ω)) (Finsupp.lmapDomain ℤ ℤ (actWord h) c) := by
  have hl : (Finsupp.lmapDomain ℤ ℤ (actWord h : Word PairState (n + 1) → Word PairState (n + 1))).comp
        (prepend PairState (some ω)) =
      (prepend PairState (some (h • ω))).comp (Finsupp.lmapDomain ℤ ℤ (actWord h)) := by
    apply chainMap_ext; intro w; simp [prepend, basis, actWord]
  exact LinearMap.congr_fun hl c

lemma boundary_actWord_comm (h : PairGroup) : ∀ (n : ℕ),
    (boundary PairState n).comp (Finsupp.lmapDomain ℤ ℤ (actWord h)) =
      (Finsupp.lmapDomain ℤ ℤ (actWord h)).comp (boundary PairState n)
  | 0 => by simp [boundary]
  | n + 1 => by
    apply chainMap_ext
    rintro ⟨a, w⟩
    have ih : boundary PairState n (basis PairState (actWord h w)) =
        Finsupp.lmapDomain ℤ ℤ (actWord h) (boundary PairState n (basis PairState w)) := by
      simpa only [LinearMap.comp_apply, lmapDomain_basis] using
        LinearMap.congr_fun (boundary_actWord_comm h n) (basis PairState w)
    cases a with
    | none =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, lmapDomain_basis, actWord,
        boundary_basis_none, boundary_basis_none, actChain_prepend_none, ih]
    | some ω =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, lmapDomain_basis, actWord,
        boundary_basis_some, boundary_basis_some, map_sub,
        actChain_prepend_none, actChain_prepend_some, ih, lmapDomain_basis]

lemma boundary_actChain (h : PairGroup) (c : PairChain) :
    boundary PairState 15 (actChain h c) = actChain h (boundary PairState 15 c) :=
  LinearMap.congr_fun (boundary_actWord_comm h 15) c

lemma actChain_homogeneous (h : PairGroup) {k : ℤ} {c : PairChain}
    (hc : Homogeneous PairState k c) : Homogeneous PairState k (actChain h c) := by
  apply homogeneous_map_of_basis PairState (actChain h) c hc
  intro w hw
  rw [actChain_basis]
  simpa only [degree_actWord, hw] using homogeneous_basis PairState 15 (actWord h w)

lemma boundary_homogeneous : ∀ (n : ℕ) {k : ℤ} (c : Chain PairState n),
    Homogeneous PairState (k + 1) c → Homogeneous PairState k (boundary PairState n c)
  | 0, k, c, hc => by simp [boundary, homogeneous_zero]
  | n + 1, k, c, hc => by
    apply homogeneous_map_of_basis PairState (boundary PairState (n + 1)) c hc
    rintro ⟨a, w⟩ hw
    cases a with
    | none =>
      rw [boundary_basis_none]
      apply homogeneous_prepend_none
      have hd : degree PairState w = k + 1 := hw
      exact boundary_homogeneous n (basis PairState w)
        (by simpa [hd] using homogeneous_basis PairState n w)
    | some ω =>
      rw [boundary_basis_some]
      apply homogeneous_sub
      · apply homogeneous_prepend_none
        have hd : degree PairState w = k := by
          change degree PairState w + 1 = k + 1 at hw
          omega
        simpa [hd] using homogeneous_basis PairState n w
      · rw [← sub_add_cancel k 1]
        apply homogeneous_prepend_some PairState ω
        have hd : degree PairState w = (k - 1) + 1 := by
          change degree PairState w + 1 = k + 1 at hw
          omega
        exact boundary_homogeneous n (basis PairState w)
          (by simpa [hd] using homogeneous_basis PairState n w)

def s4Setoid : Setoid PairWord :=
  ⟨fun w₁ w₂ => ∃ σ : Equiv.Perm (Fin 4), actWord (σ, (1 : D8)) w₁ = w₂,
   fun w => ⟨1, actWord_one_mk w⟩,
   fun ⟨σ, h⟩ => ⟨σ⁻¹, by rw [← h, ← actWord_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one,
     actWord_one_mk]⟩,
   fun ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ => ⟨σ₂ * σ₁, by
     rw [show (σ₂ * σ₁, (1 : D8)) = (σ₂, (1 : D8)) * (σ₁, (1 : D8)) from by ext <;> simp,
       actWord_mul, h₁, h₂]⟩⟩

lemma s4Setoid_rel {w₁ w₂ : PairWord} :
    s4Setoid.r w₁ w₂ ↔ ∃ σ : Equiv.Perm (Fin 4), actWord (σ, (1 : D8)) w₁ = w₂ := Iff.rfl

def s4Setoid' : Setoid PairWord := s4Setoid

def s4Rep (w : PairWord) : PairWord :=
  (Quotient.mk s4Setoid w).out

lemma s4Rep_rel (w : PairWord) : ∃ σ : Equiv.Perm (Fin 4), actWord (σ, (1 : D8)) (s4Rep w) = w :=
  Quotient.exact (Quotient.out_eq (Quotient.mk s4Setoid w))

lemma s4Rep_invariant (σ : Equiv.Perm (Fin 4)) (w : PairWord) :
    s4Rep (actWord (σ, (1 : D8)) w) = s4Rep w := by
  unfold s4Rep
  congr 1
  exact Quotient.sound ⟨σ⁻¹, by rw [← actWord_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, actWord_one_mk]⟩

lemma degree_s4Rep (w : PairWord) :
    degree PairState (s4Rep w) = degree PairState w := by
  obtain ⟨σ, hσ⟩ := s4Rep_rel w
  nth_rw 2 [← hσ]
  rw [degree_actWord]

def s4Shift (w : PairWord) : Equiv.Perm (Fin 4) :=
  Classical.choose (s4Rep_rel w)

lemma actWord_s4Shift (w : PairWord) :
    actWord (s4Shift w, (1 : D8)) (s4Rep w) = w :=
  Classical.choose_spec (s4Rep_rel w)

lemma s4Shift_act (σ : Equiv.Perm (Fin 4)) (w : PairWord)
    (hdeg : 0 < degree PairState w) :
    s4Shift (actWord (σ, (1 : D8)) w) = σ * s4Shift w := by
  have hrel1 : actWord (s4Shift (actWord (σ, (1 : D8)) w), (1 : D8)) (s4Rep w) =
      actWord (σ * s4Shift w, (1 : D8)) (s4Rep w) := by
    have hsplitR : (σ * s4Shift w, (1 : D8)) = (σ, (1 : D8)) * (s4Shift w, (1 : D8)) := by
      ext <;> simp
    conv_lhs => rw [← s4Rep_invariant σ w, actWord_s4Shift]
    rw [hsplitR, actWord_mul, actWord_s4Shift]
  have hrel2 : actWord ((σ * s4Shift w)⁻¹ * s4Shift (actWord (σ, (1 : D8)) w), (1 : D8))
      (s4Rep w) = s4Rep w := by
    have hsplit : ((σ * s4Shift w)⁻¹ * s4Shift (actWord (σ, (1 : D8)) w), (1 : D8)) =
        ((σ * s4Shift w)⁻¹, (1 : D8)) * (s4Shift (actWord (σ, (1 : D8)) w), (1 : D8)) := by
      ext <;> simp
    rw [hsplit, actWord_mul, hrel1, ← actWord_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one,
      actWord_one_mk]
  have hpos : 0 < degree PairState (s4Rep w) := by rw [degree_s4Rep]; exact hdeg
  have hone := S4_free_actWord _ (s4Rep w) hpos hrel2
  exact (inv_mul_eq_one.mp hone).symm

lemma actWord_eq_of_degree_zero : ∀ {n : ℕ} (w : Word PairState n),
    degree PairState w = 0 → ∀ h : PairGroup, actWord h w = w
  | 0, PUnit.unit, _, _ => rfl
  | _ + 1, (none, w), hw, h => by
    change (none, actWord h w) = (none, w)
    rw [actWord_eq_of_degree_zero w hw h]
  | _ + 1, (some ω, w), hw, _ => by
    have h0 := degWord_nonneg w
    change degree PairState w + 1 = 0 at hw
    omega

lemma actChain_s4_comm_d8 (σ : Equiv.Perm (Fin 4)) (d : D8) :
    (actChain (σ, (1 : D8))).comp (actChain ((1 : Equiv.Perm (Fin 4)), d)) =
      (actChain ((1 : Equiv.Perm (Fin 4)), d)).comp (actChain (σ, (1 : D8))) := by
  rw [← actChain_mul, ← actChain_mul]
  congr 1
  ext <;> simp

noncomputable def K_deg : ℕ → PairChain →ₗ[ℤ] PairChain
  | 0 => 0
  | k + 1 =>
      if _ : k ≤ 13 then
        Finsupp.linearCombination ℤ (fun w : PairWord =>
          if degree PairState w = ((k + 1 : ℕ) : ℤ) then
            actChain (s4Shift w, (1 : D8)) (contraction PairState refState 15
              ((actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState (s4Rep w)) -
                basis PairState (s4Rep w)) -
                K_deg k (boundary PairState 15 (basis PairState (s4Rep w)))))
          else 0)
      else 0

lemma K_deg_succ_basis (k : ℕ) (hk : k ≤ 13) (w : PairWord) :
    K_deg (k + 1) (basis PairState w) =
      if degree PairState w = ((k + 1 : ℕ) : ℤ) then
        actChain (s4Shift w, (1 : D8)) (contraction PairState refState 15
          ((actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState (s4Rep w)) -
            basis PairState (s4Rep w)) -
            K_deg k (boundary PairState 15 (basis PairState (s4Rep w)))))
      else 0 := by
  simp [K_deg, hk, basis]

lemma K_deg_props : ∀ k : ℕ, k ≤ 14 →
    (∀ c, Homogeneous PairState (k : ℤ) c → Homogeneous PairState ((k : ℤ) + 1) (K_deg k c)) ∧
    (∀ σ : Equiv.Perm (Fin 4), ∀ c, K_deg k (actChain (σ, (1 : D8)) c) = actChain (σ, (1 : D8)) (K_deg k c)) ∧
    (∀ c, Homogeneous PairState (k : ℤ) c →
      boundary PairState 15 (K_deg k c) + (if k = 0 then 0 else K_deg (k - 1) (boundary PairState 15 c)) =
        actChain ((1 : Equiv.Perm (Fin 4)), tau0) c - c)
  | 0, _ => by
    refine ⟨fun c _ => by simp [K_deg, homogeneous_zero], fun σ c => by simp [K_deg], fun c hc => ?_⟩
    simp only [K_deg, LinearMap.zero_apply, ↓reduceIte, add_zero]
    symm
    rw [chain_expansion PairState 15 c, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [LinearMap.map_smul, ← smul_sub, actChain_basis,
      actWord_eq_of_degree_zero w (by simpa using hc w hw), sub_self, smul_zero]
  | k + 1, hk => by
    have hk' : k ≤ 13 := by omega
    obtain ⟨ih_hom, ih_s4, ih_fill⟩ := K_deg_props k (by omega)
    have hbasis_hom : ∀ w : PairWord, degree PairState w = ((k + 1 : ℕ) : ℤ) →
        Homogeneous PairState ((k + 1 : ℕ) : ℤ)
          ((actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState w) - basis PairState w) -
            K_deg k (boundary PairState 15 (basis PairState w))) := by
      intro w hw
      have hbw : Homogeneous PairState ((k : ℤ) + 1) (basis PairState w) := by
        simpa only [hw, Nat.cast_add, Nat.cast_one] using homogeneous_basis PairState 15 w
      have hbd := boundary_homogeneous 15 (basis PairState w) hbw
      have hK := ih_hom (boundary PairState 15 (basis PairState w)) hbd
      have hact := homogeneous_sub PairState
        (actChain_homogeneous ((1 : Equiv.Perm (Fin 4)), tau0) hbw) hbw
      exact homogeneous_sub PairState hact (by simpa [Nat.cast_add, Nat.cast_one] using hK)
    have hbasis_cyc : ∀ w : PairWord, degree PairState w = ((k + 1 : ℕ) : ℤ) →
        boundary PairState 15
          ((actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState w) - basis PairState w) -
            K_deg k (boundary PairState 15 (basis PairState w))) = 0 := by
      intro w hw
      have hbw : Homogeneous PairState ((k : ℤ) + 1) (basis PairState w) := by
        simpa only [hw, Nat.cast_add, Nat.cast_one] using homogeneous_basis PairState 15 w
      have hbd := boundary_homogeneous 15 (basis PairState w) hbw
      have hdd : boundary PairState 15 (boundary PairState 15 (basis PairState w)) = 0 :=
        LinearMap.congr_fun (boundary_squared PairState 15) (basis PairState w)
      have hfill := ih_fill (boundary PairState 15 (basis PairState w)) hbd
      rw [hdd, map_zero] at hfill
      simp only [ite_self, add_zero] at hfill
      rw [map_sub, map_sub, boundary_actChain, hfill]
      abel
    have h_hom : ∀ c, Homogeneous PairState (((k + 1 : ℕ) : ℤ)) c →
        Homogeneous PairState (((k + 1 : ℕ) : ℤ) + 1) (K_deg (k + 1) c) := by
      intro c hc
      apply homogeneous_map_of_basis PairState (K_deg (k + 1)) c hc
      intro w hw
      rw [K_deg_succ_basis k hk' w, if_pos hw]
      have hrep_deg : degree PairState (s4Rep w) = ((k + 1 : ℕ) : ℤ) := by
        rw [degree_s4Rep, hw]
      have hfill := fill_fifteen_colors_through_thirteen PairState refState _ (by omega)
        (hbasis_hom (s4Rep w) hrep_deg) (hbasis_cyc (s4Rep w) hrep_deg)
      exact actChain_homogeneous (s4Shift w, 1) hfill.1
    have h_s4 : ∀ σ : Equiv.Perm (Fin 4), ∀ c,
        K_deg (k + 1) (actChain (σ, (1 : D8)) c) = actChain (σ, (1 : D8)) (K_deg (k + 1) c) := by
      intro σ c
      have heq : (K_deg (k + 1)).comp (actChain (σ, (1 : D8))) =
          (actChain (σ, (1 : D8))).comp (K_deg (k + 1)) := by
        apply chainMap_ext
        intro w
        rw [LinearMap.comp_apply, LinearMap.comp_apply, actChain_basis]
        by_cases hw : degree PairState w = ((k + 1 : ℕ) : ℤ)
        · have hw' : degree PairState (actWord (σ, (1 : D8)) w) = ((k + 1 : ℕ) : ℤ) := by
            rw [degree_actWord, hw]
          have hpos : 0 < degree PairState w := by omega
          rw [K_deg_succ_basis k hk' _, K_deg_succ_basis k hk' w,
            if_pos hw', if_pos hw, s4Rep_invariant, s4Shift_act σ w hpos,
            actChain_apply_mul, Prod.mk_mul_mk, mul_one]
        · have hw' : degree PairState (actWord (σ, (1 : D8)) w) ≠ ((k + 1 : ℕ) : ℤ) := by
            rw [degree_actWord]; exact hw
          rw [K_deg_succ_basis k hk' _, K_deg_succ_basis k hk' w,
            if_neg hw', if_neg hw, map_zero]
      exact LinearMap.congr_fun heq c
    have h_fill : ∀ c, Homogeneous PairState (((k + 1 : ℕ) : ℤ)) c →
        boundary PairState 15 (K_deg (k + 1) c) + K_deg k (boundary PairState 15 c) =
          actChain ((1 : Equiv.Perm (Fin 4)), tau0) c - c := by
      intro c hc
      rw [chain_expansion PairState 15 c]
      simp only [map_sum, LinearMap.map_smul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← smul_sub]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hdeg : degree PairState w = ((k + 1 : ℕ) : ℤ) := hc w hw
      have hrep_deg : degree PairState (s4Rep w) = ((k + 1 : ℕ) : ℤ) := by
        rw [degree_s4Rep, hdeg]
      have hfill_r := (fill_fifteen_colors_through_thirteen PairState refState _ (by omega)
        (hbasis_hom (s4Rep w) hrep_deg) (hbasis_cyc (s4Rep w) hrep_deg)).2
      have hKw : K_deg (k + 1) (basis PairState w) =
          actChain (s4Shift w, (1 : D8)) (contraction PairState refState 15
            ((actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState (s4Rep w)) -
              basis PairState (s4Rep w)) -
              K_deg k (boundary PairState 15 (basis PairState (s4Rep w))))) := by
        rw [K_deg_succ_basis k hk' w, if_pos hdeg]
      have hcomm1 : actChain (s4Shift w, (1 : D8))
          (actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState (s4Rep w)) -
            basis PairState (s4Rep w)) =
          actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState w) - basis PairState w := by
        rw [map_sub]
        have hcom := LinearMap.congr_fun (actChain_s4_comm_d8 (s4Shift w) tau0)
          (basis PairState (s4Rep w))
        simp only [LinearMap.comp_apply] at hcom
        rw [hcom, actChain_basis, actChain_basis, actWord_s4Shift, actChain_basis]
      have hcomm2 : actChain (s4Shift w, (1 : D8)) (K_deg k (boundary PairState 15 (basis PairState (s4Rep w)))) =
          K_deg k (boundary PairState 15 (basis PairState w)) := by
        rw [← ih_s4 (s4Shift w), ← boundary_actChain, actChain_basis, actWord_s4Shift]
      have hstep : boundary PairState 15 (K_deg (k + 1) (basis PairState w)) +
            K_deg k (boundary PairState 15 (basis PairState w)) =
          actChain ((1 : Equiv.Perm (Fin 4)), tau0) (basis PairState w) - basis PairState w := by
        rw [hKw, boundary_actChain, hfill_r, map_sub, hcomm1, hcomm2]
        abel
      rw [← smul_add, hstep]
    refine ⟨h_hom, h_s4, ?_⟩
    intro c hc
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    exact h_fill c hc

attribute [irreducible] K_deg

def Kbar (k : ℕ) : PairChain →ₗ[ℤ] PairChain :=
  ∑ d : D8, (actChain ((1 : Equiv.Perm (Fin 4)), d)).comp
    ((K_deg k).comp (actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹)))

lemma Kbar_hom {k : ℕ} (hk : k ≤ 14) {c : PairChain} (hc : Homogeneous PairState (k : ℤ) c) :
    Homogeneous PairState ((k : ℤ) + 1) (Kbar k c) := by
  unfold Kbar
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  refine homogeneous_sum PairState Finset.univ _ fun d _ => ?_
  exact actChain_homogeneous (1, d)
    ((K_deg_props k hk).1 _ (actChain_homogeneous (1, d⁻¹) hc))

lemma Kbar_equivariant (k : ℕ) (hk : k ≤ 14) (h : PairGroup) (c : PairChain) :
    Kbar k (actChain h c) = actChain h (Kbar k c) := by
  rcases h with ⟨σ, g⟩
  unfold Kbar
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  have h1 : ∀ d : D8,
      actChain ((1 : Equiv.Perm (Fin 4)), d)
          (K_deg k (actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹) (actChain (σ, g) c))) =
        actChain (σ, g)
          (actChain ((1 : Equiv.Perm (Fin 4)), g⁻¹ * d)
            (K_deg k (actChain ((1 : Equiv.Perm (Fin 4)), (g⁻¹ * d)⁻¹) c))) := by
    intro d
    have hsplit : ((1 : Equiv.Perm (Fin 4)), d⁻¹) * (σ, g) =
        (σ, (1 : D8)) * ((1 : Equiv.Perm (Fin 4)), d⁻¹ * g) := by
      ext <;> simp
    have hsplit3 : ((1 : Equiv.Perm (Fin 4)), d) * (σ, (1 : D8)) =
        (σ, g) * ((1 : Equiv.Perm (Fin 4)), g⁻¹ * d) := by
      ext <;> simp [mul_assoc]
    rw [actChain_apply_mul, hsplit, ← actChain_apply_mul, (K_deg_props k hk).2.1 σ,
      actChain_apply_mul, hsplit3, ← actChain_apply_mul,
      show d⁻¹ * g = (g⁻¹ * d)⁻¹ by simp [mul_inv_rev]]
  rw [Finset.sum_congr rfl fun d _ => h1 d]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun d => rfl

def homSubmodule (k : ℤ) : Submodule ℤ PairChain where
  carrier := {y | Homogeneous PairState k y}
  zero_mem' := homogeneous_zero PairState 15 k
  add_mem' ha hb := homogeneous_add PairState ha hb
  smul_mem' r _ ha := homogeneous_smul PairState r ha

lemma pair_hu_prim
    (c : PairChain →ₗ[ℤ] ℤ)
    (heq_d8 : ∀ d : D8, ∀ x : PairChain,
      c (actChain ((1 : Equiv.Perm (Fin 4)), d) x) =
        (exchangeChar ((1 : Equiv.Perm (Fin 4)), d) : ℤ) * c x)
    (hcocycle : ∀ x : PairChain, Homogeneous PairState 15 x → c (boundary PairState 15 x) = 0) :
    ∀ x : PairChain, Homogeneous PairState 14 x →
      (-c.comp (Kbar 13)) (boundary PairState 15 x) = 16 * c x := by
  intro x hx
  let Hom13 := ↥(homSubmodule 13)
  let Hom14 := ↥(homSubmodule 14)
  let Hom15 := ↥(homSubmodule 15)
  let d13 : Hom14 →ₗ[ℤ] Hom13 :=
    { toFun := fun y => ⟨boundary PairState 15 y.1, boundary_homogeneous 15 y.1 y.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul _ r a.1) }
  let d14 : Hom15 →ₗ[ℤ] Hom14 :=
    { toFun := fun y => ⟨boundary PairState 15 y.1, boundary_homogeneous 15 y.1 y.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul _ r a.1) }
  let K12 : Hom13 →ₗ[ℤ] Hom14 :=
    { toFun := fun y => ⟨Kbar 13 y.1, Kbar_hom (by omega) y.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul _ r a.1) }
  let K13 : Hom14 →ₗ[ℤ] Hom15 :=
    { toFun := fun y => ⟨Kbar 14 y.1, Kbar_hom (by omega) y.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul _ r a.1) }
  let eD8 := (Fintype.equivFin D8).symm
  let g (conjIdx : Fin 8) : Hom14 →ₗ[ℤ] Hom14 :=
    let d := eD8 conjIdx
    { toFun := fun y => ⟨actChain ((1 : Equiv.Perm (Fin 4)), d * tau0 * d⁻¹) y.1,
        actChain_homogeneous _ y.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul _ r a.1) }
  let c14 : Hom14 →ₗ[ℤ] ℤ :=
    { toFun := fun y => c y.1
      map_add' := fun a b => map_add c a.1 b.1
      map_smul' := fun r a => map_smul c r a.1 }
  have hK_id : d14.comp K13 + K12.comp d13 = ∑ j : Fin 8, g j - 8 • LinearMap.id := by
    ext1 ⟨y, hy⟩
    apply Subtype.ext
    change boundary PairState 15 (Kbar 14 y) + Kbar 13 (boundary PairState 15 y) =
      (∑ j : Fin 8, actChain ((1 : Equiv.Perm (Fin 4)), eD8 j * tau0 * (eD8 j)⁻¹) y) - 8 • y
    have hsum_d8 : (∑ j : Fin 8, actChain ((1 : Equiv.Perm (Fin 4)), eD8 j * tau0 * (eD8 j)⁻¹) y) =
        ∑ d : D8, actChain ((1 : Equiv.Perm (Fin 4)), d * tau0 * d⁻¹) y :=
      Fintype.sum_equiv eD8 _ _ fun j => rfl
    rw [hsum_d8]
    unfold Kbar
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, ← Finset.sum_add_distrib]
    have hterm : ∀ d : D8,
        boundary PairState 15 (actChain ((1 : Equiv.Perm (Fin 4)), d)
          (K_deg 14 (actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹) y))) +
          actChain ((1 : Equiv.Perm (Fin 4)), d)
            (K_deg 13 (actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹) (boundary PairState 15 y))) =
        actChain ((1 : Equiv.Perm (Fin 4)), d * tau0 * d⁻¹) y - y := by
      intro d
      have hy' : Homogeneous PairState 14 (actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹) y) :=
        actChain_homogeneous _ hy
      have hfill := (K_deg_props 14 (by omega)).2.2
        (actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹) y) hy'
      simp only [Nat.reduceEqDiff, ↓reduceIte] at hfill
      rw [boundary_actChain, ← boundary_actChain ((1 : Equiv.Perm (Fin 4)), d⁻¹) y, ← map_add, hfill]
      rw [map_sub, actChain_apply_mul, actChain_apply_mul, actChain_apply_mul]
      have h1 : (((1 : Equiv.Perm (Fin 4)), d) * ((1 : Equiv.Perm (Fin 4)), tau0)) *
          ((1 : Equiv.Perm (Fin 4)), d⁻¹) = ((1 : Equiv.Perm (Fin 4)), d * tau0 * d⁻¹) := by
        ext <;> simp
      have h2 : ((1 : Equiv.Perm (Fin 4)), d) * ((1 : Equiv.Perm (Fin 4)), d⁻¹) = (1 : PairGroup) := by
        ext <;> simp
      rw [h1, h2, actChain_one, LinearMap.id_apply]
    rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, card_D8]
  have hc14 : c14.comp d14 = 0 := by
    ext ⟨y, hy⟩
    exact hcocycle y hy
  have hg14 : ∀ j : Fin 8, c14.comp (g j) = -c14 := by
    intro j
    ext ⟨y, _⟩
    change c (actChain ((1 : Equiv.Perm (Fin 4)), eD8 j * tau0 * (eD8 j)⁻¹) y) = -c y
    rw [heq_d8, exchangeChar_conj_tau0]
    simp
  have h8 := AkopyanCochain.eight_conjugates_annihilate d13 d14 K12 K13 g c14 hK_id hc14 hg14
  have hx8 := LinearMap.congr_fun h8 ⟨x, hx⟩
  simpa [c14, K12, d13] using hx8

theorem pair_cochain_sixteen_primitive
    (c : PairChain →ₗ[ℤ] ℤ)
    (heq : ∀ h : PairGroup, ∀ x : PairChain, c (actChain h x) = (exchangeChar h : ℤ) * c x)
    (hcocycle : ∀ x : PairChain, Homogeneous PairState 15 x → c (boundary PairState 15 x) = 0) :
    let u : PairChain →ₗ[ℤ] ℤ := -c.comp (Kbar 13)
    (∀ h : PairGroup, ∀ x : PairChain, u (actChain h x) = (exchangeChar h : ℤ) * u x) ∧
    (∀ x : PairChain, Homogeneous PairState 14 x →
      u (boundary PairState 15 x) = 16 * c x) ∧
    (∀ w : PairWord, DegenerateWord w → c (basis PairState w) = 0 ∧ u (basis PairState w) = 0) := by
  intro u
  have hu_eq : ∀ h : PairGroup, ∀ x : PairChain, u (actChain h x) = (exchangeChar h : ℤ) * u x := by
    intro h x
    simp only [u, LinearMap.neg_apply, LinearMap.comp_apply, Kbar_equivariant 13 (by omega) h x,
      heq h]
    ring
  have hu_prim : ∀ x : PairChain, Homogeneous PairState 14 x →
      u (boundary PairState 15 x) = 16 * c x :=
    pair_hu_prim c (fun d x => heq ((1 : Equiv.Perm (Fin 4)), d) x) hcocycle
  have hdeg0 : ∀ w : PairWord, DegenerateWord w → c (basis PairState w) = 0 ∧ u (basis PairState w) = 0 := by
    intro w hw
    obtain ⟨d, hneg, hact⟩ := exists_fixing_exchange_of_degenerate w hw
    have hc0 : c (basis PairState w) = 0 := by
      have h1 := heq ((1 : Equiv.Perm (Fin 4)), d) (basis PairState w)
      rw [actChain_basis, hact, hneg] at h1
      change c (basis PairState w) = (-1 : ℤ) * c (basis PairState w) at h1
      omega
    have hu0 : u (basis PairState w) = 0 := by
      have h1 := hu_eq ((1 : Equiv.Perm (Fin 4)), d) (basis PairState w)
      rw [actChain_basis, hact, hneg] at h1
      change u (basis PairState w) = (-1 : ℤ) * u (basis PairState w) at h1
      omega
    exact ⟨hc0, hu0⟩
  exact ⟨hu_eq, hu_prim, hdeg0⟩

theorem pair_cochain_sixteen_primitive_P_pair
    (c : PairChain →ₗ[ℤ] ℤ)
    (heq : ∀ h ∈ P_pair, ∀ x : PairChain, c (actChain h x) = (exchangeChar h : ℤ) * c x)
    (hcocycle : ∀ x : PairChain, Homogeneous PairState 15 x → c (boundary PairState 15 x) = 0) :
    let u : PairChain →ₗ[ℤ] ℤ := -c.comp (Kbar 13)
    (∀ h ∈ P_pair, ∀ x : PairChain, u (actChain h x) = (exchangeChar h : ℤ) * u x) ∧
    (∀ x : PairChain, Homogeneous PairState 14 x →
      u (boundary PairState 15 x) = 16 * c x) ∧
    (∀ w : PairWord, DegenerateWord w → c (basis PairState w) = 0 ∧ u (basis PairState w) = 0) := by
  intro u
  have hd8_in : ∀ d : D8, ((1 : Equiv.Perm (Fin 4)), d) ∈ P_pair := fun _ _ _ => Iff.rfl
  have hu_eq : ∀ h ∈ P_pair, ∀ x : PairChain, u (actChain h x) = (exchangeChar h : ℤ) * u x := by
    intro h hh x
    simp only [u, LinearMap.neg_apply, LinearMap.comp_apply, Kbar_equivariant 13 (by omega) h x,
      heq h hh]
    ring
  have hu_prim : ∀ x : PairChain, Homogeneous PairState 14 x →
      u (boundary PairState 15 x) = 16 * c x :=
    pair_hu_prim c (fun d x => heq _ (hd8_in d) x) hcocycle
  have hdeg0 : ∀ w : PairWord, DegenerateWord w → c (basis PairState w) = 0 ∧ u (basis PairState w) = 0 := by
    intro w hw
    obtain ⟨d, hneg, hact⟩ := exists_fixing_exchange_of_degenerate w hw
    have hc0 : c (basis PairState w) = 0 := by
      have h1 := heq _ (hd8_in d) (basis PairState w)
      rw [actChain_basis, hact, hneg] at h1
      change c (basis PairState w) = (-1 : ℤ) * c (basis PairState w) at h1
      omega
    have hu0 : u (basis PairState w) = 0 := by
      have h1 := hu_eq _ (hd8_in d) (basis PairState w)
      rw [actChain_basis, hact, hneg] at h1
      change u (basis PairState w) = (-1 : ℤ) * u (basis PairState w) at h1
      omega
    exact ⟨hc0, hu0⟩
  exact ⟨hu_eq, hu_prim, hdeg0⟩

end ChainAnnihilator

end AkopyanResearch
