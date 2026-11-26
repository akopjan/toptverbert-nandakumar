module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import AkopyanResearch.PlanarTestGlobal
public import AkopyanResearch.MarksArithmetic

@[expose] public section

/-!
# Row Sylow-2 geometry, complex structure, orbit-count degrees, and S¹ null-homotopy

For the row Sylow 2-subgroup `P_row = Sylow₂(S₄) × C₂ ≤ Perm (Fin 6)`:
1. Explicit subgroup `P_row` of cardinality `16`, preserving `anchor10` / `anchorS`.
2. Orthogonal complex structure `J10` on `Rep10` commuting with all of `Perm (Fin 6)` and
   satisfying `J10 anchor10 = cA {4, 5}`, inducing a central `Circle`-action `smulCircle`.
3. Every fixed subspace `fixedSubspace K` (`K ≤ P_row`) is `J10`-invariant, hence even-dimensional,
   with `finrank ℝ (fixedSubspace P_row) = 2` and explicit basepoint phase-correction of any
   `P_row`-equivariant homotopy between `anchorS`-based maps.
4. Exact orbit-count formulas connecting `K`-fixed caps of sizes `1, 2, 3` to
   `PlanarMarksArithmetic.bubbleDegree` (`d_K ∈ {0, -2}`, `d_K ^ 7 = 64 * d_K`).
5. Explicit `S¹` null-homotopy of `q0` restricted to `S(V^{P_row})` relative to `anchorS`.
-/

noncomputable section

open scoped BigOperators InnerProductSpace Classical
open Metric

namespace AkopyanResearch

/-! ### 1. The row Sylow-2 subgroup `P_row` of `Perm (Fin 6)` -/

section RowSylow

def isRowSylow (g : Equiv.Perm (Fin 6)) : Prop :=
  (∀ i : Fin 6, i.1 < 4 → (g i).1 < 4) ∧
  (∀ i j : Fin 6, i.1 < 4 → j.1 < 4 → (i.1 % 2 = j.1 % 2 ↔ (g i).1 % 2 = (g j).1 % 2))

instance instDecidablePredIsRowSylow : DecidablePred isRowSylow :=
  fun _ => inferInstanceAs (Decidable ((∀ i : Fin 6, i.1 < 4 → _) ∧ _))

lemma isRowSylow_preserves_top4 {g : Equiv.Perm (Fin 6)}
    (hg : ∀ i : Fin 6, i.1 < 4 → (g i).1 < 4) (i : Fin 6) :
    i.1 < 4 ↔ (g i).1 < 4 := by
  let S4 : Finset (Fin 6) := Finset.univ.filter (fun j => j.1 < 4)
  have hmap : S4.map g.toEmbedding ⊆ S4 := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
    simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hg j hj
  have heq : S4.map g.toEmbedding = S4 := Finset.eq_of_subset_of_card_le hmap (by simp)
  have hmem : i ∈ S4 ↔ g i ∈ S4 := by
    constructor
    · intro hi; rw [← heq]; exact Finset.mem_map_of_mem _ hi
    · intro hgi; rw [← heq] at hgi
      obtain ⟨j, hj, hgj⟩ := Finset.mem_map.mp hgi
      have : j = i := g.injective hgj
      rwa [← this]
  simpa [S4] using hmem

def P_row : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {g | isRowSylow g}
  one_mem' := ⟨fun _ h => h, fun _ _ _ _ => Iff.rfl⟩
  mul_mem' {a b} ha hb := by
    refine ⟨fun i hi => ha.1 (b i) (hb.1 i hi), fun i j hi hj => ?_⟩
    exact (hb.2 i j hi hj).trans (ha.2 (b i) (b j) (hb.1 i hi) (hb.1 j hj))
  inv_mem' {g} hg := by
    have hlt : ∀ i : Fin 6, i.1 < 4 → (g⁻¹ i).1 < 4 := fun i hi => by
      have hi' : (g (g⁻¹ i)).1 < 4 := by simpa using hi
      exact (isRowSylow_preserves_top4 hg.1 (g⁻¹ i)).mpr hi'
    refine ⟨hlt, fun i j hi hj => ?_⟩
    have hgi : (g⁻¹ i).1 < 4 := hlt i hi
    have hgj : (g⁻¹ j).1 < 4 := hlt j hj
    symm
    simpa using hg.2 (g⁻¹ i) (g⁻¹ j) hgi hgj

lemma mem_P_row_iff (g : Equiv.Perm (Fin 6)) : g ∈ P_row ↔ isRowSylow g := Iff.rfl

instance instDecidablePredMemP_row : DecidablePred (· ∈ P_row) :=
  fun g => instDecidablePredIsRowSylow g

lemma perm10_anchor10_of_mem_P_row {g : Equiv.Perm (Fin 6)} (hg : g ∈ P_row) :
    perm10 g anchor10 = anchor10 :=
  perm10_anchor10 hg.1

lemma permSphere_anchorS_of_mem_P_row {g : Equiv.Perm (Fin 6)} (hg : g ∈ P_row) :
    permSphere g anchorS = anchorS :=
  permSphere_anchorS hg.1

lemma P_row_preserves_ge4 {g : Equiv.Perm (Fin 6)} (hg : g ∈ P_row) {i : Fin 6} (hi : 4 ≤ i.1) :
    4 ≤ (g i).1 := by
  by_contra hlt
  have hi4 : i.1 < 4 := (isRowSylow_preserves_top4 hg.1 i).mpr (Nat.lt_of_not_le hlt)
  omega

def decodeP_row (b : Bool × Bool × Bool × Bool) : Fin 6 → Fin 6 := fun i =>
  match i.1 with
  | 0 => if b.1 then (if b.2.2.1 then 3 else 1) else (if b.2.1 then 2 else 0)
  | 1 => if b.1 then (if b.2.1 then 2 else 0) else (if b.2.2.1 then 3 else 1)
  | 2 => if b.1 then (if b.2.2.1 then 1 else 3) else (if b.2.1 then 0 else 2)
  | 3 => if b.1 then (if b.2.1 then 0 else 2) else (if b.2.2.1 then 1 else 3)
  | 4 => if b.2.2.2 then 5 else 4
  | _ => if b.2.2.2 then 4 else 5

lemma decodeP_row_inj (b : Bool × Bool × Bool × Bool) :
    Function.Injective (decodeP_row b) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    rcases b with ⟨b0, b1, b2, b3⟩ <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp_all [decodeP_row]

def permOfBool4 (b : Bool × Bool × Bool × Bool) : P_row :=
  ⟨Equiv.ofBijective (decodeP_row b)
      ((Finite.injective_iff_bijective).mp (decodeP_row_inj b)), by
    rcases b with ⟨b0, b1, b2, b3⟩
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      exact ⟨fun i hi => by fin_cases i <;> simp [decodeP_row] at hi ⊢,
        fun i j hi hj => by fin_cases i <;> fin_cases j <;> simp [decodeP_row] at hi hj ⊢⟩⟩

@[simp] lemma permOfBool4_apply (b : Bool × Bool × Bool × Bool) (i : Fin 6) :
    (permOfBool4 b).1 i = decodeP_row b i := rfl

def encodeP_row (g : P_row) : Bool × Bool × Bool × Bool :=
  (decide ((g.1 0).1 % 2 = 1),
   decide (if (g.1 0).1 % 2 = 1 then 2 ≤ (g.1 1).1 else 2 ≤ (g.1 0).1),
   decide (if (g.1 0).1 % 2 = 1 then 2 ≤ (g.1 0).1 else 2 ≤ (g.1 1).1),
   decide (g.1 4 = 5))

lemma encode_permOfBool4 (b : Bool × Bool × Bool × Bool) :
    encodeP_row (permOfBool4 b) = b := by
  rcases b with ⟨b0, b1, b2, b3⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

lemma decode_encodeP_row (g : P_row) : permOfBool4 (encodeP_row g) = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change decodeP_row (encodeP_row g) i = g.1 i
  have hg := g.2
  have h0lt : (g.1 0).1 < 4 := hg.1 0 (by decide)
  have h1lt : (g.1 1).1 < 4 := hg.1 1 (by decide)
  have h2lt : (g.1 2).1 < 4 := hg.1 2 (by decide)
  have h3lt : (g.1 3).1 < 4 := hg.1 3 (by decide)
  have h4ge : 4 ≤ (g.1 4).1 := P_row_preserves_ge4 hg (by decide)
  have h5ge : 4 ≤ (g.1 5).1 := P_row_preserves_ge4 hg (by decide)
  have hp02 : (g.1 0).1 % 2 = (g.1 2).1 % 2 := (hg.2 0 2 (by decide) (by decide)).mp rfl
  have hp13 : (g.1 1).1 % 2 = (g.1 3).1 % 2 := (hg.2 1 3 (by decide) (by decide)).mp rfl
  have hp01 : (g.1 0).1 % 2 ≠ (g.1 1).1 % 2 := by
    intro h
    have := (hg.2 0 1 (by decide) (by decide)).mpr h
    norm_num at this
  have h02 : g.1 0 ≠ g.1 2 := g.1.injective.ne (by decide)
  have h13 : g.1 1 ≠ g.1 3 := g.1.injective.ne (by decide)
  have h45 : g.1 4 ≠ g.1 5 := g.1.injective.ne (by decide)
  rcases g with ⟨g', hg'⟩
  dsimp [encodeP_row, decodeP_row] at *
  fin_cases i
  · change (if decide ((g' 0).1 % 2 = 1) then
        if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 0).1 else 2 ≤ (g' 1).1) then 3 else 1
      else if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 1).1 else 2 ≤ (g' 0).1) then 2 else 0) = g' 0
    have ha : (g' 0).1 = 0 ∨ (g' 0).1 = 1 ∨ (g' 0).1 = 2 ∨ (g' 0).1 = 3 := by omega
    rcases ha with h | h | h | h <;> exact Fin.ext (by simp [h])
  · change (if decide ((g' 0).1 % 2 = 1) then
        if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 1).1 else 2 ≤ (g' 0).1) then 2 else 0
      else if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 0).1 else 2 ≤ (g' 1).1) then 3 else 1) = g' 1
    have ha : (g' 0).1 % 2 = 0 ∨ (g' 0).1 % 2 = 1 := by omega
    rcases ha with h | h
    · have hb : (g' 1).1 = 1 ∨ (g' 1).1 = 3 := by omega
      rcases hb with hb | hb <;> exact Fin.ext (by simp [h, hb])
    · have hb : (g' 1).1 = 0 ∨ (g' 1).1 = 2 := by omega
      rcases hb with hb | hb <;> exact Fin.ext (by simp [h, hb])
  · change (if decide ((g' 0).1 % 2 = 1) then
        if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 0).1 else 2 ≤ (g' 1).1) then 1 else 3
      else if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 1).1 else 2 ≤ (g' 0).1) then 0 else 2) = g' 2
    have h02' : (g' 0).1 ≠ (g' 2).1 := Fin.val_injective.ne h02
    have ha : (g' 0).1 = 0 ∨ (g' 0).1 = 1 ∨ (g' 0).1 = 2 ∨ (g' 0).1 = 3 := by omega
    rcases ha with h | h | h | h
    · have hc : (g' 2).1 = 2 := by omega
      exact Fin.ext (by simp [h, hc])
    · have hc : (g' 2).1 = 3 := by omega
      exact Fin.ext (by simp [h, hc])
    · have hc : (g' 2).1 = 0 := by omega
      exact Fin.ext (by simp [h, hc])
    · have hc : (g' 2).1 = 1 := by omega
      exact Fin.ext (by simp [h, hc])
  · change (if decide ((g' 0).1 % 2 = 1) then
        if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 1).1 else 2 ≤ (g' 0).1) then 0 else 2
      else if decide (if (g' 0).1 % 2 = 1 then 2 ≤ (g' 0).1 else 2 ≤ (g' 1).1) then 1 else 3) = g' 3
    have h13' : (g' 1).1 ≠ (g' 3).1 := Fin.val_injective.ne h13
    have ha : (g' 0).1 % 2 = 0 ∨ (g' 0).1 % 2 = 1 := by omega
    rcases ha with h | h
    · have hb : (g' 1).1 = 1 ∨ (g' 1).1 = 3 := by omega
      rcases hb with hb | hb
      · have hc : (g' 3).1 = 3 := by omega
        exact Fin.ext (by simp [h, hb, hc])
      · have hc : (g' 3).1 = 1 := by omega
        exact Fin.ext (by simp [h, hb, hc])
    · have hb : (g' 1).1 = 0 ∨ (g' 1).1 = 2 := by omega
      rcases hb with hb | hb
      · have hc : (g' 3).1 = 2 := by omega
        exact Fin.ext (by simp [h, hb, hc])
      · have hc : (g' 3).1 = 0 := by omega
        exact Fin.ext (by simp [h, hb, hc])
  · change (if decide (g' 4 = 5) then (5 : Fin 6) else 4) = g' 4
    have ha : (g' 4).1 = 4 ∨ (g' 4).1 = 5 := by have := (g' 4).isLt; omega
    rcases ha with h | h <;> exact Fin.ext (by simp [Fin.ext_iff, h])
  · change (if decide (g' 4 = 5) then (4 : Fin 6) else 5) = g' 5
    have h45' : (g' 4).1 ≠ (g' 5).1 := Fin.val_injective.ne h45
    have ha : (g' 4).1 = 4 ∨ (g' 4).1 = 5 := by have := (g' 4).isLt; omega
    rcases ha with h | h
    · have hc : (g' 5).1 = 5 := by have := (g' 5).isLt; omega
      exact Fin.ext (by simp [Fin.ext_iff, h, hc])
    · have hc : (g' 5).1 = 4 := by have := (g' 5).isLt; omega
      exact Fin.ext (by simp [Fin.ext_iff, h, hc])

def equivP_rowBool4 : P_row ≃ Bool × Bool × Bool × Bool where
  toFun := encodeP_row
  invFun := permOfBool4
  left_inv := decode_encodeP_row
  right_inv := encode_permOfBool4

theorem card_P_row : Fintype.card P_row = 16 := by
  rw [Fintype.card_congr equivP_rowBool4]
  decide

end RowSylow

/-! ### 2. Complex structure `J10` and central `Circle`-action on `Rep10` -/

section ComplexStructure

lemma natAdd_six_eq_addNat (j : Fin 6) : Fin.natAdd 6 j = j.addNat 6 :=
  Fin.ext (by simp)

def swapJVec (x : EuclideanSpace ℝ (Fin 12)) : EuclideanSpace ℝ (Fin 12) :=
  (WithLp.equiv 2 (Fin 12 → ℝ)).symm
    (splitPair6 (fun j => -x (Fin.natAdd 6 j)) (fun j => x (j.castAdd 6)))

@[simp] lemma swapJVec_castAdd (x : EuclideanSpace ℝ (Fin 12)) (j : Fin 6) :
    swapJVec x (j.castAdd 6) = -x (Fin.natAdd 6 j) := by
  change splitPair6 (fun j => -x (Fin.natAdd 6 j)) (fun j => x (j.castAdd 6)) (j.castAdd 6) =
    -x (Fin.natAdd 6 j)
  exact splitPair6_castAdd _ _ j

@[simp] lemma swapJVec_natAdd (x : EuclideanSpace ℝ (Fin 12)) (j : Fin 6) :
    swapJVec x (Fin.natAdd 6 j) = x (j.castAdd 6) := by
  change splitPair6 (fun j => -x (Fin.natAdd 6 j)) (fun j => x (j.castAdd 6)) (Fin.natAdd 6 j) =
    x (j.castAdd 6)
  exact splitPair6_natAdd _ _ j

@[simp] lemma swapJVec_addNat (x : EuclideanSpace ℝ (Fin 12)) (j : Fin 6) :
    swapJVec x (j.addNat 6) = x (j.castAdd 6) := by
  rw [← natAdd_six_eq_addNat, swapJVec_natAdd]

lemma swapJVec_mem_V10Sub {x : EuclideanSpace ℝ (Fin 12)} (hx : x ∈ V10Sub) :
    swapJVec x ∈ V10Sub := by
  rw [mem_V10Sub_iff] at hx ⊢
  constructor
  · simp only [swapJVec_castAdd, Finset.sum_neg_distrib, hx.2, neg_zero]
  · simp only [swapJVec_natAdd, hx.1]

lemma norm_swapJVec (x : EuclideanSpace ℝ (Fin 12)) : ‖swapJVec x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ i : Fin (6 + 6), ‖swapJVec x i‖ ^ 2) = ∑ i : Fin (6 + 6), ‖x i‖ ^ 2
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hL : (∑ j : Fin 6, ‖swapJVec x (j.castAdd 6)‖ ^ 2) =
      ∑ j : Fin 6, ‖x (Fin.natAdd 6 j)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [swapJVec_castAdd, norm_neg]
  have hR : (∑ j : Fin 6, ‖swapJVec x (Fin.natAdd 6 j)‖ ^ 2) =
      ∑ j : Fin 6, ‖x (j.castAdd 6)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [swapJVec_natAdd]
  rw [hL, hR, add_comm]

lemma swapJVec_swapJVec (x : EuclideanSpace ℝ (Fin 12)) : swapJVec (swapJVec x) = -x := by
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij, swapJVec_castAdd, swapJVec_natAdd]; rfl
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij, swapJVec_natAdd, swapJVec_castAdd]; rfl

lemma swapJVec_add (x y : EuclideanSpace ℝ (Fin 12)) :
    swapJVec (x + y) = swapJVec x + swapJVec y := by
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]; simp only [PiLp.add_apply, swapJVec_castAdd]; ring
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]; simp only [PiLp.add_apply, swapJVec_natAdd]

lemma swapJVec_smul (r : ℝ) (x : EuclideanSpace ℝ (Fin 12)) :
    swapJVec (r • x) = r • swapJVec x := by
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]; simp only [PiLp.smul_apply, smul_eq_mul, swapJVec_castAdd]; ring
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]; simp only [PiLp.smul_apply, smul_eq_mul, swapJVec_natAdd]

def JSub : ↥V10Sub ≃ₗᵢ[ℝ] ↥V10Sub where
  toFun x := ⟨swapJVec x.1, swapJVec_mem_V10Sub x.2⟩
  invFun x := ⟨-swapJVec x.1, V10Sub.neg_mem (swapJVec_mem_V10Sub x.2)⟩
  left_inv x := by apply Subtype.ext; change -swapJVec (swapJVec x.1) = x.1; rw [swapJVec_swapJVec, neg_neg]
  right_inv x := by
    apply Subtype.ext
    change swapJVec (-swapJVec x.1) = x.1
    rw [← neg_one_smul ℝ, swapJVec_smul, swapJVec_swapJVec, neg_one_smul, neg_neg]
  map_add' x y := by apply Subtype.ext; exact swapJVec_add x.1 y.1
  map_smul' r x := by apply Subtype.ext; exact swapJVec_smul r x.1
  norm_map' x := norm_swapJVec x.1

@[simp] lemma JSub_val (v : ↥V10Sub) : (JSub v).1 = swapJVec v.1 := rfl

def J10 : Rep10 ≃ₗᵢ[ℝ] Rep10 :=
  iso10.symm.trans (JSub.trans iso10)

lemma J10_J10 (x : Rep10) : J10 (J10 x) = -x := by
  rw [J10]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  have hsub : JSub (JSub (iso10.symm x)) = -(iso10.symm x) := by
    apply Subtype.ext; exact swapJVec_swapJVec _
  rw [hsub, map_neg, LinearIsometryEquiv.apply_symm_apply]

lemma inner_self_J10 (x : Rep10) : ⟪x, J10 x⟫_ℝ = 0 := by
  have hsym : ⟪x, J10 x⟫_ℝ = ⟪J10 x, J10 (J10 x)⟫_ℝ := (J10.inner_map_map x (J10 x)).symm
  rw [J10_J10, inner_neg_right, real_inner_comm (J10 x) x] at hsym
  rw [real_inner_comm]
  linarith

lemma inner_J10_left (x y : Rep10) : ⟪J10 x, y⟫_ℝ = -⟪x, J10 y⟫_ℝ := by
  have h2 := J10.inner_map_map x (J10 y)
  rw [J10_J10, inner_neg_right] at h2
  linarith

lemma perm10_J10 (g : Equiv.Perm (Fin 6)) (x : Rep10) :
    perm10 g (J10 x) = J10 (perm10 g x) := by
  rw [perm10, J10]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]
    change (swapJVec (iso10.symm x).1) ((perm12 g).symm (j.castAdd 6)) =
      swapJVec ((permSub g (iso10.symm x)).1) (j.castAdd 6)
    rw [perm12_symm, perm12_castAdd, swapJVec_castAdd, swapJVec_castAdd]
    change -((iso10.symm x).1 (Fin.natAdd 6 (g⁻¹ j))) =
      -((iso10.symm x).1 ((perm12 g).symm (Fin.natAdd 6 j)))
    rw [perm12_symm, perm12_natAdd]
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]
    change (swapJVec (iso10.symm x).1) ((perm12 g).symm (Fin.natAdd 6 j)) =
      swapJVec ((permSub g (iso10.symm x)).1) (Fin.natAdd 6 j)
    rw [perm12_symm, perm12_natAdd, swapJVec_natAdd, swapJVec_natAdd]
    change (iso10.symm x).1 ((g⁻¹ j).castAdd 6) = (iso10.symm x).1 ((perm12 g).symm (j.castAdd 6))
    rw [perm12_symm, perm12_castAdd]

def cap45 : InvariantCaps.CapLabel := ⟨{4, 5}, by decide⟩

lemma cA_cap45_norm_contrast : ‖contrastVec6 cap45‖ = Real.sqrt 12 / 3 := by
  have hpos : 0 ≤ ‖contrastVec6 cap45‖ := norm_nonneg _
  rw [← sq_eq_sq₀ hpos (by positivity), EuclideanSpace.norm_sq_eq]
  have hval : ∀ i : Fin 6, ‖contrastVec6 cap45 i‖ ^ 2 =
      if i.1 < 4 then (1 : ℝ) / 9 else 4 / 9 := fun i => by
    fin_cases i <;> simp [cap45, contrastVec6, InvariantCaps.contrast, WithLp.equiv_symm_apply] <;>
      norm_num
  simp only [Fin.sum_univ_six, hval,
    show ((0 : Fin 6) : ℕ) = 0 from rfl, show ((1 : Fin 6) : ℕ) = 1 from rfl,
    show ((2 : Fin 6) : ℕ) = 2 from rfl, show ((3 : Fin 6) : ℕ) = 3 from rfl,
    show ((4 : Fin 6) : ℕ) = 4 from rfl, show ((5 : Fin 6) : ℕ) = 5 from rfl]
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem J10_anchor10 : J10 anchor10 = cA cap45 := by
  rw [J10, anchor10, cA]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  ext i
  have hval : ∀ j : Fin 6, -anchorVec6 j = ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 j := by
    intro j
    rw [cA_cap45_norm_contrast]
    have hs : Real.sqrt 12 ≠ 0 := by positivity
    fin_cases j <;> simp [anchorVec6, contrastVec6, InvariantCaps.contrast, cap45, WithLp.equiv_symm_apply] <;>
      field_simp <;> ring
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    have hA : anchorSub.1 (Fin.natAdd 6 j) = anchorVec6 j := by
      change splitPair6 (fun _ => 0) anchorVec6 (Fin.natAdd 6 j) = anchorVec6 j
      exact splitPair6_natAdd _ _ j
    have hC : (cASub cap45).1 (j.castAdd 6) = ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 j := by
      change splitPair6 (fun k => ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 k) (fun _ => 0)
        (j.castAdd 6) = _
      exact splitPair6_castAdd _ _ j
    rw [hij, JSub_val, swapJVec_castAdd, hA, hC]
    exact hval j
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    have hA : anchorSub.1 (j.castAdd 6) = 0 := by
      change splitPair6 (fun _ => 0) anchorVec6 (j.castAdd 6) = 0
      exact splitPair6_castAdd _ _ j
    have hC : (cASub cap45).1 (Fin.natAdd 6 j) = 0 := by
      change splitPair6 (fun k => ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 k) (fun _ => 0)
        (Fin.natAdd 6 j) = 0
      exact splitPair6_natAdd _ _ j
    rw [hij, JSub_val, swapJVec_natAdd, hA, hC]

abbrev cA0 : Rep10 := cA cap45

lemma norm_cA0 : ‖cA0‖ = 1 := norm_cA cap45
lemma inner_cA0_anchor10 : ⟪cA0, anchor10⟫_ℝ = 0 := inner_cA_anchor10 cap45
@[simp] lemma inner_anchor10_cA0 : ⟪anchor10, cA0⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact inner_cA0_anchor10
lemma J10_cA0 : J10 cA0 = -anchor10 := by
  rw [cA0, ← J10_anchor10, J10_J10]

def smulCircleFun (z : Circle) (x : Rep10) : Rep10 :=
  (z : ℂ).re • x + (z : ℂ).im • J10 x

lemma norm_smulCircleFun (z : Circle) (x : Rep10) : ‖smulCircleFun z x‖ = ‖x‖ := by
  have hre : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  rw [smulCircleFun, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_add_sq_real,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, J10.norm_map,
    inner_smul_left, inner_smul_right, inner_self_J10, mul_pow, mul_pow, sq_abs, sq_abs]
  simp only [starRingEnd_apply, star_trivial, mul_zero, add_zero]
  nlinarith [sq_nonneg ‖x‖]

def smulCircle (z : Circle) : Rep10 ≃ₗᵢ[ℝ] Rep10 where
  toFun := smulCircleFun z
  invFun := smulCircleFun z⁻¹
  left_inv x := by
    have hre : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
    have hinv_re : ((z⁻¹ : Circle) : ℂ).re = (z : ℂ).re := by simp
    have hinv_im : ((z⁻¹ : Circle) : ℂ).im = -(z : ℂ).im := by simp
    dsimp only [smulCircleFun]
    rw [hinv_re, hinv_im]
    simp only [map_add, map_smul, J10_J10]
    calc
      (z : ℂ).re • ((z : ℂ).re • x + (z : ℂ).im • J10 x) +
          (-(z : ℂ).im) • ((z : ℂ).re • J10 x + (z : ℂ).im • (-x))
          = ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) • x := by module
      _ = x := by rw [hre, one_smul]
  right_inv x := by
    have hre : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
    have hinv_re : ((z⁻¹ : Circle) : ℂ).re = (z : ℂ).re := by simp
    have hinv_im : ((z⁻¹ : Circle) : ℂ).im = -(z : ℂ).im := by simp
    dsimp only [smulCircleFun]
    rw [hinv_re, hinv_im]
    simp only [map_add, map_smul, J10_J10]
    calc
      (z : ℂ).re • ((z : ℂ).re • x + (-(z : ℂ).im) • J10 x) +
          (z : ℂ).im • ((z : ℂ).re • J10 x + (-(z : ℂ).im) • (-x))
          = ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2) • x := by module
      _ = x := by rw [hre, one_smul]
  map_add' x y := by simp only [smulCircleFun, map_add, smul_add]; module
  map_smul' r x := by simp only [smulCircleFun, map_smul, RingHom.id_apply]; module
  norm_map' x := norm_smulCircleFun z x

@[simp] lemma smulCircle_apply (z : Circle) (x : Rep10) :
    smulCircle z x = (z : ℂ).re • x + (z : ℂ).im • J10 x := rfl

lemma smulCircle_one (x : Rep10) : smulCircle 1 x = x := by simp

lemma smulCircle_mul (z w : Circle) (x : Rep10) :
    smulCircle (z * w) x = smulCircle z (smulCircle w x) := by
  simp only [smulCircle_apply, map_add, map_smul, J10_J10]
  have hre : ((z * w : Circle) : ℂ).re = (z : ℂ).re * (w : ℂ).re - (z : ℂ).im * (w : ℂ).im := by
    simp [Complex.mul_re]
  have him : ((z * w : Circle) : ℂ).im = (z : ℂ).re * (w : ℂ).im + (z : ℂ).im * (w : ℂ).re := by
    simp [Complex.mul_im]
  rw [hre, him]
  module

lemma smulCircle_inv (z : Circle) (x : Rep10) :
    smulCircle z⁻¹ x = (z : ℂ).re • x - (z : ℂ).im • J10 x := by
  have hre : ((z⁻¹ : Circle) : ℂ).re = (z : ℂ).re := by simp
  have him : ((z⁻¹ : Circle) : ℂ).im = -(z : ℂ).im := by simp
  simp only [smulCircle_apply, hre, him, neg_smul, sub_eq_add_neg]

lemma perm10_smulCircle (g : Equiv.Perm (Fin 6)) (z : Circle) (x : Rep10) :
    perm10 g (smulCircle z x) = smulCircle z (perm10 g x) := by
  simp [smulCircle_apply, map_add, map_smul, perm10_J10]

lemma continuous_smulCircle :
    Continuous (fun p : Circle × Rep10 => smulCircle p.1 p.2) := by
  have hre : Continuous (fun p : Circle × Rep10 => (p.1 : ℂ).re) :=
    Complex.continuous_re.comp (continuous_subtype_val.comp continuous_fst)
  have him : Continuous (fun p : Circle × Rep10 => (p.1 : ℂ).im) :=
    Complex.continuous_im.comp (continuous_subtype_val.comp continuous_fst)
  have hfun : (fun p : Circle × Rep10 => smulCircle p.1 p.2) =
      fun p => (p.1 : ℂ).re • p.2 + (p.1 : ℂ).im • J10 p.2 := funext fun p => rfl
  rw [hfun]
  exact (hre.smul continuous_snd).add (him.smul (J10.continuous.comp continuous_snd))

def smulCircleSphere (z : Circle) (x : Metric.sphere (0 : Rep10) 1) :
    Metric.sphere (0 : Rep10) 1 :=
  ⟨smulCircle z x.1, by
    rw [mem_sphere_zero_iff_norm, (smulCircle z).norm_map]
    exact mem_sphere_zero_iff_norm.mp x.2⟩

@[simp] lemma smulCircleSphere_val (z : Circle) (x : Metric.sphere (0 : Rep10) 1) :
    (smulCircleSphere z x : Rep10) = smulCircle z x.1 := rfl

lemma smulCircleSphere_one (x : Metric.sphere (0 : Rep10) 1) : smulCircleSphere 1 x = x := by
  apply Subtype.ext; exact smulCircle_one x.1

lemma smulCircleSphere_mul (z w : Circle) (x : Metric.sphere (0 : Rep10) 1) :
    smulCircleSphere (z * w) x = smulCircleSphere z (smulCircleSphere w x) := by
  apply Subtype.ext; exact smulCircle_mul z w x.1

lemma permSphere_smulCircleSphere (g : Equiv.Perm (Fin 6)) (z : Circle)
    (x : Metric.sphere (0 : Rep10) 1) :
    permSphere g (smulCircleSphere z x) = smulCircleSphere z (permSphere g x) := by
  apply Subtype.ext; exact perm10_smulCircle g z x.1

lemma continuous_smulCircleSphere :
    Continuous (fun p : Circle × Metric.sphere (0 : Rep10) 1 => smulCircleSphere p.1 p.2) := by
  rw [continuous_induced_rng]
  exact continuous_smulCircle.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

end ComplexStructure

/-! ### 3. Fixed subspaces and basepoint phase correction -/

section FixedSpaces

def fixedSubspace (K : Subgroup (Equiv.Perm (Fin 6))) : Submodule ℝ Rep10 where
  carrier := {x : Rep10 | ∀ g ∈ K, perm10 g x = x}
  zero_mem' _ _ := map_zero _
  add_mem' hx hy g hg := by rw [map_add, hx g hg, hy g hg]
  smul_mem' r _ hx g hg := by rw [map_smul, hx g hg]

lemma mem_fixedSubspace_iff (K : Subgroup (Equiv.Perm (Fin 6))) (x : Rep10) :
    x ∈ fixedSubspace K ↔ ∀ g ∈ K, perm10 g x = x := Iff.rfl

lemma J10_mem_fixedSubspace {K : Subgroup (Equiv.Perm (Fin 6))} {x : Rep10}
    (hx : x ∈ fixedSubspace K) : J10 x ∈ fixedSubspace K := by
  intro g hg
  rw [perm10_J10, hx g hg]

lemma fixedSubspace_mono {K L : Subgroup (Equiv.Perm (Fin 6))} (hKL : K ≤ L) :
    fixedSubspace L ≤ fixedSubspace K := fun _ hx g hg => hx g (hKL hg)

lemma anchor10_mem_fixedSubspace_of_le_P_row {K : Subgroup (Equiv.Perm (Fin 6))}
    (hK : K ≤ P_row) : anchor10 ∈ fixedSubspace K := fun _ hg =>
  perm10_anchor10_of_mem_P_row (hK hg)

lemma cA0_mem_fixedSubspace_of_le_P_row {K : Subgroup (Equiv.Perm (Fin 6))}
    (hK : K ≤ P_row) : cA0 ∈ fixedSubspace K := by
  rw [cA0, ← J10_anchor10]
  exact J10_mem_fixedSubspace (anchor10_mem_fixedSubspace_of_le_P_row hK)

lemma permSub_eq_self_iff (g : Equiv.Perm (Fin 6)) (v : ↥V10Sub) :
    permSub g v = v ↔ (∀ i : Fin 6, v.1 ((g⁻¹ i).castAdd 6) = v.1 (i.castAdd 6)) ∧
      (∀ i : Fin 6, v.1 (Fin.natAdd 6 (g⁻¹ i)) = v.1 (Fin.natAdd 6 i)) := by
  constructor
  · intro h
    constructor <;> intro i
    · have h0 := congrArg (fun u : ↥V10Sub => u.1 (i.castAdd 6)) h
      change v.1 ((perm12 g).symm (i.castAdd 6)) = v.1 (i.castAdd 6) at h0
      rwa [perm12_symm, perm12_castAdd] at h0
    · have h0 := congrArg (fun u : ↥V10Sub => u.1 (Fin.natAdd 6 i)) h
      change v.1 ((perm12 g).symm (Fin.natAdd 6 i)) = v.1 (Fin.natAdd 6 i) at h0
      rwa [perm12_symm, perm12_natAdd] at h0
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    ext j
    rcases Nat.lt_or_ge j.1 6 with hj | hj
    · let i : Fin 6 := ⟨j.1, hj⟩
      have hij : j = i.castAdd 6 := Fin.ext rfl
      rw [hij]
      change v.1 ((perm12 g).symm (i.castAdd 6)) = v.1 (i.castAdd 6)
      rw [perm12_symm, perm12_castAdd]
      exact h1 i
    · let i : Fin 6 := ⟨j.1 - 6, by have := j.isLt; omega⟩
      have hij : j = Fin.natAdd 6 i := Fin.ext (by simp [i]; omega)
      rw [hij]
      change v.1 ((perm12 g).symm (Fin.natAdd 6 i)) = v.1 (Fin.natAdd 6 i)
      rw [perm12_symm, perm12_natAdd]
      exact h2 i

def genSwap02 : P_row := permOfBool4 (false, true, false, false)
def genSwap13 : P_row := permOfBool4 (false, false, true, false)
def genSwap01_23 : P_row := permOfBool4 (true, false, false, false)
def genSwap45 : P_row := permOfBool4 (false, false, false, true)

lemma vals_on_P_row_constant (v : ↥V10Sub) (hv : ∀ g ∈ P_row, permSub g v = v) :
    ∃ a b : ℝ,
      (∀ i : Fin 6, v.1 (i.castAdd 6) = if i.1 < 4 then a else -2 * a) ∧
      (∀ i : Fin 6, v.1 (Fin.natAdd 6 i) = if i.1 < 4 then b else -2 * b) := by
  have hc : ∀ g : P_row, (∀ i : Fin 6, v.1 ((g.1⁻¹ i).castAdd 6) = v.1 (i.castAdd 6)) ∧
      (∀ i : Fin 6, v.1 (Fin.natAdd 6 (g.1⁻¹ i)) = v.1 (Fin.natAdd 6 i)) :=
    fun g => (permSub_eq_self_iff g.1 v).mp (hv g.1 g.2)
  have inv_eq : ∀ g : P_row, (∀ i : Fin 6, v.1 ((g.1 i).castAdd 6) = v.1 (i.castAdd 6)) ∧
      (∀ i : Fin 6, v.1 (Fin.natAdd 6 (g.1 i)) = v.1 (Fin.natAdd 6 i)) := fun g =>
    ⟨fun i => by simpa using ((hc g).1 (g.1 i)).symm,
     fun i => by simpa using ((hc g).2 (g.1 i)).symm⟩
  have e02_1 : v.1 ((2 : Fin 6).castAdd 6) = v.1 ((0 : Fin 6).castAdd 6) := by
    have h := (inv_eq genSwap02).1 0
    have hg : genSwap02.1 0 = 2 := rfl
    rwa [hg] at h
  have e01_1 : v.1 ((1 : Fin 6).castAdd 6) = v.1 ((0 : Fin 6).castAdd 6) := by
    have h := (inv_eq genSwap01_23).1 0
    have hg : genSwap01_23.1 0 = 1 := rfl
    rwa [hg] at h
  have e13_1 : v.1 ((3 : Fin 6).castAdd 6) = v.1 ((1 : Fin 6).castAdd 6) := by
    have h := (inv_eq genSwap13).1 1
    have hg : genSwap13.1 1 = 3 := rfl
    rwa [hg] at h
  have e45_1 : v.1 ((5 : Fin 6).castAdd 6) = v.1 ((4 : Fin 6).castAdd 6) := by
    have h := (inv_eq genSwap45).1 4
    have hg : genSwap45.1 4 = 5 := rfl
    rwa [hg] at h
  have e02_2 : v.1 (Fin.natAdd 6 (2 : Fin 6)) = v.1 (Fin.natAdd 6 (0 : Fin 6)) := by
    have h := (inv_eq genSwap02).2 (0 : Fin 6)
    have hg : genSwap02.1 (0 : Fin 6) = 2 := rfl
    rwa [hg] at h
  have e01_2 : v.1 (Fin.natAdd 6 (1 : Fin 6)) = v.1 (Fin.natAdd 6 (0 : Fin 6)) := by
    have h := (inv_eq genSwap01_23).2 (0 : Fin 6)
    have hg : genSwap01_23.1 (0 : Fin 6) = 1 := rfl
    rwa [hg] at h
  have e13_2 : v.1 (Fin.natAdd 6 (3 : Fin 6)) = v.1 (Fin.natAdd 6 (1 : Fin 6)) := by
    have h := (inv_eq genSwap13).2 (1 : Fin 6)
    have hg : genSwap13.1 (1 : Fin 6) = 3 := rfl
    rwa [hg] at h
  have e45_2 : v.1 (Fin.natAdd 6 (5 : Fin 6)) = v.1 (Fin.natAdd 6 (4 : Fin 6)) := by
    have h := (inv_eq genSwap45).2 (4 : Fin 6)
    have hg : genSwap45.1 (4 : Fin 6) = 5 := rfl
    rwa [hg] at h
  obtain ⟨hs1, hs2⟩ := (mem_V10Sub_iff v.1).mp v.2
  rw [Fin.sum_univ_six] at hs1 hs2
  have h4_1 : v.1 ((4 : Fin 6).castAdd 6) = -2 * v.1 ((0 : Fin 6).castAdd 6) := by linarith
  have h4_2 : v.1 (Fin.natAdd 6 (4 : Fin 6)) = -2 * v.1 (Fin.natAdd 6 (0 : Fin 6)) := by linarith
  refine ⟨v.1 ((0 : Fin 6).castAdd 6), v.1 (Fin.natAdd 6 (0 : Fin 6)), ?_, ?_⟩
  · intro i
    fin_cases i
    · simp only [if_pos (by decide : (0 : Fin 6).1 < 4)]; rfl
    · simp only [if_pos (by decide : (1 : Fin 6).1 < 4)]; exact e01_1
    · simp only [if_pos (by decide : (2 : Fin 6).1 < 4)]; exact e02_1
    · simp only [if_pos (by decide : (3 : Fin 6).1 < 4)]; exact e13_1.trans e01_1
    · simp only [if_neg (by decide : ¬ (4 : Fin 6).1 < 4)]; exact h4_1
    · simp only [if_neg (by decide : ¬ (5 : Fin 6).1 < 4)]; exact e45_1.trans h4_1
  · intro i
    fin_cases i
    · simp only [if_pos (by decide : (0 : Fin 6).1 < 4)]; rfl
    · simp only [if_pos (by decide : (1 : Fin 6).1 < 4)]; exact e01_2
    · simp only [if_pos (by decide : (2 : Fin 6).1 < 4)]; exact e02_2
    · simp only [if_pos (by decide : (3 : Fin 6).1 < 4)]; exact e13_2.trans e01_2
    · simp only [if_neg (by decide : ¬ (4 : Fin 6).1 < 4)]; exact h4_2
    · simp only [if_neg (by decide : ¬ (5 : Fin 6).1 < 4)]; exact e45_2.trans h4_2

lemma anchorSub_castAdd (j : Fin 6) : anchorSub.1 (j.castAdd 6) = 0 := by
  change splitPair6 (fun _ => 0) anchorVec6 (j.castAdd 6) = 0
  exact splitPair6_castAdd _ _ j

lemma anchorSub_natAdd (j : Fin 6) : anchorSub.1 (Fin.natAdd 6 j) = anchorVec6 j := by
  change splitPair6 (fun _ => 0) anchorVec6 (Fin.natAdd 6 j) = anchorVec6 j
  exact splitPair6_natAdd _ _ j

lemma cASub45_castAdd (j : Fin 6) :
    (cASub cap45).1 (j.castAdd 6) = ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 j := by
  change splitPair6 (fun i => ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 i) (fun _ => 0)
    (j.castAdd 6) = _
  exact splitPair6_castAdd _ _ j

lemma cASub45_natAdd (j : Fin 6) : (cASub cap45).1 (Fin.natAdd 6 j) = 0 := by
  change splitPair6 (fun i => ‖contrastVec6 cap45‖⁻¹ * contrastVec6 cap45 i) (fun _ => 0)
    (Fin.natAdd 6 j) = 0
  exact splitPair6_natAdd _ _ j

private lemma cASub45_val_eq (j : Fin 6) :
    (cASub cap45).1 (j.castAdd 6) = if j.1 < 4 then -1 / Real.sqrt 12 else 2 / Real.sqrt 12 := by
  rw [cASub45_castAdd, cA_cap45_norm_contrast]
  have hs : Real.sqrt 12 ≠ 0 := by positivity
  fin_cases j <;> simp [contrastVec6, InvariantCaps.contrast, cap45, WithLp.equiv_symm_apply] <;>
    field_simp <;> ring

theorem fixedSubspace_P_row_eq_span (x : Rep10) :
    x ∈ fixedSubspace P_row ↔
      x = ⟪anchor10, x⟫_ℝ • anchor10 + ⟪cA0, x⟫_ℝ • cA0 := by
  constructor
  · intro hx
    have hv : ∀ g ∈ P_row, permSub g (iso10.symm x) = iso10.symm x := fun g hg => by
      have h := hx g hg
      rw [perm10] at h
      exact iso10.injective (by simpa using h)
    obtain ⟨a, b, h1, h2⟩ := vals_on_P_row_constant (iso10.symm x) hv
    have hs12 : Real.sqrt 12 ≠ 0 := by positivity
    have hx_sub : iso10.symm x = (Real.sqrt 12 * b) • anchorSub - (Real.sqrt 12 * a) • cASub cap45 := by
      apply Subtype.ext
      ext k
      rcases Nat.lt_or_ge k.1 6 with hk | hk
      · have hkj : k = (⟨k.1, hk⟩ : Fin 6).castAdd 6 := Fin.ext rfl
        rw [hkj]
        change (iso10.symm x).1 ((⟨k.1, hk⟩ : Fin 6).castAdd 6) =
          (Real.sqrt 12 * b) * anchorSub.1 ((⟨k.1, hk⟩ : Fin 6).castAdd 6) -
            (Real.sqrt 12 * a) * (cASub cap45).1 ((⟨k.1, hk⟩ : Fin 6).castAdd 6)
        rw [h1 ⟨k.1, hk⟩, anchorSub_castAdd, cASub45_val_eq]
        by_cases hlt : k.1 < 4 <;> simp [hlt] <;> (try field_simp) <;> ring
      · have hlt6 : k.1 - 6 < 6 := by have := k.isLt; omega
        have hkj : k = Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩ := Fin.ext (by simp; omega)
        rw [hkj]
        change (iso10.symm x).1 (Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩) =
          (Real.sqrt 12 * b) * anchorSub.1 (Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩) -
            (Real.sqrt 12 * a) * (cASub cap45).1 (Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩)
        rw [h2 ⟨k.1 - 6, hlt6⟩, anchorSub_natAdd, cASub45_natAdd, anchorVec6]
        by_cases hlt : k.1 - 6 < 4 <;> simp [hlt] <;> (try field_simp) <;> ring
    have hx_lin : x = (Real.sqrt 12 * b) • anchor10 - (Real.sqrt 12 * a) • cA0 := by
      calc
        x = iso10 (iso10.symm x) := (iso10.apply_symm_apply x).symm
        _ = iso10 ((Real.sqrt 12 * b) • anchorSub - (Real.sqrt 12 * a) • cASub cap45) := by
          rw [hx_sub]
        _ = (Real.sqrt 12 * b) • anchor10 - (Real.sqrt 12 * a) • cA0 := by
          simp [anchor10, cA0, cA]
    have hcoeff1 : ⟪anchor10, x⟫_ℝ = Real.sqrt 12 * b := by
      rw [hx_lin, inner_sub_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, norm_anchor10, real_inner_comm, inner_cA0_anchor10]
      ring
    have hcoeff2 : ⟪cA0, x⟫_ℝ = -(Real.sqrt 12 * a) := by
      rw [hx_lin, inner_sub_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10]
      ring
    rw [hcoeff1, hcoeff2]
    simpa [sub_eq_add_neg, neg_smul] using hx_lin
  · intro hx
    rw [hx]
    exact (fixedSubspace P_row).add_mem
      ((fixedSubspace P_row).smul_mem _ (anchor10_mem_fixedSubspace_of_le_P_row le_rfl))
      ((fixedSubspace P_row).smul_mem _ (cA0_mem_fixedSubspace_of_le_P_row le_rfl))

theorem fixedSubspace_P_row_eq_span_submodule :
    fixedSubspace P_row = Submodule.span ℝ ({anchor10, cA0} : Set Rep10) := by
  apply le_antisymm
  · intro x hx
    rw [(fixedSubspace_P_row_eq_span x).mp hx]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact anchor10_mem_fixedSubspace_of_le_P_row le_rfl
    · exact cA0_mem_fixedSubspace_of_le_P_row le_rfl

theorem finrank_fixedSubspace_P_row : Module.finrank ℝ (fixedSubspace P_row) = 2 := by
  rw [fixedSubspace_P_row_eq_span_submodule]
  have hli : LinearIndependent ℝ ![anchor10, cA0] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    fin_cases i
    · have h := congrArg (fun v => ⟪anchor10, v⟫_ℝ) hf
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_add_right,
        inner_smul_right, real_inner_self_eq_norm_sq, norm_anchor10,
        inner_anchor10_cA0, inner_zero_right] at h
      simpa using h
    · have h := congrArg (fun v => ⟪cA0, v⟫_ℝ) hf
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_add_right,
        inner_smul_right, real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10,
        inner_zero_right] at h
      simpa using h
  have hset : ({anchor10, cA0} : Set Rep10) = Set.range ![anchor10, cA0] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
  rw [hset, finrank_span_eq_card hli, Fintype.card_fin]

def anchorPhaseFun (y : Metric.sphere (0 : Rep10) 1) : ℂ :=
  (⟪anchor10, y.1⟫_ℝ : ℂ) + (⟪cA0, y.1⟫_ℝ : ℂ) * Complex.I

lemma anchorPhaseFun_re (y : Metric.sphere (0 : Rep10) 1) :
    (anchorPhaseFun y).re = ⟪anchor10, y.1⟫_ℝ := by
  simp [anchorPhaseFun]

lemma anchorPhaseFun_im (y : Metric.sphere (0 : Rep10) 1) :
    (anchorPhaseFun y).im = ⟪cA0, y.1⟫_ℝ := by
  simp [anchorPhaseFun]

lemma normSq_anchorPhaseFun {y : Metric.sphere (0 : Rep10) 1}
    (hy : y.1 ∈ fixedSubspace P_row) :
    Complex.normSq (anchorPhaseFun y) = 1 := by
  have hy_eq := (fixedSubspace_P_row_eq_span y.1).mp hy
  have hn : ‖y.1‖ ^ 2 = 1 := by rw [mem_sphere_zero_iff_norm.mp y.2, one_pow]
  have hsq : ‖⟪anchor10, y.1⟫_ℝ • anchor10 + ⟪cA0, y.1⟫_ℝ • cA0‖ ^ 2 =
      ⟪anchor10, y.1⟫_ℝ ^ 2 + ⟪cA0, y.1⟫_ℝ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      norm_anchor10, norm_cA0, mul_one, mul_one, sq_abs, sq_abs,
      inner_smul_left, inner_smul_right, inner_anchor10_cA0]
    ring
  rw [← hy_eq] at hsq
  rw [Complex.normSq_apply, anchorPhaseFun_re, anchorPhaseFun_im, ← pow_two, ← pow_two]
  linarith

def anchorPhase (y : Metric.sphere (0 : Rep10) 1) (hy : y.1 ∈ fixedSubspace P_row) : Circle :=
  ⟨anchorPhaseFun y, by
    change anchorPhaseFun y ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    have hns := normSq_anchorPhaseFun hy
    rw [Complex.normSq_eq_norm_sq] at hns
    nlinarith [norm_nonneg (anchorPhaseFun y)]⟩

lemma smulCircleSphere_anchorPhase (y : Metric.sphere (0 : Rep10) 1)
    (hy : y.1 ∈ fixedSubspace P_row) :
    smulCircleSphere (anchorPhase y hy) anchorS = y := by
  apply Subtype.ext
  change smulCircle (anchorPhase y hy) anchor10 = y.1
  rw [smulCircle_apply, J10_anchor10]
  change (anchorPhaseFun y).re • anchor10 + (anchorPhaseFun y).im • cA0 = y.1
  rw [anchorPhaseFun_re, anchorPhaseFun_im]
  exact ((fixedSubspace_P_row_eq_span y.1).mp hy).symm

lemma continuous_anchorPhaseFun : Continuous anchorPhaseFun := by
  unfold anchorPhaseFun
  exact (Complex.continuous_ofReal.comp (continuous_const.inner continuous_subtype_val)).add
    ((Complex.continuous_ofReal.comp (continuous_const.inner continuous_subtype_val)).mul continuous_const)

lemma continuousOn_anchorPhase :
    ContinuousOn (fun y : {y : Metric.sphere (0 : Rep10) 1 // y.1 ∈ fixedSubspace P_row} =>
      (anchorPhase y.1 y.2 : ℂ)) Set.univ :=
  (continuous_anchorPhaseFun.comp continuous_subtype_val).continuousOn

theorem basedHomotopy_of_equivariant
    (f g : C(Metric.sphere (0 : Rep10) 1, Metric.sphere (0 : Rep10) 1))
    (hf : f anchorS = anchorS) (hg : g anchorS = anchorS)
    (H : ContinuousMap.Homotopy f g)
    (hHeq : ∀ t : unitInterval, ∀ k ∈ P_row, ∀ x, H (t, permSphere k x) = permSphere k (H (t, x))) :
    ∃ H' : ContinuousMap.Homotopy f g,
      (∀ t : unitInterval, ∀ k ∈ P_row, ∀ x, H' (t, permSphere k x) = permSphere k (H' (t, x))) ∧
      (∀ t : unitInterval, H' (t, anchorS) = anchorS) := by
  have hP : ∀ t : unitInterval, (H (t, anchorS) : Rep10) ∈ fixedSubspace P_row := by
    intro t k hk
    change (permSphere k (H (t, anchorS)) : Rep10) = _
    rw [← hHeq t k hk anchorS, permSphere_anchorS_of_mem_P_row hk]
  let lam : unitInterval → Circle := fun t => anchorPhase (H (t, anchorS)) (hP t)
  have hlam_cont : Continuous lam := by
    change Continuous (fun t : unitInterval => (⟨anchorPhaseFun (H (t, anchorS)),
      (anchorPhase (H (t, anchorS)) (hP t)).2⟩ : Circle))
    exact Continuous.subtype_mk
      (continuous_anchorPhaseFun.comp (H.continuous.comp (continuous_id.prodMk continuous_const))) _
  have hlam0 : lam 0 = 1 := by
    apply Subtype.ext; apply Complex.ext
    · rw [Circle.coe_one, Complex.one_re]
      change (anchorPhaseFun (H (0, anchorS))).re = 1
      rw [anchorPhaseFun_re, H.apply_zero, hf]
      exact (real_inner_self_eq_norm_sq anchor10).trans (by simp [norm_anchor10])
    · rw [Circle.coe_one, Complex.one_im]
      change (anchorPhaseFun (H (0, anchorS))).im = 0
      rw [anchorPhaseFun_im, H.apply_zero, hf]
      exact inner_cA0_anchor10
  have hlam1 : lam 1 = 1 := by
    apply Subtype.ext; apply Complex.ext
    · rw [Circle.coe_one, Complex.one_re]
      change (anchorPhaseFun (H (1, anchorS))).re = 1
      rw [anchorPhaseFun_re, H.apply_one, hg]
      exact (real_inner_self_eq_norm_sq anchor10).trans (by simp [norm_anchor10])
    · rw [Circle.coe_one, Complex.one_im]
      change (anchorPhaseFun (H (1, anchorS))).im = 0
      rw [anchorPhaseFun_im, H.apply_one, hg]
      exact inner_cA0_anchor10
  let H' : ContinuousMap.Homotopy f g :=
    { toFun p := smulCircleSphere (lam p.1)⁻¹ (H p)
      continuous_toFun := continuous_smulCircleSphere.comp
        ((hlam_cont.inv.comp continuous_fst).prodMk H.continuous)
      map_zero_left x := by simp [hlam0, smulCircleSphere_one, H.apply_zero]
      map_one_left x := by simp [hlam1, smulCircleSphere_one, H.apply_one] }
  refine ⟨H', ?_, ?_⟩
  · intro t k hk x
    change smulCircleSphere (lam t)⁻¹ (H (t, permSphere k x)) =
      permSphere k (smulCircleSphere (lam t)⁻¹ (H (t, x)))
    rw [hHeq t k hk x, permSphere_smulCircleSphere]
  · intro t
    change smulCircleSphere (lam t)⁻¹ (H (t, anchorS)) = anchorS
    rw [← smulCircleSphere_anchorPhase (H (t, anchorS)) (hP t), ← smulCircleSphere_mul,
      inv_mul_cancel, smulCircleSphere_one]

end FixedSpaces

/-! ### 4. Orbit counts and fixed-point bubble degrees for `K ≤ P_row` -/

section OrbitCountFormula

def orbitOf (K : Subgroup (Equiv.Perm (Fin 6))) (i : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter (fun j : Fin 6 => ∃ g ∈ K, g i = j)

def orbitSet (K : Subgroup (Equiv.Perm (Fin 6))) : Finset (Finset (Fin 6)) :=
  Finset.univ.image (orbitOf K)

@[simp] lemma mem_orbitOf_iff {K : Subgroup (Equiv.Perm (Fin 6))} {i j : Fin 6} :
    j ∈ orbitOf K i ↔ ∃ g ∈ K, g i = j := by
  simp [orbitOf]

@[simp] lemma mem_orbitSet_iff {K : Subgroup (Equiv.Perm (Fin 6))} {O : Finset (Fin 6)} :
    O ∈ orbitSet K ↔ ∃ i : Fin 6, orbitOf K i = O := by
  simp [orbitSet]

attribute [irreducible] orbitOf orbitSet

lemma mem_orbitOf_self (K : Subgroup (Equiv.Perm (Fin 6))) (i : Fin 6) : i ∈ orbitOf K i :=
  mem_orbitOf_iff.mpr ⟨1, K.one_mem, rfl⟩

lemma orbitOf_nonempty (K : Subgroup (Equiv.Perm (Fin 6))) (i : Fin 6) : (orbitOf K i).Nonempty :=
  ⟨i, mem_orbitOf_self K i⟩

lemma orbitOf_eq_of_mem {K : Subgroup (Equiv.Perm (Fin 6))} {i j : Fin 6}
    (hj : j ∈ orbitOf K i) : orbitOf K j = orbitOf K i := by
  obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
  ext x
  simp only [mem_orbitOf_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, K.mul_mem hh hg, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g⁻¹, K.mul_mem hh (K.inv_mem hg), by simp⟩

lemma orbitSet_pairwiseDisjoint (K : Subgroup (Equiv.Perm (Fin 6))) :
    (orbitSet K : Set (Finset (Fin 6))).PairwiseDisjoint id := by
  intro O₁ hO₁ O₂ hO₂ hne
  obtain ⟨i, rfl⟩ := mem_orbitSet_iff.mp (Finset.mem_coe.mp hO₁)
  obtain ⟨j, rfl⟩ := mem_orbitSet_iff.mp (Finset.mem_coe.mp hO₂)
  rw [Function.onFun, id_eq, id_eq, Finset.disjoint_left]
  intro x hx₁ hx₂
  apply hne
  calc
    orbitOf K i = orbitOf K x := (orbitOf_eq_of_mem hx₁).symm
    _ = orbitOf K j := orbitOf_eq_of_mem hx₂

lemma orbitSet_biUnion (K : Subgroup (Equiv.Perm (Fin 6))) :
    (orbitSet K).biUnion id = Finset.univ := by
  ext i
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  exact ⟨orbitOf K i, mem_orbitSet_iff.mpr ⟨i, rfl⟩, mem_orbitOf_self K i⟩

lemma orbitOf_card_dvd {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) (i : Fin 6) :
    (orbitOf K i).card ∣ 16 := by
  have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K i
  have heq : ↥(MulAction.orbit K i) ≃ ↥(orbitOf K i) :=
    { toFun := fun ⟨j, hj⟩ => ⟨j, mem_orbitOf_iff.mpr (by
        obtain ⟨⟨g, hg⟩, rfl⟩ := MulAction.mem_orbit_iff.mp hj
        exact ⟨g, hg, rfl⟩)⟩
      invFun := fun ⟨j, hj⟩ => ⟨j, MulAction.mem_orbit_iff.mpr (by
        obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
        exact ⟨⟨g, hg⟩, rfl⟩)⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  have hcard : Fintype.card (MulAction.orbit K i) = (orbitOf K i).card :=
    (Fintype.card_congr heq).trans (Fintype.card_coe _)
  have hdvd1 : (orbitOf K i).card ∣ Fintype.card K :=
    ⟨Fintype.card (MulAction.stabilizer K i), by rw [← hcard]; exact hmul.symm⟩
  have hdvd2 : Fintype.card K ∣ Fintype.card P_row := by
    have hnat : Nat.card K ∣ Nat.card P_row := Subgroup.card_dvd_of_le hK
    simpa only [Nat.card_eq_fintype_card] using hnat
  rw [card_P_row] at hdvd2
  exact hdvd1.trans hdvd2

lemma orbitOf_card_le_four {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) (i : Fin 6) :
    (orbitOf K i).card ≤ 4 := by
  by_cases hi : i.1 < 4
  · have hsub : orbitOf K i ⊆ Finset.univ.filter (fun j : Fin 6 => j.1 < 4) := by
      intro j hj
      obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hK hg).1 i hi⟩
    have h4 : (Finset.univ.filter (fun j : Fin 6 => j.1 < 4)).card = 4 := by decide
    exact (Finset.card_le_card hsub).trans_eq h4
  · have hsub : orbitOf K i ⊆ Finset.univ.filter (fun j : Fin 6 => 4 ≤ j.1) := by
      intro j hj
      obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P_row_preserves_ge4 (hK hg) (Nat.le_of_not_lt hi)⟩
    have h2 : (Finset.univ.filter (fun j : Fin 6 => 4 ≤ j.1)).card = 2 := by decide
    exact (Finset.card_le_card hsub).trans (by omega)

lemma orbitOf_card_mem_124 {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row)
    {O : Finset (Fin 6)} (hO : O ∈ orbitSet K) :
    O.card = 1 ∨ O.card = 2 ∨ O.card = 4 := by
  obtain ⟨i, rfl⟩ := mem_orbitSet_iff.mp hO
  have hle := orbitOf_card_le_four hK i
  have hdvd := orbitOf_card_dvd hK i
  have hpos : 0 < (orbitOf K i).card := (orbitOf_nonempty K i).card_pos
  have hcases : (orbitOf K i).card = 1 ∨ (orbitOf K i).card = 2 ∨
      (orbitOf K i).card = 3 ∨ (orbitOf K i).card = 4 := by omega
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [h] at hdvd; norm_num at hdvd
  · exact Or.inr (Or.inr h)

def orbitCount (K : Subgroup (Equiv.Perm (Fin 6))) (m : ℕ) : ℕ :=
  ((orbitSet K).filter (fun O => O.card = m)).card

theorem orbitCount_sum_six {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    orbitCount K 1 + 2 * orbitCount K 2 + 4 * orbitCount K 4 = 6 := by
  have htot : (∑ O ∈ orbitSet K, O.card) = 6 := by
    have hbi := Finset.card_biUnion (orbitSet_pairwiseDisjoint K)
    rw [orbitSet_biUnion K, Finset.card_univ, Fintype.card_fin] at hbi
    simpa only [id_eq] using hbi.symm
  let S1 := (orbitSet K).filter (fun O => O.card = 1)
  let S2 := (orbitSet K).filter (fun O => O.card = 2)
  let S4 := (orbitSet K).filter (fun O => O.card = 4)
  have hdisj12 : Disjoint S1 S2 := Finset.disjoint_left.mpr fun O h1 h2 => by
    have c1 := (Finset.mem_filter.mp h1).2
    have c2 := (Finset.mem_filter.mp h2).2
    omega
  have hdisj124 : Disjoint (S1 ∪ S2) S4 := Finset.disjoint_left.mpr fun O h12 h4 => by
    have c4 := (Finset.mem_filter.mp h4).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have c1 := (Finset.mem_filter.mp h1).2; omega
    · have c2 := (Finset.mem_filter.mp h2).2; omega
  have hunion : orbitSet K = S1 ∪ S2 ∪ S4 := by
    ext O
    simp only [S1, S2, S4, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hO
      rcases orbitOf_card_mem_124 hK hO with c | c | c
      · exact Or.inl (Or.inl ⟨hO, c⟩)
      · exact Or.inl (Or.inr ⟨hO, c⟩)
      · exact Or.inr ⟨hO, c⟩
    · rintro ((⟨hO, _⟩ | ⟨hO, _⟩) | ⟨hO, _⟩) <;> exact hO
  rw [hunion, Finset.sum_union hdisj124, Finset.sum_union hdisj12] at htot
  have hs1 : ∑ O ∈ S1, O.card = orbitCount K 1 := by
    rw [Finset.sum_congr rfl fun O hO => (Finset.mem_filter.mp hO).2, Finset.sum_const,
      smul_eq_mul, mul_one]
    rfl
  have hs2 : ∑ O ∈ S2, O.card = 2 * orbitCount K 2 := by
    rw [Finset.sum_congr rfl fun O hO => (Finset.mem_filter.mp hO).2, Finset.sum_const,
      smul_eq_mul, mul_comm]
    rfl
  have hs4 : ∑ O ∈ S4, O.card = 4 * orbitCount K 4 := by
    rw [Finset.sum_congr rfl fun O hO => (Finset.mem_filter.mp hO).2, Finset.sum_const,
      smul_eq_mul, mul_comm]
    rfl
  rw [hs1, hs2, hs4] at htot
  exact htot

lemma orbitSet_card_eq {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    (orbitSet K).card = orbitCount K 1 + orbitCount K 2 + orbitCount K 4 := by
  let S1 := (orbitSet K).filter (fun O => O.card = 1)
  let S2 := (orbitSet K).filter (fun O => O.card = 2)
  let S4 := (orbitSet K).filter (fun O => O.card = 4)
  have hdisj12 : Disjoint S1 S2 := Finset.disjoint_left.mpr fun O h1 h2 => by
    have c1 := (Finset.mem_filter.mp h1).2
    have c2 := (Finset.mem_filter.mp h2).2
    omega
  have hdisj124 : Disjoint (S1 ∪ S2) S4 := Finset.disjoint_left.mpr fun O h12 h4 => by
    have c4 := (Finset.mem_filter.mp h4).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have c1 := (Finset.mem_filter.mp h1).2; omega
    · have c2 := (Finset.mem_filter.mp h2).2; omega
  have hunion : orbitSet K = S1 ∪ S2 ∪ S4 := by
    ext O
    simp only [S1, S2, S4, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hO
      rcases orbitOf_card_mem_124 hK hO with c | c | c
      · exact Or.inl (Or.inl ⟨hO, c⟩)
      · exact Or.inl (Or.inr ⟨hO, c⟩)
      · exact Or.inr ⟨hO, c⟩
    · rintro ((⟨hO, _⟩ | ⟨hO, _⟩) | ⟨hO, _⟩) <;> exact hO
  rw [hunion, Finset.card_union_of_disjoint hdisj124, Finset.card_union_of_disjoint hdisj12]
  rfl

def orbitWeightedSumMap (K : Subgroup (Equiv.Perm (Fin 6))) :
    (orbitSet K → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ O : orbitSet K, (O.1.card : ℝ) * c O
  map_add' c₁ c₂ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.mul_sum, mul_left_comm]

lemma orbitWeightedSumMap_surjective (K : Subgroup (Equiv.Perm (Fin 6))) :
    Function.Surjective (orbitWeightedSumMap K) := by
  intro r
  let O0 : orbitSet K := ⟨orbitOf K 0, mem_orbitSet_iff.mpr ⟨0, rfl⟩⟩
  have hpos : (O0.1.card : ℝ) ≠ 0 := by
    exact_mod_cast (orbitOf_nonempty K 0).card_pos.ne'
  refine ⟨fun O => if O = O0 then r / (O0.1.card : ℝ) else 0, ?_⟩
  change ∑ O : orbitSet K, (O.1.card : ℝ) * (if O = O0 then r / (O0.1.card : ℝ) else 0) = r
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact mul_div_cancel₀ r hpos

lemma finrank_ker_orbitWeightedSumMap {K : Subgroup (Equiv.Perm (Fin 6))} :
    Module.finrank ℝ (LinearMap.ker (orbitWeightedSumMap K)) + 1 = (orbitSet K).card := by
  have h1 := (orbitWeightedSumMap K).finrank_range_add_finrank_ker
  have hr : LinearMap.range (orbitWeightedSumMap K) = ⊤ :=
    LinearMap.range_eq_top.mpr (orbitWeightedSumMap_surjective K)
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h1
  omega

def orbitElem (K : Subgroup (Equiv.Perm (Fin 6))) (i : Fin 6) : orbitSet K :=
  ⟨orbitOf K i, mem_orbitSet_iff.mpr ⟨i, rfl⟩⟩

lemma orbitElem_eq_of_mem {K : Subgroup (Equiv.Perm (Fin 6))}
    (O : orbitSet K) {i : Fin 6} (hi : i ∈ O.1) : orbitElem K i = O := by
  apply Subtype.ext
  obtain ⟨j, hOj⟩ := mem_orbitSet_iff.mp O.2
  rw [← hOj]
  exact orbitOf_eq_of_mem (hOj.symm ▸ hi)

lemma sum_fin6_orbitElem (K : Subgroup (Equiv.Perm (Fin 6))) (g : orbitSet K → ℝ) :
    (∑ i : Fin 6, g (orbitElem K i)) = ∑ O : orbitSet K, (O.1.card : ℝ) * g O := by
  have huniv : (Finset.univ : Finset (Fin 6)) = (orbitSet K).biUnion id := (orbitSet_biUnion K).symm
  rw [huniv, Finset.sum_biUnion (orbitSet_pairwiseDisjoint K), ← Finset.sum_coe_sort (orbitSet K)]
  refine Finset.sum_congr rfl fun O _ => ?_
  have hconst : ∀ i ∈ id O.1, g (orbitElem K i) = g O := fun i hi =>
    congrArg g (orbitElem_eq_of_mem O hi)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, id_eq]

lemma kerOrbit_sum_zero {K : Subgroup (Equiv.Perm (Fin 6))}
    (f : LinearMap.ker (orbitWeightedSumMap K)) :
    (∑ i : Fin 6, f.1 (orbitElem K i)) = 0 := by
  rw [sum_fin6_orbitElem]
  exact f.2

def kerOrbitToSubspace (K : Subgroup (Equiv.Perm (Fin 6))) :
    (LinearMap.ker (orbitWeightedSumMap K) × LinearMap.ker (orbitWeightedSumMap K)) →ₗ[ℝ]
      fixedSubspace K where
  toFun p := ⟨iso10 ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm
      (splitPair6 (fun i => p.1.1 (orbitElem K i)) (fun i => p.2.1 (orbitElem K i))), by
      rw [mem_V10Sub_iff]
      simp only [WithLp.equiv_symm_apply, splitPair6_castAdd, splitPair6_natAdd]
      exact ⟨kerOrbit_sum_zero p.1, kerOrbit_sum_zero p.2⟩⟩, by
    intro g hg
    rw [perm10]
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
    congr 1
    refine (permSub_eq_self_iff g _).mpr ⟨fun i => ?_, fun i => ?_⟩
    · simp only [WithLp.equiv_symm_apply, splitPair6_castAdd]
      have horb : orbitElem K (g⁻¹ i) = orbitElem K i := by
        apply Subtype.ext
        exact orbitOf_eq_of_mem (mem_orbitOf_iff.mpr ⟨g⁻¹, K.inv_mem hg, rfl⟩)
      rw [horb]
    · simp only [WithLp.equiv_symm_apply, splitPair6_natAdd]
      have horb : orbitElem K (g⁻¹ i) = orbitElem K i := by
        apply Subtype.ext
        exact orbitOf_eq_of_mem (mem_orbitOf_iff.mpr ⟨g⁻¹, K.inv_mem hg, rfl⟩)
      rw [horb]⟩
  map_add' p q := by
    apply Subtype.ext
    change iso10 _ = iso10 _ + iso10 _
    rw [← iso10.map_add]
    congr 1; apply Subtype.ext; ext i
    rcases Nat.lt_or_ge i.1 6 with hi | hi
    · have hij : i = (⟨i.1, hi⟩ : Fin 6).castAdd 6 := Fin.ext rfl
      rw [hij]
      change splitPair6 (fun j => (p.1.1 + q.1.1) (orbitElem K j))
          (fun j => (p.2.1 + q.2.1) (orbitElem K j)) ((⟨i.1, hi⟩ : Fin 6).castAdd 6) =
        splitPair6 (fun j => p.1.1 (orbitElem K j)) (fun j => p.2.1 (orbitElem K j))
            ((⟨i.1, hi⟩ : Fin 6).castAdd 6) +
          splitPair6 (fun j => q.1.1 (orbitElem K j)) (fun j => q.2.1 (orbitElem K j))
            ((⟨i.1, hi⟩ : Fin 6).castAdd 6)
      simp only [splitPair6_castAdd]; rfl
    · have hlt6 : i.1 - 6 < 6 := by have := i.isLt; omega
      have hij : i = Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩ := Fin.ext (by simp; omega)
      rw [hij]
      change splitPair6 (fun j => (p.1.1 + q.1.1) (orbitElem K j))
          (fun j => (p.2.1 + q.2.1) (orbitElem K j)) (Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩) =
        splitPair6 (fun j => p.1.1 (orbitElem K j)) (fun j => p.2.1 (orbitElem K j))
            (Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩) +
          splitPair6 (fun j => q.1.1 (orbitElem K j)) (fun j => q.2.1 (orbitElem K j))
            (Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩)
      simp only [splitPair6_natAdd]; rfl
  map_smul' r p := by
    apply Subtype.ext
    change iso10 _ = r • iso10 _
    rw [← iso10.map_smul]
    congr 1; apply Subtype.ext; ext i
    rcases Nat.lt_or_ge i.1 6 with hi | hi
    · have hij : i = (⟨i.1, hi⟩ : Fin 6).castAdd 6 := Fin.ext rfl
      rw [hij]
      change splitPair6 (fun j => (r • p.1.1) (orbitElem K j))
          (fun j => (r • p.2.1) (orbitElem K j)) ((⟨i.1, hi⟩ : Fin 6).castAdd 6) =
        r • splitPair6 (fun j => p.1.1 (orbitElem K j)) (fun j => p.2.1 (orbitElem K j))
            ((⟨i.1, hi⟩ : Fin 6).castAdd 6)
      simp only [splitPair6_castAdd]; rfl
    · have hlt6 : i.1 - 6 < 6 := by have := i.isLt; omega
      have hij : i = Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩ := Fin.ext (by simp; omega)
      rw [hij]
      change splitPair6 (fun j => (r • p.1.1) (orbitElem K j))
          (fun j => (r • p.2.1) (orbitElem K j)) (Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩) =
        r • splitPair6 (fun j => p.1.1 (orbitElem K j)) (fun j => p.2.1 (orbitElem K j))
            (Fin.natAdd 6 ⟨i.1 - 6, hlt6⟩)
      simp only [splitPair6_natAdd]; rfl

lemma bijective_kerOrbitToSubspace (K : Subgroup (Equiv.Perm (Fin 6))) :
    Function.Bijective (kerOrbitToSubspace K) := by
  constructor
  · intro p q hpq
    dsimp only [kerOrbitToSubspace, LinearMap.coe_mk, AddHom.coe_mk] at hpq
    have hsub := iso10.injective (congrArg Subtype.val hpq)
    have hval := congrArg Subtype.val hsub
    have hL : p.1 = q.1 := by
      apply Subtype.ext; funext O
      obtain ⟨i, hOi⟩ := mem_orbitSet_iff.mp O.2
      have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 12) => v (i.castAdd 6)) hval
      simp only [WithLp.equiv_symm_apply, splitPair6_castAdd] at h0
      have hOe : orbitElem K i = O := Subtype.ext hOi
      simpa only [hOe] using h0
    have hR : p.2 = q.2 := by
      apply Subtype.ext; funext O
      obtain ⟨i, hOi⟩ := mem_orbitSet_iff.mp O.2
      have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 12) => v (Fin.natAdd 6 i)) hval
      simp only [WithLp.equiv_symm_apply, splitPair6_natAdd] at h0
      have hOe : orbitElem K i = O := Subtype.ext hOi
      simpa only [hOe] using h0
    exact Prod.ext hL hR
  · rintro ⟨x, hx⟩
    have hv : ∀ g ∈ K, permSub g (iso10.symm x) = iso10.symm x := fun g hg => by
      have h := hx g hg
      rw [perm10] at h
      exact iso10.injective (by simpa using h)
    have hconst : ∀ O : orbitSet K,
        (∃ a : ℝ, ∀ i ∈ O.1, (iso10.symm x).1 (i.castAdd 6) = a) ∧
        (∃ b : ℝ, ∀ i ∈ O.1, (iso10.symm x).1 (Fin.natAdd 6 i) = b) := by
      rintro ⟨O, hO⟩
      obtain ⟨i₀, rfl⟩ := mem_orbitSet_iff.mp hO
      constructor
      · refine ⟨(iso10.symm x).1 (i₀.castAdd 6), fun i hi => ?_⟩
        obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hi
        have hperm := ((permSub_eq_self_iff g (iso10.symm x)).mp (hv g hg)).1 (g i₀)
        simpa [Equiv.symm_apply_apply] using hperm.symm
      · refine ⟨(iso10.symm x).1 (Fin.natAdd 6 i₀), fun i hi => ?_⟩
        obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hi
        have hperm := ((permSub_eq_self_iff g (iso10.symm x)).mp (hv g hg)).2 (g i₀)
        simpa [Equiv.symm_apply_apply] using hperm.symm
    let c1 : orbitSet K → ℝ := fun O => Classical.choose (hconst O).1
    let c2 : orbitSet K → ℝ := fun O => Classical.choose (hconst O).2
    have hc1 : ∀ O i, i ∈ O.1 → (iso10.symm x).1 (i.castAdd 6) = c1 O :=
      fun O => Classical.choose_spec (hconst O).1
    have hc2 : ∀ O i, i ∈ O.1 → (iso10.symm x).1 (Fin.natAdd 6 i) = c2 O :=
      fun O => Classical.choose_spec (hconst O).2
    obtain ⟨hs1, hs2⟩ := (mem_V10Sub_iff (iso10.symm x).1).mp (iso10.symm x).2
    have hker1 : c1 ∈ LinearMap.ker (orbitWeightedSumMap K) := by
      change ∑ O : orbitSet K, (O.1.card : ℝ) * c1 O = 0
      have hsum1 : ∑ i : Fin 6, (iso10.symm x).1 (i.castAdd 6) =
          ∑ O ∈ orbitSet K, (O.card : ℝ) *
            if hO : O ∈ orbitSet K then c1 ⟨O, hO⟩ else 0 := by
        have huniv : (Finset.univ : Finset (Fin 6)) = (orbitSet K).biUnion id :=
          (orbitSet_biUnion K).symm
        rw [huniv, Finset.sum_biUnion (orbitSet_pairwiseDisjoint K)]
        refine Finset.sum_congr rfl fun O hO => ?_
        rw [dif_pos hO]
        have hconst' : ∀ i ∈ id O, (iso10.symm x).1 (i.castAdd 6) = c1 ⟨O, hO⟩ :=
          fun i hi => hc1 ⟨O, hO⟩ i hi
        rw [Finset.sum_congr rfl hconst', Finset.sum_const, nsmul_eq_mul, id_eq]
      have hcoe : (∑ O : orbitSet K, (O.1.card : ℝ) * c1 O) =
          ∑ O ∈ orbitSet K, (O.card : ℝ) *
            if hO : O ∈ orbitSet K then c1 ⟨O, hO⟩ else 0 := by
        rw [← Finset.sum_coe_sort (orbitSet K)]
        refine Finset.sum_congr rfl fun O _ => ?_
        rw [dif_pos O.2]
      rw [hcoe, ← hsum1, hs1]
    have hker2 : c2 ∈ LinearMap.ker (orbitWeightedSumMap K) := by
      change ∑ O : orbitSet K, (O.1.card : ℝ) * c2 O = 0
      have hsum2 : ∑ i : Fin 6, (iso10.symm x).1 (Fin.natAdd 6 i) =
          ∑ O ∈ orbitSet K, (O.card : ℝ) *
            if hO : O ∈ orbitSet K then c2 ⟨O, hO⟩ else 0 := by
        have huniv : (Finset.univ : Finset (Fin 6)) = (orbitSet K).biUnion id :=
          (orbitSet_biUnion K).symm
        rw [huniv, Finset.sum_biUnion (orbitSet_pairwiseDisjoint K)]
        refine Finset.sum_congr rfl fun O hO => ?_
        rw [dif_pos hO]
        have hconst' : ∀ i ∈ id O, (iso10.symm x).1 (Fin.natAdd 6 i) = c2 ⟨O, hO⟩ :=
          fun i hi => hc2 ⟨O, hO⟩ i hi
        rw [Finset.sum_congr rfl hconst', Finset.sum_const, nsmul_eq_mul, id_eq]
      have hcoe : (∑ O : orbitSet K, (O.1.card : ℝ) * c2 O) =
          ∑ O ∈ orbitSet K, (O.card : ℝ) *
            if hO : O ∈ orbitSet K then c2 ⟨O, hO⟩ else 0 := by
        rw [← Finset.sum_coe_sort (orbitSet K)]
        refine Finset.sum_congr rfl fun O _ => ?_
        rw [dif_pos O.2]
      rw [hcoe, ← hsum2, hs2]
    refine ⟨(⟨c1, hker1⟩, ⟨c2, hker2⟩), ?_⟩
    apply Subtype.ext
    dsimp only [kerOrbitToSubspace, LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [← iso10.apply_symm_apply x]
    congr 1; apply Subtype.ext; ext k
    rcases Nat.lt_or_ge k.1 6 with hk | hk
    · have hki : k = (⟨k.1, hk⟩ : Fin 6).castAdd 6 := Fin.ext rfl
      rw [hki]
      change splitPair6 (fun i => c1 (orbitElem K i)) (fun i => c2 (orbitElem K i))
          ((⟨k.1, hk⟩ : Fin 6).castAdd 6) =
        (iso10.symm x).1 ((⟨k.1, hk⟩ : Fin 6).castAdd 6)
      rw [splitPair6_castAdd]
      exact (hc1 (orbitElem K ⟨k.1, hk⟩) ⟨k.1, hk⟩ (mem_orbitOf_self K ⟨k.1, hk⟩)).symm
    · have hlt6 : k.1 - 6 < 6 := by have := k.isLt; omega
      have hki : k = Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩ := Fin.ext (by simp; omega)
      rw [hki]
      change splitPair6 (fun i => c1 (orbitElem K i)) (fun i => c2 (orbitElem K i))
          (Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩) =
        (iso10.symm x).1 (Fin.natAdd 6 ⟨k.1 - 6, hlt6⟩)
      rw [splitPair6_natAdd]
      exact (hc2 (orbitElem K ⟨k.1 - 6, hlt6⟩) ⟨k.1 - 6, hlt6⟩ (mem_orbitOf_self K ⟨k.1 - 6, hlt6⟩)).symm

theorem finrank_fixedSubspace_eq {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    Module.finrank ℝ (fixedSubspace K) = 2 * (orbitCount K 1 + orbitCount K 2 + orbitCount K 4 - 1) := by
  let e : (LinearMap.ker (orbitWeightedSumMap K) × LinearMap.ker (orbitWeightedSumMap K)) ≃ₗ[ℝ]
      fixedSubspace K := LinearEquiv.ofBijective (kerOrbitToSubspace K) (bijective_kerOrbitToSubspace K)
  rw [← e.finrank_eq, Module.finrank_prod]
  have h1 := finrank_ker_orbitWeightedSumMap (K := K)
  rw [orbitSet_card_eq hK] at h1
  omega

theorem two_le_finrank_fixedSubspace {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    2 ≤ Module.finrank ℝ (fixedSubspace K) := by
  have hsum := orbitCount_sum_six hK
  rw [finrank_fixedSubspace_eq hK]
  omega

def fixedCaps (K : Subgroup (Equiv.Perm (Fin 6))) (m : ℕ) : Finset InvariantCaps.CapLabel :=
  Finset.univ.filter (fun A => A.val.card = m ∧ ∀ g ∈ K, permCap g A = A)

@[simp] lemma mem_fixedCaps_iff {K : Subgroup (Equiv.Perm (Fin 6))} {m : ℕ}
    {A : InvariantCaps.CapLabel} :
    A ∈ fixedCaps K m ↔ A.val.card = m ∧ ∀ g ∈ K, permCap g A = A := by
  simp [fixedCaps]

attribute [irreducible] fixedCaps

lemma mem_fixedCaps_iff_cA {K : Subgroup (Equiv.Perm (Fin 6))} {m : ℕ}
    {A : InvariantCaps.CapLabel} :
    A ∈ fixedCaps K m ↔ A.val.card = m ∧ cA A ∈ fixedSubspace K := by
  simp only [mem_fixedCaps_iff, mem_fixedSubspace_iff]
  constructor
  · rintro ⟨hm, hg⟩
    refine ⟨hm, fun g hk => ?_⟩
    rw [perm10_cA, hg g hk]
  · rintro ⟨hm, hg⟩
    refine ⟨hm, fun g hk => cA_injective ?_⟩
    rw [← perm10_cA, hg g hk]

lemma bA_mem_fixedSubspace_of_cA {K : Subgroup (Equiv.Perm (Fin 6))}
    {A : InvariantCaps.CapLabel} (h : cA A ∈ fixedSubspace K) :
    bA A ∈ fixedSubspace K := by
  have hc := (mem_fixedCaps_iff_cA (K := K) (m := A.val.card) (A := A)).mpr ⟨rfl, h⟩
  have hcap := (mem_fixedCaps_iff.mp hc).2
  intro g hg
  rw [perm10_bA, hcap g hg]

lemma cap_fixed_iff_union_orbits (K : Subgroup (Equiv.Perm (Fin 6))) (A : Finset (Fin 6)) :
    (∀ g ∈ K, A.map g.toEmbedding = A) ↔
      ∃ S ⊆ orbitSet K, S.biUnion id = A := by
  constructor
  · intro hA
    refine ⟨(orbitSet K).filter (fun O => O ⊆ A), Finset.filter_subset _ _, ?_⟩
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · rintro ⟨O, ⟨_, hOA⟩, hiO⟩; exact hOA hiO
    · intro hiA
      refine ⟨orbitOf K i, ⟨mem_orbitSet_iff.mpr ⟨i, rfl⟩, fun j hj => ?_⟩,
        mem_orbitOf_self K i⟩
      obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
      rw [← hA g hg]
      exact Finset.mem_map_of_mem _ hiA
  · rintro ⟨S, hS, rfl⟩ g hg
    ext i
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨j, ⟨O, hOS, hjO⟩, rfl⟩
      refine ⟨O, hOS, ?_⟩
      obtain ⟨k, rfl⟩ := mem_orbitSet_iff.mp (hS hOS)
      obtain ⟨g₀, hg₀, rfl⟩ := mem_orbitOf_iff.mp hjO
      exact mem_orbitOf_iff.mpr ⟨g * g₀, K.mul_mem hg hg₀, rfl⟩
    · rintro ⟨O, hOS, hiO⟩
      refine ⟨g⁻¹ i, ⟨O, hOS, ?_⟩, by simp⟩
      obtain ⟨k, rfl⟩ := mem_orbitSet_iff.mp (hS hOS)
      obtain ⟨g₀, hg₀, rfl⟩ := mem_orbitOf_iff.mp hiO
      exact mem_orbitOf_iff.mpr ⟨g⁻¹ * g₀, K.mul_mem (K.inv_mem hg) hg₀, rfl⟩

def orbitSubsets (K : Subgroup (Equiv.Perm (Fin 6))) (m : ℕ) : Finset (Finset (Finset (Fin 6))) :=
  (orbitSet K).powerset.filter (fun S => (∑ O ∈ S, O.card) = m)

@[simp] lemma mem_orbitSubsets_iff {K : Subgroup (Equiv.Perm (Fin 6))} {m : ℕ}
    {S : Finset (Finset (Fin 6))} :
    S ∈ orbitSubsets K m ↔ S ⊆ orbitSet K ∧ (∑ O ∈ S, O.card) = m := by
  simp [orbitSubsets]

attribute [irreducible] orbitSubsets

lemma mem_orbitSet_subset_card_sum {K : Subgroup (Equiv.Perm (Fin 6))}
    {S : Finset (Finset (Fin 6))} (hS : S ⊆ orbitSet K) :
    (S.biUnion id).card = ∑ O ∈ S, O.card :=
  Finset.card_biUnion ((orbitSet_pairwiseDisjoint K).subset (Finset.coe_subset.mpr hS))

lemma card_fixedCaps_eq_orbitSubsets (K : Subgroup (Equiv.Perm (Fin 6)))
    {m : ℕ} (hm1 : 1 ≤ m) (hm3 : m ≤ 3) :
    (fixedCaps K m).card = (orbitSubsets K m).card := by
  have heq : Fintype.card (orbitSubsets K m) = Fintype.card (fixedCaps K m) := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun S => ⟨⟨S.1.biUnion id, by
          have hS := mem_orbitSubsets_iff.mp S.2
          rw [mem_orbitSet_subset_card_sum hS.1, hS.2]
          exact ⟨hm1, hm3⟩⟩, ?_⟩
        invFun := fun A => ⟨(orbitSet K).filter (fun O => O ⊆ A.1.val), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hS := mem_orbitSubsets_iff.mp S.2
      refine mem_fixedCaps_iff.mpr ⟨?_, fun g hg => Subtype.ext ?_⟩
      · exact (mem_orbitSet_subset_card_sum hS.1).trans hS.2
      · exact (cap_fixed_iff_union_orbits K (S.1.biUnion id)).mpr ⟨S.1, hS.1, rfl⟩ g hg
    · have hA := mem_fixedCaps_iff.mp A.2
      have hfix : ∀ g ∈ K, A.1.val.map g.toEmbedding = A.1.val := fun g hg =>
        congrArg Subtype.val (hA.2 g hg)
      have hunion : ((orbitSet K).filter (fun O => O ⊆ A.1.val)).biUnion id = A.1.val := by
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
        constructor
        · rintro ⟨O, ⟨_, hOA⟩, hiO⟩; exact hOA hiO
        · intro hiA
          refine ⟨orbitOf K i, ⟨mem_orbitSet_iff.mpr ⟨i, rfl⟩, fun j hj => ?_⟩,
            mem_orbitOf_self K i⟩
          obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
          rw [← hfix g hg]
          exact Finset.mem_map_of_mem _ hiA
      refine mem_orbitSubsets_iff.mpr ⟨Finset.filter_subset _ _, ?_⟩
      rw [← mem_orbitSet_subset_card_sum (Finset.filter_subset _ _), hunion, hA.1]
    · intro S
      apply Subtype.ext
      have hS := mem_orbitSubsets_iff.mp S.2
      ext O
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hO, hOsub⟩
        have hne : O.Nonempty := by
          obtain ⟨k, rfl⟩ := mem_orbitSet_iff.mp hO
          exact orbitOf_nonempty K k
        obtain ⟨i, hiO⟩ := hne
        have hiU : i ∈ S.1.biUnion id := hOsub hiO
        obtain ⟨O', hO'S, hiO'⟩ := Finset.mem_biUnion.mp hiU
        have heqO : O = O' := by
          by_contra hneO
          exact Finset.disjoint_left.mp (orbitSet_pairwiseDisjoint K hO (hS.1 hO'S) hneO) hiO hiO'
        rwa [heqO]
      · intro hOS
        refine ⟨hS.1 hOS, ?_⟩
        intro i hiO
        exact Finset.mem_biUnion.mpr ⟨O, hOS, hiO⟩
    · intro A
      apply Subtype.ext; apply Subtype.ext
      have hA := mem_fixedCaps_iff.mp A.2
      have hfix : ∀ g ∈ K, A.1.val.map g.toEmbedding = A.1.val := fun g hg =>
        congrArg Subtype.val (hA.2 g hg)
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
      constructor
      · rintro ⟨O, ⟨_, hOA⟩, hiO⟩; exact hOA hiO
      · intro hiA
        refine ⟨orbitOf K i, ⟨mem_orbitSet_iff.mpr ⟨i, rfl⟩, fun j hj => ?_⟩,
          mem_orbitOf_self K i⟩
        obtain ⟨g, hg, rfl⟩ := mem_orbitOf_iff.mp hj
        rw [← hfix g hg]
        exact Finset.mem_map_of_mem _ hiA
  simpa only [Fintype.card_coe] using heq.symm

lemma card_fixedCaps_one {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    (fixedCaps K 1).card = orbitCount K 1 := by
  rw [card_fixedCaps_eq_orbitSubsets K (by omega) (by omega)]
  let O1 := (orbitSet K).filter (fun O => O.card = 1)
  have hpart : orbitSubsets K 1 = O1.image (fun O => ({O} : Finset (Finset (Fin 6)))) := by
    ext S
    simp only [mem_orbitSubsets_iff, O1, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hS, hsum⟩
      have hex1 : ∃ O ∈ S, O.card = 1 := by
        have hne : S.Nonempty := by
          by_contra he
          rw [Finset.not_nonempty_iff_eq_empty.mp he] at hsum
          simp at hsum
        obtain ⟨O, hOS⟩ := hne
        refine ⟨O, hOS, ?_⟩
        have hle1 : O.card ≤ 1 := by
          have := Finset.single_le_sum (f := fun X : Finset (Fin 6) => X.card)
            (fun _ _ => Nat.zero_le _) hOS
          omega
        have hpos : 1 ≤ O.card := by
          rcases orbitOf_card_mem_124 hK (hS hOS) with c | c | c <;> omega
        omega
      obtain ⟨O, hOS, hO1⟩ := hex1
      refine ⟨O, ⟨hS hOS, hO1⟩, ?_⟩
      ext X
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl; exact hOS
      · intro hXS
        by_contra hne
        have hpair : {O, X} ⊆ S := Finset.insert_subset hOS (Finset.singleton_subset_iff.mpr hXS)
        have hpos : 1 ≤ X.card := by
          rcases orbitOf_card_mem_124 hK (hS hXS) with c | c | c <;> omega
        have hle := Finset.sum_le_sum_of_subset (f := fun Y : Finset (Fin 6) => Y.card) hpair
        rw [Finset.sum_pair (Ne.symm hne)] at hle
        omega
    · rintro ⟨O, ⟨hO, hO1⟩, rfl⟩
      exact ⟨Finset.singleton_subset_iff.mpr hO, by simp [hO1]⟩
  rw [hpart, Finset.card_image_of_injective O1 Finset.singleton_injective]
  rfl

lemma card_fixedCaps_two {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    (fixedCaps K 2).card = (orbitCount K 1).choose 2 + orbitCount K 2 := by
  rw [card_fixedCaps_eq_orbitSubsets K (by omega) (by omega)]
  let O1 := (orbitSet K).filter (fun O => O.card = 1)
  let O2 := (orbitSet K).filter (fun O => O.card = 2)
  let A := O1.powersetCard 2
  let B := O2.image (fun O => ({O} : Finset (Finset (Fin 6))))
  have hpart : orbitSubsets K 2 = A ∪ B := by
    ext S
    simp only [mem_orbitSubsets_iff, A, B, O1, O2, Finset.mem_filter,
      Finset.mem_union, Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨hS, hsum⟩
      have hno4 : ∀ O ∈ S, O.card ≠ 4 := fun O hO h4 => by
        have := Finset.single_le_sum (f := fun X : Finset (Fin 6) => X.card) (fun _ _ => Nat.zero_le _) hO
        omega
      by_cases hex2 : ∃ O ∈ S, O.card = 2
      · right
        obtain ⟨O, hOS, hO2⟩ := hex2
        refine ⟨O, ⟨hS hOS, hO2⟩, ?_⟩
        ext X
        simp only [Finset.mem_singleton]
        constructor
        · rintro rfl; exact hOS
        · intro hXS
          by_contra hne
          have hpair : {O, X} ⊆ S := Finset.insert_subset hOS (Finset.singleton_subset_iff.mpr hXS)
          have hpos : 1 ≤ X.card := by
            rcases orbitOf_card_mem_124 hK (hS hXS) with c | c | c <;> omega
          have hsum2 : ∑ Y ∈ ({O, X} : Finset (Finset (Fin 6))), Y.card ≤ ∑ Y ∈ S, Y.card :=
            Finset.sum_le_sum_of_subset hpair
          rw [Finset.sum_pair (Ne.symm hne)] at hsum2
          omega
      · left
        have h1 : ∀ O ∈ S, O.card = 1 := fun O hO => by
          rcases orbitOf_card_mem_124 hK (hS hO) with c | c | c
          · exact c
          · exact absurd ⟨O, hO, c⟩ hex2
          · exact absurd c (hno4 O hO)
        refine ⟨fun O hO => Finset.mem_filter.mpr ⟨hS hO, h1 O hO⟩, ?_⟩
        have hs : ∑ O ∈ S, O.card = ∑ _ ∈ S, 1 := Finset.sum_congr rfl fun O hO => h1 O hO
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
        omega
    · rintro (⟨hS1, hcard⟩ | ⟨O, ⟨hO, hO2⟩, rfl⟩)
      · refine ⟨fun O hO => (Finset.mem_filter.mp (hS1 hO)).1, ?_⟩
        have hs : ∑ O ∈ S, O.card = ∑ _ ∈ S, 1 :=
          Finset.sum_congr rfl fun O hO => (Finset.mem_filter.mp (hS1 hO)).2
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
        omega
      · exact ⟨Finset.singleton_subset_iff.mpr hO, by simp [hO2]⟩
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun S hSA hSB => by
    have hcard := (Finset.mem_powersetCard.mp hSA).2
    obtain ⟨O, _, rfl⟩ := Finset.mem_image.mp hSB
    simp at hcard
  rw [hpart, Finset.card_union_of_disjoint hdisj]
  congr 1
  · exact Finset.card_powersetCard 2 O1
  · exact Finset.card_image_of_injective O2 Finset.singleton_injective

lemma card_fixedCaps_three {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    (fixedCaps K 3).card = (orbitCount K 1).choose 3 + orbitCount K 1 * orbitCount K 2 := by
  rw [card_fixedCaps_eq_orbitSubsets K (by omega) (by omega)]
  let O1 := (orbitSet K).filter (fun O => O.card = 1)
  let O2 := (orbitSet K).filter (fun O => O.card = 2)
  let A := O1.powersetCard 3
  let B := (O1 ×ˢ O2).image (fun p => ({p.1, p.2} : Finset (Finset (Fin 6))))
  have hpart : orbitSubsets K 3 = A ∪ B := by
    ext S
    simp only [mem_orbitSubsets_iff, A, B, O1, O2, Finset.mem_filter,
      Finset.mem_union, Finset.mem_powersetCard, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨hS, hsum⟩
      have hno4 : ∀ O ∈ S, O.card ≠ 4 := fun O hO h4 => by
        have := Finset.single_le_sum (f := fun X : Finset (Fin 6) => X.card) (fun _ _ => Nat.zero_le _) hO
        omega
      by_cases hex2 : ∃ O ∈ S, O.card = 2
      · right
        obtain ⟨O₂, hO₂S, hO₂c⟩ := hex2
        have hrem : ∑ Y ∈ S.erase O₂, Y.card = 1 := by
          have := Finset.add_sum_erase S (fun Y : Finset (Fin 6) => Y.card) hO₂S
          omega
        have hex1 : ∃ O₁ ∈ S.erase O₂, O₁.card = 1 := by
          have hne : (S.erase O₂).Nonempty := by
            by_contra he
            rw [Finset.not_nonempty_iff_eq_empty.mp he] at hrem
            simp at hrem
          obtain ⟨O₁, hO₁⟩ := hne
          refine ⟨O₁, hO₁, ?_⟩
          have hle1 : O₁.card ≤ 1 := by
            have := Finset.single_le_sum (f := fun Y : Finset (Fin 6) => Y.card)
              (fun _ _ => Nat.zero_le _) hO₁
            omega
          have hpos : 1 ≤ O₁.card := by
            rcases orbitOf_card_mem_124 hK (hS (Finset.mem_of_mem_erase hO₁)) with c | c | c <;> omega
          omega
        obtain ⟨O₁, hO₁er, hO₁c⟩ := hex1
        have hO₁S : O₁ ∈ S := Finset.mem_of_mem_erase hO₁er
        have hne12 : O₁ ≠ O₂ := Finset.ne_of_mem_erase hO₁er
        refine ⟨(O₁, O₂), ⟨⟨hS hO₁S, hO₁c⟩, ⟨hS hO₂S, hO₂c⟩⟩, ?_⟩
        ext X
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl) <;> assumption
        · intro hXS
          by_contra hnot
          have hnot1 : X ≠ O₁ := fun h => hnot (Or.inl h)
          have hnot2 : X ≠ O₂ := fun h => hnot (Or.inr h)
          have hpair3 : ({O₁, O₂, X} : Finset (Finset (Fin 6))) ⊆ S := by
            intro Z hZ
            rcases Finset.mem_insert.mp hZ with rfl | hZ
            · exact hO₁S
            · rcases Finset.mem_insert.mp hZ with rfl | hZ
              · exact hO₂S
              · rw [Finset.mem_singleton.mp hZ]; exact hXS
          have hXpos : 1 ≤ X.card := by
            rcases orbitOf_card_mem_124 hK (hS hXS) with c | c | c <;> omega
          have hle := Finset.sum_le_sum_of_subset (f := fun Y : Finset (Fin 6) => Y.card) hpair3
          have hsum3 : ∑ Z ∈ ({O₁, O₂, X} : Finset (Finset (Fin 6))), Z.card =
              O₁.card + O₂.card + X.card := by
            rw [Finset.sum_insert, Finset.sum_pair (Ne.symm hnot2)]
            · ring
            · simp [hne12, hnot1.symm]
          omega
      · left
        have h1 : ∀ O ∈ S, O.card = 1 := fun O hO => by
          rcases orbitOf_card_mem_124 hK (hS hO) with c | c | c
          · exact c
          · exact absurd ⟨O, hO, c⟩ hex2
          · exact absurd c (hno4 O hO)
        refine ⟨fun O hO => Finset.mem_filter.mpr ⟨hS hO, h1 O hO⟩, ?_⟩
        have hs : ∑ O ∈ S, O.card = ∑ _ ∈ S, 1 := Finset.sum_congr rfl fun O hO => h1 O hO
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
        omega
    · rintro (⟨hS1, hcard⟩ | ⟨⟨O₁, O₂⟩, ⟨⟨h1, h1c⟩, ⟨h2, h2c⟩⟩, rfl⟩)
      · refine ⟨fun O hO => (Finset.mem_filter.mp (hS1 hO)).1, ?_⟩
        have hs : ∑ O ∈ S, O.card = ∑ _ ∈ S, 1 :=
          Finset.sum_congr rfl fun O hO => (Finset.mem_filter.mp (hS1 hO)).2
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
        omega
      · refine ⟨fun X hX => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hX with rfl | hX
          · exact h1
          · rw [Finset.mem_singleton.mp hX]; exact h2
        · have hne : O₁ ≠ O₂ := fun h => by
            have h1c' : O₁.card = 1 := h1c
            have h2c' : O₂.card = 2 := h2c
            rw [h] at h1c'
            exact absurd (h1c'.symm.trans h2c') (by decide)
          have h1c' : O₁.card = 1 := h1c
          have h2c' : O₂.card = 2 := h2c
          rw [Finset.sum_pair hne, h1c', h2c']
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun S hSA hSB => by
    have hcard := (Finset.mem_powersetCard.mp hSA).2
    obtain ⟨⟨O₁, O₂⟩, hmem, rfl⟩ := Finset.mem_image.mp hSB
    simp only [Finset.mem_product, O1, O2, Finset.mem_filter] at hmem
    rcases hmem with ⟨⟨_, h1c⟩, ⟨_, h2c⟩⟩
    have h1c' : O₁.card = 1 := h1c
    have h2c' : O₂.card = 2 := h2c
    have hne : O₁ ≠ O₂ := fun h => by
      rw [h] at h1c'
      exact absurd (h1c'.symm.trans h2c') (by decide)
    rw [Finset.card_pair hne] at hcard
    omega
  rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_powersetCard 3 O1]
  congr 1
  rw [Finset.card_image_iff.mpr ?_, Finset.card_product]
  · rfl
  · intro p hp q hq hpq
    dsimp only at hpq
    simp only [Finset.mem_coe, Finset.mem_product, O1, O2, Finset.mem_filter] at hp hq
    have hp1_in : p.1 ∈ ({q.1, q.2} : Finset (Finset (Fin 6))) := by
      rw [← hpq]; exact Finset.mem_insert_self _ _
    have hp2_in : p.2 ∈ ({q.1, q.2} : Finset (Finset (Fin 6))) := by
      rw [← hpq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h1 : p.1 = q.1 := by
      rcases Finset.mem_insert.mp hp1_in with h | h
      · exact h
      · exfalso; have hmem := Finset.mem_singleton.mp h
        have c1 : p.1.card = 1 := hp.1.2
        have c2 : q.2.card = 2 := hq.2.2
        rw [hmem] at c1
        exact absurd (c1.symm.trans c2) (by decide)
    have h2 : p.2 = q.2 := by
      rcases Finset.mem_insert.mp hp2_in with h | h
      · exfalso
        have c1 : p.2.card = 2 := hp.2.2
        have c2 : q.1.card = 1 := hq.1.2
        rw [h] at c1
        exact absurd (c1.symm.trans c2) (by decide)
      · exact Finset.mem_singleton.mp h
    exact Prod.ext h1 h2

lemma orbitOf_P_row_4 : orbitOf P_row 4 = {4, 5} := by
  ext j
  simp only [mem_orbitOf_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨g, hg, hj_eq⟩
    have hj : 4 ≤ j.1 := by rw [← hj_eq]; exact P_row_preserves_ge4 hg (by decide : 4 ≤ (4 : Fin 6).1)
    fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨1, P_row.one_mem, rfl⟩
    · exact ⟨genSwap45.1, genSwap45.2, rfl⟩

lemma orbitOf_P_row_0 : orbitOf P_row 0 = {0, 1, 2, 3} := by
  ext j
  simp only [mem_orbitOf_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨g, hg, hj_eq⟩
    have hj : j.1 < 4 := by rw [← hj_eq]; exact hg.1 0 (by decide)
    fin_cases j <;> simp_all
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, P_row.one_mem, rfl⟩
    · exact ⟨genSwap01_23.1, genSwap01_23.2, rfl⟩
    · exact ⟨genSwap02.1, genSwap02.2, rfl⟩
    · refine ⟨(genSwap13 * genSwap01_23).1, P_row.mul_mem genSwap13.2 genSwap01_23.2, ?_⟩
      decide

def fixedBubbleDegree (K : Subgroup (Equiv.Perm (Fin 6))) : ℤ :=
  1 - ((fixedCaps K 1).card : ℤ) - ((fixedCaps K 2).card : ℤ) + ((fixedCaps K 3).card : ℤ)

theorem fixedBubbleDegree_eq_bubbleDegree {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    fixedBubbleDegree K = PlanarMarksArithmetic.bubbleDegree (orbitCount K 1) (orbitCount K 2) := by
  unfold fixedBubbleDegree PlanarMarksArithmetic.bubbleDegree
  rw [card_fixedCaps_one hK, card_fixedCaps_two hK, card_fixedCaps_three hK]
  push_cast
  ring

theorem fixedBubbleDegree_mem {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    fixedBubbleDegree K = 0 ∨ fixedBubbleDegree K = -2 := by
  rw [fixedBubbleDegree_eq_bubbleDegree hK]
  exact PlanarMarksArithmetic.bubbleDegree_eq_zero_or_neg_two (orbitCount_sum_six hK)

theorem fixedBubbleDegree_pow_seven {K : Subgroup (Equiv.Perm (Fin 6))} (hK : K ≤ P_row) :
    (fixedBubbleDegree K) ^ 7 = 64 * fixedBubbleDegree K := by
  rw [fixedBubbleDegree_eq_bubbleDegree hK]
  exact PlanarMarksArithmetic.seventh_power_bubbleDegree (orbitCount_sum_six hK)

theorem fixedBubbleDegree_P_row : fixedBubbleDegree P_row = 0 := by
  have h1 : orbitCount P_row 1 = 0 := by
    rw [orbitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro O hO
    obtain ⟨i, rfl⟩ := mem_orbitSet_iff.mp hO
    intro hc1
    have hgt : 1 < (orbitOf P_row i).card := by
      fin_cases i
      · refine Finset.one_lt_card.mpr ⟨(0 : Fin 6), mem_orbitOf_self _ _, (2 : Fin 6),
          mem_orbitOf_iff.mpr ⟨genSwap02.1, genSwap02.2, rfl⟩, by decide⟩
      · refine Finset.one_lt_card.mpr ⟨(1 : Fin 6), mem_orbitOf_self _ _, (3 : Fin 6),
          mem_orbitOf_iff.mpr ⟨genSwap13.1, genSwap13.2, rfl⟩, by decide⟩
      · refine Finset.one_lt_card.mpr ⟨(2 : Fin 6), mem_orbitOf_self _ _, (0 : Fin 6),
          mem_orbitOf_iff.mpr ⟨genSwap02.1, genSwap02.2, rfl⟩, by decide⟩
      · refine Finset.one_lt_card.mpr ⟨(3 : Fin 6), mem_orbitOf_self _ _, (1 : Fin 6),
          mem_orbitOf_iff.mpr ⟨genSwap13.1, genSwap13.2, rfl⟩, by decide⟩
      · refine Finset.one_lt_card.mpr ⟨(4 : Fin 6), mem_orbitOf_self _ _, (5 : Fin 6),
          mem_orbitOf_iff.mpr ⟨genSwap45.1, genSwap45.2, rfl⟩, by decide⟩
      · refine Finset.one_lt_card.mpr ⟨(5 : Fin 6), mem_orbitOf_self _ _, (4 : Fin 6),
          mem_orbitOf_iff.mpr ⟨genSwap45.1, genSwap45.2, rfl⟩, by decide⟩
    omega
  have h2 : orbitCount P_row 2 = 1 := by
    have hsum := orbitCount_sum_six (K := P_row) le_rfl
    rw [h1] at hsum
    have hpos : 0 < orbitCount P_row 2 := by
      rw [orbitCount, Finset.card_pos]
      refine ⟨orbitOf P_row 4, Finset.mem_filter.mpr
        ⟨mem_orbitSet_iff.mpr ⟨4, rfl⟩, ?_⟩⟩
      rw [orbitOf_P_row_4]; decide
    have hpos4 : 0 < orbitCount P_row 4 := by
      rw [orbitCount, Finset.card_pos]
      refine ⟨orbitOf P_row 0, Finset.mem_filter.mpr
        ⟨mem_orbitSet_iff.mpr ⟨0, rfl⟩, ?_⟩⟩
      rw [orbitOf_P_row_0]; decide
    omega
  rw [fixedBubbleDegree_eq_bubbleDegree le_rfl, h1, h2]
  norm_num [PlanarMarksArithmetic.bubbleDegree]

end OrbitCountFormula

/-! ### 5. Explicit `S¹` null-homotopy of `q0` on `S(V^{P_row})` rel `anchorS` -/

section CircleNullHomotopy

abbrev FixedP_row := {x : Metric.sphere (0 : Rep10) 1 // x.1 ∈ fixedSubspace P_row}

lemma q0_fixed_mem (K : Subgroup (Equiv.Perm (Fin 6))) (x : Metric.sphere (0 : Rep10) 1)
    (hx : x.1 ∈ fixedSubspace K) : (q0 x).1 ∈ fixedSubspace K := by
  intro g hg
  change (permSphere g (q0 x) : Rep10) = (q0 x : Rep10)
  rw [← q0_equivariant]
  have hxp : permSphere g x = x := Subtype.ext (hx g hg)
  rw [hxp]

def anchorS_P_row : FixedP_row :=
  ⟨anchorS, anchor10_mem_fixedSubspace_of_le_P_row le_rfl⟩

def q0RestrictedP_row : C(FixedP_row, FixedP_row) where
  toFun x := ⟨q0 x.1, q0_fixed_mem P_row x.1 x.2⟩
  continuous_toFun := (q0.continuous.comp continuous_subtype_val).subtype_mk _

def circleParamVec (θ : ℝ) : Rep10 :=
  Real.cos θ • cA0 + Real.sin θ • anchor10

lemma norm_circleParamVec (θ : ℝ) : ‖circleParamVec θ‖ = 1 := by
  have hsq : ‖circleParamVec θ‖ ^ 2 = 1 := by
    rw [circleParamVec, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      norm_cA0, norm_anchor10, mul_one, mul_one, sq_abs, sq_abs,
      inner_smul_left, inner_smul_right, inner_cA0_anchor10]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  nlinarith [norm_nonneg (circleParamVec θ)]

lemma circleParamVec_mem_fixedSubspace (θ : ℝ) :
    circleParamVec θ ∈ fixedSubspace P_row := by
  rw [circleParamVec]
  exact (fixedSubspace P_row).add_mem
    ((fixedSubspace P_row).smul_mem _ (cA0_mem_fixedSubspace_of_le_P_row le_rfl))
    ((fixedSubspace P_row).smul_mem _ (anchor10_mem_fixedSubspace_of_le_P_row le_rfl))

def circleParam (θ : ℝ) : FixedP_row :=
  ⟨⟨circleParamVec θ, mem_sphere_zero_iff_norm.mpr (norm_circleParamVec θ)⟩,
    circleParamVec_mem_fixedSubspace θ⟩

@[simp] lemma circleParam_val (θ : ℝ) : (circleParam θ).1.1 = circleParamVec θ := rfl

lemma circleParam_pi_div_two : circleParam (Real.pi / 2) = anchorS_P_row := by
  apply Subtype.ext; apply Subtype.ext
  simp [circleParam, circleParamVec, anchorS_P_row, anchorS]

lemma continuous_circleParam : Continuous circleParam := by
  change Continuous (fun θ : ℝ => (⟨⟨circleParamVec θ, _⟩, _⟩ : FixedP_row))
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  unfold circleParamVec
  exact (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

def circleEquivFixedP_row : Circle ≃ₜ FixedP_row where
  toFun z := ⟨⟨(z : ℂ).re • cA0 + (z : ℂ).im • anchor10, mem_sphere_zero_iff_norm.mpr (by
    have hre : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
    have hsq : ‖(z : ℂ).re • cA0 + (z : ℂ).im • anchor10‖ ^ 2 = 1 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        norm_cA0, norm_anchor10, mul_one, mul_one, sq_abs, sq_abs,
        inner_smul_left, inner_smul_right, inner_cA0_anchor10]
      nlinarith
    nlinarith [norm_nonneg ((z : ℂ).re • cA0 + (z : ℂ).im • anchor10)])⟩,
    (fixedSubspace P_row).add_mem
      ((fixedSubspace P_row).smul_mem _ (cA0_mem_fixedSubspace_of_le_P_row le_rfl))
      ((fixedSubspace P_row).smul_mem _ (anchor10_mem_fixedSubspace_of_le_P_row le_rfl))⟩
  invFun y := ⟨(⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I, by
    change _ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    have h := normSq_anchorPhaseFun y.2
    rw [Complex.normSq_apply, anchorPhaseFun_re, anchorPhaseFun_im, ← pow_two, ← pow_two] at h
    have hns : Complex.normSq ((⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I) = 1 := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, mul_zero, zero_add, ← pow_two]
      linarith
    rw [Complex.normSq_eq_norm_sq] at hns
    nlinarith [norm_nonneg ((⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I)]⟩
  left_inv z := by
    apply Subtype.ext; apply Complex.ext
    · change ((⟪cA0, (z : ℂ).re • cA0 + (z : ℂ).im • anchor10⟫_ℝ : ℂ) +
        (⟪anchor10, (z : ℂ).re • cA0 + (z : ℂ).im • anchor10⟫_ℝ : ℂ) * Complex.I).re = (z : ℂ).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, sub_zero, add_zero]
      rw [inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10]
      ring
    · change ((⟪cA0, (z : ℂ).re • cA0 + (z : ℂ).im • anchor10⟫_ℝ : ℂ) +
        (⟪anchor10, (z : ℂ).re • cA0 + (z : ℂ).im • anchor10⟫_ℝ : ℂ) * Complex.I).im = (z : ℂ).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
        Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
      rw [inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, norm_anchor10, inner_anchor10_cA0]
      ring
  right_inv y := by
    apply Subtype.ext; apply Subtype.ext
    have hre : (((⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I)).re = ⟪cA0, y.1.1⟫_ℝ := by
      simp
    have him : (((⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I)).im = ⟪anchor10, y.1.1⟫_ℝ := by
      simp
    change (((⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I)).re • cA0 +
        (((⟪cA0, y.1.1⟫_ℝ : ℂ) + (⟪anchor10, y.1.1⟫_ℝ : ℂ) * Complex.I)).im • anchor10 = y.1.1
    rw [hre, him]
    simpa [add_comm] using ((fixedSubspace_P_row_eq_span y.1.1).mp y.2).symm
  continuous_toFun := by
    apply Continuous.subtype_mk; apply Continuous.subtype_mk
    exact ((Complex.continuous_re.comp continuous_subtype_val).smul continuous_const).add
      ((Complex.continuous_im.comp continuous_subtype_val).smul continuous_const)
  continuous_invFun := by
    have h1 : Continuous (fun y : FixedP_row => (⟪cA0, y.1.1⟫_ℝ : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.inner (continuous_subtype_val.comp continuous_subtype_val))
    have h2 : Continuous (fun y : FixedP_row => (⟪anchor10, y.1.1⟫_ℝ : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.inner (continuous_subtype_val.comp continuous_subtype_val))
    exact Continuous.subtype_mk (h1.add (h2.mul continuous_const)) _

def addCircleEquivFixedP_row : AddCircle (2 * Real.pi) ≃ₜ FixedP_row :=
  AddCircle.homeomorphCircle'.trans circleEquivFixedP_row

lemma addCircleEquivFixedP_row_apply_coe (θ : ℝ) :
    addCircleEquivFixedP_row (θ : AddCircle (2 * Real.pi)) = circleParam θ := by
  apply Subtype.ext; apply Subtype.ext
  change (Circle.exp θ : ℂ).re • cA0 + (Circle.exp θ : ℂ).im • anchor10 = circleParamVec θ
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rfl

lemma unique_fixed_cap_P_row {A : InvariantCaps.CapLabel}
    (hA : ∀ g ∈ P_row, permCap g A = A) : A = cap45 := by
  have hc := (cap_fixed_iff_union_orbits P_row A.val).mp
    (fun g hg => congrArg Subtype.val (hA g hg))
  obtain ⟨S, hSsub, hSunion⟩ := hc
  have hcardA : 1 ≤ A.val.card ∧ A.val.card ≤ 3 := A.property
  have hsum : ∑ O ∈ S, O.card = A.val.card := by
    rw [← hSunion, mem_orbitSet_subset_card_sum hSsub]
  have horb_cases : ∀ O ∈ orbitSet P_row, O = {0, 1, 2, 3} ∨ O = {4, 5} := by
    intro O hO
    obtain ⟨i, rfl⟩ := mem_orbitSet_iff.mp hO
    have hm : i ∈ orbitOf P_row 0 ∨ i ∈ orbitOf P_row 4 := by
      rw [orbitOf_P_row_0, orbitOf_P_row_4]; fin_cases i <;> simp
    rcases hm with hi | hi
    · left; rw [← orbitOf_P_row_0]; exact orbitOf_eq_of_mem hi
    · right; rw [← orbitOf_P_row_4]; exact orbitOf_eq_of_mem hi
  have hnot0 : ({0, 1, 2, 3} : Finset (Fin 6)) ∉ S := fun hmem => by
    have hle := Finset.single_le_sum (f := fun O : Finset (Fin 6) => O.card)
      (fun _ _ => Nat.zero_le _) hmem
    have hc4 : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 := by decide
    omega
  have hsub45 : S ⊆ {({4, 5} : Finset (Fin 6))} := fun O hOS => by
    rcases horb_cases O (hSsub hOS) with rfl | rfl
    · exact absurd hOS hnot0
    · exact Finset.mem_singleton_self _
  have hne : S.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hsum
    simp at hsum
    omega
  have hSeq : S = {({4, 5} : Finset (Fin 6))} :=
    (Finset.subset_singleton_iff.mp hsub45).resolve_left hne.ne_empty
  apply Subtype.ext
  rw [← hSunion, hSeq]
  decide

lemma norm_sub_cA_ge_of_ne_cap45 {x : FixedP_row} {B : InvariantCaps.CapLabel}
    (hB : B ≠ cap45) : capChord (2 * capDelta0 / 3) ≤ ‖(x.1 : Rep10) - cA B‖ := by
  by_contra hlt
  push Not at hlt
  have hd0 : 0 < capDelta0 := capDelta0_pos
  have hlt3 : ‖(x.1 : Rep10) - cA B‖ < capChord (3 * capDelta0 / 4) :=
    lt_trans hlt (capChord_strictMono (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have hfix : ∀ g ∈ P_row, permCap g B = B := by
    intro g hg
    by_contra hne
    have h1 : ‖(x.1 : Rep10) - cA (permCap g B)‖ < capChord (3 * capDelta0 / 4) := by
      rw [← perm10_cA, ← x.2 g hg, ← map_sub, (perm10 g).norm_map]
      exact hlt3
    exact caps_disjoint_chord (Ne.symm hne) hlt3 h1
  exact hB (unique_fixed_cap_P_row hfix)

def theta0 : ℝ := 2 * Real.arcsin (capChord (2 * capDelta0 / 3) / 2)

lemma capChord_theta0_bounds :
    0 < capChord (2 * capDelta0 / 3) / 2 ∧ capChord (2 * capDelta0 / 3) / 2 < 1 / 2 := by
  have hd0 := capDelta0_pos
  have hd1 := capDelta0_lt
  have hc0 : 0 < capChord (2 * capDelta0 / 3) := capChord_pos (by linarith)
  have hc1 : capChord (2 * capDelta0 / 3) < 2 * capDelta0 / 3 := capChord_lt_self (by linarith)
  constructor <;> linarith

lemma theta0_pos : 0 < theta0 := by
  have ⟨h0, _⟩ := capChord_theta0_bounds
  have : 0 < Real.arcsin (capChord (2 * capDelta0 / 3) / 2) := Real.arcsin_pos.mpr h0
  unfold theta0
  linarith

lemma theta0_lt_pi_div_three : theta0 < Real.pi / 3 := by
  have ⟨h0, h1⟩ := capChord_theta0_bounds
  have hlt : Real.arcsin (capChord (2 * capDelta0 / 3) / 2) < Real.arcsin (1 / 2) :=
    Real.arcsin_lt_arcsin (by linarith) h1 (by norm_num)
  have harc : Real.arcsin (1 / 2) = Real.pi / 6 :=
    Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [harc] at hlt
  unfold theta0
  linarith

lemma sin_theta0_half : Real.sin (theta0 / 2) = capChord (2 * capDelta0 / 3) / 2 := by
  have ⟨h0, h1⟩ := capChord_theta0_bounds
  have harg : theta0 / 2 = Real.arcsin (capChord (2 * capDelta0 / 3) / 2) := by
    unfold theta0; ring
  rw [harg]
  exact Real.sin_arcsin (by linarith) (by linarith)

lemma norm_circleParam_sub_cA0 (θ : ℝ) :
    ‖(circleParam θ).1.1 - cA0‖ = 2 * |Real.sin (θ / 2)| := by
  have hv : (circleParam θ).1.1 - cA0 = (Real.cos θ - 1) • cA0 + Real.sin θ • anchor10 := by
    rw [circleParam_val, circleParamVec]
    module
  have hsq : ‖(circleParam θ).1.1 - cA0‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [hv, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      norm_cA0, norm_anchor10, mul_one, mul_one, sq_abs, sq_abs,
      inner_smul_left, inner_smul_right, inner_cA0_anchor10]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have hc := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring, Real.cos_sq'] at hc
      linarith
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      simpa [show 2 * (θ / 2) = θ by ring] using Real.sin_two_mul (θ / 2)
    have hcs := Real.cos_sq_add_sin_sq (θ / 2)
    simp only [starRingEnd_apply, star_trivial]
    rw [mul_pow, sq_abs, hcos, hsin]
    calc
      (1 - 2 * Real.sin (θ / 2) ^ 2 - 1) ^ 2 +
          2 * ((1 - 2 * Real.sin (θ / 2) ^ 2 - 1) * (2 * Real.sin (θ / 2) * Real.cos (θ / 2) * 0)) +
          (2 * Real.sin (θ / 2) * Real.cos (θ / 2)) ^ 2
          = 4 * Real.sin (θ / 2) ^ 2 * (Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2) := by ring
      _ = 2 ^ 2 * Real.sin (θ / 2) ^ 2 := by rw [add_comm, hcs]; ring
  have hleft : 0 ≤ ‖(circleParam θ).1.1 - cA0‖ := norm_nonneg _
  have hright : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith

lemma q0_circleParam_eq_self {θ : ℝ} (h1 : theta0 ≤ θ) (h2 : θ ≤ 2 * Real.pi - theta0) :
    q0 (circleParam θ).1 = (circleParam θ).1 := by
  have hout0 : capChord (2 * capDelta0 / 3) ≤ ‖(circleParam θ).1.1 - cA0‖ := by
    rw [norm_circleParam_sub_cA0]
    have hth := theta0_pos
    have hth3 := theta0_lt_pi_div_three
    have hsin_ge : Real.sin (theta0 / 2) ≤ Real.sin (θ / 2) := by
      by_cases hmid : θ / 2 ≤ Real.pi / 2
      · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hmid (by linarith)
      · have hmid' : Real.pi / 2 ≤ θ / 2 := le_of_not_ge hmid
        rw [← Real.sin_pi_sub (θ / 2)]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have h0le : 0 ≤ Real.sin (θ / 2) := by
      have : 0 ≤ Real.sin (theta0 / 2) := by rw [sin_theta0_half]; exact capChord_theta0_bounds.1.le
      linarith
    rw [abs_of_nonneg h0le]
    have hs0 := sin_theta0_half
    linarith
  have hout : ∀ B : InvariantCaps.CapLabel,
      capChord (2 * capDelta0 / 3) ≤ ‖(circleParam θ).1.1 - cA B‖ := fun B => by
    by_cases hB : B = cap45
    · rw [hB]; exact hout0
    · exact norm_sub_cA_ge_of_ne_cap45 hB
  have hsp : spherePush (circleParam θ).1 (1 / 2) = (circleParam θ).1.1 :=
    spherePush_eq_self_outside hout (1 / 2)
  apply Subtype.ext
  rw [q0_val, hsp, mem_sphere_zero_iff_norm.mp (circleParam θ).1.2, inv_one, one_smul]

lemma norm_circleParam_lt_of_sin_half {θ : ℝ}
    (hsin : |Real.sin (θ / 2)| ≤ Real.sin (theta0 / 2)) :
    ‖(circleParam θ).1.1 - cA0‖ < capChord (3 * capDelta0 / 4) := by
  rw [norm_circleParam_sub_cA0]
  have hd0 := capDelta0_pos
  have hs0 := sin_theta0_half
  have hle : 2 * |Real.sin (θ / 2)| ≤ capChord (2 * capDelta0 / 3) := by linarith
  exact lt_of_le_of_lt hle (capChord_strictMono (Set.mem_Ici.mpr (by linarith))
    (Set.mem_Ici.mpr (by linarith)) (by linarith))

lemma spherePush_circleParam_inner_anchor {θ : ℝ}
    (hdist : ‖(circleParam θ).1.1 - cA0‖ < capChord (3 * capDelta0 / 4)) :
    ⟪anchor10, (q0 (circleParam θ).1 : Rep10)⟫_ℝ =
      Real.sin θ * (‖spherePush (circleParam θ).1 (1 / 2)‖⁻¹ *
        ((1 - rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖) +
         2 * rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖ / (1 + Real.cos θ))) := by
  have hd0 := capDelta0_pos
  have h2 : ‖(circleParam θ).1.1 - cA0‖ < 2 :=
    hdist.trans ((capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith))
  have hsp : spherePush (circleParam θ).1 (1 / 2) =
      localCapPush cap45 (circleParam θ).1.1 (1 / 2) :=
    spherePush_eq_localCapPush hdist (1 / 2)
  set v := stereoProj cA0 (circleParam θ).1.1
  set ρ := rhoCut ‖v‖
  have hv_eq : stereoProj (cA cap45) (circleParam θ).1.1 = v := rfl
  have hψ : capPsi cap45 v (1 / 2) = v := by
    unfold capPsi
    have hcard : cap45.val.card ≠ 3 := by decide
    simp [hcard]
  have hchart : PlanarTestLocal.capChart cA0 v = (circleParam θ).1.1 :=
    capChart_stereoProj norm_cA0 (norm_circleParamVec θ) h2
  have ht1 : timeCut (1 / 2) = 1 := timeCut_eq_one (by norm_num)
  have hlocal : localCapPush cap45 (circleParam θ).1.1 (1 / 2) =
      (1 - ρ) • (circleParam θ).1.1 + ρ • (cA0 + v) - (2 * ρ) • cA0 := by
    dsimp only [localCapPush]
    rw [hv_eq, hψ, ht1, one_mul, show (cA cap45) = cA0 from rfl, hchart]
    change (1 - ρ) • (circleParam θ).1.1 + ρ • (cA0 + v) - (4 * (1 / 2) * ρ) • cA0 = _
    have h4 : (4 : ℝ) * (1 / 2) * ρ = 2 * ρ := by ring
    rw [h4]
  have hcA_x : ⟪cA0, (circleParam θ).1.1⟫_ℝ = Real.cos θ := by
    rw [circleParam_val, circleParamVec, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10]
    ring
  have ha_x : ⟪anchor10, (circleParam θ).1.1⟫_ℝ = Real.sin θ := by
    rw [circleParam_val, circleParamVec, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_anchor10, inner_anchor10_cA0]
    ring
  have ha_v : ⟪anchor10, v⟫_ℝ = 2 * Real.sin θ / (1 + Real.cos θ) := by
    dsimp only [v, stereoProj]
    rw [hcA_x, inner_smul_right, inner_sub_right, inner_smul_right, ha_x,
      inner_anchor10_cA0, mul_zero, sub_zero]
    ring
  have ha_local : ⟪anchor10, localCapPush cap45 (circleParam θ).1.1 (1 / 2)⟫_ℝ =
      Real.sin θ * ((1 - ρ) + 2 * ρ / (1 + Real.cos θ)) := by
    rw [hlocal, inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_add_right, inner_smul_right, ha_x, inner_anchor10_cA0, ha_v]
    ring
  rw [q0_val, inner_smul_right, hsp, ha_local]
  ring

lemma spherePush_circleParam_factor_pos {θ : ℝ}
    (hdist : ‖(circleParam θ).1.1 - cA0‖ < capChord (3 * capDelta0 / 4)) :
    0 < ‖spherePush (circleParam θ).1 (1 / 2)‖⁻¹ *
      ((1 - rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖) +
       2 * rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖ / (1 + Real.cos θ)) := by
  have hd0 := capDelta0_pos
  have h2 : ‖(circleParam θ).1.1 - cA0‖ < 2 :=
    hdist.trans ((capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith))
  have hcA_x : ⟪cA0, (circleParam θ).1.1⟫_ℝ = Real.cos θ := by
    rw [circleParam_val, circleParamVec, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10]
    ring
  have hcos_pos : 0 < 1 + Real.cos θ := by
    rw [← hcA_x]
    exact one_add_inner_pos_of_norm_sub_lt norm_cA0 (norm_circleParamVec θ) h2
  have hρ0 := rhoCut_nonneg ‖stereoProj cA0 (circleParam θ).1.1‖
  have hρ1 := rhoCut_le_one ‖stereoProj cA0 (circleParam θ).1.1‖
  have hfac : 0 < (1 - rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖) +
      2 * rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖ / (1 + Real.cos θ) := by
    rcases eq_or_lt_of_le hρ0 with h0 | h0
    · rw [← h0]; norm_num
    · have hp1 : 0 ≤ 1 - rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖ := sub_nonneg.mpr hρ1
      have hp2 : 0 < 2 * rhoCut ‖stereoProj cA0 (circleParam θ).1.1‖ / (1 + Real.cos θ) :=
        div_pos (mul_pos (by norm_num) h0) hcos_pos
      linarith
  have hnorm_pos : 0 < ‖spherePush (circleParam θ).1 (1 / 2)‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (spherePush_half_ne_zero (circleParam θ).1))
  exact mul_pos hnorm_pos hfac

lemma q0_circleParam_zero : q0 (circleParam 0).1 = ⟨-cA0, by simp [norm_cA0]⟩ := by
  have hd0 := capDelta0_pos
  have hdist : ‖(circleParam 0).1.1 - cA0‖ < capChord (3 * capDelta0 / 4) := by
    rw [norm_circleParam_sub_cA0]
    simp only [zero_div, Real.sin_zero, abs_zero, mul_zero]
    exact capChord_pos (by positivity)
  have hsp : spherePush (circleParam 0).1 (1 / 2) =
      localCapPush cap45 (circleParam 0).1.1 (1 / 2) :=
    spherePush_eq_localCapPush hdist (1 / 2)
  have hx0 : (circleParam 0).1.1 = cA0 := by simp [circleParam, circleParamVec]
  have hv0 : stereoProj (cA cap45) (circleParam 0).1.1 = 0 := by
    change stereoProj cA0 (circleParam 0).1.1 = 0
    rw [hx0, stereoProj, real_inner_self_eq_norm_sq, norm_cA0]
    norm_num
  have hρ1 : rhoCut ‖stereoProj (cA cap45) (circleParam 0).1.1‖ = 1 := by
    rw [hv0, norm_zero]; exact rhoCut_eq_one (by linarith)
  have hψ0 : capPsi cap45 (stereoProj (cA cap45) (circleParam 0).1.1) (1 / 2) = 0 := by
    unfold capPsi
    have hcard : cap45.val.card ≠ 3 := by decide
    rw [hv0]
    simp only [hcard, ↓reduceIte, sub_self, norm_zero, zero_mul, smul_zero, add_zero]
  have hlocal : localCapPush cap45 (circleParam 0).1.1 (1 / 2) = -cA0 := by
    dsimp only [localCapPush]
    rw [hψ0, hρ1, timeCut_eq_one (by norm_num), one_mul, PlanarTestLocal.capChart_zero]
    show (1 - 1) • (cA0) + 1 • (cA0 + 0) - (4 * (1 / 2) * 1) • cA0 = -cA0
    module
  apply Subtype.ext
  rw [q0_val, hsp, hlocal]
  simp [norm_cA0]

lemma q0_circleParam_two_pi : q0 (circleParam (2 * Real.pi)).1 = ⟨-cA0, by simp [norm_cA0]⟩ := by
  have heq : (circleParam (2 * Real.pi)).1 = (circleParam 0).1 := by
    apply Subtype.ext; simp [circleParam, circleParamVec]
  rw [heq]; exact q0_circleParam_zero

lemma q0_circleParam_inner_cA0_bound (θ : ℝ) :
    -1 ≤ ⟪cA0, (q0 (circleParam θ).1 : Rep10)⟫_ℝ ∧
      ⟪cA0, (q0 (circleParam θ).1 : Rep10)⟫_ℝ ≤ 1 := by
  have hcs := real_inner_le_norm cA0 (q0 (circleParam θ).1 : Rep10)
  have hcs' := real_inner_le_norm (-cA0) (q0 (circleParam θ).1 : Rep10)
  rw [norm_cA0, mem_sphere_zero_iff_norm.mp (q0 (circleParam θ).1).2, mul_one] at hcs
  rw [inner_neg_left, norm_neg, norm_cA0,
    mem_sphere_zero_iff_norm.mp (q0 (circleParam θ).1).2, mul_one] at hcs'
  exact ⟨by linarith, hcs⟩

lemma norm_sub_cA0_le_of_le_theta0 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ theta0) :
    ‖(circleParam θ).1.1 - cA0‖ < capChord (3 * capDelta0 / 4) := by
  apply norm_circleParam_lt_of_sin_half
  have hth := theta0_lt_pi_div_three
  have hsin_nonneg : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [abs_of_nonneg hsin_nonneg]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)

lemma norm_sub_cA0_le_of_ge_two_pi_sub_theta0 {θ : ℝ}
    (h1 : 2 * Real.pi - theta0 ≤ θ) (h2 : θ ≤ 2 * Real.pi) :
    ‖(circleParam θ).1.1 - cA0‖ < capChord (3 * capDelta0 / 4) := by
  apply norm_circleParam_lt_of_sin_half
  have hth := theta0_lt_pi_div_three
  have hsin : |Real.sin (θ / 2)| = Real.sin (Real.pi - θ / 2) := by
    rw [Real.sin_pi_sub]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  rw [hsin]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)

lemma q0_circleParam_pos_arc {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ theta0) :
    0 ≤ ⟪anchor10, (q0 (circleParam θ).1 : Rep10)⟫_ℝ := by
  have hdist := norm_sub_cA0_le_of_le_theta0 h0 h1
  rw [spherePush_circleParam_inner_anchor hdist]
  have hth := theta0_lt_pi_div_three
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  exact mul_nonneg hsin (spherePush_circleParam_factor_pos hdist).le

lemma q0_circleParam_neg_arc {θ : ℝ}
    (h1 : 2 * Real.pi - theta0 ≤ θ) (h2 : θ ≤ 2 * Real.pi) :
    ⟪anchor10, (q0 (circleParam θ).1 : Rep10)⟫_ℝ ≤ 0 := by
  have hdist := norm_sub_cA0_le_of_ge_two_pi_sub_theta0 h1 h2
  rw [spherePush_circleParam_inner_anchor hdist]
  have hth := theta0_lt_pi_div_three
  have hsin : Real.sin θ ≤ 0 := by
    rw [show θ = (θ - 2 * Real.pi) + 2 * Real.pi by ring, Real.sin_add_two_pi]
    have hs : 0 ≤ Real.sin (2 * Real.pi - θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have : θ - 2 * Real.pi = -(2 * Real.pi - θ) := by ring
    rw [this, Real.sin_neg]
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg hsin (spherePush_circleParam_factor_pos hdist).le

def q0AngleLift (θ : ℝ) : ℝ :=
  if θ ≤ theta0 then -2 * Real.pi + Real.arccos ⟪cA0, (q0 (circleParam θ).1 : Rep10)⟫_ℝ
  else if θ ≤ 2 * Real.pi - theta0 then θ - 2 * Real.pi
  else -Real.arccos ⟪cA0, (q0 (circleParam θ).1 : Rep10)⟫_ℝ

lemma continuous_q0AngleLift_on_Icc : ContinuousOn q0AngleLift (Set.Icc 0 (2 * Real.pi)) := by
  have hth0 := theta0_pos
  have hth1 := theta0_lt_pi_div_three
  have hmid : theta0 < 2 * Real.pi - theta0 := by linarith
  let f : ℝ → ℝ := fun θ => ⟪cA0, (q0 (circleParam θ).1 : Rep10)⟫_ℝ
  have hf_cont : Continuous f :=
    continuous_const.inner (continuous_subtype_val.comp
      (q0.continuous.comp (continuous_subtype_val.comp continuous_circleParam)))
  have harccos_cont : Continuous (fun θ => Real.arccos (f θ)) := Real.continuous_arccos.comp hf_cont
  let K1 : Set ℝ := Set.Icc 0 theta0
  let K2 : Set ℝ := Set.Icc theta0 (2 * Real.pi - theta0)
  let K3 : Set ℝ := Set.Icc (2 * Real.pi - theta0) (2 * Real.pi)
  have hcov : Set.Icc 0 (2 * Real.pi) = K1 ∪ K2 ∪ K3 := by
    ext θ
    simp only [K1, K2, K3, Set.mem_union, Set.mem_Icc]
    constructor
    · intro ⟨ha, hb⟩
      rcases le_total θ theta0 with h | h
      · exact Or.inl (Or.inl ⟨ha, h⟩)
      · rcases le_total θ (2 * Real.pi - theta0) with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr ⟨h', hb⟩
    · rintro ((⟨ha, h⟩ | ⟨h, h'⟩) | ⟨h', hb⟩) <;> constructor <;> linarith
  have hc1 : ContinuousOn q0AngleLift K1 := by
    refine ContinuousOn.congr
      (((continuous_const : Continuous (fun _ : ℝ => -2 * Real.pi)).add harccos_cont).continuousOn) ?_
    intro θ hθ
    simp only [q0AngleLift, if_pos hθ.2, f]; rfl
  have hc2 : ContinuousOn q0AngleLift K2 := by
    refine ContinuousOn.congr
      ((continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => 2 * Real.pi))).continuousOn) ?_
    intro θ hθ
    by_cases h : θ = theta0
    · subst h
      rw [q0AngleLift, if_pos le_rfl, q0_circleParam_eq_self le_rfl hmid.le]
      have hc : ⟪cA0, (circleParam theta0).1.1⟫_ℝ = Real.cos theta0 := by
        rw [circleParam_val, circleParamVec, inner_add_right, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10]
        ring
      rw [hc, Real.arccos_cos theta0_pos.le (by linarith [theta0_lt_pi_div_three, Real.pi_pos])]
      change -2 * Real.pi + theta0 = theta0 - 2 * Real.pi
      ring
    · have hgt : ¬ θ ≤ theta0 := fun hle => h (le_antisymm hle hθ.1)
      simp only [q0AngleLift, if_neg hgt, if_pos hθ.2]; rfl
  have hc3 : ContinuousOn q0AngleLift K3 := by
    refine ContinuousOn.congr harccos_cont.neg.continuousOn ?_
    intro θ hθ
    have hgt1 : ¬ θ ≤ theta0 := by linarith [hθ.1]
    by_cases h : θ = 2 * Real.pi - theta0
    · subst h
      rw [q0AngleLift, if_neg hgt1, if_pos le_rfl]
      show 2 * Real.pi - theta0 - 2 * Real.pi =
        -Real.arccos ⟪cA0, (q0 (circleParam (2 * Real.pi - theta0)).1 : Rep10)⟫_ℝ
      have hc : ⟪cA0, (q0 (circleParam (2 * Real.pi - theta0)).1 : Rep10)⟫_ℝ = Real.cos theta0 := by
        rw [q0_circleParam_eq_self hmid.le le_rfl, circleParam_val, circleParamVec,
          inner_add_right, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq, norm_cA0, inner_cA0_anchor10, Real.cos_two_pi_sub]
        ring
      rw [hc, Real.arccos_cos hth0.le (by linarith)]
      ring
    · have hgt2 : ¬ θ ≤ 2 * Real.pi - theta0 := fun hle => h (le_antisymm hle hθ.1)
      simp only [q0AngleLift, if_neg hgt1, if_neg hgt2, f]; rfl
  rw [hcov]
  exact (hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc

lemma q0AngleLift_zero : q0AngleLift 0 = -Real.pi := by
  have hth := theta0_pos
  rw [q0AngleLift, if_pos hth.le, q0_circleParam_zero]
  have hinner : ⟪cA0, (-cA0 : Rep10)⟫_ℝ = -1 := by
    rw [inner_neg_right, real_inner_self_eq_norm_sq, norm_cA0]; norm_num
  rw [hinner, Real.arccos_neg_one]
  ring

lemma q0AngleLift_two_pi : q0AngleLift (2 * Real.pi) = -Real.pi := by
  have hth1 := theta0_lt_pi_div_three
  have hgt1 : ¬ 2 * Real.pi ≤ theta0 := by linarith [Real.pi_pos]
  have hgt2 : ¬ 2 * Real.pi ≤ 2 * Real.pi - theta0 := by linarith [theta0_pos]
  rw [q0AngleLift, if_neg hgt1, if_neg hgt2, q0_circleParam_two_pi]
  have hinner : ⟪cA0, (-cA0 : Rep10)⟫_ℝ = -1 := by
    rw [inner_neg_right, real_inner_self_eq_norm_sq, norm_cA0]; norm_num
  rw [hinner, Real.arccos_neg_one]

lemma q0AngleLift_pi_div_two : q0AngleLift (Real.pi / 2) = Real.pi / 2 - 2 * Real.pi := by
  have hth1 := theta0_lt_pi_div_three
  have hgt : ¬ Real.pi / 2 ≤ theta0 := by linarith [Real.pi_pos]
  have hle : Real.pi / 2 ≤ 2 * Real.pi - theta0 := by linarith [Real.pi_pos]
  rw [q0AngleLift, if_neg hgt, if_pos hle]

lemma circleParam_q0AngleLift {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ 2 * Real.pi) :
    circleParam (q0AngleLift θ) = q0RestrictedP_row (circleParam θ) := by
  let u := q0RestrictedP_row (circleParam θ)
  have hu_val : u.1.1 = (q0 (circleParam θ).1 : Rep10) := rfl
  have hu_span := (fixedSubspace_P_row_eq_span u.1.1).mp u.2
  have hu_norm : ‖u.1.1‖ ^ 2 = 1 := by rw [mem_sphere_zero_iff_norm.mp u.1.2, one_pow]
  have hpyth : ⟪anchor10, u.1.1⟫_ℝ ^ 2 + ⟪cA0, u.1.1⟫_ℝ ^ 2 = 1 := by
    have hsq : ‖⟪anchor10, u.1.1⟫_ℝ • anchor10 + ⟪cA0, u.1.1⟫_ℝ • cA0‖ ^ 2 =
        ⟪anchor10, u.1.1⟫_ℝ ^ 2 + ⟪cA0, u.1.1⟫_ℝ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        norm_anchor10, norm_cA0, mul_one, mul_one, inner_smul_left, inner_smul_right,
        sq_abs, sq_abs]
      simp only [starRingEnd_apply, star_trivial, inner_anchor10_cA0]
      ring
    rw [← hu_span] at hsq
    linarith
  by_cases hth1 : θ ≤ theta0
  · have hpos : 0 ≤ ⟪anchor10, u.1.1⟫_ℝ := hu_val ▸ q0_circleParam_pos_arc h0 hth1
    have hbd : -1 ≤ ⟪cA0, u.1.1⟫_ℝ ∧ ⟪cA0, u.1.1⟫_ℝ ≤ 1 :=
      hu_val ▸ q0_circleParam_inner_cA0_bound θ
    have hangle : q0AngleLift θ = -2 * Real.pi + Real.arccos ⟪cA0, u.1.1⟫_ℝ := by
      simp [q0AngleLift, hth1, u, q0RestrictedP_row]
    have hcos : Real.cos (q0AngleLift θ) = ⟪cA0, u.1.1⟫_ℝ := by
      rw [hangle, show -2 * Real.pi + Real.arccos ⟪cA0, u.1.1⟫_ℝ =
          Real.arccos ⟪cA0, u.1.1⟫_ℝ - 2 * Real.pi by ring, Real.cos_sub_two_pi,
        Real.cos_arccos hbd.1 hbd.2]
    have hsin : Real.sin (q0AngleLift θ) = ⟪anchor10, u.1.1⟫_ℝ := by
      rw [hangle, show -2 * Real.pi + Real.arccos ⟪cA0, u.1.1⟫_ℝ =
          Real.arccos ⟪cA0, u.1.1⟫_ℝ - 2 * Real.pi by ring, Real.sin_sub_two_pi,
        Real.sin_arccos]
      have hsq' : Real.sqrt (1 - ⟪cA0, u.1.1⟫_ℝ ^ 2) = ⟪anchor10, u.1.1⟫_ℝ := by
        rw [show 1 - ⟪cA0, u.1.1⟫_ℝ ^ 2 = ⟪anchor10, u.1.1⟫_ℝ ^ 2 by linarith]
        exact Real.sqrt_sq hpos
      exact hsq'
    apply Subtype.ext; apply Subtype.ext
    change circleParamVec (q0AngleLift θ) = u.1.1
    rw [circleParamVec, hcos, hsin, add_comm]
    exact hu_span.symm
  · by_cases hth2 : θ ≤ 2 * Real.pi - theta0
    · have hle1 : theta0 ≤ θ := le_of_not_ge hth1
      have hangle : q0AngleLift θ = θ - 2 * Real.pi := by simp [q0AngleLift, hth1, hth2]
      apply Subtype.ext; apply Subtype.ext
      change circleParamVec (q0AngleLift θ) = (q0 (circleParam θ).1 : Rep10)
      rw [q0_circleParam_eq_self hle1 hth2, hangle, circleParamVec,
        Real.cos_sub_two_pi, Real.sin_sub_two_pi]
      rfl
    · have hge2 : 2 * Real.pi - theta0 ≤ θ := le_of_not_ge hth2
      have hneg : ⟪anchor10, u.1.1⟫_ℝ ≤ 0 := hu_val ▸ q0_circleParam_neg_arc hge2 h2
      have hbd : -1 ≤ ⟪cA0, u.1.1⟫_ℝ ∧ ⟪cA0, u.1.1⟫_ℝ ≤ 1 :=
        hu_val ▸ q0_circleParam_inner_cA0_bound θ
      have hangle : q0AngleLift θ = -Real.arccos ⟪cA0, u.1.1⟫_ℝ := by
        simp [q0AngleLift, hth1, hth2, u, q0RestrictedP_row]
      have hcos : Real.cos (q0AngleLift θ) = ⟪cA0, u.1.1⟫_ℝ := by
        rw [hangle, Real.cos_neg, Real.cos_arccos hbd.1 hbd.2]
      have hsin : Real.sin (q0AngleLift θ) = ⟪anchor10, u.1.1⟫_ℝ := by
        rw [hangle, Real.sin_neg, Real.sin_arccos]
        have hsq' : Real.sqrt (1 - ⟪cA0, u.1.1⟫_ℝ ^ 2) = -⟪anchor10, u.1.1⟫_ℝ := by
          rw [show 1 - ⟪cA0, u.1.1⟫_ℝ ^ 2 = (-⟪anchor10, u.1.1⟫_ℝ) ^ 2 by linarith]
          exact Real.sqrt_sq (by linarith)
        linarith
      apply Subtype.ext; apply Subtype.ext
      change circleParamVec (q0AngleLift θ) = u.1.1
      rw [circleParamVec, hcos, hsin, add_comm]
      exact hu_span.symm

theorem nullHomotopy_q0_P_row :
    Nonempty (ContinuousMap.HomotopyRel q0RestrictedP_row
      (ContinuousMap.const FixedP_row anchorS_P_row) {anchorS_P_row}) := by
  let I2π := Set.Icc (0 : ℝ) (2 * Real.pi)
  let quot : unitInterval × I2π → unitInterval × AddCircle (2 * Real.pi) :=
    fun p => (p.1, (p.2.1 : AddCircle (2 * Real.pi)))
  have : CompactSpace I2π := isCompact_iff_compactSpace.mp isCompact_Icc
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hq_cont : Continuous quot :=
    continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp (continuous_subtype_val.comp continuous_snd))
  have hq_surj : Function.Surjective quot := by
    rintro ⟨t, a⟩
    let r : ℝ := (AddCircle.equivIco (2 * Real.pi) 0 a).1
    have hr_mem : r ∈ I2π := by
      have hr := (AddCircle.equivIco (2 * Real.pi) 0 a).coe_prop
      simp only [zero_add, Set.mem_Ico] at hr
      exact ⟨hr.1, hr.2.le⟩
    refine ⟨(t, ⟨r, hr_mem⟩), Prod.ext rfl ?_⟩
    exact AddCircle.coe_equivIco (p := 2 * Real.pi) (a := 0) (y := a)
  have hq_quot : Topology.IsQuotientMap quot :=
    hq_cont.isClosedMap.isQuotientMap hq_cont hq_surj
  let H_Icc : unitInterval × I2π → FixedP_row := fun p =>
    circleParam ((1 - (p.1 : ℝ)) * q0AngleLift p.2.1 + (p.1 : ℝ) * (Real.pi / 2 - 2 * Real.pi))
  have hH_Icc_cont : Continuous H_Icc := by
    have hlift : Continuous (fun p : unitInterval × I2π => q0AngleLift p.2.1) :=
      continuous_q0AngleLift_on_Icc.comp_continuous (continuous_subtype_val.comp continuous_snd)
        (fun p => p.2.2)
    have hcomb : Continuous (fun p : unitInterval × I2π =>
        (1 - (p.1 : ℝ)) * q0AngleLift p.2.1 + (p.1 : ℝ) * (Real.pi / 2 - 2 * Real.pi)) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hlift).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
    exact continuous_circleParam.comp hcomb
  let H_ac : unitInterval × AddCircle (2 * Real.pi) → FixedP_row := fun p =>
    H_Icc (p.1, ⟨(AddCircle.equivIco (2 * Real.pi) 0 p.2).1, by
      have hr := (AddCircle.equivIco (2 * Real.pi) 0 p.2).coe_prop
      simp only [zero_add, Set.mem_Ico] at hr
      exact ⟨hr.1, hr.2.le⟩⟩)
  have hH_ac_comp : H_ac ∘ quot = H_Icc := by
    funext ⟨t, ⟨θ, hθ0, hθ2⟩⟩
    change H_Icc (t, ⟨(AddCircle.equivIco (2 * Real.pi) 0 (θ : AddCircle (2 * Real.pi))).1, _⟩) =
      H_Icc (t, ⟨θ, hθ0, hθ2⟩)
    rcases lt_or_eq_of_le hθ2 with hlt | rfl
    · have he : AddCircle.equivIco (2 * Real.pi) 0 (θ : AddCircle (2 * Real.pi)) =
          ⟨θ, ⟨hθ0, by linarith⟩⟩ :=
        AddCircle.equivIco_coe_eq (p := 2 * Real.pi) (a := 0) ⟨hθ0, by linarith⟩
      have he1 : (AddCircle.equivIco (2 * Real.pi) 0 (θ : AddCircle (2 * Real.pi))).1 = θ :=
        congrArg Subtype.val he
      simp only [he1]
    · have h2pi : ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = (0 : AddCircle (2 * Real.pi)) := by
        simp [AddCircle.coe_period]
      have he0 : AddCircle.equivIco (2 * Real.pi) 0 ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
          ⟨0, ⟨le_rfl, by rw [zero_add]; exact Real.two_pi_pos⟩⟩ := by
        rw [h2pi]
        exact AddCircle.equivIco_coe_eq (p := 2 * Real.pi) (a := 0)
          ⟨le_rfl, by rw [zero_add]; exact Real.two_pi_pos⟩
      have he1 : (AddCircle.equivIco (2 * Real.pi) 0 ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi))).1 = 0 :=
        congrArg Subtype.val he0
      dsimp only [H_Icc]
      rw [he1, q0AngleLift_zero, q0AngleLift_two_pi]
  have hH_ac_cont : Continuous H_ac := hq_quot.continuous_iff.mpr (hH_ac_comp.symm ▸ hH_Icc_cont)
  let H : unitInterval × FixedP_row → FixedP_row := fun p =>
    H_ac (p.1, addCircleEquivFixedP_row.symm p.2)
  have hH_cont : Continuous H :=
    hH_ac_cont.comp (continuous_fst.prodMk (addCircleEquivFixedP_row.symm.continuous.comp continuous_snd))
  refine ⟨{
    toFun := H
    continuous_toFun := hH_cont
    map_zero_left := fun x => by
      obtain ⟨⟨θ, hθ0, hθ2⟩, rfl⟩ : ∃ θ : I2π, circleParam θ.1 = x := by
        obtain ⟨r, hr⟩ := hq_surj (0, addCircleEquivFixedP_row.symm x)
        refine ⟨r.2, ?_⟩
        have hre := congrArg (fun z : unitInterval × AddCircle (2 * Real.pi) =>
          addCircleEquivFixedP_row z.2) hr
        simpa only [quot, addCircleEquivFixedP_row_apply_coe, Homeomorph.apply_symm_apply] using hre
      have hH0 : H (0, circleParam θ) = H_ac (0, (θ : AddCircle (2 * Real.pi))) := by
        dsimp [H]
        rw [← addCircleEquivFixedP_row_apply_coe θ, Homeomorph.symm_apply_apply]
      change H (0, circleParam θ) = q0RestrictedP_row (circleParam θ)
      rw [hH0]
      have hq0 := congrArg (fun f : unitInterval × I2π → FixedP_row => f (0, ⟨θ, hθ0, hθ2⟩)) hH_ac_comp
      dsimp [quot, H_Icc] at hq0
      rw [hq0]
      simp only [Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
      exact circleParam_q0AngleLift hθ0 hθ2
    map_one_left := fun x => by
      obtain ⟨⟨θ, hθ0, hθ2⟩, rfl⟩ : ∃ θ : I2π, circleParam θ.1 = x := by
        obtain ⟨r, hr⟩ := hq_surj (1, addCircleEquivFixedP_row.symm x)
        refine ⟨r.2, ?_⟩
        have hre := congrArg (fun z : unitInterval × AddCircle (2 * Real.pi) =>
          addCircleEquivFixedP_row z.2) hr
        simpa only [quot, addCircleEquivFixedP_row_apply_coe, Homeomorph.apply_symm_apply] using hre
      have hH1 : H (1, circleParam θ) = H_ac (1, (θ : AddCircle (2 * Real.pi))) := by
        dsimp [H]
        rw [← addCircleEquivFixedP_row_apply_coe θ, Homeomorph.symm_apply_apply]
      change H (1, circleParam θ) = anchorS_P_row
      rw [hH1]
      have hq1 := congrArg (fun f : unitInterval × I2π → FixedP_row => f (1, ⟨θ, hθ0, hθ2⟩)) hH_ac_comp
      dsimp [quot, H_Icc] at hq1
      rw [hq1]
      simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
      apply Subtype.ext; apply Subtype.ext
      change circleParamVec (Real.pi / 2 - 2 * Real.pi) = anchor10
      rw [circleParamVec, Real.cos_sub_two_pi, Real.sin_sub_two_pi, Real.cos_pi_div_two,
        Real.sin_pi_div_two]
      simp
    prop' := fun t x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      have hLHS : H (t, anchorS_P_row) = anchorS_P_row := by
        have hpi : circleParam (Real.pi / 2) = anchorS_P_row := circleParam_pi_div_two
        have hpi_mem : Real.pi / 2 ∈ I2π := ⟨by positivity, by linarith [Real.pi_pos]⟩
        dsimp [H]
        conv_lhs => rw [← hpi, ← addCircleEquivFixedP_row_apply_coe, Homeomorph.symm_apply_apply]
        have hqp := congrArg (fun f : unitInterval × I2π → FixedP_row => f (t, ⟨Real.pi / 2, hpi_mem⟩))
          hH_ac_comp
        dsimp [quot, H_Icc] at hqp
        rw [hqp, q0AngleLift_pi_div_two]
        have hangle : (1 - (t : ℝ)) * (Real.pi / 2 - 2 * Real.pi) +
            (t : ℝ) * (Real.pi / 2 - 2 * Real.pi) = Real.pi / 2 - 2 * Real.pi := by ring
        rw [hangle]
        apply Subtype.ext; apply Subtype.ext
        change circleParamVec (Real.pi / 2 - 2 * Real.pi) = anchor10
        rw [circleParamVec, Real.cos_sub_two_pi, Real.sin_sub_two_pi, Real.cos_pi_div_two,
          Real.sin_pi_div_two]
        simp
      exact hLHS.trans (Subtype.ext q0_anchorS).symm }⟩

end CircleNullHomotopy

end AkopyanResearch
