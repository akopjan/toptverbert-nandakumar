module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import AkopyanResearch.PlanarTestLocal
public import AkopyanResearch.InvariantCaps

@[expose] public section

/-!
# Global equivariant planar test map `q₀ : S⁹ → S⁹`

Constructs the 10-dimensional `Equiv.Perm (Fin 6)`-representation `Rep10 ≃ W₆ ⊕ W₆` as
`EuclideanSpace ℝ (Fin 10)` via an explicit linear isometry from the zero-sum subspace of
`EuclideanSpace ℝ (Fin 12)`, defines the 41 disjoint stereographic cap modifications from
`PlanarTestLocal` and `InvariantCaps`, proves the global homotopy `spherePush : S⁹ × [0, 1/2] → Rep10`
vanishes precisely at `{(c_A, 1/4)}`, and normalizes `t = 1/2` to the `Equiv.Perm (Fin 6)`-equivariant
self-map `q₀ : S⁹ → S⁹` fixing the `4 + 2` contrast anchor.
-/

noncomputable section

open scoped BigOperators InnerProductSpace
open Metric

namespace AkopyanResearch

/-! ### 10-dimensional representation `W₆ ⊕ W₆` transported to `EuclideanSpace ℝ (Fin 10)` -/

section Rep

def splitPair6 (v w : Fin 6 → ℝ) (i : Fin 12) : ℝ :=
  if h : i.1 < 6 then v ⟨i.1, h⟩ else w ⟨i.1 - 6, by have := i.isLt; omega⟩

lemma splitPair6_castAdd (v w : Fin 6 → ℝ) (j : Fin 6) :
    splitPair6 v w (j.castAdd 6) = v j := by
  dsimp [splitPair6]
  split_ifs with h
  · rfl
  · exact absurd j.isLt h

lemma splitPair6_addNat (v w : Fin 6 → ℝ) (j : Fin 6) :
    splitPair6 v w (j.addNat 6) = w j := by
  dsimp [splitPair6]
  congr 1

lemma splitPair6_natAdd (v w : Fin 6 → ℝ) (j : Fin 6) :
    splitPair6 v w (Fin.natAdd 6 j) = w j := by
  dsimp [splitPair6]
  split_ifs with h
  · exfalso; simp at h
  · congr 1
    ext
    simp

private lemma sum_fin12_splitPair6 (f : Fin 12 → ℝ) :
    (∑ i : Fin 12, f i) = (∑ j : Fin 6, f (j.castAdd 6)) + ∑ j : Fin 6, f (j.addNat 6) :=
  Fin.sum_univ_add (fun j : Fin (6 + 6) => f j)

def sumFirst6 : EuclideanSpace ℝ (Fin 12) →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin 6, x (i.castAdd 6)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

def sumLast6 : EuclideanSpace ℝ (Fin 12) →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin 6, x (Fin.natAdd 6 i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

def V10Sub : Submodule ℝ (EuclideanSpace ℝ (Fin 12)) :=
  LinearMap.ker sumFirst6 ⊓ LinearMap.ker sumLast6

lemma mem_V10Sub_iff (x : EuclideanSpace ℝ (Fin 12)) :
    x ∈ V10Sub ↔ (∑ i : Fin 6, x (i.castAdd 6)) = 0 ∧ (∑ i : Fin 6, x (Fin.natAdd 6 i)) = 0 :=
  Iff.rfl

private def pairSumMap : EuclideanSpace ℝ (Fin 12) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![sumFirst6 x, sumLast6 x]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

private lemma ker_pairSumMap : LinearMap.ker pairSumMap = V10Sub := by
  ext x
  simp only [LinearMap.mem_ker, mem_V10Sub_iff, funext_iff, Fin.forall_fin_two,
    pairSumMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply]
  rfl

private lemma surjective_pairSumMap : Function.Surjective pairSumMap := by
  intro y
  let f0 : Fin 6 → ℝ := fun i => if i = 0 then y 0 else 0
  let f1 : Fin 6 → ℝ := fun i => if i = 0 then y 1 else 0
  refine ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 f0 f1), ?_⟩
  ext k
  fin_cases k
  · simp only [pairSumMap, LinearMap.coe_mk, AddHom.coe_mk,
      sumFirst6, WithLp.equiv_symm_apply, splitPair6_castAdd]
    simp [f0]
  · simp only [pairSumMap, LinearMap.coe_mk, AddHom.coe_mk,
      sumLast6, WithLp.equiv_symm_apply, splitPair6_natAdd]
    simp [f1]

theorem finrank_V10Sub : Module.finrank ℝ V10Sub = 10 := by
  have h1 := pairSumMap.finrank_range_add_finrank_ker
  have hrange : LinearMap.range pairSumMap = ⊤ :=
    LinearMap.range_eq_top.mpr surjective_pairSumMap
  rw [hrange, finrank_top, Module.finrank_fin_fun, finrank_euclideanSpace_fin,
    ker_pairSumMap] at h1
  change 2 + Module.finrank ℝ V10Sub = 12 at h1
  omega

abbrev Rep10 := EuclideanSpace ℝ (Fin 10)

def iso10 : ↥V10Sub ≃ₗᵢ[ℝ] Rep10 :=
  ((stdOrthonormalBasis ℝ V10Sub).reindex (finCongr finrank_V10Sub)).repr

def perm12 (g : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 12) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr g g).trans finSumFinEquiv)

lemma perm12_castAdd (g : Equiv.Perm (Fin 6)) (i : Fin 6) :
    perm12 g (i.castAdd 6) = (g i).castAdd 6 := by
  change finSumFinEquiv (Equiv.sumCongr g g (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma perm12_natAdd (g : Equiv.Perm (Fin 6)) (i : Fin 6) :
    perm12 g (Fin.natAdd 6 i) = Fin.natAdd 6 (g i) := by
  change finSumFinEquiv (Equiv.sumCongr g g (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma perm12_symm (g : Equiv.Perm (Fin 6)) : (perm12 g).symm = perm12 g⁻¹ := by
  apply Equiv.ext
  intro i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]
    apply (perm12 g).injective
    rw [Equiv.apply_symm_apply, perm12_castAdd, perm12_castAdd]
    exact congrArg (fun k : Fin 6 => k.castAdd 6) (by simp)
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]
    apply (perm12 g).injective
    rw [Equiv.apply_symm_apply, perm12_natAdd, perm12_natAdd]
    exact congrArg (Fin.natAdd 6) (by simp)

lemma perm12_one : perm12 (1 : Equiv.Perm (Fin 6)) = 1 := by
  ext i; simp [perm12]

lemma perm12_mul (g h : Equiv.Perm (Fin 6)) : perm12 (g * h) = perm12 g * perm12 h := by
  ext i; simp [perm12, Equiv.Perm.mul_def]

def permAmb (g : Equiv.Perm (Fin 6)) : EuclideanSpace ℝ (Fin 12) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 12) where
  toFun x := (WithLp.equiv 2 (Fin 12 → ℝ)).symm (fun i => x ((perm12 g).symm i))
  invFun x := (WithLp.equiv 2 (Fin 12 → ℝ)).symm (fun i => x (perm12 g i))
  left_inv x := by apply PiLp.ext; intro i; simp
  right_inv x := by apply PiLp.ext; intro i; simp
  map_add' x y := by apply PiLp.ext; intro i; simp
  map_smul' r x := by apply PiLp.ext; intro i; simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Fintype.sum_equiv (perm12 g).symm _ _ fun i => ?_
    simp [Real.norm_eq_abs, sq_abs]

lemma permAmb_mem_V10Sub (g : Equiv.Perm (Fin 6)) {x : EuclideanSpace ℝ (Fin 12)}
    (hx : x ∈ V10Sub) : permAmb g x ∈ V10Sub := by
  rw [mem_V10Sub_iff] at hx ⊢
  constructor
  · calc
      ∑ i : Fin 6, permAmb g x (i.castAdd 6) = ∑ i : Fin 6, x ((g⁻¹ i).castAdd 6) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        change x ((perm12 g).symm (i.castAdd 6)) = _
        rw [perm12_symm, perm12_castAdd]
      _ = ∑ i : Fin 6, x (i.castAdd 6) :=
        Fintype.sum_equiv g⁻¹ (fun i : Fin 6 => x ((g⁻¹ i).castAdd 6))
          (fun i : Fin 6 => x (i.castAdd 6)) (fun _ => rfl)
      _ = 0 := hx.1
  · calc
      ∑ i : Fin 6, permAmb g x (Fin.natAdd 6 i) = ∑ i : Fin 6, x (Fin.natAdd 6 (g⁻¹ i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        change x ((perm12 g).symm (Fin.natAdd 6 i)) = _
        rw [perm12_symm, perm12_natAdd]
      _ = ∑ i : Fin 6, x (Fin.natAdd 6 i) :=
        Fintype.sum_equiv g⁻¹ (fun i : Fin 6 => x (Fin.natAdd 6 (g⁻¹ i)))
          (fun i : Fin 6 => x (Fin.natAdd 6 i)) (fun _ => rfl)
      _ = 0 := hx.2

def permSub (g : Equiv.Perm (Fin 6)) : ↥V10Sub ≃ₗᵢ[ℝ] ↥V10Sub where
  toFun x := ⟨permAmb g x.1, permAmb_mem_V10Sub g x.2⟩
  invFun x := ⟨permAmb g⁻¹ x.1, permAmb_mem_V10Sub g⁻¹ x.2⟩
  left_inv x := by
    ext i
    change x.1 ((perm12 g).symm ((perm12 g⁻¹).symm i)) = x.1 i
    rw [perm12_symm, perm12_symm, inv_inv]
    change x.1 (perm12 g⁻¹ (perm12 g i)) = x.1 i
    rw [← Equiv.Perm.mul_apply, ← perm12_mul, inv_mul_cancel, perm12_one]
    rfl
  right_inv x := by
    ext i
    change x.1 ((perm12 g⁻¹).symm ((perm12 g).symm i)) = x.1 i
    rw [perm12_symm, perm12_symm, inv_inv]
    change x.1 (perm12 g (perm12 g⁻¹ i)) = x.1 i
    rw [← Equiv.Perm.mul_apply, ← perm12_mul, mul_inv_cancel, perm12_one]
    rfl
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl
  norm_map' x := (permAmb g).norm_map x.1

def perm10 (g : Equiv.Perm (Fin 6)) : Rep10 ≃ₗᵢ[ℝ] Rep10 :=
  iso10.symm.trans ((permSub g).trans iso10)

lemma perm10_one (x : Rep10) : perm10 1 x = x := by
  have hsub : ∀ v : ↥V10Sub, permSub 1 v = v := fun v => by
    ext i
    change v.1 ((perm12 (1 : Equiv.Perm (Fin 6))).symm i) = v.1 i
    rw [perm12_one]; rfl
  simp [perm10, hsub]

lemma perm10_mul (g h : Equiv.Perm (Fin 6)) (x : Rep10) :
    perm10 (g * h) x = perm10 g (perm10 h x) := by
  have hsub : ∀ v : ↥V10Sub, permSub (g * h) v = permSub g (permSub h v) := fun v => by
    ext i
    change v.1 ((perm12 (g * h)).symm i) = v.1 ((perm12 h).symm ((perm12 g).symm i))
    rw [perm12_mul]; rfl
  simp [perm10, hsub]

lemma perm10_inner (g : Equiv.Perm (Fin 6)) (x y : Rep10) :
    ⟪perm10 g x, perm10 g y⟫_ℝ = ⟪x, y⟫_ℝ :=
  (perm10 g).inner_map_map x y

def permSphere (g : Equiv.Perm (Fin 6)) (x : Metric.sphere (0 : Rep10) 1) :
    Metric.sphere (0 : Rep10) 1 :=
  ⟨perm10 g x.1, by simp [(perm10 g).norm_map, mem_sphere_zero_iff_norm.mp x.2]⟩

@[simp] lemma permSphere_val (g : Equiv.Perm (Fin 6)) (x : Metric.sphere (0 : Rep10) 1) :
    (permSphere g x : Rep10) = perm10 g x.1 := rfl

lemma continuous_permSphere (g : Equiv.Perm (Fin 6)) : Continuous (permSphere g) :=
  Continuous.subtype_mk ((perm10 g).continuous.comp continuous_subtype_val) _

end Rep

/-! ### The 41 orbit centers, tangent directions, and anchor -/

section Centers

instance instFintypeCapLabel : Fintype InvariantCaps.CapLabel := by
  dsimp [InvariantCaps.CapLabel]
  infer_instance

instance instDecidableEqCapLabel : DecidableEq InvariantCaps.CapLabel := by
  dsimp [InvariantCaps.CapLabel]
  infer_instance

def permCap (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) : InvariantCaps.CapLabel :=
  ⟨A.val.map g.toEmbedding, by simpa [Finset.card_map] using A.property⟩

lemma permCap_one (A : InvariantCaps.CapLabel) : permCap 1 A = A := by
  apply Subtype.ext
  ext i
  simp only [permCap, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.Perm.coe_one, id_eq,
    exists_eq_right]

lemma permCap_mul (g h : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) :
    permCap (g * h) A = permCap g (permCap h A) := by
  apply Subtype.ext
  ext i
  simp only [permCap, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.Perm.coe_mul,
    Function.comp_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨h a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩

lemma permCap_card (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) :
    (permCap g A).val.card = A.val.card := by
  simp [permCap]

lemma permCap_bijective (g : Equiv.Perm (Fin 6)) : Function.Bijective (permCap g) :=
  ⟨fun A B h => by
      have h' := congrArg (permCap g⁻¹) h
      rwa [← permCap_mul, ← permCap_mul, inv_mul_cancel, permCap_one, permCap_one] at h',
    fun A => ⟨permCap g⁻¹ A, by rw [← permCap_mul, mul_inv_cancel, permCap_one]⟩⟩

def contrastVec6 (A : InvariantCaps.CapLabel) : EuclideanSpace ℝ (Fin 6) :=
  (WithLp.equiv 2 (Fin 6 → ℝ)).symm (InvariantCaps.contrast A.val)

lemma sum_contrast (A : Finset (Fin 6)) : ∑ i : Fin 6, InvariantCaps.contrast A i = 0 := by
  simp only [InvariantCaps.contrast, Finset.sum_sub_distrib, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

lemma contrastVec6_ne_zero (A : InvariantCaps.CapLabel) : contrastVec6 A ≠ 0 := by
  have hpos : 0 < A.val.card := lt_of_lt_of_le zero_lt_one A.property.1
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hlt : A.val.card < 6 := by have := A.property.2; omega
  have hcpos : 0 < InvariantCaps.contrast A.val i :=
    (InvariantCaps.contrast_pos_iff A.val hlt i).mpr hi
  intro hz
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 6) => v i) hz
  change InvariantCaps.contrast A.val i = 0 at h0
  linarith

lemma contrastVec6_norm_pos (A : InvariantCaps.CapLabel) : 0 < ‖contrastVec6 A‖ :=
  norm_pos_iff.mpr (contrastVec6_ne_zero A)

lemma embed6Left_mem (v : Fin 6 → ℝ) (hv : ∑ i, v i = 0) :
    (WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 v (fun _ => 0)) ∈ V10Sub := by
  rw [mem_V10Sub_iff]
  simp [WithLp.equiv_symm_apply, splitPair6_castAdd, splitPair6_addNat, hv]

lemma embed6Right_mem (v : Fin 6 → ℝ) (hv : ∑ i, v i = 0) :
    (WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 (fun _ => 0) v) ∈ V10Sub := by
  rw [mem_V10Sub_iff]
  simp [WithLp.equiv_symm_apply, splitPair6_castAdd, splitPair6_addNat, hv]

def cASub (A : InvariantCaps.CapLabel) : ↥V10Sub :=
  ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm
    (splitPair6 (fun i => ‖contrastVec6 A‖⁻¹ * contrastVec6 A i) (fun _ => 0)),
    embed6Left_mem (fun i => ‖contrastVec6 A‖⁻¹ * contrastVec6 A i) (by
      rw [← Finset.mul_sum]
      have h0 : ∑ i : Fin 6, contrastVec6 A i = 0 := sum_contrast A.val
      simp [h0])⟩

def bASub (A : InvariantCaps.CapLabel) : ↥V10Sub :=
  ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm
    (splitPair6 (fun _ => 0) (fun i => ‖contrastVec6 A‖⁻¹ * contrastVec6 A i)),
    embed6Right_mem (fun i => ‖contrastVec6 A‖⁻¹ * contrastVec6 A i) (by
      rw [← Finset.mul_sum]
      have h0 : ∑ i : Fin 6, contrastVec6 A i = 0 := sum_contrast A.val
      simp [h0])⟩

def cA (A : InvariantCaps.CapLabel) : Rep10 := iso10 (cASub A)
def bA (A : InvariantCaps.CapLabel) : Rep10 := iso10 (bASub A)

private lemma sum_sq_splitPair6_left (v : Fin 6 → ℝ) :
    ∑ i : Fin 12, (splitPair6 v (fun _ => 0) i) ^ 2 = ∑ j : Fin 6, (v j) ^ 2 := by
  rw [sum_fin12_splitPair6]
  simp [splitPair6_castAdd, splitPair6_addNat]

private lemma sum_sq_splitPair6_right (v : Fin 6 → ℝ) :
    ∑ i : Fin 12, (splitPair6 (fun _ => 0) v i) ^ 2 = ∑ j : Fin 6, (v j) ^ 2 := by
  rw [sum_fin12_splitPair6]
  simp [splitPair6_castAdd, splitPair6_addNat]

lemma norm_cA (A : InvariantCaps.CapLabel) : ‖cA A‖ = 1 := by
  rw [cA, iso10.norm_map, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow]
  change ‖(cASub A).1‖ ^ 2 = 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  change ∑ i : Fin 12,
      (splitPair6 (fun j => ‖contrastVec6 A‖⁻¹ * contrastVec6 A j) (fun _ => 0) i) ^ 2 = 1
  rw [sum_sq_splitPair6_left]
  simp only [mul_pow, ← Finset.mul_sum]
  have hsq : ∑ j : Fin 6, (contrastVec6 A j) ^ 2 = ‖contrastVec6 A‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hsq]
  have hp : ‖contrastVec6 A‖ ≠ 0 := (contrastVec6_norm_pos A).ne'
  field_simp

lemma norm_bA (A : InvariantCaps.CapLabel) : ‖bA A‖ = 1 := by
  rw [bA, iso10.norm_map, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow]
  change ‖(bASub A).1‖ ^ 2 = 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  change ∑ i : Fin 12,
      (splitPair6 (fun _ => 0) (fun j => ‖contrastVec6 A‖⁻¹ * contrastVec6 A j) i) ^ 2 = 1
  rw [sum_sq_splitPair6_right]
  simp only [mul_pow, ← Finset.mul_sum]
  have hsq : ∑ j : Fin 6, (contrastVec6 A j) ^ 2 = ‖contrastVec6 A‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hsq]
  have hp : ‖contrastVec6 A‖ ≠ 0 := (contrastVec6_norm_pos A).ne'
  field_simp

lemma inner_cA_bA (A : InvariantCaps.CapLabel) : ⟪cA A, bA A⟫_ℝ = 0 := by
  rw [cA, bA, iso10.inner_map_map]
  change ⟪(cASub A).1, (bASub A).1⟫_ℝ = 0
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  simp only [cASub, bASub, WithLp.equiv_symm_apply]
  rw [sum_fin12_splitPair6]
  simp [splitPair6_castAdd, splitPair6_addNat]

lemma contrastVec6_norm_perm (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) :
    ‖contrastVec6 (permCap g A)‖ = ‖contrastVec6 A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  symm
  refine Fintype.sum_equiv g _ _ fun i => ?_
  simp only [contrastVec6, WithLp.equiv_symm_apply, permCap]
  rw [InvariantCaps.contrast_map]

lemma perm10_cA (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) :
    perm10 g (cA A) = cA (permCap g A) := by
  rw [perm10, cA, cA]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]
    change (cASub A).1 ((perm12 g).symm (j.castAdd 6)) = (cASub (permCap g A)).1 (j.castAdd 6)
    rw [perm12_symm, perm12_castAdd]
    simp only [cASub, WithLp.equiv_symm_apply, splitPair6_castAdd, contrastVec6_norm_perm]
    have hcm := InvariantCaps.contrast_map g A.val (g⁻¹ j)
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hcm
    simp only [contrastVec6, WithLp.equiv_symm_apply, permCap]
    rw [hcm]
    rfl
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]
    change (cASub A).1 ((perm12 g).symm (Fin.natAdd 6 j)) = (cASub (permCap g A)).1 (Fin.natAdd 6 j)
    rw [perm12_symm, perm12_natAdd]
    simp only [cASub, WithLp.equiv_symm_apply, splitPair6_natAdd]

lemma perm10_bA (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) :
    perm10 g (bA A) = bA (permCap g A) := by
  rw [perm10, bA, bA]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]
    change (bASub A).1 ((perm12 g).symm (j.castAdd 6)) = (bASub (permCap g A)).1 (j.castAdd 6)
    rw [perm12_symm, perm12_castAdd]
    simp only [bASub, WithLp.equiv_symm_apply, splitPair6_castAdd]
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]
    change (bASub A).1 ((perm12 g).symm (Fin.natAdd 6 j)) = (bASub (permCap g A)).1 (Fin.natAdd 6 j)
    rw [perm12_symm, perm12_natAdd]
    simp only [bASub, WithLp.equiv_symm_apply, splitPair6_natAdd, contrastVec6_norm_perm]
    have hcm := InvariantCaps.contrast_map g A.val (g⁻¹ j)
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hcm
    simp only [contrastVec6, WithLp.equiv_symm_apply, permCap]
    rw [hcm]
    rfl

lemma cA_injective : Function.Injective cA := by
  intro A B hAB
  apply InvariantCaps.normalizedContrast_injective (fun C => ‖contrastVec6 C‖⁻¹)
    (fun C => inv_pos.mpr (contrastVec6_norm_pos C))
  funext i
  have hsub : cASub A = cASub B := iso10.injective hAB
  have h := congrArg (fun v : ↥V10Sub => v.1 (i.castAdd 6)) hsub
  simpa [cASub, InvariantCaps.normalizedContrast, contrastVec6, splitPair6_castAdd] using h

lemma exists_capDelta0 :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 10 ∧
      ∀ A B : InvariantCaps.CapLabel, A ≠ B → 5 * δ ≤ ‖cA A - cA B‖ := by
  classical
  have hmin : ∃ m : ℝ, 0 < m ∧ ∀ A B : InvariantCaps.CapLabel, A ≠ B → m ≤ ‖cA A - cA B‖ := by
    let A₀ : InvariantCaps.CapLabel := ⟨{0}, by simp⟩
    let B₀ : InvariantCaps.CapLabel := ⟨{1}, by simp⟩
    have hAB₀ : A₀ ≠ B₀ := by
      intro h
      have := congrArg Subtype.val h
      simp [A₀, B₀] at this
    let S : Finset (InvariantCaps.CapLabel × InvariantCaps.CapLabel) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2)
    have hS : S.Nonempty := ⟨(A₀, B₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAB₀⟩⟩
    obtain ⟨p₀, hp₀, hp₀_min⟩ := S.exists_min_image (fun p => ‖cA p.1 - cA p.2‖) hS
    have hne₀ : p₀.1 ≠ p₀.2 := (Finset.mem_filter.mp hp₀).2
    refine ⟨‖cA p₀.1 - cA p₀.2‖,
      norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hne₀ (cA_injective h)), fun A B hne => ?_⟩
    exact hp₀_min (A, B) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  rcases hmin with ⟨m, hm_pos, hm_le⟩
  refine ⟨min (1 / 11) (m / 5), lt_min (by norm_num) (by positivity),
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), fun A B hne => ?_⟩
  have hle : m ≤ ‖cA A - cA B‖ := hm_le A B hne
  have h5 : 5 * min (1 / 11 : ℝ) (m / 5) ≤ m := by
    calc
      5 * min (1 / 11 : ℝ) (m / 5) ≤ 5 * (m / 5) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = m := by ring
  exact h5.trans hle

noncomputable def capDelta0 : ℝ := Classical.choose exists_capDelta0

lemma capDelta0_pos : 0 < capDelta0 := (Classical.choose_spec exists_capDelta0).1
lemma capDelta0_lt : capDelta0 < 1 / 10 := (Classical.choose_spec exists_capDelta0).2.1
lemma capDelta0_sep {A B : InvariantCaps.CapLabel} (hne : A ≠ B) :
    5 * capDelta0 ≤ ‖cA A - cA B‖ := (Classical.choose_spec exists_capDelta0).2.2 A B hne

/-- The imaginary `4 + 2` contrast vector `(0, (1,1,1,1,-2,-2)/√12)` fixed by `P_row`. -/
def anchorVec6 (i : Fin 6) : ℝ :=
  if i.1 < 4 then 1 / Real.sqrt 12 else -2 / Real.sqrt 12

lemma sum_anchorVec6 : ∑ i : Fin 6, anchorVec6 i = 0 := by
  simp [Fin.sum_univ_six, anchorVec6]
  ring

def anchorSub : ↥V10Sub :=
  ⟨(WithLp.equiv 2 (Fin 12 → ℝ)).symm (splitPair6 (fun _ => 0) anchorVec6),
    embed6Right_mem anchorVec6 sum_anchorVec6⟩

def anchor10 : Rep10 := iso10 anchorSub

lemma norm_anchor10 : ‖anchor10‖ = 1 := by
  rw [anchor10, iso10.norm_map, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow]
  change ‖anchorSub.1‖ ^ 2 = 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  change ∑ i : Fin 12, (splitPair6 (fun _ => 0) anchorVec6 i) ^ 2 = 1
  rw [sum_sq_splitPair6_right]
  have hsq : ∀ i : Fin 6, anchorVec6 i ^ 2 = if i.1 < 4 then (1 : ℝ) / 12 else 4 / 12 := fun i => by
    unfold anchorVec6
    split_ifs <;> norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  simp only [Fin.sum_univ_six, hsq,
    show ((0 : Fin 6) : ℕ) = 0 from rfl, show ((1 : Fin 6) : ℕ) = 1 from rfl,
    show ((2 : Fin 6) : ℕ) = 2 from rfl, show ((3 : Fin 6) : ℕ) = 3 from rfl,
    show ((4 : Fin 6) : ℕ) = 4 from rfl, show ((5 : Fin 6) : ℕ) = 5 from rfl]
  norm_num

lemma inner_cA_anchor10 (A : InvariantCaps.CapLabel) : ⟪cA A, anchor10⟫_ℝ = 0 := by
  rw [cA, anchor10, iso10.inner_map_map]
  change ⟪(cASub A).1, anchorSub.1⟫_ℝ = 0
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  simp only [cASub, anchorSub, WithLp.equiv_symm_apply]
  rw [sum_fin12_splitPair6]
  simp [splitPair6_castAdd, splitPair6_addNat]

lemma norm_anchor10_sub_cA (A : InvariantCaps.CapLabel) :
    ‖anchor10 - cA A‖ = Real.sqrt 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num),
    norm_sub_sq_real, norm_anchor10, norm_cA, real_inner_comm, inner_cA_anchor10]
  ring

lemma perm10_anchor10 {g : Equiv.Perm (Fin 6)}
    (hg : ∀ i : Fin 6, i.1 < 4 → (g i).1 < 4) :
    perm10 g anchor10 = anchor10 := by
  have hg_symm : ∀ i : Fin 6, i.1 < 4 ↔ (g⁻¹ i).1 < 4 := by
    let S4 : Finset (Fin 6) := Finset.univ.filter (fun j => j.1 < 4)
    have hmap : S4.map g.toEmbedding ⊆ S4 := fun x hx => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
      simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hg j hj
    have heq : S4.map g.toEmbedding = S4 :=
      Finset.eq_of_subset_of_card_le hmap (by simp)
    intro i
    have hmem : i ∈ S4 ↔ g⁻¹ i ∈ S4 := by
      conv_lhs => rw [← heq]
      simp [S4]
    simpa [S4] using hmem
  rw [perm10, anchor10]
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  ext i
  rcases Nat.lt_or_ge i.1 6 with hi | hi
  · let j : Fin 6 := ⟨i.1, hi⟩
    have hij : i = j.castAdd 6 := Fin.ext rfl
    rw [hij]
    change anchorSub.1 ((perm12 g).symm (j.castAdd 6)) = anchorSub.1 (j.castAdd 6)
    rw [perm12_symm, perm12_castAdd]
    simp [anchorSub, splitPair6_castAdd]
  · let j : Fin 6 := ⟨i.1 - 6, by have := i.isLt; omega⟩
    have hij : i = Fin.natAdd 6 j := Fin.ext (by simp [j]; omega)
    rw [hij]
    change anchorSub.1 ((perm12 g).symm (Fin.natAdd 6 j)) = anchorSub.1 (Fin.natAdd 6 j)
    rw [perm12_symm, perm12_natAdd]
    simp only [anchorSub, WithLp.equiv_symm_apply, splitPair6_natAdd, anchorVec6]
    by_cases hj : j.1 < 4
    · have hj' : (g⁻¹ j).1 < 4 := (hg_symm j).mp hj
      split_ifs; rfl
    · have hj' : ¬ (g⁻¹ j).1 < 4 := fun h => hj ((hg_symm j).mpr h)
      split_ifs; rfl

end Centers

/-! ### Inverse stereographic chart and global cap push -/

section GlobalPush

def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

lemma clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _
lemma clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_right _ _)
lemma clamp01_of_nonpos {x : ℝ} (hx : x ≤ 0) : clamp01 x = 0 := by
  simp [clamp01, min_eq_left (hx.trans zero_le_one), hx]
lemma clamp01_of_one_le {x : ℝ} (hx : 1 ≤ x) : clamp01 x = 1 := by
  simp [clamp01, min_eq_right hx]
lemma continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

def capChord (r : ℝ) : ℝ := 2 * r / Real.sqrt (4 + r ^ 2)

lemma capChord_pos {r : ℝ} (hr : 0 < r) : 0 < capChord r := by
  unfold capChord
  positivity

lemma capChord_lt_self {r : ℝ} (hr : 0 < r) : capChord r < r := by
  unfold capChord
  have hs : 2 < Real.sqrt (4 + r ^ 2) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

lemma capChord_strictMono : StrictMonoOn capChord (Set.Ici 0) := by
  intro a ha b hb hab
  unfold capChord
  have ha0 : 0 ≤ a := Set.mem_Ici.mp ha
  have hb0 : 0 ≤ b := Set.mem_Ici.mp hb
  have ha4 : 0 < 4 + a ^ 2 := by positivity
  have hb4 : 0 < 4 + b ^ 2 := by positivity
  have hs1 : 0 < Real.sqrt (4 + a ^ 2) := Real.sqrt_pos.mpr ha4
  have hs2 : 0 < Real.sqrt (4 + b ^ 2) := Real.sqrt_pos.mpr hb4
  rw [div_lt_div_iff₀ hs1 hs2]
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha4.le, Real.sq_sqrt hb4.le]
  have : a ^ 2 < b ^ 2 := by nlinarith
  nlinarith

def stereoProj (c x : Rep10) : Rep10 :=
  (2 / (1 + ⟪c, x⟫_ℝ)) • (x - ⟪c, x⟫_ℝ • c)

lemma inner_stereoProj {c : Rep10} (hc : ‖c‖ = 1) (x : Rep10) :
    ⟪c, stereoProj c x⟫_ℝ = 0 := by
  simp only [stereoProj, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hc,
    one_pow, mul_one, sub_self, mul_zero]

lemma one_add_inner_pos_of_norm_sub_lt {c x : Rep10} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1)
    (hdist : ‖x - c‖ < 2) : 0 < 1 + ⟪c, x⟫_ℝ := by
  have hsq : ‖x - c‖ ^ 2 < 4 := by nlinarith [norm_nonneg (x - c)]
  rw [norm_sub_sq_real, hx, hc, one_pow, real_inner_comm] at hsq
  linarith

lemma norm_sub_sq_eq {c x : Rep10} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1) :
    ‖x - c‖ ^ 2 = 2 * (1 - ⟪c, x⟫_ℝ) := by
  rw [norm_sub_sq_real, hx, hc, one_pow, real_inner_comm]
  ring

lemma normSq_stereoProj {c x : Rep10} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1)
    (hdist : ‖x - c‖ < 2) :
    ‖stereoProj c x‖ ^ 2 = 4 * ‖x - c‖ ^ 2 / (4 - ‖x - c‖ ^ 2) := by
  have hp : 0 < 1 + ⟪c, x⟫_ℝ := one_add_inner_pos_of_norm_sub_lt hc hx hdist
  have h2 : 4 - ‖x - c‖ ^ 2 = 2 * (1 + ⟪c, x⟫_ℝ) := by
    rw [norm_sub_sq_eq hc hx]; ring
  have hperp : ‖x - ⟪c, x⟫_ℝ • c‖ ^ 2 = 1 - ⟪c, x⟫_ℝ ^ 2 := by
    rw [norm_sub_sq_real, hx, norm_smul, Real.norm_eq_abs, hc, mul_one,
      inner_smul_right, real_inner_comm, sq_abs]
    ring
  rw [stereoProj, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hp),
    mul_pow, hperp, h2, norm_sub_sq_eq hc hx]
  have hp2 : 2 * (1 + ⟪c, x⟫_ℝ) ≠ 0 := by linarith
  field_simp
  ring

lemma norm_stereoProj_lt_iff {c x : Rep10} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1)
    (hdist : ‖x - c‖ < 2) {r : ℝ} (hr : 0 < r) :
    ‖stereoProj c x‖ < r ↔ ‖x - c‖ < capChord r := by
  have h4 : 0 < 4 - ‖x - c‖ ^ 2 := by nlinarith [norm_nonneg (x - c)]
  have hc2 : (capChord r) ^ 2 = 4 * r ^ 2 / (4 + r ^ 2) := by
    unfold capChord
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have h1 : ‖stereoProj c x‖ < r ↔ ‖stereoProj c x‖ ^ 2 < r ^ 2 := by
    constructor <;> intro h
    · exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    · exact lt_of_pow_lt_pow_left₀ 2 hr.le h
  have h2 : ‖x - c‖ < capChord r ↔ ‖x - c‖ ^ 2 < (capChord r) ^ 2 := by
    constructor <;> intro h
    · exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    · exact lt_of_pow_lt_pow_left₀ 2 (capChord_pos hr).le h
  rw [h1, h2, normSq_stereoProj hc hx hdist, hc2, div_lt_iff₀ h4]
  rw [lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

lemma capChart_eq (c v : Rep10) :
    PlanarTestLocal.capChart c v =
      (4 / (‖v‖ ^ 2 + 4)) • v + ((4 - ‖v‖ ^ 2) / (‖v‖ ^ 2 + 4)) • c := by
  simp only [PlanarTestLocal.capChart, stereoInvFunAux, sub_eq_add_neg, smul_add,
    smul_smul, div_eq_inv_mul, add_smul, smul_neg, neg_add, ← neg_smul]
  congr 1
  rw [← add_smul]
  congr 1
  ring

lemma capChart_stereoProj {c x : Rep10} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1)
    (hdist : ‖x - c‖ < 2) :
    PlanarTestLocal.capChart c (stereoProj c x) = x := by
  have hp : 0 < 1 + ⟪c, x⟫_ℝ := one_add_inner_pos_of_norm_sub_lt hc hx hdist
  have hpne : 1 + ⟪c, x⟫_ℝ ≠ 0 := hp.ne'
  have hnsq : ‖stereoProj c x‖ ^ 2 = 4 * (1 - ⟪c, x⟫_ℝ) / (1 + ⟪c, x⟫_ℝ) := by
    rw [normSq_stereoProj hc hx hdist, norm_sub_sq_eq hc hx]
    have hp2 : 2 * (1 + ⟪c, x⟫_ℝ) ≠ 0 := by linarith
    have h4 : 4 - 2 * (1 - ⟪c, x⟫_ℝ) = 2 * (1 + ⟪c, x⟫_ℝ) := by ring
    rw [h4]
    field_simp
  have hden : ‖stereoProj c x‖ ^ 2 + 4 = 8 / (1 + ⟪c, x⟫_ℝ) := by
    rw [hnsq]; field_simp; ring
  have hnum : 4 - ‖stereoProj c x‖ ^ 2 = 8 * ⟪c, x⟫_ℝ / (1 + ⟪c, x⟫_ℝ) := by
    rw [hnsq]; field_simp; ring
  rw [capChart_eq, hden, hnum, stereoProj, smul_smul]
  have hcoeff1 : 4 / (8 / (1 + ⟪c, x⟫_ℝ)) * (2 / (1 + ⟪c, x⟫_ℝ)) = 1 := by
    field_simp; ring
  have hcoeff2 : 8 * ⟪c, x⟫_ℝ / (1 + ⟪c, x⟫_ℝ) / (8 / (1 + ⟪c, x⟫_ℝ)) = ⟪c, x⟫_ℝ := by
    field_simp
  rw [hcoeff1, hcoeff2, one_smul, sub_add_cancel]

lemma perm10_capChart (g : Equiv.Perm (Fin 6)) (c v : Rep10) :
    perm10 g (PlanarTestLocal.capChart c v) =
      PlanarTestLocal.capChart (perm10 g c) (perm10 g v) := by
  simp only [capChart_eq, map_add, map_smul, (perm10 g).norm_map]

lemma perm10_stereoProj (g : Equiv.Perm (Fin 6)) (c x : Rep10) :
    perm10 g (stereoProj c x) = stereoProj (perm10 g c) (perm10 g x) := by
  simp only [stereoProj, map_smul, map_sub, perm10_inner]

lemma perm10_twist (g : Equiv.Perm (Fin 6)) (b v : Rep10) (a η : ℝ) :
    perm10 g (PlanarTestLocal.twist b v a η) =
      PlanarTestLocal.twist (perm10 g b) (perm10 g v) a η := by
  simp only [PlanarTestLocal.twist, map_sub, map_smul, perm10_inner]

def rhoCut (r : ℝ) : ℝ := clamp01 (2 - 6 * r / capDelta0)
def etaCut (r : ℝ) : ℝ := clamp01 (2 - 3 * r / capDelta0)
def timeCut (t : ℝ) : ℝ := clamp01 (16 * t - 1)

lemma rhoCut_nonneg (r : ℝ) : 0 ≤ rhoCut r := clamp01_nonneg _
lemma rhoCut_le_one (r : ℝ) : rhoCut r ≤ 1 := clamp01_le_one _
lemma etaCut_nonneg (r : ℝ) : 0 ≤ etaCut r := clamp01_nonneg _
lemma etaCut_le_one (r : ℝ) : etaCut r ≤ 1 := clamp01_le_one _
lemma timeCut_nonneg (t : ℝ) : 0 ≤ timeCut t := clamp01_nonneg _
lemma timeCut_le_one (t : ℝ) : timeCut t ≤ 1 := clamp01_le_one _

lemma rhoCut_eq_one {r : ℝ} (hr : r ≤ capDelta0 / 6) : rhoCut r = 1 := by
  apply clamp01_of_one_le
  have hd : 0 < capDelta0 := capDelta0_pos
  have : 6 * r / capDelta0 ≤ 1 := (div_le_one hd).mpr (by linarith)
  linarith

lemma rhoCut_eq_zero {r : ℝ} (hr : capDelta0 / 3 ≤ r) : rhoCut r = 0 := by
  apply clamp01_of_nonpos
  have hd : 0 < capDelta0 := capDelta0_pos
  have : 2 ≤ 6 * r / capDelta0 := (le_div_iff₀ hd).mpr (by linarith)
  linarith

lemma etaCut_eq_one {r : ℝ} (hr : r ≤ capDelta0 / 3) : etaCut r = 1 := by
  apply clamp01_of_one_le
  have hd : 0 < capDelta0 := capDelta0_pos
  have : 3 * r / capDelta0 ≤ 1 := (div_le_one hd).mpr (by linarith)
  linarith

lemma etaCut_eq_zero {r : ℝ} (hr : 2 * capDelta0 / 3 ≤ r) : etaCut r = 0 := by
  apply clamp01_of_nonpos
  have hd : 0 < capDelta0 := capDelta0_pos
  have : 2 ≤ 3 * r / capDelta0 := (le_div_iff₀ hd).mpr (by linarith)
  linarith

lemma etaCut_eq_one_of_rhoCut_pos {r : ℝ} (hρ : 0 < rhoCut r) : etaCut r = 1 := by
  apply etaCut_eq_one
  by_contra h
  push Not at h
  linarith [rhoCut_eq_zero h.le]

lemma timeCut_eq_zero {t : ℝ} (ht : t ≤ 1 / 16) : timeCut t = 0 := by
  apply clamp01_of_nonpos; linarith

lemma timeCut_eq_one {t : ℝ} (ht : 1 / 8 ≤ t) : timeCut t = 1 := by
  apply clamp01_of_one_le; linarith

lemma continuous_rhoCut : Continuous rhoCut :=
  continuous_clamp01.comp (continuous_const.sub ((continuous_const.mul continuous_id).div_const _))
lemma continuous_etaCut : Continuous etaCut :=
  continuous_clamp01.comp (continuous_const.sub ((continuous_const.mul continuous_id).div_const _))
lemma continuous_timeCut : Continuous timeCut :=
  continuous_clamp01.comp ((continuous_const.mul continuous_id).sub continuous_const)

def capPsi (A : InvariantCaps.CapLabel) (v : Rep10) (t : ℝ) : Rep10 :=
  if A.val.card = 3 then PlanarTestLocal.twist (bA A) v (timeCut t) (etaCut ‖v‖) else v

lemma inner_capPsi (A : InvariantCaps.CapLabel) {v : Rep10} (hv : ⟪cA A, v⟫_ℝ = 0) (t : ℝ) :
    ⟪cA A, capPsi A v t⟫_ℝ = 0 := by
  unfold capPsi
  split_ifs
  · exact PlanarTestLocal.inner_twist (inner_cA_bA A) hv _ _
  · exact hv

lemma norm_capPsi_le (A : InvariantCaps.CapLabel) (v : Rep10) (t : ℝ) :
    ‖capPsi A v t‖ ≤ ‖v‖ := by
  unfold capPsi
  split_ifs
  · have hb : ‖bA A‖ = 1 := norm_bA A
    let s : ℝ := timeCut t * etaCut ‖v‖
    have hs0 : 0 ≤ s := mul_nonneg (timeCut_nonneg t) (etaCut_nonneg ‖v‖)
    have hs1 : s ≤ 1 := by
      have ht1 : timeCut t ≤ 1 := timeCut_le_one t
      have he1 : etaCut ‖v‖ ≤ 1 := etaCut_le_one ‖v‖
      have he0 : 0 ≤ etaCut ‖v‖ := etaCut_nonneg ‖v‖
      nlinarith
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have htw : PlanarTestLocal.twist (bA A) v (timeCut t) (etaCut ‖v‖) =
        v - (2 * s * ⟪bA A, v⟫_ℝ) • bA A := by
      simp [PlanarTestLocal.twist, s, mul_assoc]
    have hcomm : ⟪v, bA A⟫_ℝ = ⟪bA A, v⟫_ℝ := real_inner_comm _ _
    rw [htw, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hb, mul_one,
      inner_smul_right, hcomm, sq_abs]
    have hcoeff : 0 ≤ 4 * s * (1 - s) * ⟪bA A, v⟫_ℝ ^ 2 := by
      have : 0 ≤ 1 - s := sub_nonneg.mpr hs1
      positivity
    nlinarith
  · exact le_rfl

lemma perm10_capPsi (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) (v : Rep10) (t : ℝ) :
    perm10 g (capPsi A v t) = capPsi (permCap g A) (perm10 g v) t := by
  unfold capPsi
  rw [permCap_card, (perm10 g).norm_map]
  split_ifs
  · rw [perm10_twist, perm10_bA]
  · rfl

lemma capPsi_eq_zero_iff {A : InvariantCaps.CapLabel} {v : Rep10} {t : ℝ}
    (ht : 1 / 8 ≤ t) (hη : etaCut ‖v‖ = 1) :
    capPsi A v t = 0 ↔ v = 0 := by
  unfold capPsi
  split_ifs
  · rw [timeCut_eq_one ht, hη]
    exact PlanarTestLocal.twist_one_eq_zero_iff (norm_bA A)
  · rfl

def localCapPush (A : InvariantCaps.CapLabel) (x : Rep10) (t : ℝ) : Rep10 :=
  let v := stereoProj (cA A) x
  let ψ := capPsi A v t
  let α := timeCut t * rhoCut ‖v‖
  (1 - α) • PlanarTestLocal.capChart (cA A) ψ + α • (cA A + ψ) - (4 * t * rhoCut ‖v‖) • cA A

def localCapDelta (A : InvariantCaps.CapLabel) (x : Rep10) (t : ℝ) : Rep10 :=
  if ‖x - cA A‖ < capChord (3 * capDelta0 / 4) then localCapPush A x t - x else 0

lemma localCapPush_eq_self_of_outer {A : InvariantCaps.CapLabel} {x : Rep10} (hx : ‖x‖ = 1)
    (hdist : capChord (2 * capDelta0 / 3) ≤ ‖x - cA A‖)
    (hin : ‖x - cA A‖ < capChord (3 * capDelta0 / 4)) (t : ℝ) :
    localCapPush A x t = x := by
  have hd0 : 0 < capDelta0 := capDelta0_pos
  have hlt2 : ‖x - cA A‖ < 2 :=
    hin.trans ((capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith))
  have hvge : 2 * capDelta0 / 3 ≤ ‖stereoProj (cA A) x‖ := by
    by_contra hlt
    push Not at hlt
    have hlt' := (norm_stereoProj_lt_iff (norm_cA A) hx hlt2 (by positivity)).mp hlt
    linarith
  have hρ : rhoCut ‖stereoProj (cA A) x‖ = 0 :=
    rhoCut_eq_zero (le_trans (by linarith) hvge)
  have hη : etaCut ‖stereoProj (cA A) x‖ = 0 := etaCut_eq_zero hvge
  have hψ : capPsi A (stereoProj (cA A) x) t = stereoProj (cA A) x := by
    unfold capPsi
    split_ifs
    · dsimp [PlanarTestLocal.twist]
      rw [hη, mul_zero, zero_mul, zero_smul, sub_zero]
    · rfl
  simp only [localCapPush, hρ, mul_zero, sub_zero, one_smul, zero_smul, add_zero, hψ]
  exact capChart_stereoProj (norm_cA A) hx hlt2

lemma localCapDelta_eq_zero_of_ge {A : InvariantCaps.CapLabel} {x : Rep10} (hx : ‖x‖ = 1)
    (hdist : capChord (2 * capDelta0 / 3) ≤ ‖x - cA A‖) (t : ℝ) :
    localCapDelta A x t = 0 := by
  unfold localCapDelta
  split_ifs with hin
  · rw [localCapPush_eq_self_of_outer hx hdist hin t, sub_self]
  · rfl

private lemma continuousOn_stereoProj (c : Rep10)
    {s : Set (Metric.sphere (0 : Rep10) 1 × ℝ)}
    (hs : ∀ p ∈ s, 1 + ⟪c, p.1.1⟫_ℝ ≠ 0) :
    ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => stereoProj c p.1.1) s := by
  have hfst : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hinn : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => ⟪c, p.1.1⟫_ℝ) :=
    continuous_const.inner hfst
  have hden : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      2 / (1 + ⟪c, p.1.1⟫_ℝ)) s :=
    continuousOn_const.div (continuous_const.add hinn).continuousOn hs
  have hvec : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      p.1.1 - ⟪c, p.1.1⟫_ℝ • c) :=
    hfst.sub (hinn.smul continuous_const)
  exact hden.smul hvec.continuousOn

private lemma continuous_twist_apply (b : Rep10) :
    Continuous (fun q : Rep10 × ℝ × ℝ => PlanarTestLocal.twist b q.1 q.2.1 q.2.2) := by
  unfold PlanarTestLocal.twist
  fun_prop

private lemma continuousOn_localCapPush (A : InvariantCaps.CapLabel)
    {s : Set (Metric.sphere (0 : Rep10) 1 × ℝ)}
    (hs : ∀ p ∈ s, ‖p.1.1 - cA A‖ < 2) :
    ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => localCapPush A p.1.1 p.2) s := by
  have h1_pos : ∀ p ∈ s, 1 + ⟪cA A, p.1.1⟫_ℝ ≠ 0 := fun p hp =>
    (one_add_inner_pos_of_norm_sub_lt (norm_cA A) (mem_sphere_zero_iff_norm.mp p.1.2)
      (hs p hp)).ne'
  have hsp : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      stereoProj (cA A) p.1.1) s :=
    continuousOn_stereoProj (cA A) h1_pos
  have hψ : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      capPsi A (stereoProj (cA A) p.1.1) p.2) s := by
    unfold capPsi
    split_ifs
    · have harg : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
          (stereoProj (cA A) p.1.1, timeCut p.2, etaCut ‖stereoProj (cA A) p.1.1‖)) s :=
        hsp.prodMk ((continuous_timeCut.comp continuous_snd).continuousOn.prodMk
          (continuous_etaCut.comp_continuousOn hsp.norm))
      exact (continuous_twist_apply (bA A)).comp_continuousOn harg
    · exact hsp
  have hchart : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      PlanarTestLocal.capChart (cA A) (capPsi A (stereoProj (cA A) p.1.1) p.2)) s :=
    (PlanarTestLocal.contDiff_capChart (cA A) (n := ⊤)).continuous.comp_continuousOn hψ
  have hρ : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      rhoCut ‖stereoProj (cA A) p.1.1‖) s :=
    continuous_rhoCut.comp_continuousOn hsp.norm
  have hα : ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
      timeCut p.2 * rhoCut ‖stereoProj (cA A) p.1.1‖) s :=
    (continuous_timeCut.comp continuous_snd).continuousOn.mul hρ
  change ContinuousOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ =>
    (1 - timeCut p.2 * rhoCut ‖stereoProj (cA A) p.1.1‖) •
      PlanarTestLocal.capChart (cA A) (capPsi A (stereoProj (cA A) p.1.1) p.2) +
    (timeCut p.2 * rhoCut ‖stereoProj (cA A) p.1.1‖) •
      (cA A + capPsi A (stereoProj (cA A) p.1.1) p.2) -
    (4 * p.2 * rhoCut ‖stereoProj (cA A) p.1.1‖) • cA A) s
  exact (((continuousOn_const.sub hα).smul hchart).add
    (hα.smul (continuousOn_const.add hψ))).sub
    (((continuousOn_const.mul continuous_snd.continuousOn).mul hρ).smul continuousOn_const)

lemma continuous_localCapDelta_sphere (A : InvariantCaps.CapLabel) :
    Continuous (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => localCapDelta A p.1.1 p.2) := by
  have hd0 : 0 < capDelta0 := capDelta0_pos
  let U1 : Set (Metric.sphere (0 : Rep10) 1 × ℝ) :=
    {p | ‖p.1.1 - cA A‖ < capChord (3 * capDelta0 / 4)}
  let U2 : Set (Metric.sphere (0 : Rep10) 1 × ℝ) :=
    {p | capChord (2 * capDelta0 / 3) < ‖p.1.1 - cA A‖}
  have hU1 : IsOpen U1 :=
    isOpen_lt ((continuous_subtype_val.comp continuous_fst).sub continuous_const).norm
      continuous_const
  have hU2 : IsOpen U2 :=
    isOpen_lt continuous_const
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const).norm
  have hcov : U1 ∪ U2 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    have hlt : capChord (2 * capDelta0 / 3) < capChord (3 * capDelta0 / 4) :=
      capChord_strictMono (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
        (by linarith)
    by_cases h : ‖p.1.1 - cA A‖ < capChord (3 * capDelta0 / 4)
    · exact Or.inl h
    · exact Or.inr (lt_of_lt_of_le hlt (not_lt.mp h))
  rw [← continuousOn_univ, ← hcov]
  refine ContinuousOn.union_of_isOpen ?_ ?_ hU1 hU2
  · have heq : Set.EqOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => localCapDelta A p.1.1 p.2)
        (fun p => localCapPush A p.1.1 p.2 - p.1.1) U1 := fun p hp => by
      have hp' : ‖p.1.1 - cA A‖ < capChord (3 * capDelta0 / 4) := hp
      simp [localCapDelta, hp']
    have hlt2 : ∀ p ∈ U1, ‖p.1.1 - cA A‖ < 2 := fun p hp =>
      lt_trans hp ((capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith))
    have hfst : Continuous (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => p.1.1) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuousOn_localCapPush A hlt2).sub hfst.continuousOn).congr heq
  · have heq : Set.EqOn (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => localCapDelta A p.1.1 p.2)
        (fun _ => 0) U2 := fun p hp =>
      localCapDelta_eq_zero_of_ge (mem_sphere_zero_iff_norm.mp p.1.2) (le_of_lt hp) p.2
    exact continuousOn_const.congr heq

def spherePush (x : Metric.sphere (0 : Rep10) 1) (t : ℝ) : Rep10 :=
  (x : Rep10) + ∑ A : InvariantCaps.CapLabel, localCapDelta A x t

lemma continuous_spherePush :
    Continuous (fun p : Metric.sphere (0 : Rep10) 1 × ℝ => spherePush p.1 p.2) := by
  unfold spherePush
  refine (continuous_subtype_val.comp continuous_fst).add ?_
  exact continuous_finsetSum _ fun A _ => continuous_localCapDelta_sphere A

lemma spherePush_zero (x : Metric.sphere (0 : Rep10) 1) : spherePush x 0 = x := by
  suffices h : ∀ A : InvariantCaps.CapLabel, localCapDelta A x 0 = 0 by
    simp [spherePush, h]
  intro A
  unfold localCapDelta
  split_ifs with hin
  · have hx : ‖(x : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hd0 : 0 < capDelta0 := capDelta0_pos
    have h2 : ‖(x : Rep10) - cA A‖ < 2 :=
      hin.trans ((capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith))
    have ht0 : timeCut 0 = 0 := timeCut_eq_zero (by norm_num)
    have hψ : capPsi A (stereoProj (cA A) x) 0 = stereoProj (cA A) x := by
      unfold capPsi
      split_ifs <;> simp [PlanarTestLocal.twist, ht0]
    simp only [localCapPush, ht0, zero_mul, sub_zero, one_smul, mul_zero, zero_smul, add_zero, hψ,
      capChart_stereoProj (norm_cA A) hx h2, sub_self]
  · rfl

lemma caps_disjoint_chord {A B : InvariantCaps.CapLabel} (hne : A ≠ B) {x : Rep10}
    (hxA : ‖x - cA A‖ < capChord (3 * capDelta0 / 4)) :
    ¬ ‖x - cA B‖ < capChord (3 * capDelta0 / 4) := by
  intro hxB
  have hd0 : 0 < capDelta0 := capDelta0_pos
  have h1 : ‖x - cA A‖ < capDelta0 :=
    hxA.trans ((capChord_lt_self (by positivity)).trans (by linarith))
  have h2 : ‖x - cA B‖ < capDelta0 :=
    hxB.trans ((capChord_lt_self (by positivity)).trans (by linarith))
  have hsep := capDelta0_sep hne
  have htri : ‖cA A - cA B‖ ≤ ‖x - cA A‖ + ‖x - cA B‖ := by
    calc
      ‖cA A - cA B‖ = ‖(x - cA B) - (x - cA A)‖ := by abel_nf
      _ ≤ ‖x - cA B‖ + ‖x - cA A‖ := norm_sub_le _ _
      _ = ‖x - cA A‖ + ‖x - cA B‖ := add_comm _ _
  linarith

lemma spherePush_eq_localCapPush {x : Metric.sphere (0 : Rep10) 1} {A : InvariantCaps.CapLabel}
    (hA : ‖(x : Rep10) - cA A‖ < capChord (3 * capDelta0 / 4)) (t : ℝ) :
    spherePush x t = localCapPush A x t := by
  unfold spherePush
  rw [Finset.sum_eq_single A]
  · simp [localCapDelta, hA]
  · intro B _ hBA
    have hnot : ¬ ‖(x : Rep10) - cA B‖ < capChord (3 * capDelta0 / 4) :=
      caps_disjoint_chord hBA.symm hA
    simp [localCapDelta, hnot]
  · intro hmem; exact (hmem (Finset.mem_univ _)).elim

lemma spherePush_eq_self_outside {x : Metric.sphere (0 : Rep10) 1}
    (hout : ∀ A : InvariantCaps.CapLabel, capChord (2 * capDelta0 / 3) ≤ ‖(x : Rep10) - cA A‖)
    (t : ℝ) : spherePush x t = x := by
  have hx : ‖(x : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hz : ∀ A, localCapDelta A x t = 0 := fun A =>
    localCapDelta_eq_zero_of_ge hx (hout A) t
  simp [spherePush, hz]

lemma perm10_localCapDelta (g : Equiv.Perm (Fin 6)) (A : InvariantCaps.CapLabel) (x : Rep10)
    (t : ℝ) :
    perm10 g (localCapDelta A x t) = localCapDelta (permCap g A) (perm10 g x) t := by
  have hnorm : ‖perm10 g x - cA (permCap g A)‖ = ‖x - cA A‖ := by
    rw [← perm10_cA g A, ← map_sub, (perm10 g).norm_map]
  unfold localCapDelta
  rw [hnorm]
  split_ifs
  · rw [map_sub]
    congr 1
    simp only [localCapPush, map_sub, map_add, map_smul, ← perm10_cA g A,
      ← perm10_stereoProj g (cA A) x, (perm10 g).norm_map, perm10_capPsi, perm10_capChart]
  · simp

lemma spherePush_equivariant (g : Equiv.Perm (Fin 6)) (x : Metric.sphere (0 : Rep10) 1) (t : ℝ) :
    spherePush (permSphere g x) t = perm10 g (spherePush x t) := by
  unfold spherePush
  rw [map_add, map_sum]
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.ofBijective (permCap g) (permCap_bijective g)) _ _ fun A => ?_
  exact perm10_localCapDelta g A x.1 t

lemma localCapPush_eq_zero_iff {A : InvariantCaps.CapLabel} {x : Metric.sphere (0 : Rep10) 1}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hxA : ‖(x : Rep10) - cA A‖ < capChord (3 * capDelta0 / 4)) :
    localCapPush A x t = 0 ↔ (x : Rep10) = cA A ∧ t = 1 / 4 := by
  have hx : ‖(x : Rep10)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hc : ‖cA A‖ = 1 := norm_cA A
  have hd0 : 0 < capDelta0 := capDelta0_pos
  have h2 : ‖(x : Rep10) - cA A‖ < 2 :=
    hxA.trans ((capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith))
  set v := stereoProj (cA A) x.1
  set ψ := capPsi A v t
  set ρ := rhoCut ‖v‖
  set α := timeCut t * ρ
  have hv_perp : ⟪cA A, v⟫_ℝ = 0 := inner_stereoProj hc x.1
  have hψ_perp : ⟪cA A, ψ⟫_ℝ = 0 := inner_capPsi A hv_perp t
  constructor
  · intro hz
    have hchart_c : ⟪cA A, PlanarTestLocal.capChart (cA A) ψ⟫_ℝ =
        (4 - ‖ψ‖ ^ 2) / (‖ψ‖ ^ 2 + 4) := by
      rw [capChart_eq, inner_add_right, inner_smul_right, inner_smul_right, hψ_perp,
        real_inner_self_eq_norm_sq, hc]
      ring
    have hchart_proj :
        PlanarTestLocal.capChart (cA A) ψ - ⟪cA A, PlanarTestLocal.capChart (cA A) ψ⟫_ℝ • cA A =
          (4 / (‖ψ‖ ^ 2 + 4)) • ψ := by
      conv_lhs => arg 1; rw [capChart_eq]
      rw [hchart_c, add_sub_cancel_right]
    have hsum_perp : ((1 - α) * (4 / (‖ψ‖ ^ 2 + 4)) + α) • ψ = 0 := by
      have hinner_all :
          ⟪cA A, localCapPush A x.1 t⟫_ℝ =
            (1 - α) * ((4 - ‖ψ‖ ^ 2) / (‖ψ‖ ^ 2 + 4)) + α - 4 * t * ρ := by
        dsimp [localCapPush]
        rw [show capPsi A (stereoProj (cA A) x.1) t = ψ from rfl,
          show rhoCut ‖stereoProj (cA A) x.1‖ = ρ from rfl,
          show timeCut t * ρ = α from rfl]
        rw [inner_sub_right, inner_add_right, inner_smul_right, hchart_c, smul_add,
          inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq, hc, hψ_perp]
        ring
      have hproj_lhs :
          localCapPush A x.1 t - ⟪cA A, localCapPush A x.1 t⟫_ℝ • cA A =
            ((1 - α) * (4 / (‖ψ‖ ^ 2 + 4)) + α) • ψ := by
        calc
          localCapPush A x.1 t - ⟪cA A, localCapPush A x.1 t⟫_ℝ • cA A
              = (1 - α) • PlanarTestLocal.capChart (cA A) ψ + α • (cA A + ψ) - (4 * t * ρ) • cA A
                  - (((1 - α) * ((4 - ‖ψ‖ ^ 2) / (‖ψ‖ ^ 2 + 4)) + α - 4 * t * ρ) • cA A) := by
                rw [hinner_all]; rfl
          _ = (1 - α) • (PlanarTestLocal.capChart (cA A) ψ -
                  ((4 - ‖ψ‖ ^ 2) / (‖ψ‖ ^ 2 + 4)) • cA A) + α • ψ := by
                module
          _ = (1 - α) • ((4 / (‖ψ‖ ^ 2 + 4)) • ψ) + α • ψ := by
                rw [← hchart_c, hchart_proj]
          _ = ((1 - α) * (4 / (‖ψ‖ ^ 2 + 4)) + α) • ψ := by module
      rw [hz, inner_zero_right, zero_smul, sub_zero] at hproj_lhs
      exact hproj_lhs.symm
    have hα0 : 0 ≤ α := mul_nonneg (timeCut_nonneg t) (rhoCut_nonneg ‖v‖)
    have hα1 : α ≤ 1 := by
      have ht1' : timeCut t ≤ 1 := timeCut_le_one t
      have hr1' : rhoCut ‖v‖ ≤ 1 := rhoCut_le_one ‖v‖
      have hr0' : 0 ≤ rhoCut ‖v‖ := rhoCut_nonneg ‖v‖
      dsimp [α]
      nlinarith
    have hfac_pos : 0 < (1 - α) * (4 / (‖ψ‖ ^ 2 + 4)) + α := by
      have h1 : 0 < 4 / (‖ψ‖ ^ 2 + 4) := by positivity
      by_cases hα : α = 1
      · rw [hα]; norm_num
      · have : 0 < 1 - α := sub_pos.mpr (lt_of_le_of_ne hα1 hα)
        nlinarith
    have hψ0 : ψ = 0 := (smul_eq_zero.mp hsum_perp).resolve_left hfac_pos.ne'
    have hinner0 : ⟪cA A, localCapPush A x.1 t⟫_ℝ = 0 := by rw [hz, inner_zero_right]
    dsimp [localCapPush] at hinner0
    rw [show capPsi A (stereoProj (cA A) x.1) t = ψ from rfl,
      show rhoCut ‖stereoProj (cA A) x.1‖ = ρ from rfl,
      show timeCut t * ρ = α from rfl,
      hψ0, PlanarTestLocal.capChart_zero, add_zero, inner_sub_right, inner_add_right,
      inner_smul_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hc] at hinner0
    have h4tρ : 4 * t * ρ = 1 := by linarith
    have hρ1 : ρ ≤ 1 := rhoCut_le_one ‖v‖
    have hρ0 : 0 ≤ ρ := rhoCut_nonneg ‖v‖
    have htq : 1 / 4 ≤ t := by nlinarith
    have hρp : 0 < ρ := by nlinarith
    have hv0 : v = 0 := (capPsi_eq_zero_iff (by linarith) (etaCut_eq_one_of_rhoCut_pos hρp)).mp hψ0
    have hx_eq : x.1 = cA A := by
      rw [← capChart_stereoProj hc hx h2]
      change PlanarTestLocal.capChart (cA A) v = cA A
      rw [hv0, PlanarTestLocal.capChart_zero]
    have hρ_val : ρ = 1 := by
      dsimp [ρ]; rw [hv0, norm_zero]; exact rhoCut_eq_one (by linarith)
    refine ⟨hx_eq, ?_⟩
    rw [hρ_val] at h4tρ
    linarith
  · rintro ⟨hx_eq, rfl⟩
    have hv0 : v = 0 := by simp [v, stereoProj, hx_eq, hc]
    have hψ0 : ψ = 0 := by
      dsimp [ψ, capPsi]
      split_ifs <;> simp [hv0, PlanarTestLocal.twist]
    have hρ1 : ρ = 1 := by
      dsimp [ρ]; rw [hv0, norm_zero]; exact rhoCut_eq_one (by linarith)
    change (1 - α) • PlanarTestLocal.capChart (cA A) ψ + α • (cA A + ψ) -
      (4 * (1 / 4) * ρ) • cA A = 0
    rw [hψ0, PlanarTestLocal.capChart_zero, hρ1]
    module

theorem spherePush_eq_zero_iff {x : Metric.sphere (0 : Rep10) 1} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    spherePush x t = 0 ↔ ∃ A : InvariantCaps.CapLabel, (x : Rep10) = cA A ∧ t = 1 / 4 := by
  have hd0 : 0 < capDelta0 := capDelta0_pos
  constructor
  · intro hsp
    by_cases hA : ∃ A : InvariantCaps.CapLabel, ‖(x : Rep10) - cA A‖ < capChord (3 * capDelta0 / 4)
    · obtain ⟨A, hAx⟩ := hA
      rw [spherePush_eq_localCapPush hAx t, localCapPush_eq_zero_iff ht0 ht1 hAx] at hsp
      exact ⟨A, hsp⟩
    · push Not at hA
      have hout : ∀ A, capChord (2 * capDelta0 / 3) ≤ ‖(x : Rep10) - cA A‖ := fun A =>
        le_trans (capChord_strictMono (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr (by linarith)) (by linarith)).le (hA A)
      rw [spherePush_eq_self_outside hout t] at hsp
      exfalso
      have hn := mem_sphere_zero_iff_norm.mp x.2
      rw [hsp, norm_zero] at hn
      norm_num at hn
  · rintro ⟨A, hxA, rfl⟩
    have hAx : ‖(x : Rep10) - cA A‖ < capChord (3 * capDelta0 / 4) := by
      rw [hxA, sub_self, norm_zero]
      exact capChord_pos (by linarith)
    rw [spherePush_eq_localCapPush hAx (1 / 4)]
    exact (localCapPush_eq_zero_iff ht0 ht1 hAx).mpr ⟨hxA, rfl⟩

attribute [irreducible] spherePush

lemma spherePush_half_ne_zero (x : Metric.sphere (0 : Rep10) 1) :
    spherePush x (1 / 2) ≠ 0 := by
  intro hz
  obtain ⟨_, _, ht⟩ := (spherePush_eq_zero_iff (by norm_num) le_rfl).mp hz
  norm_num at ht

def q0Map (x : Metric.sphere (0 : Rep10) 1) : Metric.sphere (0 : Rep10) 1 :=
  ⟨‖spherePush x (1 / 2)‖⁻¹ • spherePush x (1 / 2), by
    have hne := spherePush_half_ne_zero x
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne)),
      inv_mul_cancel₀ (norm_pos_iff.mpr hne).ne']⟩

lemma continuous_q0Map : Continuous q0Map := by
  rw [continuous_induced_rng]
  have hfix : Continuous (fun x : Metric.sphere (0 : Rep10) 1 => (x, (1 / 2 : ℝ))) :=
    continuous_id.prodMk continuous_const
  have hsp : Continuous (fun x : Metric.sphere (0 : Rep10) 1 => spherePush x (1 / 2)) :=
    Continuous.comp (g := fun p : Metric.sphere (0 : Rep10) 1 × ℝ => spherePush p.1 p.2)
      (f := fun x : Metric.sphere (0 : Rep10) 1 => (x, (1 / 2 : ℝ)))
      continuous_spherePush hfix
  have hval : (Subtype.val ∘ q0Map) =
      fun x : Metric.sphere (0 : Rep10) 1 => ‖spherePush x (1 / 2)‖⁻¹ • spherePush x (1 / 2) := rfl
  rw [hval]
  exact (hsp.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (spherePush_half_ne_zero x))).smul hsp

def q0 : C(Metric.sphere (0 : Rep10) 1, Metric.sphere (0 : Rep10) 1) :=
  ⟨q0Map, continuous_q0Map⟩

lemma q0_val (x : Metric.sphere (0 : Rep10) 1) :
    (q0 x : Rep10) = ‖spherePush x (1 / 2)‖⁻¹ • spherePush x (1 / 2) := by
  simp only [q0, ContinuousMap.coe_mk, q0Map]

lemma q0_equivariant (g : Equiv.Perm (Fin 6)) (x : Metric.sphere (0 : Rep10) 1) :
    q0 (permSphere g x) = permSphere g (q0 x) := by
  apply Subtype.ext
  rw [q0_val, permSphere_val, q0_val, spherePush_equivariant, (perm10 g).norm_map, map_smul]

def anchorS : Metric.sphere (0 : Rep10) 1 :=
  ⟨anchor10, mem_sphere_zero_iff_norm.mpr norm_anchor10⟩

lemma permSphere_anchorS {g : Equiv.Perm (Fin 6)}
    (hg : ∀ i : Fin 6, i.1 < 4 → (g i).1 < 4) :
    permSphere g anchorS = anchorS := by
  apply Subtype.ext
  exact perm10_anchor10 hg

lemma q0_anchorS : q0 anchorS = anchorS := by
  have hd0 : 0 < capDelta0 := capDelta0_pos
  have hout : ∀ A : InvariantCaps.CapLabel,
      capChord (2 * capDelta0 / 3) ≤ ‖(anchorS : Rep10) - cA A‖ := fun A => by
    change capChord (2 * capDelta0 / 3) ≤ ‖anchor10 - cA A‖
    rw [norm_anchor10_sub_cA A]
    have h1 : capChord (2 * capDelta0 / 3) < 1 :=
      (capChord_lt_self (by positivity)).trans (by have := capDelta0_lt; linarith)
    have h2 : (1 : ℝ) < Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt zero_le_one one_lt_two
    linarith
  have hsp : spherePush anchorS (1 / 2) = anchor10 :=
    spherePush_eq_self_outside hout (1 / 2)
  apply Subtype.ext
  rw [q0_val, hsp, norm_anchor10, inv_one, one_smul]
  rfl

end GlobalPush

end AkopyanResearch
