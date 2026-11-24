module

public import AkopyanResearch.Completion.QuadraticPairRank
public import AkopyanResearch.Completion.MatchingSphereMap
public import AkopyanResearch.Completion.MatchingPairCollapse

/-!
# The actual linear normal model of a critical pair

The joint centered evaluation has exactly the two forbidden matching
kernels as its kernel. For four-common-word pairs its range is the whole
common-equality subspace of the original `Rep10 × Rep10` representation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairNormalModel

open scoped Classical BigOperators
open AkopyanQuadratic OriginalJoinBridge PairSourceProjections
open MatchingSphereMap MatchingPairCollapse

theorem mean_add (a b : Rows) (t : Fin 2) :
    mean (a + b) t = mean a t + mean b t := by
  simp only [mean, Pi.add_apply, Finset.sum_add_distrib, add_div]

theorem mean_smul (r : ℝ) (a : Rows) (t : Fin 2) :
    mean (r • a) t = r * mean a t := by
  simp only [mean, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

def centeredLinear : Rows →ₗ[ℝ] V10Sub where
  toFun := centered
  map_add' a b := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change (centered (a + b)).val i = (centered a).val i + (centered b).val i
    refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
    · simp only [centered_castAdd, Pi.add_apply, mean_add]
      ring
    · simp only [centered_natAdd, Pi.add_apply, mean_add]
      ring
  map_smul' r a := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change (centered (r • a)).val i = r * (centered a).val i
    refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
    · simp only [centered_castAdd, Pi.smul_apply, smul_eq_mul, mean_smul]
      ring
    · simp only [centered_natAdd, Pi.smul_apply, smul_eq_mul, mean_smul]
      ring

def matchingRowsLinear {S : Finset (Fin 15)} (σ : S → RowGroup) :
    QuadSpace S →ₗ[ℝ] Rows where
  toFun H := matchingRows H σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matchingVectorLinear {S : Finset (Fin 15)} (σ : S → RowGroup) :
    QuadSpace S →ₗ[ℝ] Rep10 :=
  iso10.toLinearEquiv.toLinearMap.comp (centeredLinear.comp (matchingRowsLinear σ))

@[simp] theorem matchingVectorLinear_apply {S : Finset (Fin 15)}
    (σ : S → RowGroup) (H : QuadSpace S) :
    matchingVectorLinear σ H = vector (matchingRows H σ) := rfl

theorem centered_eq_zero_of_constant (a : Rows)
    (ha : ∀ i j : Fin 6, ∀ t : Fin 2, a i t = a j t) : centered a = 0 := by
  have hm (t : Fin 2) : mean a t = a 0 t := by
    calc
      mean a t = (∑ j : Fin 6, a 0 t) / 6 := by
        exact congrArg (fun x : ℝ => x / 6) (Finset.sum_congr rfl (fun j _ => ha j 0 t))
      _ = a 0 t := by simp
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change (centered a).val i = 0
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · rw [centered_castAdd, hm]
    exact sub_eq_zero.mpr (ha j 0 0)
  · rw [centered_natAdd, hm]
    exact sub_eq_zero.mpr (ha j 0 1)

theorem matchingVectorLinear_eq_zero_iff {S : Finset (Fin 15)}
    (σ : S → RowGroup) (H : QuadSpace S) :
    matchingVectorLinear σ H = 0 ↔ H ∈ L_M S (matchingWords σ) := by
  constructor
  · intro hz
    have hc : centered (matchingRows H σ) = 0 := by
      apply iso10.injective
      simpa only [matchingVectorLinear_apply, vector, map_zero] using hz
    intro u hu v hv t
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact rows_eq_of_centered_eq_zero _ hc i j t
  · intro hH
    change iso10 (centered (matchingRows H σ)) = 0
    rw [centered_eq_zero_of_constant]
    · exact map_zero iso10
    · intro i j t
      exact hH (matchingWord σ i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        (matchingWord σ j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) t

theorem ker_matchingVectorLinear {S : Finset (Fin 15)} (σ : S → RowGroup) :
    LinearMap.ker (matchingVectorLinear σ) = L_M S (matchingWords σ) := by
  ext H
  exact matchingVectorLinear_eq_zero_iff σ H

def jointTest {S : Finset (Fin 15)} (ω : S → PairState) :
    QuadSpace S →ₗ[ℝ] Rep10 × Rep10 :=
  (matchingVectorLinear (firstVertex ∘ ω)).prod
    (matchingVectorLinear (secondVertex ∘ ω))

theorem ker_jointTest {S : Finset (Fin 15)} (ω : S → PairState) :
    LinearMap.ker (jointTest ω) =
      L_M S (matchingWords (firstVertex ∘ ω)) ⊓
        L_M S (matchingWords (secondVertex ∘ ω)) := by
  rw [jointTest, LinearMap.ker_prod, ker_matchingVectorLinear, ker_matchingVectorLinear]

def commonProjection : Rep10 →ₗ[ℝ] Comm6 where
  toFun x := (splitRep10 x).snd
  map_add' x y := by rw [map_add]; rfl
  map_smul' r x := by rw [map_smul]; rfl

def commonDifference : (Rep10 × Rep10) →ₗ[ℝ] Comm6 where
  toFun x := commonProjection x.1 - commonProjection x.2
  map_add' x y := by
    change commonProjection (x.1 + y.1) - commonProjection (x.2 + y.2) = _
    rw [map_add, map_add]
    abel
  map_smul' r x := by
    change commonProjection (r • x.1) - commonProjection (r • x.2) = _
    rw [map_smul, map_smul, smul_sub]
    rfl

def commonEquality : Submodule ℝ (Rep10 × Rep10) := LinearMap.ker commonDifference

theorem mem_commonEquality (x : Rep10 × Rep10) :
    x ∈ commonEquality ↔ (splitRep10 x.1).snd = (splitRep10 x.2).snd := by
  change commonProjection x.1 - commonProjection x.2 = 0 ↔ _
  exact sub_eq_zero

theorem commonDifference_surjective : Function.Surjective commonDifference := by
  intro w
  refine ⟨(splitRep10.symm (WithLp.toLp 2 (0, w)), 0), ?_⟩
  change (splitRep10 (splitRep10.symm (WithLp.toLp 2 (0, w)))).snd -
    (splitRep10 0).snd = w
  rw [LinearIsometryEquiv.apply_symm_apply, splitRep10.map_zero]
  change w - 0 = w
  exact sub_zero w

theorem finrank_commonEquality : Module.finrank ℝ commonEquality = 14 := by
  have h := commonDifference.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr commonDifference_surjective,
    finrank_top, finrank_Comm6, Module.finrank_prod] at h
  change 6 + Module.finrank ℝ commonEquality =
    Module.finrank ℝ Rep10 + Module.finrank ℝ Rep10 at h
  norm_num [Rep10] at h
  omega

theorem jointTest_mem_commonEquality {S : Finset (Fin 15)}
    (ω : S → PairState) (H : QuadSpace S) : jointTest ω H ∈ commonEquality := by
  rw [mem_commonEquality]
  apply common_eq_of_initial_differences
    (centered (matchingRows H (firstVertex ∘ ω)))
    (centered (matchingRows H (secondVertex ∘ ω)))
    (mean (matchingRows H (secondVertex ∘ ω)) 0 -
      mean (matchingRows H (firstVertex ∘ ω)) 0)
    (mean (matchingRows H (secondVertex ∘ ω)) 1 -
      mean (matchingRows H (firstVertex ∘ ω)) 1)
  · intro i
    rw [centered_castAdd, centered_castAdd, pair_rows_common]
    ring
  · intro i
    rw [centered_natAdd, centered_natAdd, pair_rows_common]
    ring

theorem range_jointTest_le {S : Finset (Fin 15)} (ω : S → PairState) :
    LinearMap.range (jointTest ω) ≤ commonEquality := by
  rintro _ ⟨H, rfl⟩
  exact jointTest_mem_commonEquality ω H

/-- The true centered pair evaluation fills the entire 14-dimensional
common-equality normal model; surjectivity is proved from the actual
quadratic interpolation and exact pair codimension. -/
theorem range_jointTest_eq_commonEquality {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) :
    LinearMap.range (jointTest ω) = commonEquality := by
  apply Submodule.eq_of_le_of_finrank_eq (range_jointTest_le ω)
  rw [← (jointTest ω).quotKerEquivRange.finrank_eq, ker_jointTest,
    finrank_commonEquality]
  exact (QuadraticPairRank.codim_pair_eq_fourteen_iff S hS _ _
    (matchingWords_sixMatching hS _) (matchingWords_sixMatching hS _)).mpr hfour

/-- The quotient by the actual intersection of matching kernels, with
its original centered pair evaluation as the equivalence map. -/
def jointQuotientEquiv {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) :
    (QuadSpace S ⧸ (L_M S (matchingWords (firstVertex ∘ ω)) ⊓
      L_M S (matchingWords (secondVertex ∘ ω)))) ≃ₗ[ℝ] commonEquality :=
  (Submodule.quotEquivOfEq _ _ (ker_jointTest ω).symm).trans
    ((jointTest ω).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_jointTest_eq_commonEquality hS ω hfour)))

@[simp] theorem jointQuotientEquiv_mk {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) (H : QuadSpace S) :
    (jointQuotientEquiv hS ω hfour (Submodule.Quotient.mk H)).val = jointTest ω H := rfl

def jointQuotientContinuousEquiv {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) :
    (QuadSpace S ⧸ (L_M S (matchingWords (firstVertex ∘ ω)) ⊓
      L_M S (matchingWords (secondVertex ∘ ω)))) ≃L[ℝ] commonEquality := by
  let p : Submodule ℝ (QuadSpace S) :=
    L_M S (matchingWords (firstVertex ∘ ω)) ⊓
      L_M S (matchingWords (secondVertex ∘ ω))
  letI : IsClosed (p : Set (QuadSpace S)) := p.closed_of_finiteDimensional
  exact (jointQuotientEquiv hS ω hfour).toContinuousLinearEquiv

@[simp] theorem jointQuotientContinuousEquiv_mk {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) (H : QuadSpace S) :
    (jointQuotientContinuousEquiv hS ω hfour (Submodule.Quotient.mk H)).val =
      jointTest ω H := by
  exact jointQuotientEquiv_mk hS ω hfour H

theorem exists_actual_joint_values {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4)
    (u v : Rep10) (huv : (splitRep10 u).snd = (splitRep10 v).snd) :
    ∃ H : QuadSpace S,
      vector (matchingRows H (firstVertex ∘ ω)) = u ∧
      vector (matchingRows H (secondVertex ∘ ω)) = v := by
  have hmem : (u, v) ∈ LinearMap.range (jointTest ω) := by
    rw [range_jointTest_eq_commonEquality hS ω hfour, mem_commonEquality]
    exact huv
  obtain ⟨H, hH⟩ := hmem
  exact ⟨H, congrArg Prod.fst hH, congrArg Prod.snd hH⟩


end AkopyanResearch.PairNormalModel
