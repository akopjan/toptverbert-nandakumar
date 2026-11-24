module

public import AkopyanResearch.QuadraticArrangement
public import AkopyanResearch.Completion.PairSourceProjections

/-!
# The actual single-matching sphere map of a quadratic complement

Six evaluated planar values are centered and then normalized in the
original representation `Rep10`. Avoidance of the corresponding matching
kernel proves that this normalization is defined. Row enumeration and
face lifting commute with the map by exact coordinate identities.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.MatchingSphereMap

open scoped BigOperators Classical
open Metric AkopyanQuadratic OriginalJoinBridge PairSourceProjections PairSphereAction

abbrev Rows := Fin 6 → Fin 2 → ℝ

def mean (a : Rows) (t : Fin 2) : ℝ := (∑ j : Fin 6, a j t) / 6

theorem sum_sub_mean (a : Rows) (t : Fin 2) :
    ∑ j : Fin 6, (a j t - mean a t) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mean]
  ring

def centered (a : Rows) : V10Sub :=
  ⟨WithLp.toLp 2 (splitPair6 (fun j => a j 0 - mean a 0)
    (fun j => a j 1 - mean a 1)), by
    rw [mem_V10Sub_iff]
    constructor
    · simpa only [PiLp.toLp_apply, splitPair6_castAdd] using sum_sub_mean a 0
    · simpa only [PiLp.toLp_apply, splitPair6_natAdd] using sum_sub_mean a 1⟩

@[simp] theorem centered_castAdd (a : Rows) (j : Fin 6) :
    (centered a).val (j.castAdd 6) = a j 0 - mean a 0 := by
  change splitPair6 (fun j => a j 0 - mean a 0)
    (fun j => a j 1 - mean a 1) (j.castAdd 6) = _
  exact splitPair6_castAdd _ _ j

@[simp] theorem centered_natAdd (a : Rows) (j : Fin 6) :
    (centered a).val (Fin.natAdd 6 j) = a j 1 - mean a 1 := by
  change splitPair6 (fun j => a j 0 - mean a 0)
    (fun j => a j 1 - mean a 1) (Fin.natAdd 6 j) = _
  exact splitPair6_natAdd _ _ j

theorem continuous_mean (t : Fin 2) : Continuous (fun a : Rows => mean a t) := by
  exact (continuous_finsetSum _ fun j _ =>
    (continuous_apply t).comp (continuous_apply j)).div_const 6

theorem continuous_centered : Continuous centered := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Rows => WithLp.toLp 2
    (splitPair6 (fun j => a j 0 - mean a 0) (fun j => a j 1 - mean a 1)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · simp only [splitPair6_castAdd]
    have he : Continuous (fun a : Rows => a j 0) :=
      (continuous_apply (0 : Fin 2)).comp (continuous_apply j)
    exact he.sub (continuous_mean 0)
  · simp only [splitPair6_natAdd]
    have he : Continuous (fun a : Rows => a j 1) :=
      (continuous_apply (1 : Fin 2)).comp (continuous_apply j)
    exact he.sub (continuous_mean 1)

theorem rows_eq_of_centered_eq_zero (a : Rows) (h : centered a = 0)
    (i j : Fin 6) (t : Fin 2) : a i t = a j t := by
  fin_cases t
  · have hi : a i 0 - mean a 0 = 0 := by
      simpa using congrArg (fun x : V10Sub => x.val (i.castAdd 6)) h
    have hj : a j 0 - mean a 0 = 0 := by
      simpa using congrArg (fun x : V10Sub => x.val (j.castAdd 6)) h
    exact (sub_eq_zero.mp hi).trans (sub_eq_zero.mp hj).symm
  · have hi : a i 1 - mean a 1 = 0 := by
      simpa using congrArg (fun x : V10Sub => x.val (Fin.natAdd 6 i)) h
    have hj : a j 1 - mean a 1 = 0 := by
      simpa using congrArg (fun x : V10Sub => x.val (Fin.natAdd 6 j)) h
    exact (sub_eq_zero.mp hi).trans (sub_eq_zero.mp hj).symm

theorem mean_reindex (a : Rows) (τ : RowGroup) (t : Fin 2) :
    mean (fun j => a (τ j)) t = mean a t := by
  unfold mean
  congr 1
  exact Fintype.sum_equiv τ _ _ (fun _ => rfl)

theorem centered_reindex (a : Rows) (τ : RowGroup) :
    centered (fun j => a (τ j)) = permSub τ⁻¹ (centered a) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · rw [centered_castAdd]
    change a (τ j) 0 - mean (fun j => a (τ j)) 0 =
      (centered a).val ((perm12 τ⁻¹).symm (j.castAdd 6))
    rw [perm12_symm, inv_inv, perm12_castAdd, centered_castAdd, mean_reindex]
  · rw [centered_natAdd]
    change a (τ j) 1 - mean (fun j => a (τ j)) 1 =
      (centered a).val ((perm12 τ⁻¹).symm (Fin.natAdd 6 j))
    rw [perm12_symm, inv_inv, perm12_natAdd, centered_natAdd, mean_reindex]

def vector (a : Rows) : Rep10 := iso10 (centered a)

theorem continuous_vector : Continuous vector := iso10.continuous.comp continuous_centered

theorem vector_reindex (a : Rows) (τ : RowGroup) :
    vector (fun j => a (τ j)) = perm10 τ⁻¹ (vector a) := by
  unfold vector
  rw [centered_reindex]
  simp [perm10]

def sphere (a : Rows) (ha : vector a ≠ 0) : Target :=
  ⟨‖vector a‖⁻¹ • vector a, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr ha)),
      inv_mul_cancel₀ (norm_pos_iff.mpr ha).ne']⟩

theorem sphere_reindex (a : Rows) (τ : RowGroup) (ha : vector a ≠ 0)
    (hb : vector (fun j => a (τ j)) ≠ 0) :
    sphere (fun j => a (τ j)) hb = permSphere τ⁻¹ (sphere a ha) := by
  apply Subtype.ext
  change ‖vector (fun j => a (τ j))‖⁻¹ • vector (fun j => a (τ j)) =
    perm10 τ⁻¹ (‖vector a‖⁻¹ • vector a)
  rw [vector_reindex, (perm10 τ⁻¹).norm_map, map_smul]

def matchingWord {S : Finset (Fin 15)} (σ : S → RowGroup) (j : Fin 6) : S → Fin 6 :=
  fun c => σ c j

def matchingWords {S : Finset (Fin 15)} (σ : S → RowGroup) : Finset (S → Fin 6) :=
  Finset.univ.image (matchingWord σ)

theorem matchingWord_injective {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ : S → RowGroup) : Function.Injective (matchingWord σ) := by
  intro i j hij
  let c : S := ⟨hS.choose, hS.choose_spec⟩
  exact (σ c).injective (congrFun hij c)

theorem matchingWords_sixMatching {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ : S → RowGroup) : SixMatching (matchingWords σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [matchingWords, Finset.card_image_of_injective _ (matchingWord_injective hS σ)]
    simp
  · intro c u hu v hv he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact congrArg (matchingWord σ) ((σ c).injective he)
  · intro c a
    refine ⟨matchingWord σ ((σ c).symm a), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (σ c).apply_symm_apply a

def matchingRows {S : Finset (Fin 15)} (H : QuadSpace S) (σ : S → RowGroup) : Rows :=
  fun j t => (H t).val (matchingWord σ j)

theorem continuous_matchingRows {S : Finset (Fin 15)} (σ : S → RowGroup) :
    Continuous (fun H : QuadComplement S => matchingRows H.val σ) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (continuous_apply (matchingWord σ j)).comp
    (continuous_subtype_val.comp ((continuous_apply t).comp continuous_subtype_val))

theorem matchingVector_ne_zero {S : Finset (Fin 15)} (hS : S.Nonempty)
    (H : QuadComplement S) (σ : S → RowGroup) : vector (matchingRows H.val σ) ≠ 0 := by
  intro hz
  have hc : centered (matchingRows H.val σ) = 0 := by
    apply iso10.injective
    simpa [vector] using hz
  apply H.property (matchingWords σ) (matchingWords_sixMatching hS σ)
  intro u hu v hv t
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  exact rows_eq_of_centered_eq_zero _ hc i j t

def matchingSphere {S : Finset (Fin 15)} (hS : S.Nonempty)
    (H : QuadComplement S) (σ : S → RowGroup) : Target :=
  sphere (matchingRows H.val σ) (matchingVector_ne_zero hS H σ)

theorem continuous_matchingSphere {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ : S → RowGroup) : Continuous (fun H : QuadComplement S => matchingSphere hS H σ) := by
  apply Continuous.subtype_mk
  have hv := continuous_vector.comp (continuous_matchingRows σ)
  exact (hv.norm.inv₀ (fun H => norm_ne_zero_iff.mpr (matchingVector_ne_zero hS H σ))).smul hv

theorem matchingSphere_enumeration_change {S : Finset (Fin 15)} (hS : S.Nonempty)
    (H : QuadComplement S) (σ : S → RowGroup) (τ : RowGroup) :
    matchingSphere hS H (fun c => σ c * τ) = permSphere τ⁻¹ (matchingSphere hS H σ) :=
  sphere_reindex (matchingRows H.val σ) τ _ _

theorem matchingRows_liftFace {T S : Finset (Fin 15)} (hTS : T ⊆ S)
    (H : QuadSpace T) (σ : S → RowGroup) :
    matchingRows (liftFace hTS H) σ = matchingRows H (σ ∘ finsetIncl hTS) := rfl

theorem matchingSphere_liftFace {T S : Finset (Fin 15)} (hT : T.Nonempty) (hTS : T ⊆ S)
    (H : QuadComplement T) (σ : S → RowGroup) :
    matchingSphere (hT.mono hTS) (liftFaceCompl hT hTS H) σ =
      matchingSphere hT H (σ ∘ finsetIncl hTS) := rfl

/-- The actual two pair-state projections evaluate the same four common words. -/
theorem pair_rows_common {S : Finset (Fin 15)} (H : QuadSpace S)
    (ω : S → PairState) (i : Fin 4) (t : Fin 2) :
    matchingRows H (firstVertex ∘ ω) (i.castAdd 2) t =
      matchingRows H (secondVertex ∘ ω) (i.castAdd 2) t := by
  apply congrArg (fun w => (H t).val w)
  funext c
  change (ω c).1 (i.castAdd 2) =
    ((ω c).1 * blockPerm 1 (ω c).2) (i.castAdd 2)
  simp [Equiv.Perm.mul_apply, blockPerm_castAdd]

end AkopyanResearch.MatchingSphereMap
