module

public import AkopyanResearch.Completion.PairConcreteLocalModel
public import AkopyanResearch.Completion.LinearPreimageHomotopy

/-!
# The actual critical-pair evaluation is a homotopy equivalence onto the collapsed locus

For a critical pair of matching kernels, the actual joint centered test is
surjective onto the common-equality representation. Its restriction to the
complement of the two original kernels is a homotopy equivalence. Composing
with the proved local normalization equivalence gives the original pair
comparison into the collapsed locus, with no unproved connectivity hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairEvaluationEquivalence

open AkopyanQuadratic OriginalJoinBridge PairSourceProjections MatchingSphereMap
open PairNormalModel PairConcreteLocalModel
open scoped ContinuousMap

def jointCommonLinear {S : Finset (Fin 15)} (ω : S → PairState) :
    QuadSpace S →ₗ[ℝ] commonEquality :=
  (jointTest ω).codRestrict commonEquality (jointTest_mem_commonEquality ω)

def jointCommon {S : Finset (Fin 15)} (ω : S → PairState) :
    QuadSpace S →L[ℝ] commonEquality := (jointCommonLinear ω).toContinuousLinearMap

theorem jointCommon_surjective {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) : Function.Surjective (jointCommon ω) := by
  intro x
  have hx : x.val ∈ LinearMap.range (jointTest ω) := by
    rw [range_jointTest_eq_commonEquality hS ω hfour]
    exact x.property
  obtain ⟨H, hH⟩ := hx
  exact ⟨H, Subtype.ext hH⟩

abbrev PairComplement {S : Finset (Fin 15)} (ω : S → PairState) :=
  {H : QuadSpace S // H ∉ L_M S (matchingWords (firstVertex ∘ ω)) ∧
    H ∉ L_M S (matchingWords (secondVertex ∘ ω))}

def commonSafe : Set commonEquality := {x | x.val.1 ≠ 0 ∧ x.val.2 ≠ 0}

theorem jointCommon_mem_safe_iff {S : Finset (Fin 15)} (ω : S → PairState)
    (H : QuadSpace S) : jointCommon ω H ∈ commonSafe ↔
      H ∉ L_M S (matchingWords (firstVertex ∘ ω)) ∧
        H ∉ L_M S (matchingWords (secondVertex ∘ ω)) := by
  change (matchingVectorLinear (firstVertex ∘ ω) H ≠ 0 ∧
    matchingVectorLinear (secondVertex ∘ ω) H ≠ 0) ↔ _
  simp only [ne_eq, matchingVectorLinear_eq_zero_iff]

def pairPreimageHomeomorph {S : Finset (Fin 15)} (ω : S → PairState) :
    PairComplement ω ≃ₜ (jointCommon ω ⁻¹' commonSafe) :=
  (Homeomorph.refl (QuadSpace S)).subtype (fun H => (jointCommon_mem_safe_iff ω H).symm)

/-- The actual centered joint evaluation, restricted to the complement of
its original two matching kernels, is a homotopy equivalence. -/
def jointEvaluationHomotopyEquiv {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) : PairComplement ω ≃ₕ CommonComplement :=
  (pairPreimageHomeomorph ω).toHomotopyEquiv.trans
    (LinearPreimageHomotopy.surjectivePreimageEquiv
      (jointCommon ω) (jointCommon_surjective hS ω hfour) commonSafe)

theorem jointEvaluationHomotopyEquiv_apply {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) (H : PairComplement ω) :
    (jointEvaluationHomotopyEquiv hS ω hfour H).val.val = jointTest ω H.val := rfl

/-- The forward map is precisely the original pair comparison, through the
two centered evaluations and their separate normalization. -/
def pairComparisonHomotopyEquiv {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) :
    PairComplement ω ≃ₕ PairConcreteLocalModel.Collapsed :=
  (jointEvaluationHomotopyEquiv hS ω hfour).trans commonNormalizationHomotopyEquiv

def globalToPair {S : Finset (Fin 15)} (hS : S.Nonempty) (ω : S → PairState)
    (H : QuadComplement S) : PairComplement ω :=
  ⟨H.val, H.property _ (matchingWords_sixMatching hS _),
    H.property _ (matchingWords_sixMatching hS _)⟩

/-- On the full arrangement complement this is exactly the original two
matching-sphere coordinates, with the original `spherePairEquiv`. -/
theorem pairComparison_on_global {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : S → PairState)
    (hfour : (matchingWords (firstVertex ∘ ω) ∩
      matchingWords (secondVertex ∘ ω)).card = 4) (H : QuadComplement S) :
    (pairComparisonHomotopyEquiv hS ω hfour (globalToPair hS ω H)).val =
      spherePairEquiv (matchingSphere hS H (firstVertex ∘ ω),
        matchingSphere hS H (secondVertex ∘ ω)) := by
  change (commonNormalizationHomotopyEquiv
    (jointEvaluationHomotopyEquiv hS ω hfour (globalToPair hS ω H))).val = _
  rw [commonNormalization_eq_sphereNormalization]
  rfl

end AkopyanResearch.PairEvaluationEquivalence
