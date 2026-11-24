module

public import AkopyanResearch.Completion.PairOrbit
public import AkopyanResearch.Completion.ConcreteComparisonTarget
public import AkopyanResearch.Completion.QuadraticLink

/-!
# The actual single-coordinate space is a product of nine-spheres

The row-enumeration relations in the concrete target are removed by an explicit
homeomorphism indexed by the actual six-matchings. No orbit-classification or
connectivity hypothesis is assumed. This identifies only the single-coordinate
base; the full target also has its constrained pair paths.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.SingleCoordinateModel

open scoped Classical
open AkopyanQuadratic OriginalJoinBridge MatchingSphereMap PairRepresentation PairOrbit
open ConcreteComparisonTarget

abbrev Coordinates (S : Finset (Fin 15)) :=
  {f : SingleLabels S → Target // ∀ (σ : SingleLabels S) (τ : RowGroup),
    f (fun c => σ c * τ) = permSphere τ⁻¹ (f σ)}

def enumeration {S : Finset (Fin 15)} (m : MatchingIndex S) : SingleLabels S :=
  enumerationPermutation m.2
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using m.2.1)).symm

theorem matchingWords_enumeration' {S : Finset (Fin 15)} (m : MatchingIndex S) :
    matchingWords (enumeration m) = m.1 := matchingWords_enumeration m.2 _

def matchingIndex {S : Finset (Fin 15)} (hS : S.Nonempty) (σ : SingleLabels S) :
    MatchingIndex S := ⟨matchingWords σ, matchingWords_sixMatching hS σ⟩

theorem matchingIndex_enumeration {S : Finset (Fin 15)} (hS : S.Nonempty)
    (m : MatchingIndex S) : matchingIndex hS (enumeration m) = m := by
  apply Subtype.ext
  exact matchingWords_enumeration' m

theorem matchingIndex_reindex {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ : SingleLabels S) (τ : RowGroup) :
    matchingIndex hS (fun c => σ c * τ) = matchingIndex hS σ := by
  apply Subtype.ext
  exact matchingWords_reindex σ τ

def rowChange {S : Finset (Fin 15)} (hS : S.Nonempty) (σ : SingleLabels S) : RowGroup :=
  let c : S := ⟨hS.choose, hS.choose_spec⟩
  (enumeration (matchingIndex hS σ) c)⁻¹ * σ c

theorem rowChange_spec {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ : SingleLabels S) (c : S) :
    σ c = enumeration (matchingIndex hS σ) c * rowChange hS σ := by
  obtain ⟨ρ, hρ⟩ := exists_row_reindex hS (enumeration (matchingIndex hS σ)) σ
    (matchingWords_enumeration' (matchingIndex hS σ))
  have he : rowChange hS σ = ρ := by
    let c₀ : S := ⟨hS.choose, hS.choose_spec⟩
    change (enumeration (matchingIndex hS σ) c₀)⁻¹ * σ c₀ = ρ
    rw [hρ c₀]
    exact inv_mul_cancel_left _ _
  rw [he]
  exact hρ c

theorem rowChange_reindex {S : Finset (Fin 15)} (hS : S.Nonempty)
    (σ : SingleLabels S) (τ : RowGroup) :
    rowChange hS (fun c => σ c * τ) = rowChange hS σ * τ := by
  simp only [rowChange, matchingIndex_reindex, mul_assoc]

theorem rowChange_enumeration {S : Finset (Fin 15)} (hS : S.Nonempty)
    (m : MatchingIndex S) : rowChange hS (enumeration m) = 1 := by
  simp only [rowChange, matchingIndex_enumeration, inv_mul_cancel]

def encode {S : Finset (Fin 15)} (p : Coordinates S) : MatchingIndex S → Target :=
  fun m => p.1 (enumeration m)

def decode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (f : MatchingIndex S → Target) : Coordinates S :=
  ⟨fun σ => permSphere (rowChange hS σ)⁻¹ (f (matchingIndex hS σ)), by
    intro σ τ
    dsimp only
    rw [rowChange_reindex, matchingIndex_reindex, mul_inv_rev, permSphere_mul]⟩

theorem decode_encode {S : Finset (Fin 15)} (hS : S.Nonempty) (p : Coordinates S) :
    decode hS (encode p) = p := by
  apply Subtype.ext
  funext σ
  have he : (fun c => enumeration (matchingIndex hS σ) c * rowChange hS σ) = σ :=
    funext fun c => (rowChange_spec hS σ c).symm
  have hr := p.2 (enumeration (matchingIndex hS σ)) (rowChange hS σ)
  rw [he] at hr
  exact hr.symm

theorem encode_decode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (f : MatchingIndex S → Target) : encode (decode hS f) = f := by
  funext m
  change permSphere (rowChange hS (enumeration m))⁻¹
    (f (matchingIndex hS (enumeration m))) = f m
  rw [rowChange_enumeration, matchingIndex_enumeration, inv_one, permSphere_one]

theorem continuous_encode (S : Finset (Fin 15)) :
    Continuous (encode (S := S)) := by
  apply continuous_pi
  intro m
  exact (continuous_apply (enumeration m)).comp continuous_subtype_val

theorem continuous_decode {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Continuous (decode hS) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro σ
  exact (continuous_permSphere (rowChange hS σ)⁻¹).comp
    (continuous_apply (matchingIndex hS σ))

/-- The original row-enumeration relations contribute one `S⁹` for each
actual six-matching, with the product topology. -/
def coordinatesHomeomorph {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Coordinates S ≃ₜ (MatchingIndex S → Target) where
  toFun := encode
  invFun := decode hS
  left_inv := decode_encode hS
  right_inv := encode_decode hS
  continuous_toFun := continuous_encode S
  continuous_invFun := continuous_decode hS

/-- The single part of the already constructed target has exactly these
row-enumeration relations. -/
def singlePart {S : Finset (Fin 15)} (p : Space S) : Coordinates S :=
  ⟨p.1.1, p.2.row⟩

theorem continuous_singlePart (S : Finset (Fin 15)) :
    Continuous (singlePart (S := S)) :=
  Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _

end AkopyanResearch.SingleCoordinateModel
