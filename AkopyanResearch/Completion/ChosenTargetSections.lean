module

public import AkopyanResearch.Completion.JoinMassCoordinates
public import AkopyanResearch.Completion.OriginalPairPath

/-!
# Chosen single values and pair paths on one fixed fifteen-color simplex

All faces use `rowMap 14` and `pairPath 14` on the same ambient colored
join. The values therefore ignore labels at zero-mass colors literally,
without any change of iterated-join stage. The formulas provide actual
chosen target data, not an extension of every possible boundary map.

The global homotopy-fiber comparison and its relative lifting theorem
are not proved here. In particular these sections are not a safe height
table and do not by themselves prove the eighteen-dimensional case.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ChosenTargetSections

open scoped OnePoint
open EquivariantJoinStep OriginalJoinBridge OriginalJoinCoordinates
  JoinMassCoordinates JoinVertexMap PairSourceProjections OriginalPairPath

abbrev Color := Fin 15
abbrev Masses := Mass Color
abbrev Columns := Color → RowGroup
abbrev PairColumns := Color → PairState

/-- One fixed fifteen-color map, used on every mass face. -/
def singleSection (σ : Columns) (z : Masses) : Target := rowMap 14 (fromMass z σ)

theorem continuous_singleSection (σ : Columns) : Continuous (singleSection σ) :=
  (continuous_rowMap 14).comp (continuous_fromMass σ)

theorem singleSection_congr_of_support (σ τ : Columns) (z : Masses)
    (h : ∀ c, z.val c ≠ 0 → σ c = τ c) :
    singleSection σ z = singleSection τ z :=
  congrArg (rowMap 14) (fromMass_congr_of_support z σ τ h)

/-- Changing an enumeration changes the sphere coordinate contravariantly. -/
theorem singleSection_enumeration_change (σ : Columns) (τ : RowGroup) (z : Masses) :
    singleSection (fun c => σ c * τ) z = permSphere τ⁻¹ (singleSection σ z) := by
  change rowMap 14 (fromMass z (Equiv.mulRight τ ∘ σ)) = _
  rw [← relabel_fromMass, rowMap_enumeration_change]
  rfl

def singleNullSection (σ : Columns) : Masses × Time → Target :=
  fun p => rowNullhomotopy 14 (fromMass p.1 σ, p.2)

theorem continuous_singleNullSection (σ : Columns) : Continuous (singleNullSection σ) :=
  (continuous_rowNullhomotopy 14).comp
    (((continuous_fromMass σ).comp continuous_fst).prodMk continuous_snd)

theorem singleNullSection_start (σ : Columns) (z : Masses) :
    singleNullSection σ (z, timeZero) = singleSection σ z :=
  rowNullhomotopy_start 14 _

theorem singleNullSection_finish (σ : Columns) (z : Masses) :
    singleNullSection σ (z, timeOne) = anchorS :=
  rowNullhomotopy_finish 14 _

theorem singleNullSection_congr_of_support (σ τ : Columns) (z : Masses)
    (h : ∀ c, z.val c ≠ 0 → σ c = τ c) (s : Time) :
    singleNullSection σ (z, s) = singleNullSection τ (z, s) := by
  unfold singleNullSection
  rw [fromMass_congr_of_support z σ τ h]

theorem singleNullSection_block_equivariant (σ : Columns) (a : RowGroup)
    (ha : a ∈ blockSubgroup) (z : Masses) (s : Time) :
    singleNullSection (fun c => σ c * a⁻¹) (z, s) =
      permSphere a (singleNullSection σ (z, s)) := by
  change rowNullhomotopy 14 (fromMass z (Equiv.mulRight a⁻¹ ∘ σ), s) = _
  rw [← relabel_fromMass]
  exact rowNullhomotopy_right_equivariant 14 a ha _ s

/-- The actual original pair collapse is nullhomotoped, with fixed color indices. -/
def pairSection (ω : PairColumns) : Masses × Time → OnePoint PairTarget :=
  fun p => pairPath 14 (fromMass p.1 ω, p.2)

theorem continuous_pairSection (ω : PairColumns) : Continuous (pairSection ω) :=
  (continuous_pairPath 14).comp
    (((continuous_fromMass ω).comp continuous_fst).prodMk continuous_snd)

theorem pairSection_start (ω : PairColumns) (z : Masses) :
    pairSection ω (z, timeZero) = pairCollapseMap (spherePairEquiv
      (singleSection (firstVertex ∘ ω) z, singleSection (secondVertex ∘ ω) z)) := by
  simpa [pairSection, singleSection, firstProjection, secondProjection,
    mapVertices_fromMass] using pairPath_start 14 (fromMass z ω)

theorem pairSection_finish (ω : PairColumns) (z : Masses) :
    pairSection ω (z, timeOne) = ∞ := pairPath_finish 14 _

theorem pairSection_congr_of_support (ω η : PairColumns) (z : Masses)
    (h : ∀ c, z.val c ≠ 0 → ω c = η c) (s : Time) :
    pairSection ω (z, s) = pairSection η (z, s) := by
  unfold pairSection
  rw [fromMass_congr_of_support z ω η h]

theorem pairSection_equivariant (h : PairGroup) (ω : PairColumns)
    (z : Masses) (s : Time) :
    pairSection (fun c => h • ω c) (z, s) = actOnePoint h (pairSection ω (z, s)) := by
  change pairPath 14 (fromMass z (statePerm h ∘ ω), s) = _
  rw [← relabel_fromMass]
  exact pairPath_equivariant 14 h _ s

/-- A pair which degenerates on all active colors has a constant infinity path. -/
theorem pairSection_pure (ω : PairColumns) (b : Bool) (z : Masses)
    (h : ∀ c, z.val c ≠ 0 → (ω c).2 = b) (s : Time) :
    pairSection ω (z, s) = ∞ :=
  pairPath_pure 14 b (fromMassPure Prod.snd b z ω h) s

theorem pairSection_constant_phase (σ : Columns) (b : Bool) (z : Masses) (s : Time) :
    pairSection (fun c => (σ c, b)) (z, s) = ∞ :=
  pairSection_pure _ b z (fun _ _ => rfl) s

/-- Face compatibility is equality in the fixed ambient fifteen-color source. -/
theorem singleSection_face_congr (S : Finset Color) (σ τ : Columns) (z : Masses)
    (hz : ∀ c, c ∉ S → z.val c = 0) (hστ : ∀ c ∈ S, σ c = τ c) :
    singleSection σ z = singleSection τ z := by
  apply singleSection_congr_of_support
  intro c hc
  exact hστ c (by by_contra hn; exact hc (hz c hn))

theorem pairSection_face_congr (S : Finset Color) (ω η : PairColumns) (z : Masses)
    (hz : ∀ c, c ∉ S → z.val c = 0) (hωη : ∀ c ∈ S, ω c = η c) (s : Time) :
    pairSection ω (z, s) = pairSection η (z, s) := by
  apply pairSection_congr_of_support
  intro c hc
  exact hωη c (by by_contra hn; exact hc (hz c hn))

/-- This packages the chosen continuous single values and pair paths.
It asserts no lifting into an arrangement complement. -/
theorem exists_chosen_fifteen_color_sections :
    ∃ F : Columns → Masses → Target,
    ∃ P : PairColumns → Masses × Time → OnePoint PairTarget,
      (∀ σ, Continuous (F σ)) ∧
      (∀ ω, Continuous (P ω)) ∧
      (∀ (ω : PairColumns) (z : Masses), P ω (z, timeZero) = pairCollapseMap (spherePairEquiv
        (F (firstVertex ∘ ω) z, F (secondVertex ∘ ω) z))) ∧
      (∀ (ω : PairColumns) (z : Masses), P ω (z, timeOne) = ∞) ∧
      (∀ (ω : PairColumns) (b : Bool) (z : Masses), (∀ c, z.val c ≠ 0 → (ω c).2 = b) →
        ∀ s, P ω (z, s) = ∞) ∧
      (∀ (σ τ : Columns) (z : Masses), (∀ c, z.val c ≠ 0 → σ c = τ c) → F σ z = F τ z) ∧
      (∀ (ω η : PairColumns) (z : Masses), (∀ c, z.val c ≠ 0 → ω c = η c) →
        ∀ s, P ω (z, s) = P η (z, s)) :=
  ⟨singleSection, pairSection, continuous_singleSection, continuous_pairSection,
    pairSection_start, pairSection_finish, pairSection_pure,
    singleSection_congr_of_support, pairSection_congr_of_support⟩

end AkopyanResearch.ChosenTargetSections
