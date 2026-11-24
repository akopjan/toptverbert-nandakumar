module

public import AkopyanResearch.Completion.PairOrbit
public import AkopyanResearch.Completion.ConcreteComparisonTarget

/-!
# Coordinates for the actual equivariant pair-path families

Evaluation at one representative of each critical pair is a homeomorphism.
The inverse uses the unique actual `PairGroup` transport on mixed labels and
the constant path at infinity on pure labels. No connectivity theorem or
additional orbit hypothesis is used. Endpoint relations are not imposed here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairPathCoordinates

open scoped Classical OnePoint
open EquivariantJoinStep OriginalJoinBridge PairSourceProjections MatchingSphereMap PairOrbit

abbrev Labels (S : Finset (Fin 15)) := S → PairState
abbrev PathSpace := C(Time, OnePoint PairTarget)

def Critical {S : Finset (Fin 15)} (ω : Labels S) : Prop :=
  (matchingWords (firstVertex ∘ ω) ∩ matchingWords (secondVertex ∘ ω)).card = 4

abbrev CriticalPairIndex (S : Finset (Fin 15)) :=
  {p : Finset (Finset (S → Fin 6)) // ∃ ω : Labels S, Critical ω ∧ pairWords ω = p}

def classOf {S : Finset (Fin 15)} (ω : Labels S) (hω : Critical ω) : CriticalPairIndex S :=
  ⟨pairWords ω, ω, hω, rfl⟩

def representative {S : Finset (Fin 15)} (i : CriticalPairIndex S) : Labels S :=
  i.2.choose

theorem representative_critical {S : Finset (Fin 15)} (i : CriticalPairIndex S) :
    Critical (representative i) := i.2.choose_spec.1

theorem representative_pairWords {S : Finset (Fin 15)} (i : CriticalPairIndex S) :
    pairWords (representative i) = i.1 := i.2.choose_spec.2

theorem classOf_representative {S : Finset (Fin 15)} (i : CriticalPairIndex S) :
    classOf (representative i) (representative_critical i) = i :=
  Subtype.ext (representative_pairWords i)

theorem critical_action_iff {S : Finset (Fin 15)} (h : PairGroup) (ω : Labels S) :
    Critical (actLabels h ω) ↔ Critical ω := by
  unfold Critical
  rw [firstWords_action, secondWords_action]
  cases h.2.ex <;> simp [Finset.inter_comm]

theorem critical_action {S : Finset (Fin 15)} (h : PairGroup) (ω : Labels S)
    (hω : Critical ω) : Critical (actLabels h ω) :=
  (critical_action_iff h ω).mpr hω

theorem classOf_action {S : Finset (Fin 15)} (h : PairGroup) (ω : Labels S)
    (hω : Critical ω) :
    classOf (actLabels h ω) (critical_action h ω hω) = classOf ω hω :=
  Subtype.ext (pairWords_action h ω)

theorem existsUnique_shift {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : Labels S) (hω : Critical ω) :
    ∃! h : PairGroup, ∀ c, h • representative (classOf ω hω) c = ω c :=
  existsUnique_action_of_unordered_pairs_eq hS (representative (classOf ω hω)) ω
    (representative_critical (classOf ω hω)) (representative_pairWords (classOf ω hω))

def shift {S : Finset (Fin 15)} (hS : S.Nonempty) (ω : Labels S) (hω : Critical ω) : PairGroup :=
  (existsUnique_shift hS ω hω).choose

theorem shift_spec {S : Finset (Fin 15)} (hS : S.Nonempty) (ω : Labels S)
    (hω : Critical ω) (c : S) :
    shift hS ω hω • representative (classOf ω hω) c = ω c :=
  (existsUnique_shift hS ω hω).choose_spec.1 c

theorem shift_eq {S : Finset (Fin 15)} (hS : S.Nonempty) (ω : Labels S)
    (hω : Critical ω) (g : PairGroup)
    (hg : ∀ c, g • representative (classOf ω hω) c = ω c) :
    g = shift hS ω hω := (existsUnique_shift hS ω hω).choose_spec.2 g hg

theorem shift_representative {S : Finset (Fin 15)} (hS : S.Nonempty)
    (i : CriticalPairIndex S) :
    shift hS (representative i) (representative_critical i) = 1 := by
  apply (shift_eq hS (representative i) (representative_critical i) 1 ?_).symm
  intro c
  rw [classOf_representative, one_smul]

theorem shift_action {S : Finset (Fin 15)} (hS : S.Nonempty)
    (h : PairGroup) (ω : Labels S) (hω : Critical ω) :
    shift hS (actLabels h ω) (critical_action h ω hω) = h * shift hS ω hω := by
  apply (shift_eq hS (actLabels h ω) (critical_action h ω hω)
    (h * shift hS ω hω) ?_).symm
  intro c
  rw [classOf_action h ω hω, mul_smul, shift_spec hS ω hω]
  rfl

theorem pure_not_critical {S : Finset (Fin 15)} (hS : S.Nonempty)
    (ω : Labels S) (b : Bool) (hb : ∀ c, (ω c).2 = b) : ¬ Critical ω := by
  intro hω
  obtain ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩⟩ :=
    PairIntersection.mixed_of_intersection_card_four hS ω hω
  cases b
  · have he := (hb c₁).symm.trans hc₁
    exact Bool.false_ne_true he
  · have he := (hb c₀).symm.trans hc₀
    exact Bool.false_ne_true he.symm

theorem pure_of_not_critical {S : Finset (Fin 15)} (ω : Labels S)
    (hω : ¬ Critical ω) : ∃ b : Bool, ∀ c, (ω c).2 = b := by
  by_cases h₀ : ∃ c, (ω c).2 = false
  · have h₁ : ¬ ∃ c, (ω c).2 = true := fun h₁ =>
      hω (PairIntersection.intersection_card_of_mixed ω h₀ h₁)
    refine ⟨false, fun c => ?_⟩
    cases hc : (ω c).2
    · rfl
    · exact False.elim (h₁ ⟨c, hc⟩)
  · refine ⟨true, fun c => ?_⟩
    cases hc : (ω c).2
    · exact False.elim (h₀ ⟨c, hc⟩)
    · rfl

def actPath (h : PairGroup) (p : PathSpace) : PathSpace :=
  (⟨actOnePoint h, continuous_actOnePoint h⟩ : C(OnePoint PairTarget, OnePoint PairTarget)).comp p

@[simp] theorem actPath_apply (h : PairGroup) (p : PathSpace) (s : Time) :
    actPath h p s = actOnePoint h (p s) := rfl

theorem continuous_actPath (h : PairGroup) : Continuous (actPath h) :=
  ContinuousMap.continuous_postcomp ⟨actOnePoint h, continuous_actOnePoint h⟩

theorem actPath_one (p : PathSpace) : actPath 1 p = p := by
  ext s
  exact actOnePoint_one (p s)

theorem actPath_mul (h g : PairGroup) (p : PathSpace) :
    actPath (h * g) p = actPath h (actPath g p) := by
  ext s
  exact actOnePoint_mul h g (p s)

def infinityPath : PathSpace := ContinuousMap.const Time ∞

structure PathRelations {S : Finset (Fin 15)} (p : Labels S → PathSpace) : Prop where
  equivariant : ∀ (h : PairGroup) (ω : Labels S) (s : Time),
    p (actLabels h ω) s = actOnePoint h (p ω s)
  pure : ∀ (ω : Labels S) (b : Bool), (∀ c, (ω c).2 = b) →
    ∀ s : Time, p ω s = ∞

abbrev Family (S : Finset (Fin 15)) := {p : Labels S → PathSpace // PathRelations p}

def encode {S : Finset (Fin 15)} (p : Family S) : CriticalPairIndex S → PathSpace :=
  fun i => p.1 (representative i)

theorem continuous_encode (S : Finset (Fin 15)) : Continuous (encode (S := S)) :=
  continuous_pi fun i => (continuous_apply (representative i)).comp continuous_subtype_val

def decodeRaw {S : Finset (Fin 15)} (hS : S.Nonempty)
    (q : CriticalPairIndex S → PathSpace) (ω : Labels S) : PathSpace :=
  if hω : Critical ω then actPath (shift hS ω hω) (q (classOf ω hω)) else infinityPath

theorem continuous_decodeRaw {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Continuous (decodeRaw hS) := by
  apply continuous_pi
  intro ω
  unfold decodeRaw
  split_ifs with hω
  · exact (continuous_actPath _).comp (continuous_apply _)
  · exact continuous_const

theorem decodeRaw_equivariant {S : Finset (Fin 15)} (hS : S.Nonempty)
    (q : CriticalPairIndex S → PathSpace) (h : PairGroup) (ω : Labels S) (s : Time) :
    decodeRaw hS q (actLabels h ω) s = actOnePoint h (decodeRaw hS q ω s) := by
  by_cases hω : Critical ω
  · have hhω := critical_action h ω hω
    simp only [decodeRaw, dite_eq_left hω, dite_eq_left hhω, actPath_apply]
    rw [shift_action hS h ω hω, classOf_action h ω hω, actOnePoint_mul]
  · have hhω : ¬ Critical (actLabels h ω) := fun hh => hω ((critical_action_iff h ω).mp hh)
    simp only [decodeRaw, dite_eq_right hω, dite_eq_right hhω]
    rfl

theorem decodeRaw_pure {S : Finset (Fin 15)} (hS : S.Nonempty)
    (q : CriticalPairIndex S → PathSpace) (ω : Labels S) (b : Bool)
    (hb : ∀ c, (ω c).2 = b) (s : Time) : decodeRaw hS q ω s = ∞ := by
  rw [decodeRaw, dite_eq_right (pure_not_critical hS ω b hb)]
  rfl

def decode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (q : CriticalPairIndex S → PathSpace) : Family S :=
  ⟨decodeRaw hS q, ⟨decodeRaw_equivariant hS q, decodeRaw_pure hS q⟩⟩

theorem continuous_decode {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Continuous (decode hS) :=
  (continuous_decodeRaw hS).subtype_mk _

theorem encode_decode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (q : CriticalPairIndex S → PathSpace) : encode (decode hS q) = q := by
  funext i
  change decodeRaw hS q (representative i) = q i
  rw [decodeRaw, dite_eq_left (representative_critical i), shift_representative,
    classOf_representative, actPath_one]

theorem decode_encode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : Family S) : decode hS (encode p) = p := by
  apply Subtype.ext
  funext ω
  apply ContinuousMap.ext
  intro s
  change decodeRaw hS (encode p) ω s = p.1 ω s
  by_cases hω : Critical ω
  · rw [decodeRaw, dite_eq_left hω]
    change actOnePoint (shift hS ω hω) (p.1 (representative (classOf ω hω)) s) = p.1 ω s
    have he := p.2.equivariant (shift hS ω hω) (representative (classOf ω hω)) s
    have hω' : actLabels (shift hS ω hω) (representative (classOf ω hω)) = ω :=
      funext (shift_spec hS ω hω)
    rw [hω'] at he
    exact he.symm
  · rw [decodeRaw, dite_eq_right hω]
    obtain ⟨b, hb⟩ := pure_of_not_critical ω hω
    exact (p.2.pure ω b hb s).symm

/-- The exact pair-path factor of the concrete target has one independent
compact-open path coordinate per critical unordered pair. -/
def homeomorph {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Family S ≃ₜ (CriticalPairIndex S → PathSpace) where
  toFun := encode
  invFun := decode hS
  left_inv := decode_encode hS
  right_inv := encode_decode hS
  continuous_toFun := continuous_encode S
  continuous_invFun := continuous_decode hS

/-- Extracts the actual pair families, forgetting only the endpoint relations. -/
def pairPart {S : Finset (Fin 15)} (p : ConcreteComparisonTarget.Space S) : Family S :=
  ⟨p.1.2, ⟨p.2.equivariant, p.2.pure⟩⟩

theorem continuous_pairPart (S : Finset (Fin 15)) : Continuous (pairPart (S := S)) :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _


open AkopyanQuadratic PairRepresentation


/-- The image-based coordinate index contains every actual critical pair. -/
theorem exists_index_of_matchings {S : Finset (Fin 15)}
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n)
    (hcommon : (m ∩ n).card = 4) :
    ∃ i : CriticalPairIndex S, i.1 = {m, n} := by
  obtain ⟨ω, hmω, hnω⟩ := exists_pair_labels m n hm hn hcommon
  have hω : Critical ω := by
    unfold Critical
    rw [hmω, hnω]
    exact hcommon
  refine ⟨classOf ω hω, ?_⟩
  change pairWords ω = {m, n}
  unfold pairWords
  rw [hmω, hnω]

theorem index_spec {S : Finset (Fin 15)} (hS : S.Nonempty) (i : CriticalPairIndex S) :
    ∃ m n : Finset (S → Fin 6),
      SixMatching m ∧ SixMatching n ∧ (m ∩ n).card = 4 ∧ m ≠ n ∧ i.1 = {m, n} := by
  let ω := representative i
  let m := matchingWords (firstVertex ∘ ω)
  let n := matchingWords (secondVertex ∘ ω)
  have hm : SixMatching m := matchingWords_sixMatching hS _
  have hn : SixMatching n := matchingWords_sixMatching hS _
  have hmn : (m ∩ n).card = 4 := representative_critical i
  refine ⟨m, n, hm, hn, hmn, ?_, ?_⟩
  · intro he
    rw [he, Finset.inter_self, hn.1] at hmn
    omega
  · exact (representative_pairWords i).symm

end AkopyanResearch.PairPathCoordinates
