module

public import AkopyanResearch.Completion.SingleCoordinateModel
public import AkopyanResearch.Completion.PairPathCoordinates
public import AkopyanResearch.Completion.TargetCollapseModel
public import AkopyanResearch.Completion.ConcreteComparison

/-!
# The concrete target as an actual homotopy-fiber coordinate space

Single values are indexed by actual matchings. Compact-open paths are
indexed by actual critical unordered pairs and start at the corresponding
actual pair collapse. Both directions preserve these endpoint conditions;
the inverse reconstructs all row and pair symmetries, including pure labels.
No connectivity or relative lifting hypothesis is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.TargetFiberModel

open scoped Classical OnePoint
open EquivariantJoinStep OriginalJoinBridge PairOrbit PairPathCoordinates
open TargetCollapseModel

abbrev SingleProduct (S : Finset (Fin 15)) := MatchingIndex S → Target
abbrev PairProduct (S : Finset (Fin 15)) := CriticalPairIndex S → OnePoint PairTarget
abbrev PairPaths (S : Finset (Fin 15)) := CriticalPairIndex S → PathSpace

def collapseCoordinates {S : Finset (Fin 15)} (hS : S.Nonempty)
    (f : SingleProduct S) : PairProduct S :=
  fun i => collapseValues (SingleCoordinateModel.decode hS f) (representative i)

theorem continuous_collapseCoordinates {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Continuous (collapseCoordinates hS) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (representative i)).comp
    ((continuous_collapseValues S).comp (SingleCoordinateModel.continuous_decode hS))

abbrev FiberModel {S : Finset (Fin 15)} (hS : S.Nonempty) :=
  {p : SingleProduct S × PairPaths S //
    (∀ i, p.2 i timeZero = collapseCoordinates hS p.1 i) ∧
    (∀ i, p.2 i timeOne = ∞)}

def encode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : ConcreteComparisonTarget.Space S) : FiberModel hS := by
  refine ⟨(SingleCoordinateModel.encode (SingleCoordinateModel.singlePart p),
    PairPathCoordinates.encode (pairPart p)), ?_, ?_⟩
  · intro i
    change p.1.2 (representative i) timeZero =
      collapseValues (SingleCoordinateModel.decode hS
        (SingleCoordinateModel.encode (SingleCoordinateModel.singlePart p))) (representative i)
    rw [SingleCoordinateModel.decode_encode]
    exact p.2.start (representative i)
  · intro i
    exact p.2.finish (representative i)

def decode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : FiberModel hS) : ConcreteComparisonTarget.Space S := by
  let f := SingleCoordinateModel.decode hS p.1.1
  let q := PairPathCoordinates.decode hS p.1.2
  refine ⟨(f.1, q.1), {
    row := f.2
    start := ?_
    finish := ?_
    equivariant := q.2.equivariant
    pure := q.2.pure }⟩
  · intro ω
    change decodeRaw hS p.1.2 ω timeZero = collapseValues f ω
    by_cases hω : Critical ω
    · rw [decodeRaw, dite_eq_left hω]
      change actOnePoint (shift hS ω hω) (p.1.2 (classOf ω hω) timeZero) =
        collapseValues f ω
      rw [p.2.1 (classOf ω hω)]
      change actOnePoint (shift hS ω hω)
        (collapseValues f (representative (classOf ω hω))) = collapseValues f ω
      have he := collapseValues_equivariant f (shift hS ω hω)
        (representative (classOf ω hω))
      have hlabel : actLabels (shift hS ω hω) (representative (classOf ω hω)) = ω :=
        funext (shift_spec hS ω hω)
      rw [hlabel] at he
      exact he.symm
    · rw [decodeRaw, dite_eq_right hω]
      obtain ⟨b, hb⟩ := pure_of_not_critical ω hω
      exact (collapseValues_pure f ω b hb).symm
  · intro ω
    change decodeRaw hS p.1.2 ω timeOne = ∞
    by_cases hω : Critical ω
    · rw [decodeRaw, dite_eq_left hω]
      change actOnePoint (shift hS ω hω) (p.1.2 (classOf ω hω) timeOne) = ∞
      rw [p.2.2 (classOf ω hω)]
      rfl
    · rw [decodeRaw, dite_eq_right hω]
      rfl

theorem decode_encode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : ConcreteComparisonTarget.Space S) : decode hS (encode hS p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val
      (SingleCoordinateModel.decode_encode hS (SingleCoordinateModel.singlePart p))
  · exact congrArg Subtype.val (PairPathCoordinates.decode_encode hS (pairPart p))

theorem encode_decode {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : FiberModel hS) : encode hS (decode hS p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact SingleCoordinateModel.encode_decode hS p.1.1
  · exact PairPathCoordinates.encode_decode hS p.1.2

theorem continuous_encode {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Continuous (encode hS) := by
  apply Continuous.subtype_mk
  exact ((SingleCoordinateModel.continuous_encode S).comp
      (SingleCoordinateModel.continuous_singlePart S)).prodMk
    ((PairPathCoordinates.continuous_encode S).comp (continuous_pairPart S))

theorem continuous_decode {S : Finset (Fin 15)} (hS : S.Nonempty) :
    Continuous (decode hS) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp
      ((SingleCoordinateModel.continuous_decode hS).comp
        (continuous_fst.comp continuous_subtype_val))).prodMk
    (continuous_subtype_val.comp ((PairPathCoordinates.continuous_decode hS).comp
      (continuous_snd.comp continuous_subtype_val)))

/-- A homeomorphism for the full concrete target, with the original collapse
map and both path endpoints retained. It is not a connectivity theorem. -/
def homeomorph {S : Finset (Fin 15)} (hS : S.Nonempty) :
    ConcreteComparisonTarget.Space S ≃ₜ FiberModel hS where
  toFun := encode hS
  invFun := decode hS
  left_inv := decode_encode hS
  right_inv := encode_decode hS
  continuous_toFun := continuous_encode hS
  continuous_invFun := continuous_decode hS

@[simp] theorem homeomorph_single_apply {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : ConcreteComparisonTarget.Space S) (m : MatchingIndex S) :
    (homeomorph hS p).1.1 m = p.1.1 (SingleCoordinateModel.enumeration m) := rfl

@[simp] theorem homeomorph_pair_apply {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : ConcreteComparisonTarget.Space S) (i : CriticalPairIndex S) (s : Time) :
    (homeomorph hS p).1.2 i s = p.1.2 (representative i) s := rfl

def assemblePaths {S : Finset (Fin 15)} (q : PairPaths S) : C(Time, PairProduct S) :=
  ⟨fun t i => q i t, continuous_pi fun i => (q i).continuous⟩

def splitPaths {S : Finset (Fin 15)} (q : C(Time, PairProduct S)) : PairPaths S :=
  fun i => ⟨fun t => q t i, (continuous_apply i).comp q.continuous⟩

theorem continuous_assemblePaths (S : Finset (Fin 15)) :
    Continuous (assemblePaths (S := S)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : PairPaths S × Time => fun i : CriticalPairIndex S => p.1 i p.2)
  apply continuous_pi
  intro i
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun q : PairPaths S => q i, continuous_apply i⟩ :
      C(PairPaths S, C(Time, OnePoint PairTarget)))

theorem continuous_splitPaths (S : Finset (Fin 15)) :
    Continuous (splitPaths (S := S)) := by
  apply continuous_pi
  intro i
  exact ContinuousMap.continuous_postcomp
    (⟨fun x : PairProduct S => x i, continuous_apply i⟩ :
      C(PairProduct S, OnePoint PairTarget))

def pathsHomeomorph (S : Finset (Fin 15)) : PairPaths S ≃ₜ C(Time, PairProduct S) where
  toFun := assemblePaths
  invFun := splitPaths
  left_inv q := by
    funext i
    apply ContinuousMap.ext
    intro t
    rfl
  right_inv q := by
    apply ContinuousMap.ext
    intro t
    funext i
    rfl
  continuous_toFun := continuous_assemblePaths S
  continuous_invFun := continuous_splitPaths S

/-- The ordinary path-space model of the homotopy fiber over the all-infinity
point of the actual product collapse map. -/
abbrev HomotopyFiber {S : Finset (Fin 15)} (hS : S.Nonempty) :=
  {p : SingleProduct S × C(Time, PairProduct S) //
    p.2 timeZero = collapseCoordinates hS p.1 ∧ p.2 timeOne = fun _ => ∞}

def assembleFiber {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : FiberModel hS) : HomotopyFiber hS :=
  ⟨(p.1.1, assemblePaths p.1.2), funext p.2.1, funext p.2.2⟩

def splitFiber {S : Finset (Fin 15)} (hS : S.Nonempty)
    (p : HomotopyFiber hS) : FiberModel hS :=
  ⟨(p.1.1, splitPaths p.1.2), congrFun p.2.1, congrFun p.2.2⟩

def standardFiberHomeomorph {S : Finset (Fin 15)} (hS : S.Nonempty) :
    FiberModel hS ≃ₜ HomotopyFiber hS where
  toFun := assembleFiber hS
  invFun := splitFiber hS
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (pathsHomeomorph S).left_inv p.1.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (pathsHomeomorph S).right_inv p.1.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_assemblePaths S).comp (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_splitPaths S).comp (continuous_snd.comp continuous_subtype_val))

/-- The full target is homeomorphic to the genuine path-space homotopy
fiber of the actual product collapse map. This does not assert connectivity. -/
def homotopyFiberHomeomorph {S : Finset (Fin 15)} (hS : S.Nonempty) :
    ConcreteComparisonTarget.Space S ≃ₜ HomotopyFiber hS :=
  (homeomorph hS).trans (standardFiberHomeomorph hS)

@[simp] theorem comparison_single {S : Finset (Fin 15)} (hS : S.Nonempty)
    (H : QuadComplement S) (m : MatchingIndex S) :
    (homotopyFiberHomeomorph hS (ConcreteComparison.comparisonMap S hS H)).1.1 m =
      MatchingSphereMap.matchingSphere hS H (SingleCoordinateModel.enumeration m) := rfl

@[simp] theorem comparison_path {S : Finset (Fin 15)} (hS : S.Nonempty)
    (H : QuadComplement S) (s : Time) (i : CriticalPairIndex S) :
    (homotopyFiberHomeomorph hS (ConcreteComparison.comparisonMap S hS H)).1.2 s i = ∞ := rfl


end AkopyanResearch.TargetFiberModel
