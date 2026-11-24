module

public import AkopyanResearch.Completion.ChosenTargetSections
public import AkopyanResearch.Completion.RelativeFaceDiagram
public import Mathlib.Topology.CompactOpen

/-!
# A concrete natural target with single values and pair paths

The single coordinates are indexed by enumerated matchings, with the exact
row-enumeration relations imposed. The pair coordinates are paths for the
original collapse, with its exact symmetry and constant pure-phase relations.
Thus redundant enumerations do not introduce independent sphere factors.

Color restriction defines the face lifts. The chosen fifteen-color join maps
give a continuous section compatible with every face. No comparison
connectivity or relative lifting theorem is assumed in this construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ConcreteComparisonTarget

open scoped OnePoint
open EquivariantJoinStep OriginalJoinBridge PairSourceProjections
  ChosenTargetSections RelativeFaceDiagram

abbrev SingleLabels (S : Finset (Fin 15)) := S → RowGroup
abbrev PairLabels (S : Finset (Fin 15)) := S → PairState
abbrev Raw (S : Finset (Fin 15)) :=
  (SingleLabels S → Target) × (PairLabels S → C(Time, OnePoint PairTarget))

/-- All relations are pointwise equalities in the original sphere and collapse.
The topology is inherited from the finite products and compact-open path spaces. -/
structure Relations (S : Finset (Fin 15)) (p : Raw S) : Prop where
  row : ∀ (σ : SingleLabels S) (τ : RowGroup),
    p.1 (fun c => σ c * τ) = permSphere τ⁻¹ (p.1 σ)
  start : ∀ ω : PairLabels S,
    p.2 ω timeZero = pairCollapseMap (spherePairEquiv
      (p.1 (firstVertex ∘ ω), p.1 (secondVertex ∘ ω)))
  finish : ∀ ω : PairLabels S, p.2 ω timeOne = ∞
  equivariant : ∀ (h : PairGroup) (ω : PairLabels S) (s : Time),
    p.2 (fun c => h • ω c) s = actOnePoint h (p.2 ω s)
  pure : ∀ (ω : PairLabels S) (b : Bool), (∀ c, (ω c).2 = b) →
    ∀ s : Time, p.2 ω s = ∞

abbrev Space (S : Finset (Fin 15)) := {p : Raw S // Relations S p}

def restrict {V : Type*} {T S : Finset (Fin 15)} (hTS : T ⊆ S)
    (σ : S → V) : T → V := fun c => σ ⟨c.1, hTS c.2⟩

def lift {T S : Finset (Fin 15)} (hTS : T ⊆ S) (p : Space T) : Space S :=
  ⟨(fun σ => p.1.1 (restrict hTS σ), fun ω => p.1.2 (restrict hTS ω)), by
    constructor
    · intro σ τ
      exact p.2.row (restrict hTS σ) τ
    · intro ω
      exact p.2.start (restrict hTS ω)
    · intro ω
      exact p.2.finish (restrict hTS ω)
    · intro h ω s
      exact p.2.equivariant h (restrict hTS ω) s
    · intro ω b hω s
      exact p.2.pure (restrict hTS ω) b (fun c => hω _) s⟩

theorem continuous_lift {T S : Finset (Fin 15)} (hTS : T ⊆ S) :
    Continuous (lift hTS) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro σ
    exact (continuous_apply (restrict hTS σ)).comp
      (continuous_fst.comp continuous_subtype_val)
  · apply continuous_pi
    intro ω
    exact (continuous_apply (restrict hTS ω)).comp
      (continuous_snd.comp continuous_subtype_val)

theorem lift_refl (S : Finset (Fin 15)) (p : Space S) :
    lift (Finset.Subset.refl S) p = p := rfl

theorem lift_comp {R T S : Finset (Fin 15)} (hRT : R ⊆ T) (hTS : T ⊆ S)
    (p : Space R) : lift hTS (lift hRT p) = lift (hRT.trans hTS) p := rfl

/-- This diagram has no universal extension field. -/
def diagram : Diagram where
  Space := Space
  topSpace _ := inferInstance
  lift _ hTS := lift hTS
  continuous_lift _ hTS := continuous_lift hTS
  lift_refl S _ p := lift_refl S p
  lift_comp _ _ hRT hTS p := lift_comp hRT hTS p

def extendLabels {V : Type*} (S : Finset (Fin 15)) (v₀ : V) (σ : S → V) : Fin 15 → V :=
  fun i => if hi : i ∈ S then σ ⟨i, hi⟩ else v₀

@[simp] theorem extendLabels_mem {V : Type*} (S : Finset (Fin 15)) (v₀ : V)
    (σ : S → V) (i : Fin 15) (hi : i ∈ S) :
    extendLabels S v₀ σ i = σ ⟨i, hi⟩ := by
  simp [extendLabels, hi]

theorem mem_of_nonzero {S : Finset (Fin 15)} (z : FaceSimplex S)
    {i : Fin 15} (hi : z.1.1 i ≠ 0) : i ∈ S := by
  by_contra hn
  exact hi (z.2 i hn)

def singleValue (S : Finset (Fin 15)) (σ : SingleLabels S) (z : FaceSimplex S) : Target :=
  singleSection (extendLabels S 1 σ) z.1

def pairValue (S : Finset (Fin 15)) (ω : PairLabels S) (z : FaceSimplex S) :
    C(Time, OnePoint PairTarget) where
  toFun s := pairSection (extendLabels S (1, false) ω) (z.1, s)
  continuous_toFun := (continuous_pairSection _).comp (continuous_const.prodMk continuous_id)

theorem continuous_singleValue (S : Finset (Fin 15)) (σ : SingleLabels S) :
    Continuous (singleValue S σ) :=
  (continuous_singleSection _).comp continuous_subtype_val

theorem continuous_pairValue (S : Finset (Fin 15)) (ω : PairLabels S) :
    Continuous (pairValue S ω) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_pairSection _).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem singleValue_eq_of_extension (S : Finset (Fin 15)) (σ : SingleLabels S)
    (τ : Columns) (hτ : ∀ i (hi : i ∈ S), τ i = σ ⟨i, hi⟩) (z : FaceSimplex S) :
    singleValue S σ z = singleSection τ z.1 := by
  apply singleSection_congr_of_support
  intro i hi
  have hm := mem_of_nonzero z hi
  rw [extendLabels_mem S 1 σ i hm, hτ i hm]

theorem pairValue_eq_of_extension (S : Finset (Fin 15)) (ω : PairLabels S)
    (η : PairColumns) (hη : ∀ i (hi : i ∈ S), η i = ω ⟨i, hi⟩)
    (z : FaceSimplex S) (s : Time) :
    pairValue S ω z s = pairSection η (z.1, s) := by
  apply pairSection_congr_of_support
  intro i hi
  have hm := mem_of_nonzero z hi
  rw [extendLabels_mem S (1, false) ω i hm, hη i hm]

theorem chosen_relations (S : Finset (Fin 15)) (z : FaceSimplex S) :
    Relations S (fun σ => singleValue S σ z, fun ω => pairValue S ω z) := by
  constructor
  · intro σ τ
    change singleValue S (fun c => σ c * τ) z =
      permSphere τ⁻¹ (singleValue S σ z)
    exact (singleValue_eq_of_extension S (fun c => σ c * τ)
      (fun i => extendLabels S 1 σ i * τ)
      (fun i hi => by rw [extendLabels_mem S 1 σ i hi]) z).trans
      (singleSection_enumeration_change _ τ _)
  · intro ω
    change pairSection (extendLabels S (1, false) ω) ((z.1 : Masses), timeZero) =
      pairCollapseMap (spherePairEquiv
        (singleValue S (firstVertex ∘ ω) z, singleValue S (secondVertex ∘ ω) z))
    apply Eq.trans (pairSection_start _ (z.1 : Masses))
    apply congrArg pairCollapseMap
    apply congrArg spherePairEquiv
    apply Prod.ext
    · exact (singleValue_eq_of_extension S (firstVertex ∘ ω)
        (firstVertex ∘ extendLabels S (1, false) ω)
        (fun i hi => by simp only [Function.comp_apply, extendLabels_mem S _ ω i hi]) z).symm
    · exact (singleValue_eq_of_extension S (secondVertex ∘ ω)
        (secondVertex ∘ extendLabels S (1, false) ω)
        (fun i hi => by simp only [Function.comp_apply, extendLabels_mem S _ ω i hi]) z).symm
  · intro ω
    exact pairSection_finish _ _
  · intro h ω s
    rw [pairValue_eq_of_extension S (fun c => h • ω c)
      (fun i => h • extendLabels S (1, false) ω i)
      (fun i hi => by rw [extendLabels_mem S _ ω i hi]) z s]
    exact pairSection_equivariant h _ _ s
  · intro ω b hω s
    apply pairSection_pure _ b _ _ s
    intro i hi
    rw [extendLabels_mem S _ ω i (mem_of_nonzero z hi)]
    exact hω _

/-- An actual chosen point in every nonempty simplex face target. -/
def sectionMap (S : Finset (Fin 15)) (z : FaceSimplex S) : Space S :=
  ⟨(fun σ => singleValue S σ z, fun ω => pairValue S ω z), chosen_relations S z⟩

theorem continuous_sectionMap (S : Finset (Fin 15)) : Continuous (sectionMap S) := by
  apply Continuous.subtype_mk
  exact (continuous_pi (continuous_singleValue S)).prodMk
    (continuous_pi (continuous_pairValue S))

theorem sectionMap_natural {T S : Finset (Fin 15)} (hTS : T ⊆ S) (z : FaceSimplex T) :
    sectionMap S (faceIncl hTS z) = lift hTS (sectionMap T z) := by
  apply Subtype.ext
  apply Prod.ext
  · funext σ
    apply singleSection_congr_of_support
    intro i hi
    have hiT := mem_of_nonzero z hi
    simp only [extendLabels_mem S _ σ i (hTS hiT),
      extendLabels_mem T _ (restrict hTS σ) i hiT, restrict]
  · funext ω
    apply ContinuousMap.ext
    intro s
    apply pairSection_congr_of_support
    intro i hi
    have hiT := mem_of_nonzero z hi
    simp only [extendLabels_mem S _ ω i (hTS hiT),
      extendLabels_mem T _ (restrict hTS ω) i hiT, restrict]

end AkopyanResearch.ConcreteComparisonTarget
