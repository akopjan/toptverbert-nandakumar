module

public import AkopyanResearch.Completion.SingleCoordinateModel
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# The actual collapse applied to arbitrary single-coordinate values

Every row-equivariant single family induces pair values with the precise
PairGroup covariance and pure-phase value infinity. These are properties of
the actual collapse, and do not require that the family comes from a quadratic
table or from the chosen join section.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.TargetCollapseModel

open scoped OnePoint Classical
open OriginalJoinBridge PairSourceProjections PairSphereAction PairOrbit
open ConcreteComparisonTarget SingleCoordinateModel

def collapseValues {S : Finset (Fin 15)} (f : Coordinates S) (ω : PairLabels S) :
    OnePoint PairTarget :=
  pairCollapseMap (spherePairEquiv (f.1 (firstVertex ∘ ω), f.1 (secondVertex ∘ ω)))

theorem first_evaluation_action {S : Finset (Fin 15)} (f : Coordinates S)
    (h : PairGroup) (ω : PairLabels S) :
    f.1 (firstVertex ∘ actLabels h ω) =
      if h.2.ex then permSphere (blockPerm h.1 h.2.sb) (f.1 (secondVertex ∘ ω))
      else permSphere (blockPerm h.1 h.2.sa) (f.1 (firstVertex ∘ ω)) := by
  cases he : h.2.ex
  · have hfirst : firstVertex ∘ actLabels h ω =
        (fun c => (firstVertex ∘ ω) c * (blockPerm h.1 h.2.sa)⁻¹) := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk, he,
        Bool.false_eq_true, ↓reduceIte] using firstVertex_action h (ω c)
    rw [hfirst, f.2, inv_inv]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · have hfirst : firstVertex ∘ actLabels h ω =
        (fun c => (secondVertex ∘ ω) c * (blockPerm h.1 h.2.sb)⁻¹) := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk, he, ↓reduceIte]
        using firstVertex_action h (ω c)
    rw [hfirst, f.2, inv_inv]
    simp only [↓reduceIte]

theorem second_evaluation_action {S : Finset (Fin 15)} (f : Coordinates S)
    (h : PairGroup) (ω : PairLabels S) :
    f.1 (secondVertex ∘ actLabels h ω) =
      if h.2.ex then permSphere (blockPerm h.1 h.2.sa) (f.1 (firstVertex ∘ ω))
      else permSphere (blockPerm h.1 h.2.sb) (f.1 (secondVertex ∘ ω)) := by
  cases he : h.2.ex
  · have hsecond : secondVertex ∘ actLabels h ω =
        (fun c => (secondVertex ∘ ω) c * (blockPerm h.1 h.2.sb)⁻¹) := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk, he,
        Bool.false_eq_true, ↓reduceIte] using secondVertex_action h (ω c)
    rw [hsecond, f.2, inv_inv]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · have hsecond : secondVertex ∘ actLabels h ω =
        (fun c => (firstVertex ∘ ω) c * (blockPerm h.1 h.2.sa)⁻¹) := by
      funext c
      simpa only [Function.comp_apply, actLabels, statePerm, Equiv.coe_fn_mk, he, ↓reduceIte]
        using secondVertex_action h (ω c)
    rw [hsecond, f.2, inv_inv]
    simp only [↓reduceIte]

theorem collapseValues_equivariant {S : Finset (Fin 15)} (f : Coordinates S)
    (h : PairGroup) (ω : PairLabels S) :
    collapseValues f (actLabels h ω) = actOnePoint h (collapseValues f ω) := by
  have he : (f.1 (firstVertex ∘ actLabels h ω), f.1 (secondVertex ∘ actLabels h ω)) =
      pairAction h (f.1 (firstVertex ∘ ω), f.1 (secondVertex ∘ ω)) := by
    rw [first_evaluation_action, second_evaluation_action]
    cases hb : h.2.ex <;> simp only [pairAction, hb, Bool.false_eq_true, ↓reduceIte]
  unfold collapseValues
  rw [he, spherePairEquiv_equivariant, pairCollapseMap_equivariant]

theorem collapseValues_pure {S : Finset (Fin 15)} (f : Coordinates S)
    (ω : PairLabels S) (b : Bool) (hb : ∀ c, (ω c).2 = b) :
    collapseValues f ω = ∞ := by
  have he : secondVertex ∘ ω = (fun c => (firstVertex ∘ ω) c * blockPerm 1 b) := by
    funext c
    simp only [Function.comp_apply, firstVertex, secondVertex, hb c]
  unfold collapseValues
  rw [he, f.2, blockPerm_inv, inv_one]
  cases b
  · simpa only [blockPerm, Bool.false_eq_true, ↓reduceIte, mul_one,
      liftPerm4_one, permSphere_one] using collapse_diagonal (f.1 (firstVertex ∘ ω))
  · simpa only [blockPerm, ↓reduceIte, liftPerm4_one, one_mul]
      using collapse_swap45 (f.1 (firstVertex ∘ ω))

theorem continuous_collapseValues (S : Finset (Fin 15)) :
    Continuous (collapseValues (S := S)) := by
  apply continuous_pi
  intro ω
  exact continuous_pairCollapseMap.comp (spherePairEquiv.continuous.comp
    (((continuous_apply (firstVertex ∘ ω)).comp continuous_subtype_val).prodMk
      ((continuous_apply (secondVertex ∘ ω)).comp continuous_subtype_val)))

/-- The actual compactified pair target is a thirteen-sphere. -/
def pairTargetSphereHomeomorph :
    OnePoint PairTarget ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 14)) 1 :=
  onePointEquivSphereOfFinrankEq (by rw [finrank_PairTarget]; simp)

end AkopyanResearch.TargetCollapseModel
