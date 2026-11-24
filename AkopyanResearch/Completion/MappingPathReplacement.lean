module

public import AkopyanResearch.Completion.HomotopyFiberFibration
public import Submission.Homotopy.DiscTrivialisation

/-!
# The unrestricted mapping-path replacement

For `f : X → Y`, the replacement consists of a point `x` and a path
starting at `f x`, with unrestricted endpoint. Projection to `X` is an
explicit homotopy equivalence, and its endpoint fiber is the original
homotopy-fiber model.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingPathReplacement

open ContinuousMap

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y))

abbrev Time := unitInterval
abbrev Space := {q : X × C(Time, Y) // q.2 0 = f q.1}

def projection : C(Space f, X) := ⟨fun q => q.val.1, continuous_fst.comp continuous_subtype_val⟩

def endpoint : C(Space f, Y) :=
  ⟨fun q => q.val.2 1,
    (continuous_eval_const 1).comp (continuous_snd.comp continuous_subtype_val)⟩

def sectionMap : C(X, Space f) :=
  ⟨fun x => ⟨(x, ContinuousMap.const Time (f x)), rfl⟩,
    (continuous_id.prodMk (ContinuousMap.continuous_const'.comp f.continuous)).subtype_mk _⟩

theorem section_projection : (projection f).comp (sectionMap f) = ContinuousMap.id X := rfl
theorem section_endpoint : (endpoint f).comp (sectionMap f) = f := rfl

def contractionAux : C((Time × Space f) × Time, Y) :=
  ⟨fun z => z.1.2.val.2 (Submission.mulCM (unitInterval.symm z.1.1, z.2)),
    Continuous.eval
      ((continuous_snd.comp continuous_subtype_val).comp (continuous_snd.comp continuous_fst))
      (Submission.mulCM.continuous.comp
        ((unitInterval.continuous_symm.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd))⟩

theorem contractionAux_source (z : Time × Space f) :
    (contractionAux f).curry z 0 = f z.2.val.1 := by
  change z.2.val.2 (Submission.mulCM (unitInterval.symm z.1, 0)) = f z.2.val.1
  rw [Submission.mulCM_zero_right]
  exact z.2.property

def contractionMap : C(Time × Space f, Space f) where
  toFun z := ⟨(z.2.val.1, (contractionAux f).curry z), contractionAux_source f z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((projection f).continuous.comp continuous_snd).prodMk
      (contractionAux f).curry.continuous

def contraction : (ContinuousMap.id (Space f)).Homotopy ((sectionMap f).comp (projection f)) where
  toContinuousMap := contractionMap f
  map_zero_left q := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply ContinuousMap.ext
    intro t
    change q.val.2 (Submission.mulCM (unitInterval.symm 0, t)) = q.val.2 t
    rw [unitInterval.symm_zero, Submission.mulCM_one_left]
  map_one_left q := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply ContinuousMap.ext
    intro t
    change q.val.2 (Submission.mulCM (unitInterval.symm 1, t)) = f q.val.1
    rw [unitInterval.symm_one, Submission.mulCM_zero_left]
    exact q.property

def projectionEquiv : Space f ≃ₕ X where
  toFun := projection f
  invFun := sectionMap f
  left_inv := ⟨(contraction f).symm⟩
  right_inv := Homotopic.refl (ContinuousMap.id X)

def FibreSet (y₀ : Y) : Set (Space f) := {q | endpoint f q = y₀}

def fibreHomeomorph (y₀ : Y) : FibreSet f y₀ ≃ₜ HomotopyFiberFibration.Space f y₀ where
  toFun q := ⟨q.val.val, q.val.property, q.property⟩
  invFun q := ⟨⟨q.val, q.property.1⟩, q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def basedPathInclusion (x : X) : C(Submission.PathSpace Y (f x), Space f) :=
  ⟨fun γ => ⟨(x, γ.val), γ.property⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

theorem basedPathInclusion_endpoint (x : X) :
    (endpoint f).comp (basedPathInclusion f x) = Submission.ev₁ Y (f x) := rfl

end AkopyanResearch.MappingPathReplacement
