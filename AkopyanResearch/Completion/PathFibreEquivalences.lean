module

public import Submission.Homotopy.DiscTrivialisation

/-!
# Explicit homotopy equivalences between path fibres

Appending a fixed path changes the endpoint of a path fibre by a homotopy
equivalence. The cancellation homotopies are the actual continuous
families from `DiscTrivialisation`. Reversal then gives change of basepoint
for the usual compact-open loop spaces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PathFibreEquivalences

open ContinuousMap

universe w
variable {X : Type w} [TopologicalSpace X]

def pathFibreHomeomorph (a b : X) : Submission.PathFibre X a b ≃ₜ Path a b where
  toFun γ := { toContinuousMap := γ.val.val, source' := γ.val.property, target' := γ.property }
  invFun γ := ⟨⟨γ.toContinuousMap, γ.source⟩, γ.target⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_induced_rng.mpr (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := (continuous_induced_dom.subtype_mk _).subtype_mk _

def reverseHomeomorph (a b : X) : Path a b ≃ₜ Path b a where
  toFun := Path.symm
  invFun := Path.symm
  left_inv := Path.symm_symm
  right_inv := Path.symm_symm
  continuous_toFun := Path.continuous_symm
  continuous_invFun := Path.continuous_symm

def pathFamily {a b : X} (p : Path a b) :
    Submission.BasedPathFamily PUnit.{w + 1} X a where
  curve := ⟨fun z => p z.2, p.continuous.comp continuous_snd⟩
  curve_zero _ := p.source

def constantTotalHomeomorph (x : X) {a b : X} (p : Path a b) :
    Submission.BasedPathFamily.Total (pathFamily p) x ≃ₜ Submission.PathFibre X x b where
  toFun q := ⟨q.val.2, q.property.symm.trans p.target⟩
  invFun γ := ⟨(PUnit.unit, γ.val), p.target.trans γ.property.symm⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  continuous_toFun :=
    (Submission.Pullback.snd (pathFamily p).endpt (Submission.ev₁ X x)).continuous.subtype_mk _
  continuous_invFun :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _

def fibreEndpointEquiv (x : X) {a b : X} (p : Path a b) :
    Submission.PathFibre X x a ≃ₕ Submission.PathFibre X x b :=
  (Homeomorph.prodUnique (Submission.PathFibre X x a) PUnit.{w + 1}).symm.toHomotopyEquiv.trans
    ((Submission.BasedPathFamily.homotopyEquiv (pathFamily p) x).symm.trans
      (constantTotalHomeomorph x p).toHomotopyEquiv)

/-- Appending a fixed path is a homotopy equivalence of compact-open
path spaces with the same initial point. -/
def endpointEquiv (x : X) {a b : X} (p : Path a b) : Path x a ≃ₕ Path x b :=
  (pathFibreHomeomorph x a).symm.toHomotopyEquiv.trans
    ((fibreEndpointEquiv x p).trans (pathFibreHomeomorph x b).toHomotopyEquiv)

/-- A nonempty path fibre is equivalent to the based loop space at its
target; a specific joining path supplies the equivalence. -/
def endpointLoopEquiv {a b : X} (p : Path a b) : Path a b ≃ₕ Path b b :=
  (reverseHomeomorph a b).toHomotopyEquiv.trans (endpointEquiv b p)

def loopBasepointEquiv {a b : X} (p : Path a b) : Path a a ≃ₕ Path b b :=
  (endpointEquiv a p).trans (endpointLoopEquiv p)

end AkopyanResearch.PathFibreEquivalences
