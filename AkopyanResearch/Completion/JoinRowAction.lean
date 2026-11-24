module

public import AkopyanResearch.Completion.PhaseExtension
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Units.Equiv

@[expose] public section

/-!
# Converting the right row convention to a left equivariant source

The actual normalizer action on matching vertices has the form
`g ↦ g * a⁻¹`. Coordinatewise inversion converts it to left multiplication.
This module verifies the conversion on the coordinate colored join itself,
with its topology, and for maps into any space with a group action.
-/

set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.JoinRowAction

open PhaseExtension

universe u v w
variable {C : Type u} {G : Type v} [Fintype C] [Fintype G] [Group G]

abbrev Vertex (G : Type v) := G × Bool
abbrev Source (C : Type u) (G : Type v) [Fintype C] [Fintype G] :=
  Join C (Vertex G)

def inversionVertex : Equiv.Perm (Vertex G) :=
  Equiv.prodCongr (Equiv.inv G) (Equiv.refl Bool)

def leftVertex (a : G) : Equiv.Perm (Vertex G) :=
  Equiv.prodCongr (Equiv.mulLeft a) (Equiv.refl Bool)

def rightVertex (a : G) : Equiv.Perm (Vertex G) :=
  Equiv.prodCongr (Equiv.mulRight a⁻¹) (Equiv.refl Bool)

def inversion : Source C G → Source C G := relabel inversionVertex
def leftAction (a : G) : Source C G → Source C G := relabel (leftVertex a)
def rightAction (a : G) : Source C G → Source C G := relabel (rightVertex a)

theorem inversion_involutive : Function.Involutive (inversion (C := C) (G := G)) := by
  intro x
  apply Subtype.ext
  funext i
  rcases i with ⟨c, g, b⟩
  simp [inversion, inversionVertex, relabel]

theorem continuous_inversion : Continuous (inversion (C := C) (G := G)) :=
  continuous_relabel _

def inversionHomeomorph : Source C G ≃ₜ Source C G where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  continuous_toFun := continuous_inversion
  continuous_invFun := continuous_inversion

/-- This is the required inversion, not an identification of left and right
actions without a change of coordinates. -/
theorem inversion_rightAction (a : G) (x : Source C G) :
    inversion (rightAction a x) = leftAction a (inversion x) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨c, g, b⟩
  simp [inversion, rightAction, leftAction, inversionVertex, rightVertex,
    leftVertex, relabel, mul_inv_rev]

theorem inversion_preserves_phase (b : Bool) (x : Source C G) :
    mass Prod.snd b (inversion x) = mass Prod.snd b x := by
  exact mass_relabel Prod.snd inversionVertex (Equiv.refl Bool)
    (fun _ => rfl) b x

variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y]

omit [MulAction G Y] in
theorem continuous_converted_map (F : Source C G → Y) (hF : Continuous F) :
    Continuous (F ∘ inversion) := hF.comp continuous_inversion

omit [TopologicalSpace Y] in
/-- A left-equivariant map yields a map satisfying the actual right row
convention by precomposition with the explicit inversion homeomorphism. -/
theorem converted_map_equivariant (F : Source C G → Y)
    (hF : ∀ (a : G) (x : Source C G), F (leftAction a x) = a • F x)
    (a : G) (x : Source C G) :
    (F ∘ inversion) (rightAction a x) = a • (F ∘ inversion) x := by
  simp only [Function.comp_apply, inversion_rightAction, hF]

end AkopyanResearch.JoinRowAction

#print axioms AkopyanResearch.JoinRowAction.inversionHomeomorph
#print axioms AkopyanResearch.JoinRowAction.converted_map_equivariant

end
