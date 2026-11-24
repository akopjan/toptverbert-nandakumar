module

public import AkopyanResearch.Completion.PairCofiberModel

/-!
# A section of the actual pair-cofiber collapse

Fixing a common unit direction gives a proper inclusion of the actual normal
fiber. Its one-point compactification is a section of the original quotient
collapse. Thus every functor, in particular singular homology, sends this
collapse to a split epimorphism. No connectivity theorem is used.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairCofiberSection

open PairCofiberModel ContinuousMap
open scoped OnePoint

def direction : UnitDirections := by
  let : Nontrivial Comm6 :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_Comm6]; decide)
  let h := exists_norm_eq Comm6 (by norm_num : (0 : ℝ) ≤ 1)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

theorem proper_fixedDirection (w : UnitDirections) :
    IsProperMap (fun y : PairTarget => (w, y)) :=
  ((isProperMap_const (X := PUnit.{1}) w).prodMap isProperMap_id).comp
    (Homeomorph.punitProd PairTarget).symm.isProperMap

def fiberSection (w : UnitDirections) :
    C(OnePoint PairTarget, OnePoint (UnitDirections × PairTarget)) :=
  ⟨OnePoint.map (fun y => (w, y)),
    OpenComplementQuotient.continuous_onePointMap (proper_fixedDirection w)⟩

theorem projection_fiberSection (w : UnitDirections) :
    ∀ x, projection (fiberSection w x) = x :=
  OnePoint.forall.mpr ⟨rfl, fun _ => rfl⟩

def quotientCollapse : C(Cofiber, OnePoint PairTarget) :=
  projection.comp ⟨cofiberHomeomorph, cofiberHomeomorph.continuous⟩

def cofiberSection : C(OnePoint PairTarget, Cofiber) :=
  ContinuousMap.comp ⟨cofiberHomeomorph.symm, cofiberHomeomorph.symm.continuous⟩
    (fiberSection direction)

theorem quotientCollapse_quotientMap (x : PairSpace) :
    quotientCollapse (quotientMap x) = pairCollapseMap x :=
  (original_collapse_factor x).symm

theorem quotientCollapse_section (x : OnePoint PairTarget) :
    quotientCollapse (cofiberSection x) = x := by
  change projection (cofiberHomeomorph
    (cofiberHomeomorph.symm (fiberSection direction x))) = x
  rw [cofiberHomeomorph.apply_symm_apply]
  exact projection_fiberSection direction x

theorem rightInverse_section : Function.RightInverse cofiberSection quotientCollapse :=
  quotientCollapse_section

theorem surjective_quotientCollapse : Function.Surjective quotientCollapse :=
  rightInverse_section.surjective

theorem injective_cofiberSection : Function.Injective cofiberSection :=
  rightInverse_section.injective

theorem section_infty : cofiberSection ∞ = quotientMap (baseUnit, baseUnit) := by
  apply cofiberHomeomorph.injective
  change cofiberHomeomorph (cofiberHomeomorph.symm (fiberSection direction ∞)) = _
  rw [cofiberHomeomorph.apply_symm_apply, cofiberHomeomorph_quotientMap]
  change (∞ : OnePoint (UnitDirections × PairTarget)) =
    properCollapse Domain chart (baseUnit, baseUnit)
  apply (properCollapse_of_notMem _ _).symm
  change ¬ (‖(0 : Comm6)‖ • (0 : Comm6) ≠ ‖(0 : Comm6)‖ • (0 : Comm6))
  simp

end AkopyanResearch.PairCofiberSection
