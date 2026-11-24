module

public import AkopyanResearch.Completion.PairCofibration
public import AkopyanResearch.Completion.PairCofiberSection
public import Hatcher.Singular.GoodPairPointQuotientHomology

/-!
# Relative homology and the actual pair cofiber

The explicit neighborhood deformation makes the original closed chart
complement a good pair. The proved good-pair quotient theorem therefore
applies to this very inclusion. The categorical point quotient is identified
with the concrete quotient, preserving the quotient projection exactly.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairGoodPair

open CategoryTheory CategoryTheory.Limits Set
open PairCofiberModel PairCofibration Hatcher.Relative
open scoped OnePoint

abbrev pair : TopPair := TopPair.ofSubset (X := TopCat.of PairSpace) ClosedLocus

def goodPairData : GoodPairData pair where
  nonempty := closedLocus_nonempty.to_subtype
  isClosed_range := by
    change IsClosed (Set.range (Subtype.val : ClosedLocus → PairSpace))
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using isClosed_closedLocus
  V := NeighborhoodSet
  range_subset_interior := by
    change Set.range (Subtype.val : ClosedLocus → PairSpace) ⊆ interior NeighborhoodSet
    rw [isOpen_neighborhood.interior_eq]
    rintro x ⟨a, rfl⟩
    exact closedLocus_subset_neighborhood a.property
  strongDeformationRetract :=
    { retract := ⟨PairNeighborhoodDeformation.retraction,
        PairNeighborhoodDeformation.continuous_retraction⟩
      retract_inclusion := by
        ext a
        exact PairNeighborhoodDeformation.retraction_inclusion a
      deformation :=
        { toFun := PairNeighborhoodDeformation.deformation
          continuous_toFun := PairNeighborhoodDeformation.continuous_deformation
          map_zero_left := PairNeighborhoodDeformation.deformation_start
          map_one_left := PairNeighborhoodDeformation.deformation_end
          prop' := by
            rintro t _ ⟨a, rfl⟩
            exact PairNeighborhoodDeformation.deformation_fixes t a } }

theorem isGoodPair : IsGoodPair pair := ⟨goodPairData⟩

def quotientHomeomorph : pointQuotient pair ≃ₜ Cofiber :=
  (compactComplementQuotientOnePointHomeomorph (TopCat.of PairSpace)
    Domain PairCollapse.isOpen_chartDomain closedLocus_nonempty).trans
    (OpenComplementQuotient.homeomorph
      PairCollapse.isOpen_chartDomain closedLocus_nonempty).symm

theorem quotientHomeomorph_projection (x : PairSpace) :
    quotientHomeomorph (pointQuotientProjection pair x) = quotientMap x := by
  apply (OpenComplementQuotient.homeomorph
    PairCollapse.isOpen_chartDomain closedLocus_nonempty).injective
  dsimp only [quotientHomeomorph, Homeomorph.trans_apply]
  rw [Homeomorph.apply_symm_apply]
  change compactComplementQuotientOnePointHomeomorph (TopCat.of PairSpace)
      Domain PairCollapse.isOpen_chartDomain closedLocus_nonempty
      (pointQuotientProjection pair x) = OpenComplementQuotient.collapse Domain x
  by_cases hx : x ∈ Domain
  · rw [OpenComplementQuotient.collapse_of_mem hx]
    exact compactComplementQuotientOnePointHomeomorph_apply_projection
      (TopCat.of PairSpace) Domain PairCollapse.isOpen_chartDomain closedLocus_nonempty ⟨x, hx⟩
  · rw [OpenComplementQuotient.collapse_of_not_mem hx]
    have hq : pointQuotientProjection pair x = pointQuotientPoint pair := by
      change x ∈ pointQuotientProjection pair ⁻¹' {pointQuotientPoint pair}
      rw [pointQuotientProjection_preimage_point]
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [hq]
    exact compactComplementQuotientOnePointHomeomorph_apply_point
      (TopCat.of PairSpace) Domain PairCollapse.isOpen_chartDomain closedLocus_nonempty

universe u v
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

/-- The canonical quotient map induces the relative homology isomorphism
for the original closed pair locus, in every degree. -/
theorem quotientComparison_isIso (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map (pointQuotientComparison.app pair)) :=
  goodPairData.pointQuotientComparison_homologyMap_isIso R n

/-- Relative homology of the actual pair is reduced homology of its actual
concrete cofiber. No cofibration or good-pair hypothesis remains. -/
def relativeHomologyIso (R : C) (n : ℕ) :
    (homologyFunctor R n).obj pair ≅
      (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of Cofiber) :=
  goodPairRelativeHomologyIsoReducedPointQuotient pair isGoodPair R n ≪≫
    (Hatcher.Reduced.homologyFunctor R n).mapIso (TopCat.isoOfHomeo quotientHomeomorph)

end AkopyanResearch.PairGoodPair
