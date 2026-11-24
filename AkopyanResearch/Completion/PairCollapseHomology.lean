module

public import AkopyanResearch.Completion.PairRelativeHomology
public import AkopyanResearch.Completion.RankOneSplit

/-!
# Primitive degree of the original pair collapse

The canonical map of the actual pair to its pointed quotient is a homology
isomorphism. The collapse of that quotient has an explicit pointed section.
Both degree-thirteen integral groups are infinite cyclic. Consequently the
actual relative collapse is an isomorphism, with coefficient `1` or `-1`
in the generators chosen by the preceding geometric calculations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairCollapseHomology

open CategoryTheory CategoryTheory.Limits
open PairCofiberModel PairCofiberSection Hatcher.Relative
open scoped OnePoint

def cofiberPoint : Cofiber := quotientMap (baseUnit, baseUnit)

abbrev cofiberPair : TopPair := pointedPair (TopCat.of Cofiber) cofiberPoint
abbrev targetPair : TopPair := pointedPair (TopCat.of (OnePoint PairTarget)) ∞

theorem base_mem_closed : (baseUnit, baseUnit) ∈ ClosedLocus := by
  change ¬ (‖(0 : Comm6)‖ • (0 : Comm6) ≠ ‖(0 : Comm6)‖ • (0 : Comm6))
  simp

theorem quotientMap_closed (x : ClosedLocus) : quotientMap x = cofiberPoint :=
  (quotientMap_eq_iff _ _).mpr (Or.inr ⟨x.property, base_mem_closed⟩)

theorem quotientHomeomorph_point :
    PairGoodPair.quotientHomeomorph (pointQuotientPoint PairGoodPair.pair) = cofiberPoint := by
  have h : pointQuotientProjection PairGoodPair.pair (baseUnit, baseUnit) =
      pointQuotientPoint PairGoodPair.pair := by
    change (baseUnit, baseUnit) ∈
      pointQuotientProjection PairGoodPair.pair ⁻¹' {pointQuotientPoint PairGoodPair.pair}
    rw [pointQuotientProjection_preimage_point]
    exact ⟨⟨(baseUnit, baseUnit), base_mem_closed⟩, rfl⟩
  rw [← h]
  exact PairGoodPair.quotientHomeomorph_projection _

def quotientPairIso : pointQuotientPair PairGoodPair.pair ≅ cofiberPair :=
  MorphismProperty.Arrow.isoMk (Iso.refl _) (TopCat.isoOfHomeo PairGoodPair.quotientHomeomorph)
    (by ext x; exact quotientHomeomorph_point.symm)

def quotientPairMap : PairGoodPair.pair ⟶ cofiberPair :=
  TopPair.ofHom (TopCat.ofHom ⟨quotientMap, continuous_quotientMap⟩)
    (TopCat.isTerminalPUnit.from _) (by
      ext x
      exact (quotientMap_closed x).symm)

theorem quotientPairMap_factor :
    pointQuotientComparison.app PairGoodPair.pair ≫ quotientPairIso.hom = quotientPairMap := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · ext x
    exact PairGoodPair.quotientHomeomorph_projection x

theorem quotientCollapse_point : quotientCollapse cofiberPoint = ∞ := by
  dsimp only [cofiberPoint]
  rw [← section_infty]
  exact quotientCollapse_section ∞

def collapsePairMap : cofiberPair ⟶ targetPair :=
  TopPair.ofHom (TopCat.ofHom quotientCollapse) (𝟙 _) (by
    ext x
    exact quotientCollapse_point.symm)

def sectionPairMap : targetPair ⟶ cofiberPair :=
  TopPair.ofHom (TopCat.ofHom cofiberSection) (𝟙 _) (by
    ext x
    exact section_infty.symm)

theorem sectionPairMap_collapsePairMap : sectionPairMap ≫ collapsePairMap = 𝟙 targetPair := by
  apply MorphismProperty.Arrow.Hom.ext
  · simp [sectionPairMap, collapsePairMap]
  · ext x
    exact quotientCollapse_section x

instance : IsSplitEpi collapsePairMap :=
  IsSplitEpi.mk' ⟨sectionPairMap, sectionPairMap_collapsePairMap⟩

/-- The actual map of pairs, with ambient map the original collapse. -/
def originalPairMap : PairGoodPair.pair ⟶ targetPair := quotientPairMap ≫ collapsePairMap

theorem originalPairMap_apply (x : PairSpace) :
    TopPair.Hom.fst originalPairMap x = pairCollapseMap x :=
  quotientCollapse_quotientMap x

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

theorem quotientPairMap_homology_isIso (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map quotientPairMap) := by
  rw [← quotientPairMap_factor, Functor.map_comp]
  have := PairGoodPair.quotientComparison_isIso R n
  infer_instance

theorem originalPairMap_homology_splitEpi (R : C) (n : ℕ) :
    IsSplitEpi ((homologyFunctor R n).map originalPairMap) := by
  dsimp only [originalPairMap]
  rw [Functor.map_comp]
  have := quotientPairMap_homology_isIso R n
  infer_instance

def targetHomologyIso (R : C) : (homologyFunctor R 13).obj targetPair ≅ R :=
  pointedPairHomologyIso (TopCat.of (OnePoint PairTarget)) ∞ R 13 ≪≫
    RepresentationSphereInvariants.pairReducedHomologyIso R

/-- The integral relative collapse is an isomorphism, with no degree or
primitivity hypothesis. -/
theorem originalPairMap_homology_isIso :
    IsIso ((homologyFunctor RankOneSplit.IntegerGroup 13).map originalPairMap) := by
  have := originalPairMap_homology_splitEpi RankOneSplit.IntegerGroup 13
  exact RankOneSplit.isIso_of_splitEpi
    (PairRelativeHomology.relativeHomologyIso RankOneSplit.IntegerGroup)
    (targetHomologyIso RankOneSplit.IntegerGroup) _

def integralDegreeEnd : RankOneSplit.IntegerGroup ⟶ RankOneSplit.IntegerGroup :=
  (PairRelativeHomology.relativeHomologyIso RankOneSplit.IntegerGroup).inv ≫
    (homologyFunctor RankOneSplit.IntegerGroup 13).map originalPairMap ≫
      (targetHomologyIso RankOneSplit.IntegerGroup).hom

theorem integralDegree_eq_one_or_neg_one : integralDegreeEnd 1 = 1 ∨ integralDegreeEnd 1 = -1 := by
  have := originalPairMap_homology_isIso
  have : IsIso integralDegreeEnd := by dsimp [integralDegreeEnd]; infer_instance
  exact RankOneSplit.integerEnd_unit_coefficient integralDegreeEnd

end AkopyanResearch.PairCollapseHomology
