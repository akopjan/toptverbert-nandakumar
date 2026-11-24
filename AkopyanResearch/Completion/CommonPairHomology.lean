module

public import AkopyanResearch.Completion.LinearPairComplementHomology
public import AkopyanResearch.Completion.PairConcreteLocalModel

/-!
# The two ordered covers of the actual common-equality normal space

Both orders of the two nonzero tests are retained. This permits the
atom-addition argument to use whichever cover member corresponds to the
old atom, without changing the actual pair coordinate or its target.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.CommonPairHomology

open CategoryTheory CategoryTheory.Limits
open MatchingSphereMap PairNormalModel PairConcreteLocalModel ProductSphereKernel
open LinearPairComplementHomology

def firstLinear : commonEquality →ₗ[ℝ] Rep10 where
  toFun x := x.val.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondLinear : commonEquality →ₗ[ℝ] Rep10 where
  toFun x := x.val.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def firstTest : commonEquality →L[ℝ] Rep10 := firstLinear.toContinuousLinearMap
def secondTest : commonEquality →L[ℝ] Rep10 := secondLinear.toContinuousLinearMap

theorem firstTest_surjective : Function.Surjective firstTest := by
  intro x
  exact ⟨⟨(x, x), by rw [mem_commonEquality]⟩, rfl⟩

theorem secondTest_surjective : Function.Surjective secondTest := by
  intro x
  exact ⟨⟨(x, x), by rw [mem_commonEquality]⟩, rfl⟩

def test : Bool → commonEquality →L[ℝ] Rep10
  | false => firstTest
  | true => secondTest

theorem test_surjective (b : Bool) : Function.Surjective (test b) := by
  cases b
  · exact firstTest_surjective
  · exact secondTest_surjective

theorem test_joint_zero (b : Bool) (x : commonEquality)
    (hf : test b x = 0) (hg : test (!b) x = 0) : x = 0 := by
  apply Subtype.ext
  cases b
  · exact Prod.ext hf hg
  · exact Prod.ext hg hf

def orderedComplementHomeomorph (b : Bool) :
    CommonComplement ≃ₜ LinearPairComplementHomology.Complement (test b) (test (!b)) :=
  Homeomorph.setCongr (by
    ext x
    cases b <;> simp [test, firstTest, secondTest, firstLinear, secondLinear, and_comm])

def orderedIntersectionHomeomorph (b : Bool) :
    CommonComplement ≃ₜ ↥(nonzeroSet (test b) ∩ nonzeroSet (test (!b))) :=
  (orderedComplementHomeomorph b).trans
    (LinearPairComplementHomology.intersectionHomeomorph (test b) (test (!b)))

theorem orderedCover (b : Bool) :
    Hatcher.Excision.CoverCondition (X := TopCat.of (PuncturedSpace.Space commonEquality))
      (nonzeroSet (test b)) (nonzeroSet (test (!b))) :=
  LinearPairComplementHomology.cover (test b) (test (!b)) (test_joint_zero b)

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

theorem member_homology_zero (b : Bool) (R : C) (i : ℕ) (hi : i = 12 ∨ i = 13) :
    IsZero (homology R i (TopCat.of ↥(nonzeroSet (test b)))) :=
  (SphereHomology.isZero_offDiagonal R 9 i (by omega) (by omega)).of_iso
    (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      (memberSphereEquiv (test b) (test_surjective b) 9 (finrank_euclideanSpace_fin)) R i)

theorem connecting_isIso (b : Bool) (R : C) :
    IsIso (Hatcher.MayerVietoris.connecting (orderedCover b) R 13 12 rfl) := by
  have hz (i : ℕ) (hi : i = 12 ∨ i = 13) :
      IsZero (homology R i (TopCat.of ↥(nonzeroSet (test b))) ⊞
        homology R i (TopCat.of ↥(nonzeroSet (test (!b))))) :=
    (biprod_isZero_iff _ _).mpr
      ⟨member_homology_zero b R i hi, member_homology_zero (!b) R i hi⟩
  exact (Hatcher.MayerVietoris.sequence_exact (orderedCover b) R 13 12 rfl).isIso_map'
    1 (by decide) ((hz 13 (Or.inr rfl)).eq_zero_of_src _)
      ((hz 12 (Or.inl rfl)).eq_zero_of_tgt _)

/-- The forward map is the actual local Mayer--Vietoris boundary, with
the explicit intersection coordinates returned to the original target. -/
def boundaryIso (b : Bool) (R : C) :
    homology R 13 (TopCat.of (PuncturedSpace.Space commonEquality)) ≅
      homology R 12 (TopCat.of CommonComplement) := by
  have := connecting_isIso b R
  exact asIso (Hatcher.MayerVietoris.connecting (orderedCover b) R 13 12 rfl) ≪≫
    (homologyFunctor R 12).mapIso (TopCat.isoOfHomeo (orderedIntersectionHomeomorph b).symm)

def ambientHomologyIso (R : C) :
    homology R 13 (TopCat.of (PuncturedSpace.Space commonEquality)) ≅ R :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    (PuncturedSpace.sphereEquiv commonEquality 13 finrank_commonEquality) R 13 ≪≫
    SphereHomology.diagonalIso R 13 (by decide)

def commonHomologyIso (R : C) : homology R 12 (TopCat.of CommonComplement) ≅ R :=
  (boundaryIso false R).symm ≪≫ ambientHomologyIso R

end AkopyanResearch.CommonPairHomology
