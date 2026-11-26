module

public import AkopyanResearch.Completion.LinearPairComplementHomology
public import AkopyanResearch.Completion.PairConcreteLocalModel
public import AkopyanResearch.Completion.PairCofiberModel

/-!
# Degree twelve of the original closed pair locus

The two actual tests in the explicit normal coordinates have common
kernel zero and ten-dimensional ranges. Their complement therefore has
degree-twelve homology equal to the coefficient group. The previously
proved normalization homotopy equivalence transfers this calculation to
the actual closed locus of the original pair collapse.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairNormalHomology

open CategoryTheory CategoryTheory.Limits
open PairConcreteLocalModel ProductSphereKernel

abbrev TestSpace := Comm6 × Priv4

def firstLinear : RawNormal →ₗ[ℝ] TestSpace where
  toFun x := (x.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondLinear : RawNormal →ₗ[ℝ] TestSpace where
  toFun x := (x.1, x.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def firstTest : RawNormal →L[ℝ] TestSpace := firstLinear.toContinuousLinearMap
def secondTest : RawNormal →L[ℝ] TestSpace := secondLinear.toContinuousLinearMap

theorem firstTest_surjective : Function.Surjective firstTest :=
  fun x => ⟨(x.1, x.2, 0), rfl⟩

theorem secondTest_surjective : Function.Surjective secondTest :=
  fun x => ⟨(x.1, 0, x.2), rfl⟩

theorem joint_zero (x : RawNormal) (ha : firstTest x = 0) (hb : secondTest x = 0) : x = 0 := by
  change (x.1, x.2.1) = (0, 0) at ha
  change (x.1, x.2.2) = (0, 0) at hb
  have hz := (Prod.mk.inj ha).1
  have hfirst := (Prod.mk.inj ha).2
  have hsecond := (Prod.mk.inj hb).2
  exact Prod.ext hz (Prod.ext hfirst hsecond)

theorem finrank_normal : Module.finrank ℝ RawNormal = 14 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_Comm6, finrank_Priv4]

theorem finrank_test : Module.finrank ℝ TestSpace = 10 := by
  rw [Module.finrank_prod, finrank_Comm6, finrank_Priv4]

theorem safe_iff_tests (x : RawNormal) :
    PairDeformation.Safe x ↔ firstTest x ≠ 0 ∧ secondTest x ≠ 0 := by
  change (x.1 ≠ 0 ∨ x.2.1 ≠ 0) ∧ (x.1 ≠ 0 ∨ x.2.2 ≠ 0) ↔
    (x.1, x.2.1) ≠ (0, 0) ∧ (x.1, x.2.2) ≠ (0, 0)
  simp only [ne_eq, Prod.mk.injEq, not_and_or]

def normalHomeomorph :
    Normal ≃ₜ LinearPairComplementHomology.Complement firstTest secondTest := by
  change ↥({x : RawNormal | PairDeformation.Safe x} : Set RawNormal) ≃ₜ
    ↥({x : RawNormal | firstTest x ≠ 0 ∧ secondTest x ≠ 0} : Set RawNormal)
  exact Homeomorph.setCongr (Set.ext safe_iff_tests)

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
variable (R : C)

def normalHomologyIso : homology R 12 (TopCat.of Normal) ≅ R :=
  (homologyFunctor R 12).mapIso (TopCat.isoOfHomeo normalHomeomorph) ≪≫
    LinearPairComplementHomology.boundaryHomologyIso firstTest secondTest
      firstTest_surjective secondTest_surjective joint_zero
      finrank_normal finrank_test finrank_test R

/-- The actual group of the actual closed chart complement; no homology
calculation is left as a hypothesis. -/
def collapsedHomologyIso :
    homology R 12 (TopCat.of PairCofiberModel.ClosedLocus) ≅ R :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    (PairLocalEquivalence.normalizationHomotopyEquiv
      (U := Priv4) (V := Priv4) (W := Comm6)).symm R 12 ≪≫ normalHomologyIso R

end AkopyanResearch.PairNormalHomology
