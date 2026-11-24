module

public import Hatcher.Excision.SmallChainEquivalence
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# The singular small-chain API used by the Hurewicz development

These are transparent names for the actual singular subcomplexes and the
proved small-chain homotopy equivalence in Hatcher. This adapter avoids
vendoring a second subdivision and excision development.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits HomologicalComplex Simplicial Opposite

universe u v w

namespace TopCat
variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X}

namespace toSSet
abbrev subcomplexOfSet (V : Set X) := Hatcher.Excision.smallSubcomplexOfSet V
abbrev subcomplexOfSets (U : ι → Set X) := Hatcher.Excision.smallSubcomplex U

theorem mem_subcomplexOfSet_iff (V : Set X) {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSet V).obj _ ↔
      Set.range (toSSetObjEquiv _ _ s) ⊆ V :=
  Hatcher.Excision.mem_smallSubcomplexOfSet_iff V s

theorem subcomplexOfSet_inter (V₁ V₂ : Set X) :
    subcomplexOfSet (V₁ ∩ V₂) = subcomplexOfSet V₁ ⊓ subcomplexOfSet V₂ :=
  Hatcher.Excision.smallSubcomplexOfSet_inter V₁ V₂

theorem subcomplexOfSets_bool (U : Bool → Set X) :
    subcomplexOfSets U = subcomplexOfSet (U false) ⊔ subcomplexOfSet (U true) :=
  Hatcher.Excision.smallSubcomplex_bool U

theorem mem_subcomplexOfSets_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSets U).obj _ ↔
      ∃ i, Set.range (toSSetObjEquiv _ _ s) ⊆ U i :=
  Hatcher.Excision.mem_smallSubcomplex_iff s

theorem mem_subcomplexOfSets_iff' {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSets U).obj _ ↔
      ∃ (i : ι) (t : toSSet.obj (TopCat.of (U i)) _⦋n⦌),
        (toSSet.map (ofHom ⟨Subtype.val, by fun_prop⟩)).app _ t = s :=
  Hatcher.Excision.mem_smallSubcomplex_iff_exists_lift s
end toSSet

abbrev SmallSimplicesCondition (U : ι → Set X) :=
  Hatcher.Excision.SmallSimplicesCondition U

namespace SmallSimplicesCondition
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

def homotopyEquiv (hU : SmallSimplicesCondition U) (R : C) :
    HomotopyEquiv ((toSSet.subcomplexOfSets U).toSSet.chainComplex R)
      (Hatcher.Excision.singularChains X R) :=
  Hatcher.Excision.smallChainInclusionHomotopyEquiv hU R

@[simp] theorem homotopyEquiv_hom (hU : SmallSimplicesCondition U) (R : C) :
    (homotopyEquiv hU R).hom =
      SSet.chainComplexMap (toSSet.subcomplexOfSets U).ι R := rfl
theorem homotopyEquivalences (hU : SmallSimplicesCondition U) (R : C) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ)
      (SSet.chainComplexMap (toSSet.subcomplexOfSets U).ι R) :=
  Hatcher.Excision.smallChainInclusion_homotopyEquivalences hU R
end SmallSimplicesCondition
end TopCat

namespace Submission
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Degreewise freeness preserves monomorphisms of simplicial sets. -/
instance mono_simplicialChainMap {S T : SSet.{w}} (f : S ⟶ T) [Mono f] (R : C) :
    Mono (SSet.chainComplexMap f R) := by
  apply HomologicalComplex.mono_of_mono_f
  intro k
  change Mono ((sigmaConst.obj R).map (f.app (op ⦋k⦌)))
  infer_instance
end Submission
