module

public import Submission.Homology.RelMap
public import Hatcher.Singular.Relative
public import Hatcher.Singular.PointedRelative

/-!
# Natural comparison of the two relative singular homology constructions

Both chain complexes are cokernels of the same map of ordinary integral
singular chains. The canonical isomorphism preserves the quotient maps
and commutes with every actual map of topological pairs. In particular,
the relative Hurewicz map's target and the Mayer–Vietoris calculation use
the same relative homology through an explicit natural chain isomorphism.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.RelativeHomologyBridge

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

abbrev Coefficients := AddCommGrpCat.of ℤ

instance mono_pairMap (P : TopPair.{0}) : Mono P.map :=
  (TopCat.mono_iff_injective P.map).mpr P.isEmbedding_map.injective

def chainIso (P : TopPair.{0}) : Submission.relComplex P.map ≅
    (Hatcher.Relative.chainComplexFunctor Coefficients).obj P :=
  (cokernelIsCokernel (Submission.CsingMap P.map)).coconePointUniqueUpToIso
    (Hatcher.Relative.isColimitCokernelCoforkChainComplex Coefficients P)

@[reassoc]
theorem quotient_chainIso (P : TopPair.{0}) :
    Submission.relProj P.map ≫ (chainIso P).hom =
      (Hatcher.Relative.chainComplexFunctorπ Coefficients).app P :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (Submission.CsingMap P.map))
    (Hatcher.Relative.isColimitCokernelCoforkChainComplex Coefficients P)
    WalkingParallelPair.one

def submissionChainMap {P Q : TopPair.{0}} (g : P ⟶ Q) :
    Submission.relComplex P.map ⟶ Submission.relComplex Q.map :=
  Submission.relComplexMap P.map Q.map (TopPair.Hom.w g).symm

theorem chainIso_naturality {P Q : TopPair.{0}} (g : P ⟶ Q) :
    submissionChainMap g ≫ (chainIso Q).hom =
      (chainIso P).hom ≫ (Hatcher.Relative.chainComplexFunctor Coefficients).map g := by
  have : Epi (Submission.relProj P.map) := coequalizer.π_epi
  apply (cancel_epi (Submission.relProj P.map)).mp
  calc
    Submission.relProj P.map ≫ submissionChainMap g ≫ (chainIso Q).hom =
        Submission.CsingMap (TopPair.Hom.fst g) ≫ Submission.relProj Q.map ≫ (chainIso Q).hom := by
      rw [← Category.assoc]
      exact congrArg (fun m => m ≫ (chainIso Q).hom)
        (Submission.relProj_comp_relComplexMap P.map Q.map (TopPair.Hom.w g).symm)
    _ = Submission.CsingMap (TopPair.Hom.fst g) ≫
        (Hatcher.Relative.chainComplexFunctorπ Coefficients).app Q := by rw [quotient_chainIso]
    _ = (Hatcher.Relative.chainComplexFunctorπ Coefficients).app P ≫
        (Hatcher.Relative.chainComplexFunctor Coefficients).map g :=
      (Hatcher.Relative.chainComplexFunctorπ Coefficients).naturality g
    _ = Submission.relProj P.map ≫ (chainIso P).hom ≫
        (Hatcher.Relative.chainComplexFunctor Coefficients).map g := by rw [quotient_chainIso_assoc]

def homologyIso (P : TopPair.{0}) (n : ℕ) : Submission.Hrel n P.map ≅
    (Hatcher.Relative.homologyFunctor Coefficients n).obj P :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).mapIso (chainIso P)

def submissionHomologyMap {P Q : TopPair.{0}} (g : P ⟶ Q) (n : ℕ) :
    Submission.Hrel n P.map ⟶ Submission.Hrel n Q.map :=
  HomologicalComplex.homologyMap (submissionChainMap g) n

theorem homologyIso_naturality {P Q : TopPair.{0}} (g : P ⟶ Q) (n : ℕ) :
    submissionHomologyMap g n ≫ (homologyIso Q n).hom =
      (homologyIso P n).hom ≫ (Hatcher.Relative.homologyFunctor Coefficients n).map g := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    chainIso_naturality]
  rfl

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set X} {B : Set Y} {a : A} {b : B}

def basedPairMap (f : Submission.BasedPairMap A B a b) :
    TopPair.ofSubset (X := TopCat.of X) A ⟶ TopPair.ofSubset (X := TopCat.of Y) B :=
  TopPair.ofHom f.ambientHom f.subspaceHom f.subIncl_naturality.symm

def subsetHomologyIso (A : Set X) (n : ℕ) :
    Submission.HrelSet (Y := TopCat.of X) n A ≅
      (Hatcher.Relative.homologyFunctor Coefficients n).obj (TopPair.ofSubset (X := TopCat.of X) A) :=
  homologyIso (TopPair.ofSubset (X := TopCat.of X) A) n

theorem basedPairMap_naturality (f : Submission.BasedPairMap A B a b) (n : ℕ) :
    f.hrelMap n ≫ (subsetHomologyIso B n).hom =
      (subsetHomologyIso A n).hom ≫
        (Hatcher.Relative.homologyFunctor Coefficients n).map (basedPairMap f) :=
  homologyIso_naturality (basedPairMap f) n

theorem basedPairMap_isIso (f : Submission.BasedPairMap A B a b) (n : ℕ)
    (h : IsIso (f.hrelMap n)) :
    IsIso ((Hatcher.Relative.homologyFunctor Coefficients n).map (basedPairMap f)) := by
  apply (isIso_comp_left_iff (subsetHomologyIso A n).hom _).mp
  rw [← basedPairMap_naturality]
  infer_instance

def singletonHomeomorph (y : Y) : ({y} : Set Y) ≃ₜ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨y, rfl⟩
  left_inv z := Subtype.ext z.property.symm
  right_inv _ := rfl
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

def singletonPairIso (y : Y) :
    TopPair.ofSubset (X := TopCat.of Y) ({y} : Set Y) ≅
      Hatcher.Relative.pointedPair (TopCat.of Y) y :=
  MorphismProperty.Arrow.isoMk (TopCat.isoOfHomeo (singletonHomeomorph y)) (Iso.refl _) (by
    ext z
    exact z.property.symm)

end AkopyanResearch.RelativeHomologyBridge
