module

public import AkopyanResearch.Completion.FreeRelativeClass
public import Submission.Hurewicz.RelativeRepresentatives
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Relative simplex classes and descent to actual relative homology

The algebraic descent is separated from its geometric input: the
alternating sum of the face classes of one normalized simplex vanishes.
Every map below uses Mathlib's singular relative complex and the ordinary
relative homotopy group. The boundary relation is an explicit hypothesis
of the descent theorem, not an axiom or a replacement definition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor
attribute [local implicit_reducible] Submission.relComplex Submission.Hrel RelHomotopyGroup

namespace AkopyanResearch.RelativeHurewiczDescent
open Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X}
variable (a : A) [PathConnectedSpace A]
variable (hπ : Subsingleton (HomotopyGroup.Pi 1 A a))

/-- The actual relative homotopy class of a normalized simplex. -/
def simplexClass (s : PairNormalizedSimplex n (TopCat.of X) A) :
    π_rel (n + 2) X A a :=
  FreeRelativeClass.classOf a s.cubeMap s.cubeMap_isMapOfPairs

include hπ in
/-- A cube loop survives conversion to a simplex and back without a change of class. -/
@[simp] theorem simplexClass_ofRelGenLoop (p : RelGenLoop (n + 2) X A a) :
    simplexClass a (PairNormalizedSimplex.ofRelGenLoop p) =
      (⟦p⟧ : π_rel (n + 2) X A a) := by
  unfold simplexClass
  simp only [PairNormalizedSimplex.ofRelGenLoop_cubeMap]
  exact FreeRelativeClass.classOf_relGenLoop a hπ p

/-- The explicit-simplex Hurewicz evaluator takes this class to the given simplex class. -/
theorem simplexRelativeHurewicz_simplexClass
    (s : PairNormalizedSimplex n (TopCat.of X) A) :
    simplexRelativeHurewicz n A a (simplexClass a s) = s.relativeClass := by
  let p := FreeRelativeClass.representative a s.cubeMap s.cubeMap_isMapOfPairs
  change RelGenLoop.hrelMap (n + 2) p (cubeSimplexRelativeClass n) = _
  have h := PairCube.homologyMap_congr s.cubeMap_isMapOfPairs p.property.1
    (FreeRelativeClass.representative_homotopic a s.cubeMap s.cubeMap_isMapOfPairs) (n + 2)
  rw [PairCube.homologyMap_relGenLoop] at h
  rw [← h]
  exact s.homologyMap_cubeSimplexRelativeClass

include hπ in
/-- Coherent normalization preserves the relative class of an already normalized simplex. -/
theorem simplexClass_normalization
    (h : IsNConnectedPair (n + 1) X A)
    (s : PairNormalizedSimplex n (TopCat.of X) A) :
    simplexClass a ((h.normalization ⟨a, a.property⟩).normalizeRelativeTopSimplex s.simplex) =
      simplexClass a s := by
  exact (FreeRelativeClass.classOf_congr a hπ s.cubeMap_isMapOfPairs _
    (s.normalization_homotopicWith h ⟨a, a.property⟩)).symm

section Chains

variable (h : IsNConnectedPair (n + 2) X A)

/-- The top normalized class, in dimension at least three so the relative group is abelian. -/
def normalizedClass (s : Sng (TopCat.of X) _⦋n + 3⦌) : π_rel (n + 3) X A a :=
  simplexClass a ((h.normalization ⟨a, a.property⟩).normalizeRelativeTopSimplex s)

/-- Extend normalized relative homotopy classes linearly to singular chains. -/
def classChain : (Csing (TopCat.of X)).X (n + 3) ⟶
    AddCommGrpCat.of (Additive (π_rel (n + 3) X A a)) :=
  ccDesc fun s => intHom (Additive.ofMul (normalizedClass a h s))

@[simp] theorem classChain_gen (s : Sng (TopCat.of X) _⦋n + 3⦌) :
    classChain a h (gen s) = Additive.ofMul (normalizedClass a h s) := by
  exact (ccDesc_gen (S := Sng (TopCat.of X))
    (T := AddCommGrpCat.of (Additive (π_rel (n + 3) X A a)))
    (fun t => intHom (Additive.ofMul (normalizedClass a h t))) s).trans
      (intHom_one (G := AddCommGrpCat.of (Additive (π_rel (n + 3) X A a))) _)

include hπ in
/-- The normalized class of a simplex supported in `A` is trivial. -/
theorem normalizedClass_inclusion (s : Sng (TopCat.of A) _⦋n + 3⦌) :
    normalizedClass a h ((sngIncl A).app _ s) = 1 := by
  let t := (h.normalization ⟨a, a.property⟩).normalizeRelativeTopSimplex
    ((sngIncl A).app _ s)
  have ht : ∀ y, t.cubeMap y ∈ A := by
    intro y
    change sngEquiv (TopCat.of X) (n + 3)
      ((h.normalization ⟨a, a.property⟩).ρ (n + 3) ((sngIncl A).app _ s))
      (cubeHomeoSimplex (n + 3) y) ∈ A
    rw [(h.normalization ⟨a, a.property⟩).ρ_fix, sngEquiv_incl]
    exact (sngEquiv (TopCat.of A) (n + 3) s (cubeHomeoSimplex (n + 3) y)).property
  exact FreeRelativeClass.classOf_eq_one_of_range_subset a hπ t.cubeMap ht

include hπ in
/-- The class map annihilates chains supported in the subspace. -/
theorem inclusion_comp_classChain :
    (CsingMap (subIncl (Y := TopCat.of X) A)).f (n + 3) ≫ classChain a h = 0 := by
  refine chainComplexX_hom_ext fun s => ?_
  change classChain a h ((CsingMap (subIncl (Y := TopCat.of X) A)).f (n + 3)
    (gen s)) = 0
  calc
    _ = classChain a h (gen ((sngIncl A).app _ s)) :=
      congrArg (classChain a h) (CsingMap_gen (subIncl (Y := TopCat.of X) A) s)
    _ = Additive.ofMul (normalizedClass a h ((sngIncl A).app _ s)) :=
      classChain_gen a h _
    _ = 0 := congrArg Additive.ofMul (normalizedClass_inclusion a hπ h s)

/-- The only remaining geometric input: addition of the oriented faces of one simplex. -/
def BoundaryRelation : Prop :=
  ∀ s : Sng (TopCat.of X) _⦋n + 4⦌,
    ∑ i : Fin (n + 5), ((-1 : ℤ) ^ (i : ℕ)) •
      Additive.ofMul (normalizedClass a h ((Sng (TopCat.of X)).δ i s)) = 0

/-- The face relation is precisely annihilation of the incoming singular differential. -/
theorem differential_comp_classChain (hb : BoundaryRelation a h) :
    (Csing (TopCat.of X)).d (n + 4) (n + 3) ≫ classChain a h = 0 := by
  refine chainComplexX_hom_ext fun s => ?_
  change classChain a h ((Csing (TopCat.of X)).d (n + 4) (n + 3) (gen s)) = 0
  have hd := congrArg (classChain a h)
    (d_gen (S := Sng (TopCat.of X)) (n := n + 3) s)
  calc
    _ = classChain a h (∑ i : Fin (n + 5), ((-1 : ℤ) ^ (i : ℕ)) •
        gen ((Sng (TopCat.of X)).δ i s)) := hd
    _ = ∑ i : Fin (n + 5), ((-1 : ℤ) ^ (i : ℕ)) •
        Additive.ofMul (normalizedClass a h ((Sng (TopCat.of X)).δ i s)) := by
      simp only [map_sum, map_zsmul]
      exact Finset.sum_congr rfl (fun i _ => congrArg
        (fun z => ((-1 : ℤ) ^ (i : ℕ)) • z) (classChain_gen a h _))
    _ = 0 := hb s

/-- The class map on the actual quotient complex of the pair. -/
def relativeClassChain :
    (relComplex (subIncl (Y := TopCat.of X) A)).X (n + 3) ⟶
      AddCommGrpCat.of (Additive (π_rel (n + 3) X A a)) :=
  cokDesc (CsingMap (subIncl (Y := TopCat.of X) A)) (n + 3)
    (classChain a h) (inclusion_comp_classChain a hπ h)

theorem projection_comp_relativeClassChain :
    (relProj (subIncl (Y := TopCat.of X) A)).f (n + 3) ≫ relativeClassChain a hπ h =
      classChain a h :=
  π_cokDesc _ _ _ _

/-- The incoming relative differential also maps to zero. -/
theorem differential_comp_relativeClassChain (hb : BoundaryRelation a h) :
    (relComplex (subIncl (Y := TopCat.of X) A)).d (n + 4) (n + 3) ≫
      relativeClassChain a hπ h = 0 := by
  letI : Epi ((relProj (subIncl (Y := TopCat.of X) A)).f (n + 4)) := by
    change Epi ((cokernel.π (CsingMap (subIncl (Y := TopCat.of X) A))).f (n + 4))
    infer_instance
  apply (cancel_epi ((relProj (subIncl (Y := TopCat.of X) A)).f (n + 4))).1
  rw [← Category.assoc, (relProj (subIncl (Y := TopCat.of X) A)).comm,
    Category.assoc, projection_comp_relativeClassChain,
    differential_comp_classChain a h hb, comp_zero]

/-- Descent to ordinary integral relative singular homology. -/
def homologyInverse (hb : BoundaryRelation a h) :
    HrelSet (Y := TopCat.of X) (n + 3) A ⟶
      AddCommGrpCat.of (Additive (π_rel (n + 3) X A a)) :=
  homologyDesc (relComplex (subIncl (Y := TopCat.of X) A)) (n + 3)
    (relativeClassChain a hπ h) (by
      rw [ChainComplex.prev ℕ (n + 3)]
      exact differential_comp_relativeClassChain a hπ h hb)

@[simp] theorem homologyInverse_homologyMk (hb : BoundaryRelation a h)
    (c : (relComplex (subIncl (Y := TopCat.of X) A)).X (n + 3))
    (hc : (relComplex (subIncl (Y := TopCat.of X) A)).d (n + 3)
      ((ComplexShape.down ℕ).next (n + 3)) c = 0) :
    homologyInverse a hπ h hb (homologyMk c hc) = relativeClassChain a hπ h c :=
  homologyDesc_homologyMk _ _ _ _

/-- Evaluation on a normalized simplex recovers its original relative homotopy class. -/
theorem homologyInverse_relativeClass (hb : BoundaryRelation a h)
    (s : PairNormalizedSimplex (n + 1) (TopCat.of X) A) :
    homologyInverse a hπ h hb s.relativeClass = Additive.ofMul (simplexClass a s) := by
  unfold PairNormalizedSimplex.relativeClass relativeSimplexClass
  rw [homologyInverse_homologyMk]
  change relativeClassChain a hπ h
    ((relProj (subIncl (Y := TopCat.of X) A)).f (n + 3) (gen s.simplex)) = _
  rw [← ConcreteCategory.comp_apply, projection_comp_relativeClassChain, classChain_gen]
  exact congrArg Additive.ofMul (simplexClass_normalization a hπ h s)

/-- The explicit-simplex relative Hurewicz evaluator has a left inverse when the
geometric face-addition relation holds. -/
theorem homologyInverse_simplexRelativeHurewicz (hb : BoundaryRelation a h)
    (z : π_rel (n + 3) X A a) :
    homologyInverse a hπ h hb (simplexRelativeHurewicz (n + 1) A a z) = Additive.ofMul z := by
  induction z using Quotient.inductionOn with
  | _ p =>
      let s := PairNormalizedSimplex.ofRelGenLoop (n := n + 1) (X := TopCat.of X) p
      have hs : simplexClass a s = (⟦p⟧ : π_rel (n + 3) X A a) :=
        simplexClass_ofRelGenLoop a hπ p
      rw [← hs, simplexRelativeHurewicz_simplexClass,
        homologyInverse_relativeClass]

include hπ in
/-- Injectivity follows from the concrete left-inverse calculation. -/
theorem simplexRelativeHurewicz_injective_of_boundaryRelation (hb : BoundaryRelation a h) :
    Function.Injective (simplexRelativeHurewicz (n + 1) A a) := by
  intro z w hzw
  have he := congrArg (homologyInverse a hπ h hb) hzw
  rw [homologyInverse_simplexRelativeHurewicz, homologyInverse_simplexRelativeHurewicz] at he
  exact Additive.ofMul.injective he

include hπ in
/-- Vanishing of relative homology kills the first relative homotopy group,
with the geometric face relation kept explicit. -/
theorem subsingleton_relativeHomotopy_of_boundaryRelation
    (hb : BoundaryRelation a h) (hz : IsZero (HrelSet (Y := TopCat.of X) (n + 3) A)) :
    Subsingleton (π_rel (n + 3) X A a) := by
  letI hs : Subsingleton (HrelSet (Y := TopCat.of X) (n + 3) A) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  exact (simplexRelativeHurewicz_injective_of_boundaryRelation a hπ h hb).subsingleton

end Chains
end AkopyanResearch.RelativeHurewiczDescent
