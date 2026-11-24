module

public import AkopyanResearch.Completion.ProductSphereProjection
public import Hatcher.MayerVietoris.Sequence

/-!
# Mayer--Vietoris steps for complements of arrangement strata

All maps below are the actual singular-homology maps of the named open cover.
The first lemma gives the direct-sum step for disjoint deleted strata. The
short-exact step gives the new pair-meridian classes when an atom is added.
The endpoint vanishing lemma uses surjectivity from one cover member, so it
does not require vanishing of the ambient homology one degree too high.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.ComplementMayerVietoris

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel
open Hatcher.MayerVietoris

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X : TopCat.{w}} {A B : Set X}

/-- If the ambient homology vanishes in two adjacent degrees, the actual
intersection map identifies the homology of the intersection with the
biproduct of the homologies of the cover members. -/
theorem isIso_intersectionMap_of_ambient_zero
    (h : Hatcher.Excision.CoverCondition A B) (R : C) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    IsIso (intersectionMap A B R i) := by
  exact (sequence_exact h R (i + 1) i rfl).isIso_map' 2 (by decide)
    (hnext.eq_zero_of_src _) (hcur.eq_zero_of_tgt _)

def intersectionHomologyIso
    (h : Hatcher.Excision.CoverCondition A B) (R : C) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    homology R i (TopCat.of ↥(A ∩ B)) ≅
      homology R i (TopCat.of ↥A) ⊞ homology R i (TopCat.of ↥B) := by
  have := isIso_intersectionMap_of_ambient_zero h R i hnext hcur
  exact asIso (intersectionMap A B R i)

/-- Vanishing in the two cover members and the next degree of the union
implies vanishing in their intersection. -/
theorem isZero_intersection_of_zero
    (h : Hatcher.Excision.CoverCondition A B) (R : C) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X))
    (hA : IsZero (homology R i (TopCat.of ↥A)))
    (hB : IsZero (homology R i (TopCat.of ↥B))) :
    IsZero (homology R i (TopCat.of ↥(A ∩ B))) := by
  exact ((sequence_exact h R (i + 1) i rfl).exact 2).isZero_of_both_isZero
    hnext ((biprod_isZero_iff _ _).mpr ⟨hA, hB⟩)

/-- The middle part of the genuine adjacent-degree Mayer--Vietoris window. -/
def boundaryComplex (h : Hatcher.Excision.CoverCondition A B) (R : C) (i : ℕ) :
    ShortComplex C :=
  ShortComplex.mk (connecting h R (i + 1) i rfl) (intersectionMap A B R i)
    ((sequence_exact h R (i + 1) i rfl).toIsComplex.zero 2)

/-- This is the short exact sequence which adds the new pair-meridian
classes when a new atom is deleted. -/
theorem boundaryComplex_shortExact
    (h : Hatcher.Excision.CoverCondition A B) (R : C) (i : ℕ)
    (hA : IsZero (homology R (i + 1) (TopCat.of ↥A)))
    (hB : IsZero (homology R (i + 1) (TopCat.of ↥B)))
    (hX : IsZero (homology R i X)) :
    (boundaryComplex h R i).ShortExact := by
  have hAB : IsZero
      (homology R (i + 1) (TopCat.of ↥A) ⊞ homology R (i + 1) (TopCat.of ↥B)) :=
    (biprod_isZero_iff _ _).mpr ⟨hA, hB⟩
  exact ShortComplex.ShortExact.mk'
    ((sequence_exact h R (i + 1) i rfl).exact 2)
    (((sequence_exact h R (i + 1) i rfl).exact 1).mono_g (hAB.eq_zero_of_src _))
    (((sequence_exact h R (i + 1) i rfl).exact 3).epi_f (hX.eq_zero_of_tgt _))

/-- Surjectivity from one cover member already makes the union map onto. -/
theorem epi_unionMap_of_right (R : C) (i : ℕ)
    (hB : Epi ((homologyFunctor R i).map (subspaceInclusion B))) :
    Epi (unionMap A B R i) := by
  exact epi_of_epi_fac (biprod.inr_desc
    ((homologyFunctor R i).map (subspaceInclusion A))
    ((homologyFunctor R i).map (subspaceInclusion B)))

/-- Endpoint vanishing with an epi hypothesis in the next degree. In
particular, `i = 14` requires no vanishing assumption on `H₁₅(X)`. -/
theorem isZero_intersection_of_epi_right
    (h : Hatcher.Excision.CoverCondition A B) (R : C) (i : ℕ)
    (hnext : Epi ((homologyFunctor R (i + 1)).map (subspaceInclusion B)))
    (hA : IsZero (homology R i (TopCat.of ↥A)))
    (hB : IsZero (homology R i (TopCat.of ↥B))) :
    IsZero (homology R i (TopCat.of ↥(A ∩ B))) := by
  have := epi_unionMap_of_right (A := A) R (i + 1) hnext
  let hs := sequence_exact h R (i + 1) i rfl
  let T : ShortComplex C := hs.sc 1
  have : Epi T.f := by change Epi (unionMap A B R (i + 1)); infer_instance
  have hz : T.g = 0 := zero_of_epi_comp T.f T.zero
  exact (hs.exact 2).isZero_X₂ hz
    (((biprod_isZero_iff _ _).mpr ⟨hA, hB⟩).eq_zero_of_tgt _)

/-- The pair long exact sequence supplies the epi hypothesis above from
vanishing of the actual relative homology. -/
theorem epi_inclusion_of_relative_zero (P : TopPair.{w}) (R : C) (i : ℕ)
    (h : IsZero ((Hatcher.Relative.homologyFunctor R i).obj P)) :
    Epi ((homologyFunctor R i).map P.map) :=
  ((Hatcher.Relative.singularPairFunctor.obj P).homology_exact₂ R i).epi_f
    (h.eq_zero_of_tgt _)

theorem isZero_subspace_of_relative_and_ambient_zero (P : TopPair.{w}) (R : C) (i : ℕ)
    (hrel : IsZero ((Hatcher.Relative.homologyFunctor R (i + 1)).obj P))
    (hamb : IsZero (homology R i P.fst)) :
    IsZero (homology R i P.snd) :=
  ((Hatcher.Relative.pairSequence_exact P R (i + 1) i rfl).exact 2)
    |>.isZero_of_both_isZero hrel hamb

theorem isIso_pairConnecting_of_ambient_zero (P : TopPair.{w}) (R : C) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) P.fst))
    (hcur : IsZero (homology R i P.fst)) :
    IsIso (Hatcher.Relative.pairConnecting P R (i + 1) i rfl) :=
  (Hatcher.Relative.pairSequence_exact P R (i + 1) i rfl).isIso_map' 1 (by decide)
    (hnext.eq_zero_of_src _) (hcur.eq_zero_of_tgt _)

end AkopyanResearch.ComplementMayerVietoris
