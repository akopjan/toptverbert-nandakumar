module

public import AkopyanResearch.Completion.ComplementMayerVietoris

/-!
# Homology after deleting finitely many disjoint closed strata

The endpoint statement uses only the actual relative homology of each single
stratum. Ordinary Mayer--Vietoris supplies the finite induction. In particular
there is no assumption of a Thom formula for a disconnected union, and no
assumption about ambient homology one degree beyond the required range.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.DisjointComplementHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel ComplementMayerVietoris

universe w v u t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X : TopCat.{w}} {ι : Type t}

/-- The complement in the original ambient space of a finite union. -/
def complementSet (D : ι → Set X) (F : Finset ι) : Set X := (⋃ j ∈ F, D j)ᶜ

theorem complementSet_empty (D : ι → Set X) : complementSet D ∅ = Set.univ := by
  simp [complementSet]

theorem complementSet_insert [DecidableEq ι] (D : ι → Set X) (F : Finset ι) (j : ι) :
    complementSet D (insert j F) = complementSet D F ∩ (D j)ᶜ := by
  ext x
  simp only [complementSet, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_insert,
    Set.mem_inter_iff]
  aesop

theorem complementSet_isOpen (D : ι → Set X) (F : Finset ι)
    (hD : ∀ j ∈ F, IsClosed (D j)) : IsOpen (complementSet D F) :=
  (isClosed_biUnion_finset hD).isOpen_compl

/-- A new disjoint stratum and the old finite union have complementary
open sets covering the actual ambient space. -/
theorem complementCover (D : ι → Set X) (F : Finset ι) (j : ι)
    (hF : ∀ k ∈ F, IsClosed (D k)) (hj : IsClosed (D j))
    (hd : ∀ k ∈ F, Disjoint (D k) (D j)) :
    Hatcher.Excision.CoverCondition (complementSet D F) (D j)ᶜ where
  union_interior := by
    rw [(complementSet_isOpen D F hF).interior_eq, hj.isOpen_compl.interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ D j
    · left
      intro hmem
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hkmem, hxk⟩ := Set.mem_iUnion.mp hxk
      exact Set.disjoint_left.mp (hd k hkmem) hxk hx
    · exact Or.inr hx

def emptyComplementHomeomorph (D : ι → Set X) : complementSet D ∅ ≃ₜ X :=
  (Homeomorph.setCongr (complementSet_empty D)).trans (Homeomorph.Set.univ X)

/-- The finite-deletion endpoint. This will be used with `i = 14`, where
each relative group in degree fifteen vanishes by the single-stratum normal
calculation and connectedness of that stratum. -/
theorem isZero_finiteComplement_of_relative_zero
    (D : ι → Set X) (F : Finset ι) (R : C) (i : ℕ)
    (hclosed : ∀ j ∈ F, IsClosed (D j))
    (hdisjoint : ∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (D j) (D k))
    (hamb : IsZero (homology R i X))
    (hrel : ∀ j ∈ F,
      IsZero ((Hatcher.Relative.homologyFunctor R (i + 1)).obj
        (TopPair.ofSubset (D j)ᶜ))) :
    IsZero (homology R i (TopCat.of ↥(complementSet D F))) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact hamb.of_iso ((homologyFunctor R i).mapIso
        (TopCat.isoOfHomeo (emptyComplementHomeomorph D)))
  | @insert j F hj ih =>
      have hF : ∀ k ∈ F, IsClosed (D k) :=
        fun k hk => hclosed k (Finset.mem_insert_of_mem hk)
      have hDj : IsClosed (D j) := hclosed j (Finset.mem_insert_self j F)
      have hd : ∀ k ∈ F, Disjoint (D k) (D j) := by
        intro k hk
        exact hdisjoint k (Finset.mem_insert_of_mem hk) j
          (Finset.mem_insert_self j F) (fun h => hj (h ▸ hk))
      have hA : IsZero (homology R i (TopCat.of ↥(complementSet D F))) :=
        ih hF (fun k hk l hl hkl => hdisjoint k (Finset.mem_insert_of_mem hk)
          l (Finset.mem_insert_of_mem hl) hkl)
          (fun k hk => hrel k (Finset.mem_insert_of_mem hk))
      have hrelj := hrel j (Finset.mem_insert_self j F)
      have hB : IsZero (homology R i (TopCat.of ↥((D j)ᶜ))) :=
        isZero_subspace_of_relative_and_ambient_zero (TopPair.ofSubset (D j)ᶜ) R i
          hrelj hamb
      have hz := isZero_intersection_of_epi_right (complementCover D F j hF hDj hd) R i
        (epi_inclusion_of_relative_zero (TopPair.ofSubset (D j)ᶜ) R (i + 1) hrelj)
        hA hB
      exact hz.of_iso ((homologyFunctor R i).mapIso
        (TopCat.isoOfHomeo (Homeomorph.setCongr (complementSet_insert D F j))))

end AkopyanResearch.DisjointComplementHomology
