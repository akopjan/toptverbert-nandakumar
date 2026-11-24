module

public import AkopyanResearch.Completion.DisjointComplementCoordinates
public import AkopyanResearch.Completion.OpenUnionMayerVietoris

/-!
# Inclusion coordinates for finite complements with acyclic cover unions

The deleted subsets need not be disjoint. The required vanishing concerns
the actual union of the two complement sets at each finite-deletion step.
This is the form used for the degree-nine atom coordinates.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FiniteComplementCoordinates

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel DisjointComplementHomology DisjointComplementCoordinates

variable {X : TopCat} {ι : Type}

def unionRestrictionIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) (OpenUnionMayerVietoris.unionSpace A B)))
    (hcur : IsZero (homology R i (OpenUnionMayerVietoris.unionSpace A B))) :
    homology R i (TopCat.of ↥(A ∩ B)) ≅
      homology R i (TopCat.of ↥A) ⊞ homology R i (TopCat.of ↥B) :=
  (OpenUnionMayerVietoris.intersectionHomologyIso A B R i).symm ≪≫
    unsignedIntersectionIso (OpenUnionMayerVietoris.cover A B hA hB) R i hnext hcur ≪≫
      biprod.mapIso (OpenUnionMayerVietoris.leftHomologyIso A B R i)
        (OpenUnionMayerVietoris.rightHomologyIso A B R i)

@[reassoc] theorem unionRestrictionIso_hom_fst (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) (OpenUnionMayerVietoris.unionSpace A B)))
    (hcur : IsZero (homology R i (OpenUnionMayerVietoris.unionSpace A B))) :
    (unionRestrictionIso A B hA hB R i hnext hcur).hom ≫ biprod.fst =
      (homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_left) := by
  simp only [unionRestrictionIso, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
    biprod.map_fst]
  erw [unsignedIntersectionIso_hom_fst_assoc]
  simp only [OpenUnionMayerVietoris.intersectionHomologyIso,
    OpenUnionMayerVietoris.leftHomologyIso, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, ← Functor.map_comp]
  rfl

@[reassoc] theorem unionRestrictionIso_hom_snd (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) (OpenUnionMayerVietoris.unionSpace A B)))
    (hcur : IsZero (homology R i (OpenUnionMayerVietoris.unionSpace A B))) :
    (unionRestrictionIso A B hA hB R i hnext hcur).hom ≫ biprod.snd =
      (homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_right) := by
  simp only [unionRestrictionIso, Iso.trans_hom, biprod.mapIso_hom, Category.assoc,
    biprod.map_snd]
  erw [unsignedIntersectionIso_hom_snd_assoc]
  simp only [OpenUnionMayerVietoris.intersectionHomologyIso,
    OpenUnionMayerVietoris.rightHomologyIso, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, ← Functor.map_comp]
  rfl

theorem isIso_binaryRestriction_of_union_zero (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) (OpenUnionMayerVietoris.unionSpace A B)))
    (hcur : IsZero (homology R i (OpenUnionMayerVietoris.unionSpace A B))) :
    IsIso (binaryRestriction A B R i) := by
  have heq : binaryRestriction A B R i =
      (unionRestrictionIso A B hA hB R i hnext hcur).hom ≫
        (AddCommGrpCat.biprodIsoProd _ _).hom := by
    rw [← Iso.comp_inv_eq]
    apply biprod.hom_ext
    · simp only [Category.assoc, AddCommGrpCat.biprodIsoProd_inv_comp_fst,
        binaryRestriction_comp_fst, unionRestrictionIso_hom_fst]
    · simp only [Category.assoc, AddCommGrpCat.biprodIsoProd_inv_comp_snd,
        binaryRestriction_comp_snd, unionRestrictionIso_hom_snd]
  rw [heq]
  infer_instance

def insertionIso [DecidableEq ι] (D : ι → Set X) (F : Finset ι) (j : ι)
    (R : AddCommGrpCat) (i : ℕ)
    [IsIso (binaryRestriction (complementSet D F) (D j)ᶜ R i)] :
    homology R i (TopCat.of ↥(complementSet D (insert j F))) ≅
      AddCommGrpCat.of (↥(homology R i (TopCat.of ↥(complementSet D F))) ×
        ↥(homology R i (TopCat.of ↥((D j)ᶜ)))) :=
  (homologyFunctor R i).mapIso
    (TopCat.isoOfHomeo (Homeomorph.setCongr (complementSet_insert D F j))) ≪≫
      asIso (binaryRestriction (complementSet D F) (D j)ᶜ R i)

@[reassoc] theorem insertionIso_hom_fst [DecidableEq ι]
    (D : ι → Set X) (F : Finset ι) (j : ι) (R : AddCommGrpCat) (i : ℕ)
    [IsIso (binaryRestriction (complementSet D F) (D j)ᶜ R i)] :
    (insertionIso D F j R i).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (homologyFunctor R i).map (subsetInclusion D (Finset.subset_insert j F)) := by
  simp only [insertionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc, binaryRestriction_comp_fst, ← Functor.map_comp]
  rfl

@[reassoc] theorem insertionIso_hom_snd [DecidableEq ι]
    (D : ι → Set X) (F : Finset ι) (j : ι) (R : AddCommGrpCat) (i : ℕ)
    [IsIso (binaryRestriction (complementSet D F) (D j)ᶜ R i)] :
    (insertionIso D F j R i).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (homologyFunctor R i).map (inclusion
        (complementSet_subset_single D (insert j F) j (Finset.mem_insert_self j F))) := by
  simp only [insertionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc, binaryRestriction_comp_snd, ← Functor.map_comp]
  rfl

/-- Finite induction for the literal coordinate restrictions. The step
hypothesis concerns only the actual binary inclusion map, and will be
discharged by the preceding open-union Mayer--Vietoris theorem. -/
theorem restriction_bijective_of_binary (D : ι → Set X) (F : Finset ι)
    (R : AddCommGrpCat) (i : ℕ) (hcur : IsZero (homology R i X))
    (hstep : ∀ (G : Finset ι) (j : ι), j ∉ G →
      IsIso (binaryRestriction (complementSet D G) (D j)ᶜ R i)) :
    Function.Bijective (restriction D F R i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hz : IsZero (homology R i (TopCat.of ↥(complementSet D ∅))) :=
        hcur.of_iso ((homologyFunctor R i).mapIso
          (TopCat.isoOfHomeo (emptyComplementHomeomorph D)))
      let := AddCommGrpCat.subsingleton_of_isZero hz
      constructor
      · intro x y _
        exact Subsingleton.elim x y
      · intro y
        exact ⟨0, Subsingleton.elim _ _⟩
  | @insert j F hj ih =>
      have := hstep F j hj
      let e := insertionIso D F j R i
      have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso _
      have heL (x : ↥(homology R i (TopCat.of ↥(complementSet D (insert j F))))) :
          (e.hom x).1 =
            (homologyFunctor R i).map (subsetInclusion D (Finset.subset_insert j F)) x :=
        ConcreteCategory.congr_hom (insertionIso_hom_fst D F j R i) x
      have heR (x : ↥(homology R i (TopCat.of ↥(complementSet D (insert j F))))) :
          (e.hom x).2 = restriction D (insert j F) R i x
            ⟨j, Finset.mem_insert_self j F⟩ :=
        ConcreteCategory.congr_hom (insertionIso_hom_snd D F j R i) x
      have hnat (x : ↥(homology R i (TopCat.of ↥(complementSet D (insert j F))))) (k : F) :
          restriction D F R i (e.hom x).1 k = restriction D (insert j F) R i x
            ⟨k.val, Finset.mem_insert_of_mem k.property⟩ := by
        rw [heL]
        exact restriction_naturality D (Finset.subset_insert j F) R i x k
      constructor
      · intro x y hxy
        apply he.1
        apply Prod.ext
        · apply ih.1
          funext k
          rw [hnat, hnat]
          exact congrFun hxy _
        · rw [heR, heR]
          exact congrFun hxy _
      · intro z
        obtain ⟨a, ha⟩ := ih.2 (fun k => z ⟨k.val, Finset.mem_insert_of_mem k.property⟩)
        obtain ⟨x, hx⟩ := he.2 (a, z ⟨j, Finset.mem_insert_self j F⟩)
        refine ⟨x, funext fun k => ?_⟩
        by_cases hkj : k.val = j
        · have hk : k = ⟨j, Finset.mem_insert_self j F⟩ := Subtype.ext hkj
          rw [hk, ← heR]
          exact congrArg Prod.snd hx
        · have hkF : k.val ∈ F := (Finset.mem_insert.mp k.property).resolve_left hkj
          calc
            restriction D (insert j F) R i x k =
                restriction D F R i (e.hom x).1 ⟨k.val, hkF⟩ := (hnat x ⟨k.val, hkF⟩).symm
            _ = restriction D F R i a ⟨k.val, hkF⟩ := by rw [congrArg Prod.fst hx]
            _ = z k := congrFun ha ⟨k.val, hkF⟩

def restrictionIsoOfBinary (D : ι → Set X) (F : Finset ι)
    (R : AddCommGrpCat) (i : ℕ) (hcur : IsZero (homology R i X))
    (hstep : ∀ (G : Finset ι) (j : ι), j ∉ G →
      IsIso (binaryRestriction (complementSet D G) (D j)ᶜ R i)) :
    homology R i (TopCat.of ↥(complementSet D F)) ≅
      AddCommGrpCat.of (∀ j : F, ↥(homology R i (TopCat.of ↥((D j.val)ᶜ)))) := by
  have := (ConcreteCategory.isIso_iff_bijective (restriction D F R i)).mpr
    (restriction_bijective_of_binary D F R i hcur hstep)
  exact asIso (restriction D F R i)

end AkopyanResearch.FiniteComplementCoordinates
