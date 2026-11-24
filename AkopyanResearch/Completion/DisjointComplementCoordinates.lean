module

public import AkopyanResearch.Completion.DisjointComplementHomology
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Canonical homology coordinates for disjoint deleted strata

The coordinate maps are induced by the actual inclusions of the complement
of a finite union into each single-stratum complement. Mayer--Vietoris proves
that these maps form an isomorphism; the signs in its intersection map are
removed explicitly.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.DisjointComplementCoordinates

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel ComplementMayerVietoris DisjointComplementHomology
open Hatcher.MayerVietoris

variable {X : TopCat} {ι : Type}

def inclusion {A B : Set X} (h : A ⊆ B) : TopCat.of ↥A ⟶ TopCat.of ↥B :=
  TopCat.ofHom (ContinuousMap.inclusion h)

@[simp] theorem inclusion_comp {A B D : Set X} (hAB : A ⊆ B) (hBD : B ⊆ D) :
    inclusion hAB ≫ inclusion hBD = inclusion (hAB.trans hBD) := rfl

/-- The unsigned version of the actual Mayer--Vietoris intersection map. -/
def unsignedIntersectionIso {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    homology R i (TopCat.of ↥(A ∩ B)) ≅
      homology R i (TopCat.of ↥A) ⊞ homology R i (TopCat.of ↥B) :=
  intersectionHomologyIso h R i hnext hcur ≪≫
    biprod.mapIso (Iso.refl _) (-(Iso.refl _))

@[reassoc] theorem unsignedIntersectionIso_hom_fst {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    (unsignedIntersectionIso h R i hnext hcur).hom ≫ biprod.fst =
      (homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_left) := by
  simp [unsignedIntersectionIso, intersectionHomologyIso, intersectionMap]
  change biprod.lift
    ((homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_left))
    (-((homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_right))) ≫
      biprod.fst = _
  simp

@[reassoc] theorem unsignedIntersectionIso_hom_snd {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    (unsignedIntersectionIso h R i hnext hcur).hom ≫ biprod.snd =
      (homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_right) := by
  simp [unsignedIntersectionIso, intersectionHomologyIso, intersectionMap]
  change -biprod.lift
    ((homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_left))
    (-((homologyFunctor R i).map (inclusion (A := A ∩ B) Set.inter_subset_right))) ≫
      biprod.snd = _
  simp

def binaryRestriction (A B : Set X) (R : AddCommGrpCat) (i : ℕ) :
    homology R i (TopCat.of ↥(A ∩ B)) ⟶ AddCommGrpCat.of
      (↥(homology R i (TopCat.of ↥A)) × ↥(homology R i (TopCat.of ↥B))) :=
  AddCommGrpCat.ofHom
    (((homologyFunctor R i).map (inclusion Set.inter_subset_left)).hom.prod
      ((homologyFunctor R i).map (inclusion Set.inter_subset_right)).hom)

@[simp, reassoc] theorem binaryRestriction_comp_fst (A B : Set X)
    (R : AddCommGrpCat) (i : ℕ) :
    binaryRestriction A B R i ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (homologyFunctor R i).map (inclusion Set.inter_subset_left) := rfl

@[simp, reassoc] theorem binaryRestriction_comp_snd (A B : Set X)
    (R : AddCommGrpCat) (i : ℕ) :
    binaryRestriction A B R i ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (homologyFunctor R i).map (inclusion Set.inter_subset_right) := rfl

theorem isIso_binaryRestriction {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B) (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    IsIso (binaryRestriction A B R i) := by
  have heq : binaryRestriction A B R i =
      (unsignedIntersectionIso h R i hnext hcur).hom ≫
        (AddCommGrpCat.biprodIsoProd _ _).hom := by
    rw [← Iso.comp_inv_eq]
    apply biprod.hom_ext
    · simp only [Category.assoc, AddCommGrpCat.biprodIsoProd_inv_comp_fst,
        unsignedIntersectionIso_hom_fst]
      rfl
    · simp only [Category.assoc, AddCommGrpCat.biprodIsoProd_inv_comp_snd,
        unsignedIntersectionIso_hom_snd]
      rfl
  rw [heq]
  infer_instance

theorem complementSet_subset_single (D : ι → Set X) (F : Finset ι) (j : ι) (hj : j ∈ F) :
    complementSet D F ⊆ (D j)ᶜ := by
  intro x hx hxj
  exact hx (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hxj⟩⟩)

def restriction (D : ι → Set X) (F : Finset ι) (R : AddCommGrpCat) (i : ℕ) :
    homology R i (TopCat.of ↥(complementSet D F)) ⟶
      AddCommGrpCat.of (∀ j : F, ↥(homology R i (TopCat.of ↥((D j.val)ᶜ)))) :=
  AddCommGrpCat.ofHom
    { toFun := fun x j =>
        (homologyFunctor R i).map (inclusion (complementSet_subset_single D F j j.property)) x
      map_zero' := by funext j; exact map_zero _
      map_add' := by intro x y; funext j; exact map_add _ _ _ }

theorem complementSet_antitone (D : ι → Set X) {F G : Finset ι} (h : F ⊆ G) :
    complementSet D G ⊆ complementSet D F := by
  intro x hx hxF
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxF
  obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxj
  exact hx (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨h hj, hxj⟩⟩)

def subsetInclusion (D : ι → Set X) {F G : Finset ι} (h : F ⊆ G) :
    TopCat.of ↥(complementSet D G) ⟶ TopCat.of ↥(complementSet D F) :=
  inclusion (complementSet_antitone D h)

theorem restriction_naturality (D : ι → Set X) {F G : Finset ι} (h : F ⊆ G)
    (R : AddCommGrpCat) (i : ℕ) (x : ↥(homology R i (TopCat.of ↥(complementSet D G))))
    (j : F) :
    restriction D F R i ((homologyFunctor R i).map (subsetInclusion D h) x) j =
      restriction D G R i x ⟨j.val, h j.property⟩ := by
  change ((homologyFunctor R i).map (subsetInclusion D h) ≫
    (homologyFunctor R i).map (inclusion (complementSet_subset_single D F j j.property))) x = _
  rw [← Functor.map_comp]
  rfl

def insertHomologyIso [DecidableEq ι] (D : ι → Set X) (F : Finset ι) (j : ι)
    (hF : ∀ k ∈ F, IsClosed (D k)) (hj : IsClosed (D j))
    (hd : ∀ k ∈ F, Disjoint (D k) (D j))
    (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    homology R i (TopCat.of ↥(complementSet D (insert j F))) ≅
      AddCommGrpCat.of (↥(homology R i (TopCat.of ↥(complementSet D F))) ×
        ↥(homology R i (TopCat.of ↥((D j)ᶜ)))) := by
  have := isIso_binaryRestriction (complementCover D F j hF hj hd) R i hnext hcur
  exact (homologyFunctor R i).mapIso
    (TopCat.isoOfHomeo (Homeomorph.setCongr (complementSet_insert D F j))) ≪≫
      asIso (binaryRestriction (complementSet D F) (D j)ᶜ R i)

@[reassoc] theorem insertHomologyIso_hom_fst [DecidableEq ι]
    (D : ι → Set X) (F : Finset ι) (j : ι)
    (hF : ∀ k ∈ F, IsClosed (D k)) (hj : IsClosed (D j))
    (hd : ∀ k ∈ F, Disjoint (D k) (D j))
    (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    (insertHomologyIso D F j hF hj hd R i hnext hcur).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        (homologyFunctor R i).map (subsetInclusion D (Finset.subset_insert j F)) := by
  simp only [insertHomologyIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc, binaryRestriction_comp_fst, ← Functor.map_comp]
  rfl

@[reassoc] theorem insertHomologyIso_hom_snd [DecidableEq ι]
    (D : ι → Set X) (F : Finset ι) (j : ι)
    (hF : ∀ k ∈ F, IsClosed (D k)) (hj : IsClosed (D j))
    (hd : ∀ k ∈ F, Disjoint (D k) (D j))
    (R : AddCommGrpCat) (i : ℕ)
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    (insertHomologyIso D F j hF hj hd R i hnext hcur).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        (homologyFunctor R i).map (inclusion
          (complementSet_subset_single D (insert j F) j (Finset.mem_insert_self j F))) := by
  simp only [insertHomologyIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc, binaryRestriction_comp_snd, ← Functor.map_comp]
  rfl

/-- The actual restriction map is bijective. Its proof uses a finite
induction and the unsigned genuine Mayer--Vietoris map. -/
theorem restriction_bijective (D : ι → Set X) (F : Finset ι)
    (R : AddCommGrpCat) (i : ℕ)
    (hclosed : ∀ j ∈ F, IsClosed (D j))
    (hdisjoint : ∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (D j) (D k))
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    Function.Bijective (restriction D F R i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hz : IsZero (homology R i (TopCat.of ↥(complementSet D ∅))) :=
        hcur.of_iso ((homologyFunctor R i).mapIso
        (TopCat.isoOfHomeo (emptyComplementHomeomorph D)))
      let := AddCommGrpCat.subsingleton_of_isZero hz
      constructor
      · intro x y hxy
        exact Subsingleton.elim x y
      · intro y
        exact ⟨0, Subsingleton.elim _ _⟩
  | @insert j F hj ih =>
      have hF : ∀ k ∈ F, IsClosed (D k) :=
        fun k hk => hclosed k (Finset.mem_insert_of_mem hk)
      have hDj : IsClosed (D j) := hclosed j (Finset.mem_insert_self j F)
      have hd : ∀ k ∈ F, Disjoint (D k) (D j) := by
        intro k hk
        exact hdisjoint k (Finset.mem_insert_of_mem hk) j
          (Finset.mem_insert_self j F) (fun h => hj (h ▸ hk))
      have hIH := ih hF (fun k hk l hl hkl =>
        hdisjoint k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl)
      let e := insertHomologyIso D F j hF hDj hd R i hnext hcur
      have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso _
      have heL (x : ↥(homology R i (TopCat.of ↥(complementSet D (insert j F))))) :
          (e.hom x).1 =
            (homologyFunctor R i).map (subsetInclusion D (Finset.subset_insert j F)) x :=
        ConcreteCategory.congr_hom
          (insertHomologyIso_hom_fst D F j hF hDj hd R i hnext hcur) x
      have heR (x : ↥(homology R i (TopCat.of ↥(complementSet D (insert j F))))) :
          (e.hom x).2 = restriction D (insert j F) R i x
            ⟨j, Finset.mem_insert_self j F⟩ :=
        ConcreteCategory.congr_hom
          (insertHomologyIso_hom_snd D F j hF hDj hd R i hnext hcur) x
      have hnat (x : ↥(homology R i (TopCat.of ↥(complementSet D (insert j F))))) (k : F) :
          restriction D F R i (e.hom x).1 k = restriction D (insert j F) R i x
            ⟨k.val, Finset.mem_insert_of_mem k.property⟩ := by
        rw [heL]
        exact restriction_naturality D (Finset.subset_insert j F) R i x k
      constructor
      · intro x y hxy
        apply he.1
        apply Prod.ext
        · apply hIH.1
          funext k
          rw [hnat, hnat]
          exact congrFun hxy _
        · rw [heR, heR]
          exact congrFun hxy _
      · intro z
        obtain ⟨a, ha⟩ := hIH.2 (fun k => z ⟨k.val, Finset.mem_insert_of_mem k.property⟩)
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

/-- Canonical, inclusion-induced coordinates for the complement of a
finite family of disjoint closed subsets. -/
def restrictionIso (D : ι → Set X) (F : Finset ι)
    (R : AddCommGrpCat) (i : ℕ)
    (hclosed : ∀ j ∈ F, IsClosed (D j))
    (hdisjoint : ∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (D j) (D k))
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X)) :
    homology R i (TopCat.of ↥(complementSet D F)) ≅
      AddCommGrpCat.of (∀ j : F, ↥(homology R i (TopCat.of ↥((D j.val)ᶜ)))) := by
  have := (ConcreteCategory.isIso_iff_bijective (restriction D F R i)).mpr
    (restriction_bijective D F R i hclosed hdisjoint hnext hcur)
  exact asIso (restriction D F R i)

theorem restrictionIso_hom_apply (D : ι → Set X) (F : Finset ι)
    (R : AddCommGrpCat) (i : ℕ)
    (hclosed : ∀ j ∈ F, IsClosed (D j))
    (hdisjoint : ∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (D j) (D k))
    (hnext : IsZero (homology R (i + 1) X)) (hcur : IsZero (homology R i X))
    (x : ↥(homology R i (TopCat.of ↥(complementSet D F)))) (j : F) :
    (restrictionIso D F R i hclosed hdisjoint hnext hcur).hom x j =
      (homologyFunctor R i).map (inclusion (complementSet_subset_single D F j j.property)) x := rfl

end AkopyanResearch.DisjointComplementCoordinates
