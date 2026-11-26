module

public import AkopyanResearch.Completion.LoopProduct13Coordinates
public import AkopyanResearch.Completion.FiniteProductTopology
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Homology coordinates for finite products of loop thirteen-spheres

The isomorphism in degree twelve is induced by the literal coordinate
projections. Positive homology through degree fourteen vanishes away from
twelve. Both statements follow from the ordinary Mayer--Vietoris product
calculation and finite induction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.FiniteLoop13Homology

open CategoryTheory CategoryTheory.Limits ProductSphereKernel

abbrev Loop := LoopSphereCover.Fibre.{0} 12
abbrev Product (n : ℕ) := Fin n → Loop
abbrev Coefficients := AddCommGrpCat.of ℤ
abbrev LoopHomology := homology Coefficients 12 (TopCat.of Loop)

theorem product_isNConnected (n : ℕ) : Submission.IsNConnected 11 (Product n) :=
  ConnectivityTransport.pi fun _ => LoopProduct13Homology.fibre_isNConnected

theorem homology_vanish_fin (n i : ℕ) (hi : 0 < i) (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    IsZero (homology Coefficients i (TopCat.of (Product n))) := by
  induction n with
  | zero =>
      exact (Hatcher.Singular.isZero_pointHomology Coefficients i (by omega)).of_iso
        ((homologyFunctor Coefficients i).mapIso
          (TopCat.isoOfHomeo (FiniteProductTopology.finZero Loop)))
  | succ n ih =>
      exact ih.of_iso
        ((homologyFunctor Coefficients i).mapIso
          (TopCat.isoOfHomeo (FiniteProductTopology.finSucc Loop n)) ≪≫
            LoopProduct13Homology.projectionIso (Product n) (product_isNConnected n)
              i hi hi₁₄ hne)

theorem homology_vanish (ι : Type) [Fintype ι]
    (i : ℕ) (hi : 0 < i) (hi₁₄ : i ≤ 14) (hne : i ≠ 12) :
    IsZero (homology Coefficients i (TopCat.of (ι → Loop))) :=
  (homology_vanish_fin (Fintype.card ι) i hi hi₁₄ hne).of_iso
    ((homologyFunctor Coefficients i).mapIso
      (TopCat.isoOfHomeo (FiniteProductTopology.reindex Loop ι)))

def evaluation (n : ℕ) (j : Fin n) : C(Product n, Loop) :=
  ⟨fun x => x j, continuous_apply j⟩

def initialCoordinates (n : ℕ) : C(Product (n + 1), Product n) :=
  ⟨fun x j => x j.castSucc, continuous_pi fun j => continuous_apply j.castSucc⟩

def coordinates (n : ℕ) : homology Coefficients 12 (TopCat.of (Product n)) ⟶
    AddCommGrpCat.of (Fin n → LoopHomology) := AddCommGrpCat.ofHom {
  toFun x j := (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation n j)) x
  map_zero' := by funext j; exact map_zero _
  map_add' := by intro x y; funext j; exact map_add _ x y }

def inductionIso (n : ℕ) : homology Coefficients 12 (TopCat.of (Product (n + 1))) ≅
    AddCommGrpCat.of (↥(homology Coefficients 12 (TopCat.of (Product n))) × LoopHomology) :=
  (homologyFunctor Coefficients 12).mapIso
      (TopCat.isoOfHomeo (FiniteProductTopology.finSucc Loop n)) ≪≫
    LoopProduct13Coordinates.coordinatesIso (Product n) (product_isNConnected n) ≪≫
      AddCommGrpCat.biprodIsoProd _ _

theorem inductionIso_fst (n : ℕ) :
    (inductionIso n).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (initialCoordinates n)) := by
  rw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst]
  simp only [inductionIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc,
    LoopProduct13Coordinates.coordinatesIso, asIso_hom,
    BinaryProductHomology.coordinates, biprod.lift_fst]
  change (homologyFunctor Coefficients 12).map _ ≫
    (homologyFunctor Coefficients 12).map _ = _
  rw [← Functor.map_comp]
  congr 1
  ext x j
  exact FiniteProductTopology.finSucc_fst_apply Loop n x j

theorem inductionIso_snd (n : ℕ) :
    (inductionIso n).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation (n + 1) (Fin.last n))) := by
  rw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd]
  simp only [inductionIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc,
    LoopProduct13Coordinates.coordinatesIso, asIso_hom,
    BinaryProductHomology.coordinates, biprod.lift_snd]
  change (homologyFunctor Coefficients 12).map _ ≫
    (homologyFunctor Coefficients 12).map _ = _
  rw [← Functor.map_comp]
  rfl

theorem coordinates_naturality (n : ℕ)
    (x : ↥(homology Coefficients 12 (TopCat.of (Product (n + 1))))) (j : Fin n) :
    coordinates n ((homologyFunctor Coefficients 12).map
      (TopCat.ofHom (initialCoordinates n)) x) j = coordinates (n + 1) x j.castSucc := by
  have h : (homologyFunctor Coefficients 12).map (TopCat.ofHom (initialCoordinates n)) ≫
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation n j)) =
        (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation (n + 1) j.castSucc)) := by
    rw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h x

theorem coordinates_bijective (n : ℕ) : Function.Bijective (coordinates n) := by
  induction n with
  | zero =>
      have hz' : IsZero (homology Coefficients 12 (TopCat.of (Product 0))) :=
        (Hatcher.Singular.isZero_pointHomology Coefficients 12 (by decide)).of_iso
          ((homologyFunctor Coefficients 12).mapIso
            (TopCat.isoOfHomeo (FiniteProductTopology.finZero Loop)))
      let := AddCommGrpCat.subsingleton_of_isZero hz'
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | succ n ih =>
      let e := inductionIso n
      have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso _
      have hL (x : ↥(homology Coefficients 12 (TopCat.of (Product (n + 1))))) :
          (e.hom x).1 = (homologyFunctor Coefficients 12).map
            (TopCat.ofHom (initialCoordinates n)) x :=
        ConcreteCategory.congr_hom (inductionIso_fst n) x
      have hR (x : ↥(homology Coefficients 12 (TopCat.of (Product (n + 1))))) :
          (e.hom x).2 = coordinates (n + 1) x (Fin.last n) :=
        ConcreteCategory.congr_hom (inductionIso_snd n) x
      have hnat (x : ↥(homology Coefficients 12 (TopCat.of (Product (n + 1))))) (j : Fin n) :
          coordinates n (e.hom x).1 j = coordinates (n + 1) x j.castSucc := by
        rw [hL]
        exact coordinates_naturality n x j
      constructor
      · intro x y hxy
        apply he.1
        apply Prod.ext
        · apply ih.1
          funext j
          rw [hnat, hnat]
          exact congrFun hxy j.castSucc
        · rw [hR, hR]
          exact congrFun hxy (Fin.last n)
      · intro z
        obtain ⟨a, ha⟩ := ih.2 (fun j => z j.castSucc)
        obtain ⟨x, hx⟩ := he.2 (a, z (Fin.last n))
        refine ⟨x, funext fun j => ?_⟩
        refine Fin.lastCases ?_ (fun k => ?_) j
        · rw [← hR]
          exact congrArg Prod.snd hx
        · rw [← hnat, congrArg Prod.fst hx]
          exact congrFun ha k

def coordinatesIso (n : ℕ) : homology Coefficients 12 (TopCat.of (Product n)) ≅
    AddCommGrpCat.of (Fin n → LoopHomology) := by
  letI := (ConcreteCategory.isIso_iff_bijective (coordinates n)).mpr (coordinates_bijective n)
  exact asIso (coordinates n)

end AkopyanResearch.FiniteLoop13Homology
