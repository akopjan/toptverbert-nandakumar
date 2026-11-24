module

public import AkopyanResearch.Completion.FiniteLoop13Homology

/-! # Degree-twelve loop-product coordinates with an arbitrary finite index -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.FiniteLoop13Coordinates

open CategoryTheory CategoryTheory.Limits ProductSphereKernel FiniteLoop13Homology

variable (ι : Type) [Fintype ι]

def evaluation (j : ι) : C(ι → Loop, Loop) := ⟨fun x => x j, continuous_apply j⟩

def coordinates : homology Coefficients 12 (TopCat.of (ι → Loop)) ⟶
    AddCommGrpCat.of (ι → LoopHomology) := AddCommGrpCat.ofHom {
  toFun x j := (homologyFunctor Coefficients 12).map (TopCat.ofHom (evaluation ι j)) x
  map_zero' := by funext j; exact map_zero _
  map_add' := by intro x y; funext j; exact map_add _ x y }

def reindexIso : homology Coefficients 12 (TopCat.of (ι → Loop)) ≅
    homology Coefficients 12 (TopCat.of (Product (Fintype.card ι))) :=
  (homologyFunctor Coefficients 12).mapIso
    (TopCat.isoOfHomeo (FiniteProductTopology.reindex Loop ι))

theorem coordinates_reindex (x : ↥(homology Coefficients 12 (TopCat.of (ι → Loop))))
    (j : Fin (Fintype.card ι)) :
    FiniteLoop13Homology.coordinates _ ((reindexIso ι).hom x) j =
      coordinates ι x ((Fintype.equivFin ι).symm j) := by
  have h : (reindexIso ι).hom ≫
      (homologyFunctor Coefficients 12).map (TopCat.ofHom (FiniteLoop13Homology.evaluation _ j)) =
        (homologyFunctor Coefficients 12).map
          (TopCat.ofHom (evaluation ι ((Fintype.equivFin ι).symm j))) := by
    change (homologyFunctor Coefficients 12).map _ ≫ (homologyFunctor Coefficients 12).map _ = _
    rw [← Functor.map_comp]
    congr 1
    ext q
    change Equiv.piCongrLeft (fun _ => Loop) (Fintype.equivFin ι) q j =
      q ((Fintype.equivFin ι).symm j)
    simp [Equiv.piCongrLeft_apply]
  exact ConcreteCategory.congr_hom h x

theorem coordinates_bijective : Function.Bijective (coordinates ι) := by
  have he : Function.Bijective (reindexIso ι).hom := ConcreteCategory.bijective_of_isIso _
  have hc := FiniteLoop13Homology.coordinates_bijective (Fintype.card ι)
  constructor
  · intro x y hxy
    apply he.1
    apply hc.1
    funext j
    rw [coordinates_reindex, coordinates_reindex]
    exact congrFun hxy _
  · intro z
    obtain ⟨a, ha⟩ := hc.2 (fun j => z ((Fintype.equivFin ι).symm j))
    obtain ⟨x, hx⟩ := he.2 a
    refine ⟨x, funext fun j => ?_⟩
    have h := coordinates_reindex ι x ((Fintype.equivFin ι) j)
    rw [hx, ha] at h
    simpa only [Equiv.symm_apply_apply] using h.symm

def coordinatesIso : homology Coefficients 12 (TopCat.of (ι → Loop)) ≅
    AddCommGrpCat.of (ι → LoopHomology) := by
  letI := (ConcreteCategory.isIso_iff_bijective (coordinates ι)).mpr (coordinates_bijective ι)
  exact asIso (coordinates ι)

end AkopyanResearch.FiniteLoop13Coordinates
