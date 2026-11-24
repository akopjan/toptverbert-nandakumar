module

public import Hatcher.Singular.Relative
public import AkopyanResearch.Completion.ProductSphereProjection

/-!
# Comparing actual pair maps through the natural connecting homomorphism

If the two adjacent ambient homology groups vanish, the pair boundary is
an isomorphism. Naturality then identifies a relative homology map with
the map induced on the actual subspaces by conjugation with boundaries.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairBoundaryComparison

open CategoryTheory CategoryTheory.Limits
open ProductSphereKernel

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (P : TopPair.{w}) (R : C) (i : ℕ)
variable (hhi : IsZero (homology R (i + 1) P.fst)) (hlo : IsZero (homology R i P.fst))

include hhi hlo in
theorem connecting_isIso : IsIso (Hatcher.Relative.pairConnecting P R (i + 1) i rfl) :=
  (Hatcher.Relative.pairSequence_exact P R (i + 1) i rfl).isIso_map'
    1 (by decide) (hhi.eq_zero_of_src _) (hlo.eq_zero_of_tgt _)

def boundaryIso : (Hatcher.Relative.homologyFunctor R (i + 1)).obj P ≅ homology R i P.snd := by
  letI := connecting_isIso P R i hhi hlo
  exact asIso (Hatcher.Relative.pairConnecting P R (i + 1) i rfl)

variable {P} {Q : TopPair.{w}} (g : P ⟶ Q)
variable (hQhi : IsZero (homology R (i + 1) Q.fst)) (hQlo : IsZero (homology R i Q.fst))

theorem relativeMap_factor :
    (Hatcher.Relative.homologyFunctor R (i + 1)).map g =
      (boundaryIso P R i hhi hlo).hom ≫ (homologyFunctor R i).map (TopPair.Hom.snd g) ≫
        (boundaryIso Q R i hQhi hQlo).inv := by
  apply (cancel_mono (boundaryIso Q R i hQhi hQlo).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (Hatcher.Relative.pairConnecting_naturality g R (i + 1) i rfl).symm

theorem subspaceMap_factor :
    (homologyFunctor R i).map (TopPair.Hom.snd g) =
      (boundaryIso P R i hhi hlo).inv ≫ (Hatcher.Relative.homologyFunctor R (i + 1)).map g ≫
        (boundaryIso Q R i hQhi hQlo).hom := by
  apply (cancel_epi (boundaryIso P R i hhi hlo).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact Hatcher.Relative.pairConnecting_naturality g R (i + 1) i rfl

include hhi hlo hQhi hQlo in
theorem relative_isIso_iff_subspace :
    IsIso ((Hatcher.Relative.homologyFunctor R (i + 1)).map g) ↔
      IsIso ((homologyFunctor R i).map (TopPair.Hom.snd g)) := by
  constructor
  · intro h
    rw [subspaceMap_factor R i hhi hlo g hQhi hQlo]
    infer_instance
  · intro h
    rw [relativeMap_factor R i hhi hlo g hQhi hQlo]
    infer_instance

end AkopyanResearch.PairBoundaryComparison
