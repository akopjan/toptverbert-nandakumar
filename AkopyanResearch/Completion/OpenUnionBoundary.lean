module

public import AkopyanResearch.Completion.OpenUnionMayerVietoris

/-!
# The actual Mayer--Vietoris boundary extension for an open union

When the second cover member has zero homology in the current degree,
the target of the boundary extension is the homology of the first member.
The outgoing map is the actual inclusion of the intersection.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.OpenUnionBoundary

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel ComplementMayerVietoris OpenUnionMayerVietoris

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

def transport (T : ShortComplex C) {A B D : C}
    (e₁ : T.X₁ ≅ A) (e₂ : T.X₂ ≅ B) (e₃ : T.X₃ ≅ D) : ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ T.f ≫ e₂.hom) (e₂.inv ≫ T.g ≫ e₃.hom) (by
    simp [Category.assoc])

def transportIso (T : ShortComplex C) {A B D : C}
    (e₁ : T.X₁ ≅ A) (e₂ : T.X₂ ≅ B) (e₃ : T.X₃ ≅ D) :
    T ≅ transport T e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃ (by simp [transport]) (by simp [transport])

omit [HasCoproducts.{w} C] in
theorem transport_shortExact (T : ShortComplex C) {A B D : C}
    (e₁ : T.X₁ ≅ A) (e₂ : T.X₂ ≅ B) (e₃ : T.X₃ ≅ D) (hT : T.ShortExact) :
    (transport T e₁ e₂ e₃).ShortExact :=
  ShortComplex.shortExact_of_iso (transportIso T e₁ e₂ e₃) hT

def biprodLeftIso (A B : C) (hB : IsZero B) : A ⊞ B ≅ A where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext
    · simp
    · exact hB.eq_of_tgt _ _
  inv_hom_id := biprod.inl_fst

variable {X : TopCat.{w}} (A B : Set X)

def sequence (hA : IsOpen A) (hB : IsOpen B) (R : C) (i : ℕ)
    (hHB : IsZero (homology R i (TopCat.of ↥B))) : ShortComplex C :=
  transport (boundaryComplex (cover A B hA hB) R i) (Iso.refl _)
    (OpenUnionMayerVietoris.intersectionHomologyIso A B R i)
    (biprod.mapIso (leftHomologyIso A B R i) (rightHomologyIso A B R i) ≪≫
      biprodLeftIso _ _ hHB)

theorem sequence_shortExact (hA : IsOpen A) (hB : IsOpen B) (R : C) (i : ℕ)
    (hHB : IsZero (homology R i (TopCat.of ↥B)))
    (hA' : IsZero (homology R (i + 1) (TopCat.of ↥A)))
    (hB' : IsZero (homology R (i + 1) (TopCat.of ↥B)))
    (hU : IsZero (homology R i (unionSpace A B))) :
    (sequence A B hA hB R i hHB).ShortExact := by
  apply transport_shortExact
  exact boundaryComplex_shortExact (cover A B hA hB) R i
    (hA'.of_iso (leftHomologyIso A B R (i + 1)))
    (hB'.of_iso (rightHomologyIso A B R (i + 1))) hU

theorem sequence_f (hA : IsOpen A) (hB : IsOpen B) (R : C) (i : ℕ)
    (hHB : IsZero (homology R i (TopCat.of ↥B))) :
    (sequence A B hA hB R i hHB).f =
      Hatcher.MayerVietoris.connecting (cover A B hA hB) R (i + 1) i rfl ≫
        (OpenUnionMayerVietoris.intersectionHomologyIso A B R i).hom := by
  simp [sequence, transport, boundaryComplex]

theorem intersectionMap_fst {T : TopCat.{w}} (U V : Set T) (R : C) (i : ℕ) :
    Hatcher.MayerVietoris.intersectionMap U V R i ≫ biprod.fst =
      (homologyFunctor R i).map (Hatcher.MayerVietoris.intersectionToLeft U V) := by
  change biprod.lift
    ((homologyFunctor R i).map (Hatcher.MayerVietoris.intersectionToLeft U V))
    (-((homologyFunctor R i).map (Hatcher.MayerVietoris.intersectionToRight U V))) ≫
      biprod.fst = _
  simp

@[reassoc] theorem intersectionMap_fst_comp {T : TopCat.{w}} (U V : Set T)
    (R : C) (i : ℕ) {D : C} (f : homology R i (TopCat.of ↥U) ⟶ D) :
    Hatcher.MayerVietoris.intersectionMap U V R i ≫ biprod.fst ≫ f =
      (homologyFunctor R i).map (Hatcher.MayerVietoris.intersectionToLeft U V) ≫ f := by
  rw [← Category.assoc, intersectionMap_fst]

/-- The quotient map in the boundary extension is exactly the inclusion
of the original intersection into the first original cover member. -/
theorem sequence_g (hA : IsOpen A) (hB : IsOpen B) (R : C) (i : ℕ)
    (hHB : IsZero (homology R i (TopCat.of ↥B))) :
    (sequence A B hA hB R i hHB).g =
      (homologyFunctor R i).map (Hatcher.MayerVietoris.intersectionToLeft A B) := by
  simp only [sequence, transport, boundaryComplex, Iso.trans_hom, biprod.mapIso_hom,
    biprodLeftIso, biprod.map_fst]
  erw [intersectionMap_fst_comp]
  simp only [OpenUnionMayerVietoris.intersectionHomologyIso, leftHomologyIso,
    Functor.mapIso_hom, Functor.mapIso_inv, ← Functor.map_comp]
  rfl

end AkopyanResearch.OpenUnionBoundary
