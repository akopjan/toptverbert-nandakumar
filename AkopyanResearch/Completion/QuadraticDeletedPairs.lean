module

public import AkopyanResearch.Completion.QuadraticMayerVietorisSets
public import Hatcher.Singular.Relative

/-!
# Actual pair coordinates for deleted quadratic strata

The arrangement complement and the ordinary exceptional-set complement
have the same points and topology. These homeomorphisms and pair
isomorphisms identify the precise objects used by excision and the normal
calculation, while retaining the original source spaces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.QuadraticDeletedPairs

open CategoryTheory
open AkopyanQuadratic QuadraticDeletion QuadraticMayerVietorisSets ArrangementConnectivity

variable {S : Finset (Fin 15)}

abbrev ExceptionalAmbient (S : Finset (Fin 15)) :=
  {x : QuadSpace S // x ∉ deletedLocus S}

def ambientHomeomorph : OpenAmbient S ≃ₜ ExceptionalAmbient S where
  toFun x := ⟨x.val, fun hx => by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact x.property j hj⟩
  invFun x := ⟨x.val, fun j hj => x.property (Set.mem_iUnion.mpr ⟨j, hj⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The pair obtained by deleting the surviving part of one actual linear
subspace from the original open ambient quadratic space. -/
abbrev deletionPair (U : Submodule ℝ (QuadSpace S)) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (OpenAmbient S)) {x | x.val ∉ U}

/-- The literal exceptional-set pair appearing in the normed Thom theorem. -/
abbrev exceptionalPair (U : Submodule ℝ (QuadSpace S)) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ExceptionalAmbient S)) {x | x.val ∉ U}

def complementHomeomorph (U : Submodule ℝ (QuadSpace S)) :
    (deletionPair U).snd ≃ₜ (exceptionalPair U).snd :=
  ambientHomeomorph.subtype (fun _ => Iff.rfl)

/-- Both the ambient map and the subspace map are the identity on the
underlying quadratic table. -/
def deletionPairIso (U : Submodule ℝ (QuadSpace S)) : deletionPair U ≅ exceptionalPair U :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (complementHomeomorph U))
    (TopCat.isoOfHomeo ambientHomeomorph) (by ext x; rfl)

abbrev ExceptionalBase (U : Submodule ℝ (QuadSpace S)) :=
  {a : U // a.val ∉ deletedLocus S}

def baseComplementHomeomorph (U : Submodule ℝ (QuadSpace S)) :
    Complement (E := ↥U) (fun j : DeletedIndex S => (deletedFlat S j).comap U.subtype) ≃ₜ
      ExceptionalBase U where
  toFun x := ⟨x.val, fun hx => by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact x.property j hj⟩
  invFun x := ⟨x.val, fun j hj => x.property (Set.mem_iUnion.mpr ⟨j, hj⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def stratumBaseHomeomorph (U : Submodule ℝ (QuadSpace S)) :
    {x : OpenAmbient S // x.val ∈ U} ≃ₜ ExceptionalBase U :=
  (restrictedComplementHomeomorph U).symm.trans (baseComplementHomeomorph U)

def atomBaseHomeomorph (m : MatchingIndex S) :
    ↥(atomSet S m) ≃ₜ ExceptionalBase (L_M S m.val) :=
  stratumBaseHomeomorph (L_M S m.val)

def criticalBaseHomeomorph (e : PairPathCoordinates.CriticalPairIndex S) :
    ↥(criticalPairSet S e) ≃ₜ ExceptionalBase (criticalFlat e) :=
  (Homeomorph.setCongr (criticalPairSet_eq_subspace e)).trans
    (stratumBaseHomeomorph (criticalFlat e))

/-- The literal complement of the indexed critical stratum is the second
space in the actual linear-deletion pair. -/
def criticalDeletionPairIso (e : PairPathCoordinates.CriticalPairIndex S) :
    TopPair.ofSubset (X := TopCat.of (OpenAmbient S)) (criticalPairSet S e)ᶜ ≅
      deletionPair (criticalFlat e) :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (Homeomorph.setCongr (by
      rw [criticalPairSet_eq_subspace]
      rfl)))
    (Iso.refl _) (by ext x; rfl)

end AkopyanResearch.QuadraticDeletedPairs
