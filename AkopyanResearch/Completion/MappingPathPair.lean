module

public import AkopyanResearch.Completion.MappingPathReplacement
public import Hatcher.Singular.Relative
public import Hatcher.Singular.PointedRelative

/-!
# Actual pairs in the mapping-path replacement

The source pair, the unrestricted mapping-path pair, and the pointed
target are connected by strict maps of topological pairs. Their composite
is the original map. A fixed source point gives the ordinary based-path
pair, and this inclusion also commutes strictly with endpoint evaluation.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingPathPair

open CategoryTheory CategoryTheory.Limits
open MappingPathReplacement

universe w
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y₀ : Y)

abbrev pair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (MappingPathReplacement.Space f)) (FibreSet f y₀)

abbrev targetPair : TopPair.{w} := Hatcher.Relative.pointedPair (TopCat.of Y) y₀

def endpointPair : pair f y₀ ⟶ targetPair y₀ :=
  TopPair.ofHom (TopCat.ofHom (endpoint f)) (TopCat.isTerminalPUnit.from _) (by
    ext q
    exact q.property.symm)

abbrev basedPair (x : X) : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (Submission.PathSpace Y (f x)))
    {γ | Submission.ev₁ Y (f x) γ = y₀}

def basedFibreHomeomorph (x : X) : (basedPair f y₀ x).snd ≃ₜ
    Submission.PathFibre Y (f x) y₀ where
  toFun γ := ⟨γ.val, γ.property⟩
  invFun γ := ⟨γ.val, γ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def basedFibreInclusion (x : X) : C((basedPair f y₀ x).snd, (pair f y₀).snd) :=
  ⟨fun γ => ⟨basedPathInclusion f x γ.val, γ.property⟩,
    ((basedPathInclusion f x).continuous.comp continuous_subtype_val).subtype_mk _⟩

def basedPairInclusion (x : X) : basedPair f y₀ x ⟶ pair f y₀ :=
  TopPair.ofHom (TopCat.ofHom (basedPathInclusion f x))
    (TopCat.ofHom (basedFibreInclusion f y₀ x)) rfl

def basedEndpointPair (x : X) : basedPair f y₀ x ⟶ targetPair y₀ :=
  TopPair.ofHom (TopCat.ofHom (Submission.ev₁ Y (f x)))
    (TopCat.isTerminalPUnit.from _) (by ext γ; exact γ.property.symm)

theorem basedEndpoint_factor (x : X) :
    basedPairInclusion f y₀ x ≫ endpointPair f y₀ = basedEndpointPair f y₀ x := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · rfl

variable (A : Set X) (hA : ∀ x ∈ A, f x = y₀)

abbrev sourcePair : TopPair.{w} := TopPair.ofSubset (X := TopCat.of X) A

def sourceFibreInclusion : C(A, (pair f y₀).snd) :=
  ⟨fun x => ⟨sectionMap f x.val, hA x.val x.property⟩,
    ((sectionMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

def sourcePairMap : sourcePair A ⟶ pair f y₀ :=
  TopPair.ofHom (TopCat.ofHom (sectionMap f))
    (TopCat.ofHom (sourceFibreInclusion f y₀ A hA)) rfl

def originalPairMap : sourcePair A ⟶ targetPair y₀ :=
  TopPair.ofHom (TopCat.ofHom f) (TopCat.isTerminalPUnit.from _) (by
    ext x
    exact (hA x.val x.property).symm)

theorem originalPairMap_factor :
    sourcePairMap f y₀ A hA ≫ endpointPair f y₀ = originalPairMap f y₀ A hA := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · rfl

end AkopyanResearch.MappingPathPair
