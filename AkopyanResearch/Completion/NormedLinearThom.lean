module

public import AkopyanResearch.Completion.LinearTubeClosed
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Relative Thom isomorphism in any finite-dimensional normed real space

Continuous linear coordinates transfer the actual pair to a Euclidean
space, without replacing the norm or topology of the original space.
The pair and the base complement are transported by explicit
homeomorphisms. Empty exceptional sets are included.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.NormedLinearThom

open CategoryTheory CategoryTheory.Limits
open LinearTube LinearTubePair ProductSphereKernel

universe w v u
variable (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev EuclideanModel : Type w :=
  EuclideanSpace ℝ (ULift.{w} (Fin (Module.finrank ℝ E)))

def coordinates : E ≃L[ℝ] EuclideanModel E :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [EuclideanModel])

variable (L : Submodule ℝ E) (Z : Set E)

abbrev SourceBase : Type w := {a : L // a.val ∉ Z}
abbrev SourcePunctured : Set (Ambient Z) := {x | x.val ∉ L}
abbrev SourcePair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (Ambient Z)) (SourcePunctured E L Z)

def euclideanSubmodule : Submodule ℝ (EuclideanModel E) :=
  L.map (coordinates E).toLinearMap

def euclideanExceptional : Set (EuclideanModel E) := coordinates E '' Z

theorem coordinates_mem_submodule (x : E) :
    coordinates E x ∈ euclideanSubmodule E L ↔ x ∈ L := by
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
    exact (coordinates E).injective hxy ▸ hy
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

theorem coordinates_mem_exceptional (x : E) :
    coordinates E x ∈ euclideanExceptional E Z ↔ x ∈ Z :=
  (coordinates E).injective.mem_set_image

theorem isClosed_euclideanExceptional (hZ : IsClosed Z) :
    IsClosed (euclideanExceptional E Z) :=
  (coordinates E).toHomeomorph.isClosedMap _ hZ

def ambientHomeomorph :
    Ambient Z ≃ₜ Ambient (euclideanExceptional E Z) :=
  (coordinates E).toHomeomorph.subtype
    (fun x => (not_congr (coordinates_mem_exceptional E Z x)).symm)

def puncturedHomeomorph :
    SourcePunctured E L Z ≃ₜ Punctured (euclideanSubmodule E L) (euclideanExceptional E Z) :=
  (ambientHomeomorph E Z).subtype
    (fun x => (not_congr (coordinates_mem_submodule E L x.val)).symm)

/-- The normed-space and Euclidean versions of the actual relative pair
are isomorphic as topological pairs. -/
def ambientPairIso :
    SourcePair E L Z ≅ AmbientPair (euclideanSubmodule E L) (euclideanExceptional E Z) :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (puncturedHomeomorph E L Z))
    (TopCat.isoOfHomeo (ambientHomeomorph E Z)) (by ext p; rfl)

def baseHomeomorph :
    SourceBase E L Z ≃ₜ Base (euclideanSubmodule E L) (euclideanExceptional E Z) :=
  ((coordinates E).submoduleMap L).toHomeomorph.subtype
    (fun a => (not_congr (coordinates_mem_exceptional E Z a.val)).symm)

theorem codim_preserved :
    Module.finrank ℝ (EuclideanModel E ⧸ euclideanSubmodule E L) =
      Module.finrank ℝ (E ⧸ L) := by
  have hE := (coordinates E).toLinearEquiv.finrank_eq
  have hL := ((coordinates E).submoduleMap L).toLinearEquiv.finrank_eq
  have h₁ := L.finrank_quotient_add_finrank
  have h₂ := (euclideanSubmodule E L).finrank_quotient_add_finrank
  change Module.finrank ℝ L = Module.finrank ℝ (euclideanSubmodule E L) at hL
  omega

variable (hZ : IsClosed Z)
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The genuine relative Thom isomorphism for a finite-dimensional normed
real space. Its source retains the original norm and subspace topologies. -/
def relativeThomIso (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (c + i)).obj (SourcePair E L Z) ≅
      homology R i (TopCat.of (SourceBase E L Z)) :=
  ((Hatcher.Relative.homologyFunctor R (c + i)).mapIso (ambientPairIso E L Z)).trans
    ((LinearTubeClosed.relativeThomIso
      (euclideanSubmodule E L) (euclideanExceptional E Z)
      (isClosed_euclideanExceptional E Z hZ) c hc
      ((codim_preserved E L).trans hcodim) R i).trans
      ((homologyFunctor R i).mapIso (TopCat.isoOfHomeo (baseHomeomorph E L Z))).symm)

def relativeThomDegreeIso (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) (hci : c ≤ i) :
    (Hatcher.Relative.homologyFunctor R i).obj (SourcePair E L Z) ≅
      homology R (i - c) (TopCat.of (SourceBase E L Z)) := by
  simpa only [Nat.add_sub_of_le hci] using
    relativeThomIso E L Z hZ c hc hcodim R (i - c)

include hZ in
theorem isZero_relative_below_codim (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ) (hi : i < c) :
    IsZero ((Hatcher.Relative.homologyFunctor R i).obj (SourcePair E L Z)) :=
  (LinearTubeClosed.isZero_relative_below_codim
    (euclideanSubmodule E L) (euclideanExceptional E Z)
    (isClosed_euclideanExceptional E Z hZ) c hc
    ((codim_preserved E L).trans hcodim) R i hi).of_iso
    ((Hatcher.Relative.homologyFunctor R i).mapIso (ambientPairIso E L Z))

include hZ in
theorem isZero_relative_of_base (c : ℕ) (hc : 0 < c)
    (hcodim : Module.finrank ℝ (E ⧸ L) = c) (R : C) (i : ℕ)
    (hi : IsZero (homology R i (TopCat.of (SourceBase E L Z)))) :
    IsZero ((Hatcher.Relative.homologyFunctor R (c + i)).obj (SourcePair E L Z)) :=
  hi.of_iso (relativeThomIso E L Z hZ c hc hcodim R i)

end AkopyanResearch.NormedLinearThom
