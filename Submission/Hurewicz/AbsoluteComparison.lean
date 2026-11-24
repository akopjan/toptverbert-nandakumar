module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
public import Submission.Hurewicz.AbsoluteSurjectivity

@[expose] public section

/-!
# Naturality of the absolute Hurewicz homomorphism

The maintained absolute Hurewicz homomorphism is defined through the relative Hurewicz map of
the singleton pair.  Including that singleton in an arbitrary based subspace gives the expected
compatibility between the absolute-to-relative maps in homotopy and homology.  This is the
comparison square needed for pairs with contractible distinguished subspace.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {X : Type} [TopologicalSpace X]

/-- A based continuous map, regarded as a map between the singleton pairs at its source and
target basepoints. -/
def singletonBasedPairMap {Y : Type} [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y) :
    BasedPairMap ({x} : Set X) ({y} : Set Y)
      (⟨x, rfl⟩ : ({x} : Set X)) (⟨y, rfl⟩ : ({y} : Set Y)) where
  toContinuousMap := f
  mapsTo' := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz ⊢
    simpa [hz] using hf
  map_basepoint' := hf

/-- Inclusion of the singleton at the basepoint into an arbitrary based subspace, with the
identity map on the ambient space. -/
def singletonToBasedPair (A : Set X) (a : A) :
    BasedPairMap ({(a : X)} : Set X) A
      (⟨a, rfl⟩ : ({(a : X)} : Set X)) a where
  toContinuousMap := ContinuousMap.id X
  mapsTo' := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact a.property
  map_basepoint' := rfl

/-- Relative Hurewicz applied after `j_*` agrees with absolute Hurewicz followed by the
absolute-to-relative map in homology. -/
theorem relativeHurewicz_jStar (n : ℕ) (A : Set X) (a : A)
    (z : π_ (n + 2) X (a : X)) :
    relativeHurewicz n A a
        (RelHomotopyGroup.jStar (n + 2) X A a z) =
      relJ (n + 2) (subIncl (Y := TopCat.of X) A)
        (absoluteHurewiczAdd n (a : X) (Additive.ofMul z)) := by
  let a₀ : ({(a : X)} : Set X) := ⟨a, rfl⟩
  let f := singletonToBasedPair A a
  have hHur := relativeHurewicz_naturality n f
    (RelHomotopyGroup.jStar (n + 2) X ({(a : X)} : Set X) a₀ z)
  have hJ := ConcreteCategory.congr_hom
    (relJ_naturality (n + 2)
      (subIncl (Y := TopCat.of X) ({(a : X)} : Set X))
      (subIncl (Y := TopCat.of X) A)
      f.subIncl_naturality)
    (absoluteHurewiczAdd n (a : X) (Additive.ofMul z))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hJ
  change f.hrelMap (n + 2)
      (relativeHurewicz n ({(a : X)} : Set X) a₀
        (RelHomotopyGroup.jStar (n + 2) X ({(a : X)} : Set X) a₀ z)) = _ at hHur
  rw [RelHomotopyGroup.map_jStar] at hHur
  have hmap : HomotopyGroup.map f.toContinuousMap f.map_basepoint' z = z := by
    change HomotopyGroup.map (ContinuousMap.id X) _ z = z
    exact HomotopyGroup.map_id_apply z
  rw [hmap] at hHur
  rw [relJ_absoluteHurewiczAdd] at hJ
  have hamb : f.ambientHom = 𝟙 (TopCat.of X) := rfl
  have hHgrp : HgrpMap (n + 2) f.ambientHom = 𝟙 _ := by
    rw [hamb, HgrpMap_id]
  have hHgrpApply := ConcreteCategory.congr_hom hHgrp
    (absoluteHurewiczAdd n (a : X) (Additive.ofMul z))
  rw [ConcreteCategory.id_apply] at hHgrpApply
  change f.hrelMap (n + 2)
      (relativeHurewicz n ({(a : X)} : Set X) a₀
        (RelHomotopyGroup.jStar (n + 2) X ({(a : X)} : Set X) a₀ z)) =
    relJ (n + 2) (subIncl (Y := TopCat.of X) A)
      (HgrpMap (n + 2) f.ambientHom
        (absoluteHurewiczAdd n (a : X) (Additive.ofMul z))) at hJ
  exact hHur.symm.trans (hJ.trans (congrArg
    (fun q => relJ (n + 2) (subIncl (Y := TopCat.of X) A) q) hHgrpApply))

/-- The absolute Hurewicz homomorphism is natural under based continuous maps. -/
theorem absoluteHurewiczAdd_naturality (n : ℕ)
    {Y : Type} [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y) (z : Additive (π_ (n + 2) X x)) :
    HgrpMap (n + 2) (TopCat.ofHom f) (absoluteHurewiczAdd n x z) =
      absoluteHurewiczAdd n y
        (Additive.ofMul (HomotopyGroup.map f hf z.toMul)) := by
  let a : ({x} : Set X) := ⟨x, rfl⟩
  let b : ({y} : Set Y) := ⟨y, rfl⟩
  let F := singletonBasedPairMap f hf
  let i := subIncl (Y := TopCat.of X) ({x} : Set X)
  let j := subIncl (Y := TopCat.of Y) ({y} : Set Y)
  have hHur := relativeHurewicz_naturality n F
    (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)
  change F.hrelMap (n + 2)
      (relativeHurewicz n ({x} : Set X) a
        (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)) = _ at hHur
  rw [RelHomotopyGroup.map_jStar] at hHur
  change F.hrelMap (n + 2)
      (relativeHurewicz n ({x} : Set X) a
        (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)) =
    relativeHurewicz n ({y} : Set Y) b
      (RelHomotopyGroup.jStar (n + 2) Y ({y} : Set Y) b
        (HomotopyGroup.map f hf z.toMul)) at hHur
  have hJ := ConcreteCategory.congr_hom
    (relJ_naturality (n + 2) i j F.subIncl_naturality)
    (absoluteHurewiczAdd n x z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hJ
  have hsource := relJ_absoluteHurewiczAdd n x z
  have htarget := relJ_absoluteHurewiczAdd n y
    (Additive.ofMul (HomotopyGroup.map f hf z.toMul))
  change relJ (n + 2) i (absoluteHurewiczAdd n x z) =
    relativeHurewicz n ({x} : Set X) a
      (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul) at hsource
  change relJ (n + 2) j
      (absoluteHurewiczAdd n y
        (Additive.ofMul (HomotopyGroup.map f hf z.toMul))) =
    relativeHurewicz n ({y} : Set Y) b
      (RelHomotopyGroup.jStar (n + 2) Y ({y} : Set Y) b
        (HomotopyGroup.map f hf z.toMul)) at htarget
  have hjBij : Function.Bijective (relJ (n + 2) j) := by
    letI : IsIso (relJ (n + 2) j) := isIso_relJ_singleton n y
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  apply hjBij.injective
  calc
    relJ (n + 2) j
        (HgrpMap (n + 2) (TopCat.ofHom f) (absoluteHurewiczAdd n x z)) =
        F.hrelMap (n + 2) (relJ (n + 2) i (absoluteHurewiczAdd n x z)) := hJ.symm
    _ = F.hrelMap (n + 2)
        (relativeHurewicz n ({x} : Set X) a
          (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)) := by
      rw [hsource]
    _ = relativeHurewicz n ({y} : Set Y) b
        (RelHomotopyGroup.jStar (n + 2) Y ({y} : Set Y) b
          (HomotopyGroup.map f hf z.toMul)) := hHur
    _ = relJ (n + 2) j
        (absoluteHurewiczAdd n y
          (Additive.ofMul (HomotopyGroup.map f hf z.toMul))) := htarget.symm

end Submission
