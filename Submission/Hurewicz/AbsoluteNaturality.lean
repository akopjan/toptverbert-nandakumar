module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
public import Submission.Hurewicz.AbsoluteIsomorphism
public import Submission.Hurewicz.AbsoluteComparison

@[expose] public section


open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval
noncomputable section
namespace Submission
variable {X : Type} [TopologicalSpace X]

/-- If the distinguished subspace is contractible, the relative Hurewicz map in the first
nonvanishing degree is an isomorphism whenever the corresponding absolute Hurewicz map is.

This is a cancellation argument around the preceding square: both absolute-to-relative maps
`j_*` and `j` are isomorphisms for a contractible subspace. -/
theorem IsNConnected.relativeHurewiczAdd_bijective_of_contractibleSubspace
    {n : ℕ} (hX : IsNConnected (n + 1) X) (A : Set X) (a : A)
    [ContractibleSpace A] :
    Function.Bijective (relativeHurewiczAdd n A a) := by
  let i := subIncl (Y := TopCat.of X) A
  have hJ : Function.Bijective (RelHomotopyGroup.jStarHom n X A a) :=
    bijective_jStar_of_subsingleton n a
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) a)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) a)
  let eJ : Additive (π_ (n + 2) X (a : X)) ≃+
      Additive (π_rel (n + 2) X A a) :=
    MulEquiv.toAdditive
      (MulEquiv.ofBijective (RelHomotopyGroup.jStarHom n X A a) hJ)
  have hJAdd : Function.Bijective
      (RelHomotopyGroup.jStarHom n X A a).toAdditive := by
    exact eJ.bijective
  have htop : IsZero (Hgrp (n + 2) (TopCat.of A)) :=
    isZero_Hgrp_of_contractible (X := TopCat.of A) (n + 1)
  have hprev : IsZero (Hgrp (n + 1) (TopCat.of A)) :=
    isZero_Hgrp_of_contractible (X := TopCat.of A) n
  letI : IsIso (relJ (n + 2) i) :=
    isIso_relJ i (n + 1) (htop.eq_zero_of_src _) (hprev.mono _)
  have hRelJ : Function.Bijective (relJ (n + 2) i) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hcomm :
      (fun z => relativeHurewiczAdd n A a
        ((RelHomotopyGroup.jStarHom n X A a).toAdditive z)) =
      fun z => relJ (n + 2) i (absoluteHurewiczAdd n (a : X) z) := by
    funext z
    exact relativeHurewicz_jStar n A a z.toMul
  have hcomp : Function.Bijective
      (relativeHurewiczAdd n A a ∘
        (RelHomotopyGroup.jStarHom n X A a).toAdditive) := by
    change Function.Bijective (fun z => relativeHurewiczAdd n A a
      ((RelHomotopyGroup.jStarHom n X A a).toAdditive z))
    rw [hcomm]
    exact hRelJ.comp (hX.absoluteHurewiczAdd_bijective (a : X))
  exact (Function.Bijective.of_comp_iff _ hJAdd).mp hcomp

end Submission
