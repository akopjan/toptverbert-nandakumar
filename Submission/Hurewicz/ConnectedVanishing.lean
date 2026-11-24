module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The bounded deformation below is extracted from Hurewicz/VanishingSorries.lean
at homotopy-groups-lean commit c66523531ff172d7f41913d94e56921e790a1b47.
The final absolute vanishing consequence uses that construction and the
singleton-pair lemma, with the ordinary Mathlib singular homology functor.
-/

public import Submission.Hurewicz.Compression
public import Submission.Homotopy.SingletonPair

@[expose] public section
noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology

namespace Submission

/-- Coherent compression of all singular simplices through a bounded dimension.
This is the original bounded construction, with no connectivity assumptions
hidden in a newly defined homology object. -/
theorem exists_simplicialDeformation_of_connectedPair (M : ℕ)
    (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) :
    Nonempty (SimplicialDeformation X A M) :=
  ⟨deformation (fun j => (towerLE M hA h₀ h j).step) (towerLE_isNext M hA h₀ h) M
    (fun n hn => (towerLE M hA h₀ h n).compresses hn)⟩

/-- An `M`-connected space has zero positive-degree singular homology through
`M`. The conclusion is Mathlib's singular homology with integer coefficients. -/
theorem IsNConnected.isZero_homology {M : ℕ} {X : Type} [TopologicalSpace X]
    (hX : IsNConnected M X) (k : ℕ) (hk : k ≤ M) (hk0 : k ≠ 0) :
    IsZero (Hgrp k (TopCat.of X)) := by
  let x : X := Classical.choice hX.nonempty
  have hp := hX.connectedSingletonPair x
  obtain ⟨d⟩ := exists_simplicialDeformation_of_connectedPair M (TopCat.of X)
    ({x} : Set X) (Set.singleton_nonempty x) hp.surjective_iStar_zero
    (fun n hn => hp.unique_piRel n (by omega))
  have hz := isZero_Hgrp_of_totallyDisconnected k hk0 (TopCat.of ({x} : Set X))
  have := d.epi_relIota k hk
  exact IsZero.of_epi (X := Hgrp k (TopCat.of ({x} : Set X)))
    (Y := Hgrp k (TopCat.of X)) (HgrpMap k (subIncl (Y := TopCat.of X) ({x} : Set X))) hz

end Submission
