module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The two pointed-set lemmas below are extracted from Homotopy/HomotopyLesTools.lean
at homotopy-groups-lean commit c66523531ff172d7f41913d94e56921e790a1b47.
They do not require the relative group-law construction.
-/

public import Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
public import Submission.Homotopy.Connected
public import Submission.ForMathlib.HomotopyGroup.Contractible

@[expose] public section
noncomputable section
open scoped Topology Topology.Homotopy

namespace Submission
variable {X : Type*} [TopologicalSpace X] {A : Set X}

/-- **A relative homotopy group vanishes when its two neighbours do.**  If `π_{n+1}(X)` and
`π_n(A)` are trivial then so is `π_{n+1}(X, A)`.

This is exactness of `π_{n+1}(X) → π_{n+1}(X, A) → π_n(A)` at the middle term, in the pointed-set
form supplied by the vendored library, so it applies in degree `1` as well, where there is no
group structure.  Note that only *one* neighbour has to be trivial for each of the two halves:
`π_n(A) = 0` makes `j_*` surjective and `π_{n+1}(X) = 0` collapses its image, so no bijectivity of
`i_*` — and hence no group structure — is ever needed. -/
theorem relativeUnique_of_adjacent_subsingleton (n : ℕ) (a : A)
    (hX : Subsingleton (π_ (n + 1) X (a : X))) (hA : Subsingleton (π_ n A a)) :
    Nonempty (Unique (π_rel (n + 1) X A a)) := by
  refine ⟨⟨⟨default⟩, fun z => ?_⟩⟩
  have hz : z ∈ Set.range (RelHomotopyGroup.jStar (n + 1) X A a) := by
    rw [← RelHomotopyGroup.isExactAt_jStar_bd n X A a]
    exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hA.elim _ _))
  obtain ⟨w, rfl⟩ := hz
  rw [hX.elim w default]
  exact (RelHomotopyGroup.jStar_isPointedMap (n + 1) X A a).map_default

/-- An `n`-connected space gives an `n`-connected pair after adjoining any chosen point as its
subspace.  This is the bridge from absolute connectivity to the relative simplex-compression
machinery. -/
theorem IsNConnected.connectedSingletonPair {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (hY : IsNConnected n Y) (y : Y) : IsNConnectedPair n Y ({y} : Set Y) := by
  letI : PathConnectedSpace Y := hY.pathConnected
  constructor
  · intro a z
    exact ⟨default,
      ((RelHomotopyGroup.iStar_isPointedMap 0 Y ({y} : Set Y) a).map_default).trans
        ((subsingleton_homotopyGroup_zero (a : Y)).elim _ z)⟩
  · intro k hk a
    exact relativeUnique_of_adjacent_subsingleton k a
      (hY.subsingleton_pi k hk (a : Y))
      (subsingleton_homotopyGroup_of_subsingleton a)

end Submission
