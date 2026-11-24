module

public import AkopyanResearch.Completion.ArrangementHomology
public import AkopyanResearch.Completion.QuadraticConnectivity

/-!
# Low-dimensional integral homology of the actual quadratic complement

The homotopy groups proved trivial in `QuadraticConnectivity` now imply the
vanishing of ordinary integral singular homology in degrees one through eight.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

namespace AkopyanResearch

/-- The actual matching-kernel complement is eight-connected. -/
theorem isNConnected_quadComplement (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Submission.IsNConnected 8 (QuadComplement S) := by
  letI : PathConnectedSpace (QuadComplement S) := pathConnectedSpace_quadComplement S hS
  exact ⟨inferInstance, inferInstance,
    fun k hk b => subsingleton_homotopyGroup_quadComplement S hS (k + 1) hk b⟩

/-- Its positive-degree ordinary integral singular homology vanishes through
 degree eight. No change to the comparison target is involved. -/
theorem isZero_homology_quadComplement (S : Finset (Fin 15)) (hS : S.Nonempty)
    (k : ℕ) (hk : k ≤ 8) (hk0 : k ≠ 0) :
    IsZero (Submission.Hgrp k (TopCat.of (QuadComplement S))) :=
  (isNConnected_quadComplement S hS).isZero_homology k hk hk0

end AkopyanResearch
