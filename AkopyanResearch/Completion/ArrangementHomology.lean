module

public import AkopyanResearch.Completion.ArrangementConnectivity
public import Submission.Hurewicz.ConnectedVanishing

/-!
# Integral homology below the codimension range of a linear arrangement

This connects the actual complement and its based homotopy groups to Mathlib's
ordinary singular homology. All maps and topologies are the original ones.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

namespace AkopyanResearch.ArrangementConnectivity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι]

/-- A finite arrangement of codimension at least `n+2` has `n`-connected
complement, in the ordinary based-homotopy sense. -/
theorem isNConnected_complement (L : ι → Submodule ℝ E) (n : ℕ)
    (hdim : ∀ i, n + 2 ≤ Module.finrank ℝ (E ⧸ L i)) :
    Submission.IsNConnected n (Complement L) := by
  letI : PathConnectedSpace (Complement L) := pathConnectedSpace_complement L (by
    intro i
    have hd := (L i).finrank_quotient_add_finrank
    have hc := hdim i
    omega)
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro k hk b
  exact subsingleton_homotopyGroup_of_codim L (k + 1)
    (fun i => by have hc := hdim i; omega) b

/-- The positive-degree integral singular homology vanishes in the same range. -/
theorem isZero_homology_complement (L : ι → Submodule ℝ E) (n k : ℕ)
    (hdim : ∀ i, n + 2 ≤ Module.finrank ℝ (E ⧸ L i))
    (hk : k ≤ n) (hk0 : k ≠ 0) :
    IsZero (Submission.Hgrp k (TopCat.of (Complement L))) :=
  (isNConnected_complement L n hdim).isZero_homology k hk hk0

end AkopyanResearch.ArrangementConnectivity
