module

public import AkopyanResearch.Completion.UniversalSimplexAddition
public import AkopyanResearch.Completion.ConnectedPair

/-!
# From relative homology vanishing to bounded relative connectivity

Starting from the actual relative homotopy groups supplied by the pair
exact sequence, the first relative Hurewicz theorem raises connectivity
one degree at a time. The degree-fourteen application only uses relative
homology in degrees nine through fourteen.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.RelativeHomologyConnectivity

open CategoryTheory CategoryTheory.Limits Submission
open scoped Topology Topology.Homotopy

variable {X : Type} [TopologicalSpace X] {A : Set X}

/-- One genuine relative Hurewicz step. -/
theorem step (n : ℕ) (hA : IsNConnected 1 A)
    (h : IsNConnectedPair (n + 2) X A)
    (hz : IsZero (HrelSet (Y := TopCat.of X) (n + 3) A)) :
    IsNConnectedPair (n + 3) X A := by
  letI : PathConnectedSpace A := hA.pathConnected
  refine ⟨h.surjective_iStar_zero, ?_⟩
  intro k hk a
  by_cases hkle : k + 1 ≤ n + 2
  · exact h.unique_piRel k hkle a
  · have he : k = n + 2 := by omega
    subst k
    letI : Subsingleton (π_rel (n + 3) X A a) :=
      UniversalSimplexAddition.subsingleton_relativeHomotopy n a
        (hA.subsingleton_pi 0 (by decide) a) h hz
    exact ⟨⟨⟨default⟩, fun z => Subsingleton.elim z default⟩⟩

/-- Iterate the first nonzero relative-degree argument over a finite range. -/
theorem raiseThrough (q t : ℕ) (hA : IsNConnected 1 A)
    (h : IsNConnectedPair (q + 2) X A)
    (hz : ∀ k, q + 2 < k → k ≤ q + 2 + t →
      IsZero (HrelSet (Y := TopCat.of X) k A)) :
    IsNConnectedPair (q + 2 + t) X A := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
      have hprev : IsNConnectedPair (q + t + 2) X A := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (fun k hk hkt => hz k hk (by omega))
      have hnext := step (q + t) hA hprev (hz (q + t + 3) (by omega) (by omega))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/-- The exact connectivity range needed for fifteen-color face lifting. -/
theorem fourteen (hX : IsNConnected 8 X) (hA : IsNConnected 8 A)
    (hz : ∀ k, 9 ≤ k → k ≤ 14 → IsZero (HrelSet (Y := TopCat.of X) k A)) :
    IsNConnectedPair 14 X A := by
  exact raiseThrough 6 6 (hA.mono (by decide)) (initial 8 hX hA)
    (fun k hk hkt => hz k (by omega) hkt)

end AkopyanResearch.RelativeHomologyConnectivity
