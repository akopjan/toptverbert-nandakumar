module

public import AkopyanResearch.Completion.PairNeighborhoodDeformation
public import AkopyanResearch.Completion.PairCofiberModel
public import AkopyanResearch.Completion.NeighborhoodNDR

/-!
# Homotopy extension for the actual closed pair locus

The explicit weighted-alignment deformation gives an open neighborhood of
the actual closed chart complement. The metric separator turns it into NDR
data on the original product of representation spheres. Consequently the
inclusion of the actual collapsed locus has the homotopy-extension property
for every topological target.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairCofibration

open Set ContinuousMap
open PairCofiberModel

abbrev NeighborhoodSet : Set PairSpace :=
  (PairNeighborhoodDeformation.badAntipodal (U := Priv4) (V := Priv4) (W := Comm6))ᶜ

theorem isOpen_neighborhood : IsOpen NeighborhoodSet :=
  PairNeighborhoodDeformation.isOpen_neighborhood

theorem closedLocus_subset_neighborhood : ClosedLocus ⊆ NeighborhoodSet := by
  intro x hx
  exact PairNeighborhoodDeformation.locus_not_bad ⟨x, hx⟩

/-- The removed locus contains an actual antipodal pair of common unit
vectors; it does not require a nonemptiness hypothesis. -/
theorem neighborhood_compl_nonempty : NeighborhoodSetᶜ.Nonempty := by
  let : Nontrivial Comm6 :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_Comm6]; decide)
  obtain ⟨w, hw⟩ := exists_norm_eq Comm6 (by norm_num : (0 : ℝ) ≤ 1)
  let a : PairCollapse.FullUnit Priv4 Comm6 := ⟨(0, w), by simp [hw]⟩
  let b : PairCollapse.FullUnit Priv4 Comm6 := ⟨(0, -w), by
    have hneg : ‖(-w : Comm6)‖ = 1 := (norm_neg w).trans hw
    have hz : ‖(0 : Priv4)‖ = 0 := norm_zero
    change ‖(0 : Priv4)‖ ^ 2 + ‖(-w : Comm6)‖ ^ 2 = 1
    rw [hz, hneg]
    norm_num⟩
  refine ⟨(a, b), ?_⟩
  change ¬ ¬ (a.val.1 = 0 ∧ b.val.1 = 0 ∧ a.val.2 + b.val.2 = 0)
  exact not_not.mpr ⟨rfl, rfl, add_neg_cancel w⟩

def localDeformation : NeighborhoodNDR.LocalDeformation ClosedLocus NeighborhoodSet where
  h := ⟨PairNeighborhoodDeformation.deformationRaw,
    PairNeighborhoodDeformation.continuous_deformationRaw⟩
  start x := congrArg Subtype.val (PairNeighborhoodDeformation.deformation_start x)
  fixed x hx t := PairNeighborhoodDeformation.deformationRaw_fixes t ⟨x.val, hx⟩
  finish := PairNeighborhoodDeformation.deformationRaw_end_mem_locus

def control : NeighborhoodNDR.Control ClosedLocus NeighborhoodSet :=
  NeighborhoodNDR.metricControl isClosed_closedLocus isOpen_neighborhood
    closedLocus_subset_neighborhood closedLocus_nonempty neighborhood_compl_nonempty

/-- Actual NDR data for the original product of two unit spheres and its
original closed chart complement. -/
def ndrData : NDRCylinder.Data ClosedLocus :=
  control.ndrData localDeformation

/-- The inclusion `ClosedLocus → PairSpace` has homotopy extension into
every topological space, with exact values on the bottom and the side. -/
theorem homotopyExtension {Y : Type*} [TopologicalSpace Y]
    (f : C(PairSpace, Y)) (g : C(NDRCylinder.Time × ClosedLocus, Y))
    (hg : ∀ a : ClosedLocus, g (0, a) = f a.val) :
    ∃ H : C(NDRCylinder.Time × PairSpace, Y),
      (∀ x, H (0, x) = f x) ∧ (∀ t a, H (t, a.val) = g (t, a)) :=
  ndrData.homotopyExtension f g hg

end AkopyanResearch.PairCofibration
