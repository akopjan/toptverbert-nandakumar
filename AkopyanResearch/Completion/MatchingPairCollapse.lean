module

public import AkopyanResearch.Completion.PairSphereAction

/-!
# Equal common rows force the actual pair collapse to infinity

Centering two row tables that agree on four rows changes their first four
entries only by constants, separately in the two coordinates. Their common
orthogonal projections therefore agree. Positive normalization preserves
the common direction, which is precisely the complement of the collapse
chart. This criterion uses the original `V10Sub` and `spherePairEquiv`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MatchingPairCollapse

open scoped InnerProductSpace OnePoint BigOperators

theorem difference_mem_private (x y : V10Sub) (a b : ℝ)
    (hL : ∀ i : Fin 4,
      x.1 ((i.castAdd 2).castAdd 6) - y.1 ((i.castAdd 2).castAdd 6) = a)
    (hR : ∀ i : Fin 4,
      x.1 (Fin.natAdd 6 (i.castAdd 2)) - y.1 (Fin.natAdd 6 (i.castAdd 2)) = b) :
    x - y ∈ Comm6SubV10ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hw' := (mem_Comm6SubV10_iff w).mp hw
  have hwL : w.1 0 + w.1 1 + w.1 2 + w.1 3 = 0 := by
    have h := ((mem_V10Sub_iff w.1).mp w.2).1
    simpa [Fin.sum_univ_six, hw'.1, hw'.2.1] using h
  have hwR : w.1 6 + w.1 7 + w.1 8 + w.1 9 = 0 := by
    have h := ((mem_V10Sub_iff w.1).mp w.2).2
    simpa [Fin.sum_univ_six, hw'.2.2.1, hw'.2.2.2] using h
  change ⟪w.1, (x - y).1⟫_ℝ = 0
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [fin12_sum_split]
  change (∑ i : Fin 6, (x.1 (i.castAdd 6) - y.1 (i.castAdd 6)) * w.1 (i.castAdd 6)) +
    (∑ i : Fin 6, (x.1 (Fin.natAdd 6 i) - y.1 (Fin.natAdd 6 i)) *
      w.1 (Fin.natAdd 6 i)) = 0
  have hL0 : x.1 0 - y.1 0 = a := hL 0
  have hL1 : x.1 1 - y.1 1 = a := hL 1
  have hL2 : x.1 2 - y.1 2 = a := hL 2
  have hL3 : x.1 3 - y.1 3 = a := hL 3
  have hR0 : x.1 6 - y.1 6 = b := hR 0
  have hR1 : x.1 7 - y.1 7 = b := hR 1
  have hR2 : x.1 8 - y.1 8 = b := hR 2
  have hR3 : x.1 9 - y.1 9 = b := hR 3
  simp only [Fin.sum_univ_six]
  change (x.1 0 - y.1 0) * w.1 0 + (x.1 1 - y.1 1) * w.1 1 +
    (x.1 2 - y.1 2) * w.1 2 + (x.1 3 - y.1 3) * w.1 3 +
    (x.1 4 - y.1 4) * w.1 4 + (x.1 5 - y.1 5) * w.1 5 +
    ((x.1 6 - y.1 6) * w.1 6 + (x.1 7 - y.1 7) * w.1 7 +
      (x.1 8 - y.1 8) * w.1 8 + (x.1 9 - y.1 9) * w.1 9 +
      (x.1 10 - y.1 10) * w.1 10 + (x.1 11 - y.1 11) * w.1 11) = 0
  rw [hL0, hL1, hL2, hL3, hR0, hR1, hR2, hR3,
    hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2]
  linear_combination a * hwL + b * hwR

theorem common_iso10 (x : V10Sub) :
    (splitRep10 (iso10 x)).snd = Comm6SubV10.orthogonalProjectionOnto x := by
  simp [splitRep10, swapWithLp]

theorem common_eq_of_initial_differences (x y : V10Sub) (a b : ℝ)
    (hL : ∀ i : Fin 4,
      x.1 ((i.castAdd 2).castAdd 6) - y.1 ((i.castAdd 2).castAdd 6) = a)
    (hR : ∀ i : Fin 4,
      x.1 (Fin.natAdd 6 (i.castAdd 2)) - y.1 (Fin.natAdd 6 (i.castAdd 2)) = b) :
    (splitRep10 (iso10 x)).snd = (splitRep10 (iso10 y)).snd := by
  rw [common_iso10, common_iso10]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    (difference_mem_private x y a b hL hR)

theorem collapse_of_initial_differences (x y : V10Sub) (a b : ℝ)
    (hL : ∀ i : Fin 4,
      x.1 ((i.castAdd 2).castAdd 6) - y.1 ((i.castAdd 2).castAdd 6) = a)
    (hR : ∀ i : Fin 4,
      x.1 (Fin.natAdd 6 (i.castAdd 2)) - y.1 (Fin.natAdd 6 (i.castAdd 2)) = b)
    (sx sy : Metric.sphere (0 : Rep10) 1) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : sx.1 = r • iso10 x) (hy : sy.1 = s • iso10 y) :
    pairCollapseMap (spherePairEquiv (sx, sy)) = ∞ := by
  apply PairCollapse.collapse_eq_infty_of_common_nonnegative_multiples
    (U := Priv4) (V := Priv4) (W := Comm6)
    pairF norm_pairF _ (splitRep10 (iso10 x)).snd r s hr hs
  · change (splitRep10 sx.1).snd = r • (splitRep10 (iso10 x)).snd
    rw [hx, map_smul]
    rfl
  · change (splitRep10 sy.1).snd = s • (splitRep10 (iso10 x)).snd
    rw [hy, map_smul]
    change s • (splitRep10 (iso10 y)).snd = s • (splitRep10 (iso10 x)).snd
    rw [common_eq_of_initial_differences x y a b hL hR]

end AkopyanResearch.MatchingPairCollapse
