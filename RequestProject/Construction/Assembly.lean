module

public import RequestProject.Construction.Safety
public import RequestProject.Construction.Chart
public import RequestProject.Construction.Obstacles
public import RequestProject.Surgery.Main
public import RequestProject.Construction.Good

@[expose] public section

/-!
# Assembly: the height extension

`Fmap q y = F0 q (toBary (ret y))` is a good map for the obstacles `ellLin m` (proved in
`RequestProject/Construction/Good.lean`), so the surgery theorem removes all its zeros inside the
open simplex; pulling back along the chart gives the required height table.
-/

open Set Surgery

namespace Tverberg6R

noncomputable section

theorem goodMap_Fmap {q : Fin 6 → Fin 6 → ℝ} (hq : IsGeneric q) : GoodMap Qs Uo (Fmap q) :=
  goodMap_Fmap' hq

lemma toBary_mem_Uo_iff {y : ℝ × (Fin 4 → ℝ)} : y ∈ Uo ↔ ∀ i, 0 < toBary y i := Iff.rfl

/-- **The height extension.** -/
theorem exists_height :
    ∃ H : (Fin 6 → ℝ) → Table, ContinuousOn H massSimplex ∧ Compatible H ∧ Safe H := by
  obtain ⟨q, hq⟩ := exists_generic
  have hF := goodMap_Fmap hq
  obtain ⟨G, hGc, K, hK, hKU, hGF, hG⟩ := surgery (V := Table) (k := 4) (by norm_num)
    (Qs := Qs) (fun j => finrank_ker_ellLin j.2)
    (fun i j h => ellLin_rank_two i.2 j.2 h) isOpen_Uo convex_Uo hF
  refine ⟨fun l => G (fromBary l), (hGc.comp (by unfold fromBary; fun_prop)).continuousOn,
    ?_, ?_⟩
  · intro l hl i hi u v huv
    have hnot : fromBary l ∉ K := by
      intro hmem
      have := hKU hmem i
      rw [toBary_fromBary hl.2, hi] at this
      exact lt_irrefl _ this
    simp only
    rw [hGF _ hnot, Fmap, ret_eq_self (by rw [toBary_fromBary hl.2]; exact hl.1),
      toBary_fromBary hl.2]
    exact compat_F0 q hl hi huv
  · intro l _ m hm
    by_contra hc
    push_neg at hc
    apply hG (fromBary l) ⟨m, hm⟩
    funext r
    show ell m (G (fromBary l)) r = 0
    simp only [ell]
    rw [hc r.castSucc, hc 5, sub_self]

end

end Tverberg6R
