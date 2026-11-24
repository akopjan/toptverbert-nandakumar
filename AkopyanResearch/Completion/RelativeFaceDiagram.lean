module

public import AkopyanResearch.QuadraticArrangement

/-!
# Finite gluing of maps on the actual simplex faces

A diagram supplies spaces and functorial continuous face lifts. No extension
property is imposed. Compatible maps on a finite skeleton give a continuous
boundary map, and specified extensions produce the next skeleton.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.RelativeFaceDiagram

open scoped BigOperators

structure Diagram where
  Space : Finset (Fin 15) → Type
  topSpace : ∀ S, TopologicalSpace (Space S)
  lift : ∀ {T S : Finset (Fin 15)}, T.Nonempty → T ⊆ S → Space T → Space S
  continuous_lift : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hTS : T ⊆ S),
    @Continuous _ _ (topSpace T) (topSpace S) (lift hT hTS)
  lift_refl : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (x : Space S),
    lift hS (Finset.Subset.refl S) x = x
  lift_comp : ∀ {R T S : Finset (Fin 15)} (hR : R.Nonempty) (hT : T.Nonempty)
    (hRT : R ⊆ T) (hTS : T ⊆ S) (x : Space R),
    lift hT hTS (lift hR hRT x) = lift hR (hRT.trans hTS) x

attribute [instance] Diagram.topSpace

structure Skeleton (D : Diagram) (k : ℕ) where
  table : ∀ (S : Finset (Fin 15)), S.Nonempty → S.card ≤ k →
    FaceSimplex S → D.Space S
  continuous_table : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hk : S.card ≤ k),
    Continuous (table S hS hk)
  compatible : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hS : S.Nonempty)
    (hkT : T.card ≤ k) (hkS : S.card ≤ k) (hTS : T ⊆ S) (z : FaceSimplex T),
    table S hS hkS (faceIncl hTS z) = D.lift hT hTS (table T hT hkT z)

def boundary {D : Diagram} {k : ℕ} (sk : Skeleton D k)
    (S : Finset (Fin 15)) (_hS : S.Nonempty) (hcard : S.card = k + 1)
    (hk_pos : 1 ≤ k) :
    FaceBoundary S → D.Space S :=
  fun z =>
    let i := z.2.choose
    have hiS : i ∈ S := z.2.choose_spec.1
    have hzi : z.1.1.val i = 0 := z.2.choose_spec.2
    have hTi : (S.erase i).Nonempty := by
      have hcard_erase : (S.erase i).card = k := by
        rw [Finset.card_erase_of_mem hiS, hcard]; omega
      exact Finset.card_pos.mp (by omega)
    have hkTi : (S.erase i).card ≤ k := by
      rw [Finset.card_erase_of_mem hiS, hcard]; omega
    D.lift hTi (Finset.erase_subset i S)
      (sk.table (S.erase i) hTi hkTi (projectToBoundaryFacet z.1 hzi))

lemma boundary_eq_of_zero {D : Diagram} {k : ℕ} (sk : Skeleton D k)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1) (hk_pos : 1 ≤ k)
    (z : FaceBoundary S) (j : Fin 15) (hjS : j ∈ S) (hzj : z.1.1.val j = 0)
    (hTj : (S.erase j).Nonempty) (hkTj : (S.erase j).card ≤ k) :
    boundary sk S hS hcard hk_pos z =
      D.lift hTj (Finset.erase_subset j S)
        (sk.table (S.erase j) hTj hkTj (projectToBoundaryFacet z.1 hzj)) := by
  let i := z.2.choose
  have hiS : i ∈ S := z.2.choose_spec.1
  have hzi : z.1.1.val i = 0 := z.2.choose_spec.2
  have hTi : (S.erase i).Nonempty := by
    have : (S.erase i).card = k := by rw [Finset.card_erase_of_mem hiS, hcard]; omega
    exact Finset.card_pos.mp (by omega)
  have hkTi : (S.erase i).card ≤ k := by
    rw [Finset.card_erase_of_mem hiS, hcard]; omega
  change D.lift hTi (Finset.erase_subset i S)
      (sk.table (S.erase i) hTi hkTi (projectToBoundaryFacet z.1 hzi)) = _
  by_cases hij : i = j
  · subst hij; rfl
  · let R := (S.erase i).erase j
    have hR : R.Nonempty := by
      by_contra hR_empty
      rw [Finset.not_nonempty_iff_eq_empty] at hR_empty
      have htot := faceSimplex_sum_eq_one z.1
      have hsum0 : ∑ m ∈ S, z.1.1.val m = 0 := by
        refine Finset.sum_eq_zero fun m hmS => ?_
        by_cases hmi : m = i
        · subst hmi; exact hzi
        · by_cases hmj : m = j
          · subst hmj; exact hzj
          · have hmR : m ∈ R :=
              Finset.mem_erase.mpr ⟨hmj, Finset.mem_erase.mpr ⟨hmi, hmS⟩⟩
            rw [hR_empty] at hmR
            exact (Finset.notMem_empty m hmR).elim
      linarith
    have hkR : R.card ≤ k :=
      (Finset.card_erase_le.trans (Finset.card_erase_of_mem hiS).le).trans (by omega)
    let zR : FaceSimplex R :=
      ⟨z.1.1, fun m hmR => by
        by_cases hmi : m = i
        · subst hmi; exact hzi
        · by_cases hmj : m = j
          · subst hmj; exact hzj
          · exact z.1.2 m (fun hmS =>
              hmR (Finset.mem_erase.mpr ⟨hmj, Finset.mem_erase.mpr ⟨hmi, hmS⟩⟩))⟩
    have hR_sub_i : R ⊆ S.erase i := Finset.erase_subset j (S.erase i)
    have hR_sub_j : R ⊆ S.erase j := by
      intro m hmR
      have hm1 := Finset.mem_erase.mp hmR
      have hm2 := Finset.mem_erase.mp hm1.2
      exact Finset.mem_erase.mpr ⟨hm1.1, hm2.2⟩
    have hzi_eq : projectToBoundaryFacet z.1 hzi = faceIncl hR_sub_i zR := by
      apply Subtype.ext; rfl
    have hzj_eq : projectToBoundaryFacet z.1 hzj = faceIncl hR_sub_j zR := by
      apply Subtype.ext; rfl
    rw [hzi_eq, hzj_eq, sk.compatible hR hTi hkR hkTi hR_sub_i zR,
      sk.compatible hR hTj hkR hkTj hR_sub_j zR, D.lift_comp, D.lift_comp]

lemma continuous_boundary {D : Diagram} {k : ℕ} (sk : Skeleton D k)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1) (hk_pos : 1 ≤ k) :
    Continuous (boundary sk S hS hcard hk_pos) := by
  let A : Fin 15 → Set (FaceBoundary S) := fun j =>
    if j ∈ S then {z : FaceBoundary S | z.1.1.val j = 0} else ∅
  have hA_closed : ∀ j ∈ (Finset.univ : Finset (Fin 15)), IsClosed (A j) := fun j _ => by
    dsimp [A]
    split_ifs with hjS
    · exact isClosed_eq
        ((continuous_apply j).comp (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_subtype_val)))
        continuous_const
    · exact isClosed_empty
  have hA_cover : (⋃ j ∈ (Finset.univ : Finset (Fin 15)), A j) = Set.univ := by
    ext z
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hjS, hzj⟩ := z.2
    refine ⟨j, ?_⟩
    simp [A, hjS, hzj]
  rw [← continuousOn_univ, ← hA_cover]
  refine continuousOn_biUnion_of_isClosed Finset.univ A _ hA_closed fun j _ => ?_
  dsimp [A]
  split_ifs with hjS
  · have hTj : (S.erase j).Nonempty := by
      have : (S.erase j).card = k := by rw [Finset.card_erase_of_mem hjS, hcard]; omega
      exact Finset.card_pos.mp (by omega)
    have hkTj : (S.erase j).card ≤ k := by
      rw [Finset.card_erase_of_mem hjS, hcard]; omega
    let E_j : {z : FaceBoundary S // z.1.1.val j = 0} → FaceSimplex (S.erase j) :=
      fun z => projectToBoundaryFacet z.1.1 z.2
    have hEj_cont : Continuous E_j := by
      have h1 : Continuous (fun z : {z : FaceBoundary S // z.1.1.val j = 0} => z.1) :=
        continuous_subtype_val
      have h2 : Continuous (fun z : FaceBoundary S => z.1) :=
        continuous_subtype_val
      have h3 : Continuous (fun z : FaceSimplex S => z.1) :=
        continuous_subtype_val
      exact Continuous.subtype_mk (h3.comp (h2.comp h1)) _
    let F_j : {z : FaceBoundary S // z.1.1.val j = 0} → D.Space S :=
      fun z => D.lift hTj (Finset.erase_subset j S)
        (sk.table (S.erase j) hTj hkTj (E_j z))
    have hFj_cont : Continuous F_j :=
      (D.continuous_lift hTj (Finset.erase_subset j S)).comp
        ((sk.continuous_table (S.erase j) hTj hkTj).comp hEj_cont)
    rw [continuousOn_iff_continuous_domRestrict]
    refine hFj_cont.congr fun z => ?_
    exact (boundary_eq_of_zero sk S hS hcard hk_pos z.1 j hjS z.2 hTj hkTj).symm
  · exact continuousOn_empty _

def extendStep {D : Diagram} {k : ℕ} (sk : Skeleton D k) (hk_pos : 1 ≤ k)
    (ext : ∀ (S : Finset (Fin 15)) (_hS : S.Nonempty) (_hcard : S.card = k + 1),
      FaceSimplex S → D.Space S)
    (hext_cont : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1),
      Continuous (ext S hS hcard))
    (hext_bdry : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1)
      (z : FaceBoundary S),
      ext S hS hcard z.1 = boundary sk S hS hcard hk_pos z) :
    Skeleton D (k + 1) where
  table S hS hkS :=
    if hle : S.card ≤ k then sk.table S hS hle
    else ext S hS (by omega)
  continuous_table S hS hkS := by
    split_ifs with hle
    · exact sk.continuous_table S hS hle
    · exact hext_cont S hS (by omega)
  compatible {T S} hT hS hkT hkS hTS z := by
    split_ifs with hleS hleT hleT
    · exact sk.compatible hT hS hleT hleS hTS z
    · exfalso
      have := Finset.card_le_card hTS
      omega
    · have hcardS : S.card = k + 1 := by omega
      have hne_diff : (S \ T).Nonempty := by
        apply Finset.nonempty_of_ne_empty
        intro hempty
        have hST : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hempty
        have := Finset.card_le_card hST
        omega
      let j := hne_diff.choose
      have hj_diff : j ∈ S \ T := hne_diff.choose_spec
      have hjS : j ∈ S := (Finset.mem_sdiff.mp hj_diff).1
      have hjT : j ∉ T := (Finset.mem_sdiff.mp hj_diff).2
      have hzj : (faceIncl hTS z).1.val j = 0 := z.2 j hjT
      let zB : FaceBoundary S := ⟨faceIncl hTS z, ⟨j, hjS, hzj⟩⟩
      have hTj : (S.erase j).Nonempty := by
        have : (S.erase j).card = k := by rw [Finset.card_erase_of_mem hjS, hcardS]; omega
        exact Finset.card_pos.mp (by omega)
      have hkTj : (S.erase j).card ≤ k := by
        rw [Finset.card_erase_of_mem hjS, hcardS]; omega
      have hT_sub_Tj : T ⊆ S.erase j := fun m hmT =>
        Finset.mem_erase.mpr ⟨fun hmj => hjT (hmj ▸ hmT), hTS hmT⟩
      have hproj_eq : projectToBoundaryFacet zB.1 hzj = faceIncl hT_sub_Tj z := by
        apply Subtype.ext; rfl
      change ext S hS hcardS zB.1 = D.lift hT hTS (sk.table T hT hleT z)
      rw [hext_bdry S hS hcardS zB,
        boundary_eq_of_zero sk S hS hcardS hk_pos zB j hjS hzj hTj hkTj,
        hproj_eq, sk.compatible hT hTj hleT hkTj hT_sub_Tj z, D.lift_comp]
    · have hcardT : T.card = k + 1 := by omega
      have hcardS : S.card = k + 1 := by omega
      have hTS_eq : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
      subst hTS_eq
      rw [faceIncl_refl, D.lift_refl]

theorem boundary_isEmpty_of_card_le_one (S : Finset (Fin 15)) (hk : S.card ≤ 1) :
    IsEmpty (FaceBoundary S) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨i, hi, hz⟩ := z.2
  have heq : ({i} : Finset (Fin 15)) = S :=
    Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hi) (by simpa using hk)
  have hs := faceSimplex_sum_eq_one z.1
  have hzero : ∑ j ∈ S, z.1.1.val j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ∈ ({i} : Finset (Fin 15)) := heq.symm ▸ hj
    have hji' : j = i := Finset.mem_singleton.mp hji
    simpa only [hji'] using hz
  linarith

end AkopyanResearch.RelativeFaceDiagram
