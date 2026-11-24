module

public import AkopyanResearch.Completion.RelativeFaceDiagram
public import Mathlib.Topology.CompactOpen

/-!
# Relative comparison with a chosen target section

The extension input includes a prescribed boundary homotopy to a fixed,
face-natural target section. Both the table and this homotopy are extended.
There is no universal extension assumption on the target spaces. The final
safe table is conditional on the explicitly stated relative lifting property;
this module does not prove the needed arrangement-comparison connectivity.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.RelativeComparison

open RelativeFaceDiagram AkopyanQuadratic
open scoped BigOperators

abbrev Time := Set.Icc (0 : ℝ) 1

def timeZero : Time := ⟨0, by simp⟩
def timeOne : Time := ⟨1, by simp⟩

abbrev quadDiagram : Diagram where
  Space := QuadComplement
  topSpace _ := inferInstance
  lift := liftFaceCompl
  continuous_lift := continuous_liftFaceCompl
  lift_refl := liftFaceCompl_refl
  lift_comp := liftFaceCompl_comp

/-- Continuous paths carry their compact-open topology. -/
abbrev pathDiagram (P : Diagram) : Diagram where
  Space S := C(Time, P.Space S)
  topSpace _ := inferInstance
  lift hT hTS f := (⟨P.lift hT hTS, P.continuous_lift hT hTS⟩ :
    C(P.Space _, P.Space _)).comp f
  continuous_lift hT hTS := ContinuousMap.continuous_postcomp
    ⟨P.lift hT hTS, P.continuous_lift hT hTS⟩
  lift_refl S hS f := by
    ext t
    exact P.lift_refl S hS (f t)
  lift_comp hR hT hRT hTS f := by
    ext t
    exact P.lift_comp hR hT hRT hTS (f t)

structure Comparison (P : Diagram) where
  comp : ∀ (S : Finset (Fin 15)), S.Nonempty → C(QuadComplement S, P.Space S)
  natural : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hS : S.Nonempty)
    (hTS : T ⊆ S) (x : QuadComplement T),
    comp S hS (liftFaceCompl hT hTS x) = P.lift hT hTS (comp T hT x)

structure ChosenSection (P : Diagram) where
  value : ∀ (S : Finset (Fin 15)), S.Nonempty → C(FaceSimplex S, P.Space S)
  natural : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hS : S.Nonempty)
    (hTS : T ⊆ S) (z : FaceSimplex T),
    value S hS (faceIncl hTS z) = P.lift hT hTS (value T hT z)

/-- The actual relative lifting obligation. It is a hypothesis, not a
connectivity theorem. Curried continuous maps encode jointly continuous
homotopies, since `Time` is compact and locally compact. -/
structure RelativeLifting (P : Diagram) (C : Comparison P) (p : ChosenSection P) : Prop where
  extend : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty)
    (g : C(FaceBoundary S, QuadComplement S))
    (eta : C(FaceBoundary S, C(Time, P.Space S))),
    (∀ z, eta z timeZero = C.comp S hS (g z)) →
    (∀ z, eta z timeOne = p.value S hS z.1) →
    ∃ G : C(FaceSimplex S, QuadComplement S),
    ∃ H : C(FaceSimplex S, C(Time, P.Space S)),
      (∀ z : FaceBoundary S, G z.1 = g z) ∧
      (∀ z : FaceBoundary S, H z.1 = eta z) ∧
      (∀ z, H z timeZero = C.comp S hS (G z)) ∧
      (∀ z, H z timeOne = p.value S hS z)

/-- In particular, the homotopies in this interface are genuinely jointly continuous. -/
theorem continuous_homotopy_uncurry {P : Diagram} {S : Finset (Fin 15)}
    {X : Type*} [TopologicalSpace X] (H : C(X, C(Time, P.Space S))) :
    Continuous (fun z : X × Time => H z.1 z.2) :=
  ContinuousMap.continuous_uncurry_of_continuous H

structure TrackedSkeleton {P : Diagram} (C : Comparison P) (p : ChosenSection P) (k : ℕ) where
  table : Skeleton quadDiagram k
  eta : Skeleton (pathDiagram P) k
  start : ∀ S hS hk z, eta.table S hS hk z timeZero = C.comp S hS (table.table S hS hk z)
  finish : ∀ S hS hk z, eta.table S hS hk z timeOne = p.value S hS z

theorem boundary_start {P : Diagram} {C : Comparison P} {p : ChosenSection P} {k : ℕ}
    (sk : TrackedSkeleton C p k) (S : Finset (Fin 15)) (hS : S.Nonempty)
    (hc : S.card = k + 1) (hk : 1 ≤ k) (z : FaceBoundary S) :
    boundary sk.eta S hS hc hk z timeZero =
      C.comp S hS (boundary sk.table S hS hc hk z) := by
  dsimp only [boundary, pathDiagram, ContinuousMap.comp_apply]
  rw [sk.start]
  exact (C.natural _ hS _ _).symm

theorem boundary_finish {P : Diagram} {C : Comparison P} {p : ChosenSection P} {k : ℕ}
    (sk : TrackedSkeleton C p k) (S : Finset (Fin 15)) (hS : S.Nonempty)
    (hc : S.card = k + 1) (hk : 1 ≤ k) (z : FaceBoundary S) :
    boundary sk.eta S hS hc hk z timeOne = p.value S hS z.1 := by
  dsimp only [boundary, pathDiagram, ContinuousMap.comp_apply]
  rw [sk.finish]
  exact (p.natural _ hS _ _).symm

def singletonSkeleton (D : Diagram)
    (f : ∀ S : Finset (Fin 15), S.Nonempty → S.card ≤ 1 → C(FaceSimplex S, D.Space S)) :
    Skeleton D 1 where
  table S hS hk := f S hS hk
  continuous_table S hS hk := (f S hS hk).continuous
  compatible {T S} hT hS hkT hkS hTS z := by
    have heq : T = S := Finset.eq_of_subset_of_card_le hTS (by have := hT.card_pos; omega)
    subst heq
    rw [faceIncl_refl, D.lift_refl]

/-- The relative property itself supplies the zero-dimensional start, because
all singleton boundaries are empty. No initial tracked skeleton is assumed. -/
def base {P : Diagram} (C : Comparison P) (p : ChosenSection P)
    (L : RelativeLifting P C p) : TrackedSkeleton C p 1 := by
  have hex : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (_hk : S.card ≤ 1),
      ∃ G : C(FaceSimplex S, QuadComplement S),
      ∃ H : C(FaceSimplex S, C(Time, P.Space S)),
        (∀ z, H z timeZero = C.comp S hS (G z)) ∧
        (∀ z, H z timeOne = p.value S hS z) := by
    intro S hS hk
    let : IsEmpty (FaceBoundary S) := boundary_isEmpty_of_card_le_one S hk
    let g : C(FaceBoundary S, QuadComplement S) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
    let eta : C(FaceBoundary S, C(Time, P.Space S)) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
    obtain ⟨G, H, _, _, hstart, hfinish⟩ :=
      L.extend S hS g eta (fun z => isEmptyElim z) (fun z => isEmptyElim z)
    exact ⟨G, H, hstart, hfinish⟩
  choose G H hstart hfinish using hex
  exact ⟨singletonSkeleton quadDiagram G, singletonSkeleton (pathDiagram P) H,
    hstart, hfinish⟩

/-- Extend both the maps and their prescribed homotopies by one skeleton. -/
def step {P : Diagram} {C : Comparison P} {p : ChosenSection P}
    (L : RelativeLifting P C p) {k : ℕ} (hk : 1 ≤ k)
    (sk : TrackedSkeleton C p k) : TrackedSkeleton C p (k + 1) := by
  have hex : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hc : S.card = k + 1),
      ∃ G : C(FaceSimplex S, QuadComplement S),
      ∃ H : C(FaceSimplex S, C(Time, P.Space S)),
        (∀ z : FaceBoundary S, G z.1 = boundary sk.table S hS hc hk z) ∧
        (∀ z : FaceBoundary S, H z.1 = boundary sk.eta S hS hc hk z) ∧
        (∀ z, H z timeZero = C.comp S hS (G z)) ∧
        (∀ z, H z timeOne = p.value S hS z) := by
    intro S hS hc
    exact L.extend S hS
      ⟨boundary sk.table S hS hc hk, continuous_boundary sk.table S hS hc hk⟩
      ⟨boundary sk.eta S hS hc hk, continuous_boundary sk.eta S hS hc hk⟩
      (boundary_start sk S hS hc hk) (boundary_finish sk S hS hc hk)
  choose G H hG hH hstart hfinish using hex
  refine ⟨extendStep sk.table hk (fun S hS hc => G S hS hc)
      (fun S hS hc => (G S hS hc).continuous) hG,
    extendStep sk.eta hk (fun S hS hc => H S hS hc)
      (fun S hS hc => (H S hS hc).continuous) hH, ?_, ?_⟩
  · intro S hS hc z
    by_cases hle : S.card ≤ k
    · simpa only [extendStep, hle, ↓reduceDIte] using sk.start S hS hle z
    · simpa only [extendStep, hle, ↓reduceDIte] using hstart S hS (by omega) z
  · intro S hS hc z
    by_cases hle : S.card ≤ k
    · simpa only [extendStep, hle, ↓reduceDIte] using sk.finish S hS hle z
    · simpa only [extendStep, hle, ↓reduceDIte] using hfinish S hS (by omega) z

def iterate {P : Diagram} {C : Comparison P} {p : ChosenSection P}
    (L : RelativeLifting P C p) {k : ℕ} (hk : 1 ≤ k)
    (sk : TrackedSkeleton C p k) (n : ℕ) : TrackedSkeleton C p (k + n) := by
  induction n with
  | zero => exact sk
  | succ n ih => exact step L (k := k + n) (by omega) ih

def full {P : Diagram} (C : Comparison P) (p : ChosenSection P)
    (L : RelativeLifting P C p) : TrackedSkeleton C p 15 :=
  iterate L (by norm_num : 1 ≤ 1) (base C p L) 14

def toOriginalSkeleton {P : Diagram} {C : Comparison P} {p : ChosenSection P} {k : ℕ}
    (sk : TrackedSkeleton C p k) : CompatibleSkeletonTable k where
  table := sk.table.table
  continuous_table := sk.table.continuous_table
  compatible := sk.table.compatible

/-- A full compatible skeleton is already a safe compatible quadratic table.
This extraction uses no comparison or extension assumptions. -/
theorem exists_safe_table_of_skeleton (sk15 : CompatibleSkeletonTable 15) :
    ∃ H : MassSimplex → TableWords → Fin 2 → ℝ,
      Continuous H ∧
      (∀ z t, (fun w => H z w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6)) ∧
      (∀ z i, z.val i = 0 → ∀ t, IgnoresColor (fun w => H z w t) i) ∧
      (∀ z : MassSimplex, ∀ σ : MatchingColumns,
        ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) := by
  classical
  let U : Finset (Fin 15) := Finset.univ
  have hU : U.Nonempty := Finset.univ_nonempty
  have hU_card : U.card ≤ 15 := by simp [U]
  let toFaceU (z : MassSimplex) : FaceSimplex U :=
    ⟨z, fun i hi => (hi (Finset.mem_univ i)).elim⟩
  have htoFaceU_cont : Continuous toFaceU :=
    Continuous.subtype_mk continuous_id _
  let G_univ : MassSimplex → QuadComplement U :=
    fun z => sk15.table U hU hU_card (toFaceU z)
  have hG_univ_cont : Continuous G_univ :=
    (sk15.continuous_table U hU hU_card).comp htoFaceU_cont
  let H : MassSimplex → TableWords → Fin 2 → ℝ :=
    fun z => liftToFull U (G_univ z).1
  have hlift_linear : Continuous (liftToFull U) := by
    refine continuous_pi fun w => continuous_pi fun t => ?_
    have hproj : Continuous (fun Q : QuadSpace U => (Q t).1 (fun i : U => w i.1)) :=
      (continuous_apply (fun i : U => w i.1)).comp
        (continuous_subtype_val.comp (continuous_apply t))
    exact hproj
  have hH_cont : Continuous H :=
    hlift_linear.comp (continuous_subtype_val.comp hG_univ_cont)
  refine ⟨H, hH_cont, ?_, ?_, ?_⟩
  · intro z t
    exact liftToFull_mem_quadratic U (G_univ z).1 t
  · intro z i hzi t
    let T : Finset (Fin 15) := U.erase i
    have hT : T.Nonempty := by
      have : T.card = 14 := by simp [T, U]
      exact Finset.card_pos.mp (by omega)
    have hT_card : T.card ≤ 15 := by simp [T, U]
    have hTU : T ⊆ U := Finset.erase_subset i U
    let zT : FaceSimplex T :=
      ⟨z, fun j hjT => by
        by_cases hji : j = i
        · subst hji; exact hzi
        · exact (hjT (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)).elim⟩
    have hinc : faceIncl hTU zT = toFaceU z := by
      apply Subtype.ext; rfl
    have hcompat := sk15.compatible hT hU hT_card hU_card hTU zT
    rw [hinc] at hcompat
    have hG_eq : G_univ z = liftFaceCompl hT hTU (sk15.table T hT hT_card zT) := hcompat
    have hH_eq : H z = liftToFull T (sk15.table T hT hT_card zT).1 := by
      funext w s
      change ((G_univ z).1 s).1 (fun j : U => w j.1) = _
      rw [hG_eq]
      rfl
    rw [hH_eq]
    exact ignoresColor_liftToFull T (sk15.table T hT hT_card zT).1 (Finset.notMem_erase i U) t
  · intro z σ
    let f : Fin 6 → (U → Fin 6) := fun j => fun i : U => σ i.1 j
    let m : Finset (U → Fin 6) := Finset.univ.image f
    have hf_inj : Function.Injective f := by
      intro j₁ j₂ h
      exact (σ 0).injective (congrFun h ⟨0, Finset.mem_univ 0⟩)
    have hm : SixMatching m := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injective Finset.univ hf_inj, Finset.card_univ, Fintype.card_fin]
      · intro i u hu v hv huv
        obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hv
        have hj : j₁ = j₂ := (σ i.1).injective huv
        rw [hj]
      · intro i a
        exact ⟨f ((σ i.1).symm a), Finset.mem_image_of_mem f (Finset.mem_univ _),
          (σ i.1).apply_symm_apply a⟩
    have hnot_mem : (G_univ z).1 ∉ L_M U m := (G_univ z).2 m hm
    by_contra hno
    push Not at hno
    apply hnot_mem
    intro u hu v hv t
    obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hv
    have h1 : H z (fun i => σ i j₁) = H z (fun i => σ i 0) := hno j₁
    have h2 : H z (fun i => σ i j₂) = H z (fun i => σ i 0) := hno j₂
    exact congrFun (h1.trans h2.symm) t

/-- Corrected final reduction: the lifting property is explicit, and no
universal target-extension property is present. -/
theorem exists_safe_table_of_relative_lifting
    (P : Diagram) (C : Comparison P) (p : ChosenSection P)
    (L : RelativeLifting P C p) :
    ∃ H : MassSimplex → TableWords → Fin 2 → ℝ,
      Continuous H ∧
      (∀ z t, (fun w => H z w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6)) ∧
      (∀ z i, z.val i = 0 → ∀ t, IgnoresColor (fun w => H z w t) i) ∧
      (∀ z : MassSimplex, ∀ σ : MatchingColumns,
        ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) :=
  exists_safe_table_of_skeleton (toOriginalSkeleton (full C p L))

end AkopyanResearch.RelativeComparison
