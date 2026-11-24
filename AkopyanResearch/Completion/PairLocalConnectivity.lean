module

public import AkopyanResearch.Completion.PairConcreteLocalModel
public import AkopyanResearch.Completion.ArrangementConnectivity

/-!
# Eight-connectivity of the actual local pair models

The two forbidden coordinate subspaces in the fourteen-dimensional normal
representation both have codimension ten. Finite linear general position
therefore kills the actual homotopy groups through degree eight. The proved
normalization homotopy equivalence transfers this statement to the original
closed pair locus.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.PairLocalConnectivity

open Module PairConcreteLocalModel
open scoped ContinuousMap Topology Topology.Homotopy

def firstProjection : RawNormal →ₗ[ℝ] Comm6 × Priv4 where
  toFun x := (x.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondProjection : RawNormal →ₗ[ℝ] Comm6 × Priv4 where
  toFun x := (x.1, x.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstProjection_surjective : Function.Surjective firstProjection :=
  fun x => ⟨(x.1, x.2, 0), rfl⟩

theorem secondProjection_surjective : Function.Surjective secondProjection :=
  fun x => ⟨(x.1, 0, x.2), rfl⟩

def kernels : Bool → Submodule ℝ RawNormal
  | false => firstProjection.ker
  | true => secondProjection.ker

theorem codim_kernels (i : Bool) : finrank ℝ (RawNormal ⧸ kernels i) = 10 := by
  have hd : finrank ℝ (Comm6 × Priv4) = 10 := by
    rw [Module.finrank_prod, finrank_Comm6, finrank_Priv4]
  cases i
  · exact (firstProjection.quotKerEquivOfSurjective firstProjection_surjective).finrank_eq.trans hd
  · exact (secondProjection.quotKerEquivOfSurjective secondProjection_surjective).finrank_eq.trans hd

theorem safe_iff_avoids (x : RawNormal) :
    PairDeformation.Safe x ↔ ∀ i, x ∉ kernels i := by
  change ((x.1 ≠ 0 ∨ x.2.1 ≠ 0) ∧ (x.1 ≠ 0 ∨ x.2.2 ≠ 0)) ↔ _
  simp only [Bool.forall_bool, kernels, LinearMap.mem_ker, firstProjection,
    secondProjection, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero, not_and_or]

def normalArrangementHomeomorph :
    Normal ≃ₜ ArrangementConnectivity.Complement kernels :=
  (Homeomorph.refl RawNormal).subtype safe_iff_avoids

theorem pathConnectedSpace_normal : PathConnectedSpace Normal := by
  let : PathConnectedSpace (ArrangementConnectivity.Complement kernels) :=
    ArrangementConnectivity.pathConnectedSpace_complement kernels (by
      intro i
      have hq := (kernels i).finrank_quotient_add_finrank
      have hc := codim_kernels i
      omega)
  exact normalArrangementHomeomorph.symm.surjective.pathConnectedSpace
    normalArrangementHomeomorph.symm.continuous

/-- Path connectedness is invariant under an ordinary, freely based homotopy
equivalence; both endpoint paths are retained explicitly. -/
theorem pathConnectedSpace_of_homotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (e : X ≃ₕ Y) : PathConnectedSpace Y := by
  obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := X)
  obtain ⟨h⟩ := e.right_inv
  refine ⟨⟨e x₀⟩, fun y z => ?_⟩
  have hy : Joined y (e (e.invFun y)) := ⟨(h.evalAt y).symm⟩
  have hm : Joined (e (e.invFun y)) (e (e.invFun z)) :=
    (PathConnectedSpace.joined (e.invFun y) (e.invFun z)).map e.toFun.continuous
  exact hy.trans (hm.trans ⟨h.evalAt z⟩)

theorem pathConnectedSpace_collapsed : PathConnectedSpace Collapsed := by
  let := pathConnectedSpace_normal
  exact pathConnectedSpace_of_homotopyEquiv
    (PairLocalEquivalence.normalizationHomotopyEquiv (U := Priv4) (V := Priv4) (W := Comm6))

theorem subsingleton_homotopyGroup_normal (n : ℕ) (hn : n ≤ 8) (b : Normal) :
    Subsingleton (HomotopyGroup.Pi n Normal b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · let := pathConnectedSpace_normal
    exact (HomotopyGroup.pi0EquivZerothHomotopy (x := b)).subsingleton
  · let : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    have htriv : Subsingleton (HomotopyGroup.Pi n (ArrangementConnectivity.Complement kernels)
        (normalArrangementHomeomorph b)) :=
      ArrangementConnectivity.subsingleton_homotopyGroup_of_codim kernels n (by
        intro i
        rw [codim_kernels]
        omega) _
    obtain ⟨e⟩ := Submission.nonempty_mulEquiv_of_homotopyEquiv'
      (N := Fin n) normalArrangementHomeomorph.toHomotopyEquiv b
    exact ⟨fun a c => e.injective (htriv.elim _ _)⟩

/-- The actual closed chart complement is eight-connected, stated using
Mathlib's homotopy groups in all degrees zero through eight. -/
theorem subsingleton_homotopyGroup_collapsed (n : ℕ) (hn : n ≤ 8) (b : Collapsed) :
    Subsingleton (HomotopyGroup.Pi n Collapsed b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · let := pathConnectedSpace_collapsed
    exact (HomotopyGroup.pi0EquivZerothHomotopy (x := b)).subsingleton
  · let : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    let e := PairLocalEquivalence.normalizationHomotopyEquiv
      (U := Priv4) (V := Priv4) (W := Comm6)
    let : Subsingleton (HomotopyGroup.Pi n Normal (e.symm b)) :=
      subsingleton_homotopyGroup_normal n hn _
    obtain ⟨eπ⟩ := Submission.nonempty_mulEquiv_of_homotopyEquiv' (N := Fin n) e.symm b
    exact eπ.toEquiv.subsingleton

end AkopyanResearch.PairLocalConnectivity
