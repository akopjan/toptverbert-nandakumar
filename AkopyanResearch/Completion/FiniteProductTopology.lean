module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Explicit finite-product coordinates -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.FiniteProductTopology

universe w v
variable (X : Type w) [TopologicalSpace X]

def finZero : (Fin 0 → X) ≃ₜ PUnit.{w + 1} where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

def finSucc (n : ℕ) : (Fin (n + 1) → X) ≃ₜ (Fin n → X) × X :=
  (Homeomorph.funSplitAt X (Fin.last n)).trans
    ((Homeomorph.prodCongr (Homeomorph.refl X)
      (Homeomorph.piCongrLeft (Y := fun _ => X) (finSuccAboveEquiv (Fin.last n))).symm).trans
      (Homeomorph.prodComm _ _))

@[simp] theorem finSucc_fst_apply (n : ℕ) (f : Fin (n + 1) → X) (i : Fin n) :
    (finSucc X n f).1 i = f i.castSucc := by
  change f ((Fin.last n).succAbove i) = f i.castSucc
  rw [Fin.succAbove_last]

@[simp] theorem finSucc_snd (n : ℕ) (f : Fin (n + 1) → X) :
    (finSucc X n f).2 = f (Fin.last n) := rfl

def reindex (ι : Type v) [Fintype ι] : (ι → X) ≃ₜ (Fin (Fintype.card ι) → X) :=
  Homeomorph.piCongrLeft (Y := fun _ => X) (Fintype.equivFin ι)

end AkopyanResearch.FiniteProductTopology
