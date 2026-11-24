module

public import AkopyanResearch.PairCollapseEquivariant

/-!
# The actual row action in the pair-collapse coordinates

This module identifies the block permutations of the original `Rep10` sphere
with the explicit `actY` from `PairCollapseEquivariant`. It also verifies that
the collapse is infinity on the diagonal and the residual-swap diagonal.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace AkopyanResearch.PairSphereAction

open scoped InnerProductSpace OnePoint

abbrev Sphere := Metric.sphere (0 : Rep10) 1

def swap45 : Equiv.Perm (Fin 6) := Equiv.swap 4 5

def blockPerm (g : Equiv.Perm (Fin 4)) (b : Bool) : Equiv.Perm (Fin 6) :=
  liftPerm4 g * if b then swap45 else 1

theorem permSub_mul (g h : Equiv.Perm (Fin 6)) (x : V10Sub) :
    permSub (g * h) x = permSub g (permSub h x) := by
  apply Subtype.ext
  ext i
  change x.1 ((perm12 (g * h)).symm i) =
    x.1 ((perm12 h).symm ((perm12 g).symm i))
  rw [perm12_mul]
  rfl

theorem permSub_one (x : V10Sub) : permSub 1 x = x := by
  apply Subtype.ext
  ext i
  change x.1 ((perm12 1).symm i) = x.1 i
  rw [perm12_one]
  rfl

private theorem lift_tail_left (g : Equiv.Perm (Fin 4)) (x : V10Sub) (j : Fin 2) :
    (permSub (liftPerm4 g) x).1 ((Fin.natAdd 4 j).castAdd 6) =
      x.1 ((Fin.natAdd 4 j).castAdd 6) := by
  change x.1 ((perm12 (liftPerm4 g)).symm ((Fin.natAdd 4 j).castAdd 6)) = _
  rw [perm12_symm, liftPerm4_inv, perm12_castAdd, liftPerm4_natAdd]

private theorem lift_tail_right (g : Equiv.Perm (Fin 4)) (x : V10Sub) (j : Fin 2) :
    (permSub (liftPerm4 g) x).1 (Fin.natAdd 6 (Fin.natAdd 4 j)) =
      x.1 (Fin.natAdd 6 (Fin.natAdd 4 j)) := by
  change x.1 ((perm12 (liftPerm4 g)).symm (Fin.natAdd 6 (Fin.natAdd 4 j))) = _
  rw [perm12_symm, liftPerm4_inv, perm12_natAdd, liftPerm4_natAdd]

theorem permSub_lift_mem_priv (g : Equiv.Perm (Fin 4)) (u : Priv4) :
    permSub (liftPerm4 g) u.1 ∈ Comm6SubV10ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  let w' : V10Sub := permSub (liftPerm4 g⁻¹) w
  have hw' : w' ∈ Comm6SubV10 := permSub_liftPerm4_mem_Comm6 g⁻¹ hw
  have htw : permSub (liftPerm4 g) w' = w := by
    dsimp [w']
    rw [← liftPerm4_inv]
    exact (permSub (liftPerm4 g)).right_inv w
  have hi := (permSub (liftPerm4 g)).inner_map_map w' u.1
  rw [htw] at hi
  rw [hi]
  have hu := u.2
  rw [Submodule.mem_orthogonal] at hu
  exact hu w' hw'

theorem permSub_lift_priv (g : Equiv.Perm (Fin 4)) (u : Priv4) :
    permSub (liftPerm4 g) u.1 = u.1 := by
  let v := permSub (liftPerm4 g) u.1 - u.1
  have hv : v ∈ Comm6SubV10 := by
    rw [mem_Comm6SubV10_iff]
    exact ⟨sub_eq_zero.mpr (lift_tail_left g u.1 0),
      sub_eq_zero.mpr (lift_tail_left g u.1 1),
      sub_eq_zero.mpr (lift_tail_right g u.1 0),
      sub_eq_zero.mpr (lift_tail_right g u.1 1)⟩
  have hvperp : v ∈ Comm6SubV10ᗮ :=
    Submodule.sub_mem _ (permSub_lift_mem_priv g u) u.2
  rw [Submodule.mem_orthogonal] at hvperp
  have hi : ⟪v, v⟫_ℝ = 0 := hvperp v hv
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hi)

theorem permSub_swap_comm (w : Comm6) : permSub swap45 w.1 = w.1 := by
  have hw := (mem_Comm6SubV10_iff w.1).mp w.2
  apply Subtype.ext
  ext i
  change w.1.1 ((perm12 (Equiv.swap 4 5)).symm i) = w.1.1 i
  rw [perm12_swap45_symm_apply]
  fin_cases i <;> simp [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]

theorem permSub_block_comm (g : Equiv.Perm (Fin 4)) (b : Bool) (w : Comm6) :
    permSub (blockPerm g b) w.1 = (actComm g w).1 := by
  cases b
  · simp only [blockPerm, Bool.false_eq_true, ↓reduceIte, mul_one]
    rfl
  · rw [blockPerm, ite_eq_left rfl, permSub_mul, permSub_swap_comm]
    rfl

theorem permSub_block_priv (g : Equiv.Perm (Fin 4)) (b : Bool) (u : Priv4) :
    permSub (blockPerm g b) u.1 = (privSign b u).1 := by
  cases b
  · simp only [blockPerm, Bool.false_eq_true, ↓reduceIte, mul_one, privSign_false]
    exact permSub_lift_priv g u
  · rw [blockPerm, ite_eq_left rfl, permSub_mul]
    change permSub (liftPerm4 g) (swapPriv u).1 = (swapPriv u).1
    exact permSub_lift_priv g (swapPriv u)

theorem splitRep10_symm_apply (p : WithLp 2 (Priv4 × Comm6)) :
    splitRep10.symm p = iso10 (p.snd.1 + p.fst.1) := rfl

theorem splitRep10_block (g : Equiv.Perm (Fin 4)) (b : Bool) (x : Rep10) :
    splitRep10 (perm10 (blockPerm g b) x) =
      WithLp.toLp 2 (privSign b (splitRep10 x).fst, actComm g (splitRep10 x).snd) := by
  apply splitRep10.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, splitRep10_symm_apply]
  have hx : x = iso10 ((splitRep10 x).snd.1 + (splitRep10 x).fst.1) := by
    rw [← splitRep10_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  conv_lhs => rw [hx]
  simp only [perm10, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, map_add,
    permSub_block_comm, permSub_block_priv]
  rfl

def pairAction (h : PairGroup) (p : Sphere × Sphere) : Sphere × Sphere :=
  if h.2.ex then
    (permSphere (blockPerm h.1 h.2.sb) p.2, permSphere (blockPerm h.1 h.2.sa) p.1)
  else
    (permSphere (blockPerm h.1 h.2.sa) p.1, permSphere (blockPerm h.1 h.2.sb) p.2)

theorem spherePairEquiv_equivariant (h : PairGroup) (p : Sphere × Sphere) :
    spherePairEquiv (pairAction h p) = actY h (spherePairEquiv p) := by
  cases he : h.2.ex
  · simp only [pairAction, actY, he, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg WithLp.ofLp (splitRep10_block h.1 h.2.sa p.1.1)
    · exact congrArg WithLp.ofLp (splitRep10_block h.1 h.2.sb p.2.1)
  · simp only [pairAction, actY, he, ↓reduceIte]
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg WithLp.ofLp (splitRep10_block h.1 h.2.sb p.2.1)
    · exact congrArg WithLp.ofLp (splitRep10_block h.1 h.2.sa p.1.1)

theorem collapse_diagonal (x : Sphere) :
    pairCollapseMap (spherePairEquiv (x, x)) = ∞ := by
  apply PairCollapse.collapse_eq_infty_of_common_nonnegative_multiples
    (U := Priv4) (V := Priv4) (W := Comm6)
    pairF norm_pairF _ (splitRep10 x.1).snd 1 1 (by norm_num) (by norm_num)
  · simp [spherePairEquiv]
  · simp [spherePairEquiv]

theorem splitRep10_swap45_common (x : Rep10) :
    (splitRep10 (perm10 swap45 x)).snd = (splitRep10 x).snd := by
  have hs := splitRep10_block (1 : Equiv.Perm (Fin 4)) true x
  simpa [blockPerm, liftPerm4_one, actComm_one] using congrArg WithLp.snd hs

theorem collapse_swap45 (x : Sphere) :
    pairCollapseMap (spherePairEquiv (x, permSphere swap45 x)) = ∞ := by
  apply PairCollapse.collapse_eq_infty_of_common_nonnegative_multiples
    (U := Priv4) (V := Priv4) (W := Comm6)
    pairF norm_pairF _ (splitRep10 x.1).snd 1 1 (by norm_num) (by norm_num)
  · simp [spherePairEquiv]
  · simpa [spherePairEquiv] using splitRep10_swap45_common x.1

end AkopyanResearch.PairSphereAction
