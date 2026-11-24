module

public import AkopyanResearch.Completion.OriginalJoinCoordinates
public import AkopyanResearch.Completion.JoinVertexMap
public import AkopyanResearch.Completion.PairSphereAction

/-!
# The two actual row projections of the universal pair source

For a column state `(sigma,b)`, the first matching uses `sigma`, while the
second uses `sigma` followed by the residual transposition when `b` is true.
Both projections are continuous pushforwards of actual join coordinates.
Their covariance is verified against the original `PairGroup` action.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairSourceProjections

open PhaseExtension JoinVertexMap PairSphereAction OriginalJoinBridge

abbrev Source (k : ℕ) := Join (Fin (k + 1)) PairState
abbrev RowSource (k : ℕ) := OriginalJoinCoordinates.Source k

theorem swap45_castAdd (i : Fin 4) : swap45 (i.castAdd 2) = i.castAdd 2 := by
  fin_cases i <;> decide

theorem swap45_natAdd (j : Fin 2) :
    swap45 (Fin.natAdd 4 j) = Fin.natAdd 4 (Equiv.swap 0 1 j) := by
  fin_cases j <;> decide

theorem blockPerm_castAdd (g : Equiv.Perm (Fin 4)) (b : Bool) (i : Fin 4) :
    blockPerm g b (i.castAdd 2) = (g i).castAdd 2 := by
  cases b <;> simp [blockPerm, Equiv.Perm.mul_apply, swap45_castAdd, liftPerm4_castAdd]

theorem blockPerm_natAdd (g : Equiv.Perm (Fin 4)) (b : Bool) (j : Fin 2) :
    blockPerm g b (Fin.natAdd 4 j) =
      Fin.natAdd 4 (if b then Equiv.swap 0 1 j else j) := by
  cases b <;> simp [blockPerm, Equiv.Perm.mul_apply, swap45_natAdd, liftPerm4_natAdd]

theorem blockPerm_mul (g h : Equiv.Perm (Fin 4)) (b c : Bool) :
    blockPerm g b * blockPerm h c = blockPerm (g * h) (xor b c) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (m := 4) (n := 2) (fun j => ?_) (fun j => ?_) i
  · simp [Equiv.Perm.mul_apply, blockPerm_castAdd]
  · simp only [Equiv.Perm.mul_apply, blockPerm_natAdd]
    cases b <;> cases c <;> fin_cases j <;> rfl

theorem blockPerm_inv (g : Equiv.Perm (Fin 4)) (b : Bool) :
    (blockPerm g b)⁻¹ = blockPerm g⁻¹ b := by
  apply mul_left_cancel (a := blockPerm g b)
  rw [mul_inv_cancel, blockPerm_mul, mul_inv_cancel]
  cases b <;> simp [blockPerm, liftPerm4_one]

theorem blockPerm_mem (g : Equiv.Perm (Fin 4)) (b : Bool) :
    blockPerm g b ∈ blockSubgroup := by
  intro i
  refine Fin.addCases (m := 4) (n := 2) (fun j => ?_) (fun j => ?_) i
  · rw [blockPerm_castAdd]
    exact iff_of_true j.isLt (g j).isLt
  · rw [blockPerm_natAdd]
    change 4 + j.val < 4 ↔ 4 + (if b then Equiv.swap 0 1 j else j).val < 4
    omega

theorem colPerm4_eq_blockPerm (g : Equiv.Perm (Fin 4)) (d : D8) (b : Bool) :
    colPerm4 g d b = blockPerm g (if d.ex then xor d.sa b else d.sa) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (m := 4) (n := 2) (fun j => ?_) (fun j => ?_) i
  · rw [colPerm4_castAdd, blockPerm_castAdd]
  · rw [colPerm4_natAdd, blockPerm_natAdd]
    rcases d with ⟨sa, sb, ex⟩
    cases sa <;> cases ex <;> cases b <;> rfl

def firstVertex : PairState → RowGroup := Prod.fst

def secondVertex (w : PairState) : RowGroup := w.1 * blockPerm 1 w.2

def statePerm (h : PairGroup) : Equiv.Perm PairState where
  toFun w := h • w
  invFun w := h⁻¹ • w
  left_inv w := inv_smul_smul h w
  right_inv w := smul_inv_smul h w

def action (k : ℕ) (h : PairGroup) : Source k → Source k := relabel (statePerm h)

theorem continuous_action (k : ℕ) (h : PairGroup) : Continuous (action k h) :=
  continuous_relabel _

theorem action_one (k : ℕ) (x : Source k) : action k 1 x = x := by
  apply Subtype.ext
  funext i
  simp [action, relabel, statePerm]

theorem action_mul (k : ℕ) (h g : PairGroup) (x : Source k) :
    action k (h * g) x = action k h (action k g x) := by
  apply Subtype.ext
  funext i
  simp [action, relabel, statePerm, mul_inv_rev, mul_smul]

def firstProjection (k : ℕ) : Source k → RowSource k := mapVertices firstVertex
def secondProjection (k : ℕ) : Source k → RowSource k := mapVertices secondVertex

theorem continuous_firstProjection (k : ℕ) : Continuous (firstProjection k) :=
  continuous_mapVertices _

theorem continuous_secondProjection (k : ℕ) : Continuous (secondProjection k) :=
  continuous_mapVertices _

theorem firstVertex_action (h : PairGroup) (w : PairState) :
    firstVertex (statePerm h w) =
      if h.2.ex then secondVertex w * (blockPerm h.1 h.2.sb)⁻¹
      else firstVertex w * (blockPerm h.1 h.2.sa)⁻¹ := by
  rcases h with ⟨g, ⟨sa, sb, ex⟩⟩
  rcases w with ⟨sigma, b⟩
  cases sa <;> cases sb <;> cases ex <;> cases b <;>
    simp [firstVertex, secondVertex, statePerm, pairGroup_smul_pairState,
      actPairStateFun, d8_inv_def, colPerm4_eq_blockPerm, blockPerm_inv,
      mul_assoc, blockPerm_mul]

theorem secondVertex_action (h : PairGroup) (w : PairState) :
    secondVertex (statePerm h w) =
      if h.2.ex then firstVertex w * (blockPerm h.1 h.2.sa)⁻¹
      else secondVertex w * (blockPerm h.1 h.2.sb)⁻¹ := by
  rcases h with ⟨g, ⟨sa, sb, ex⟩⟩
  rcases w with ⟨sigma, b⟩
  cases sa <;> cases sb <;> cases ex <;> cases b <;>
    simp [firstVertex, secondVertex, statePerm, pairGroup_smul_pairState,
      actPairStateFun, d8_inv_def, colPerm4_eq_blockPerm, blockPerm_inv,
      mul_assoc, blockPerm_mul]

theorem firstProjection_action (k : ℕ) (h : PairGroup) (x : Source k) :
    firstProjection k (action k h x) =
      if h.2.ex then relabel (Equiv.mulRight (blockPerm h.1 h.2.sb)⁻¹) (secondProjection k x)
      else relabel (Equiv.mulRight (blockPerm h.1 h.2.sa)⁻¹) (firstProjection k x) := by
  cases he : h.2.ex
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold firstProjection action
    rw [mapVertices_relabel, ← mapVertices_perm, mapVertices_comp]
    congr 1
    funext w
    exact (firstVertex_action h w).trans (by simp [he])
  · simp only [↓reduceIte]
    unfold firstProjection secondProjection action
    rw [mapVertices_relabel, ← mapVertices_perm, mapVertices_comp]
    congr 1
    funext w
    exact (firstVertex_action h w).trans (by simp [he])

theorem secondProjection_action (k : ℕ) (h : PairGroup) (x : Source k) :
    secondProjection k (action k h x) =
      if h.2.ex then relabel (Equiv.mulRight (blockPerm h.1 h.2.sa)⁻¹) (firstProjection k x)
      else relabel (Equiv.mulRight (blockPerm h.1 h.2.sb)⁻¹) (secondProjection k x) := by
  cases he : h.2.ex
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold secondProjection action
    rw [mapVertices_relabel, ← mapVertices_perm, mapVertices_comp]
    congr 1
    funext w
    exact (secondVertex_action h w).trans (by simp [he])
  · simp only [↓reduceIte]
    unfold firstProjection secondProjection action
    rw [mapVertices_relabel, ← mapVertices_perm, mapVertices_comp]
    congr 1
    funext w
    exact (secondVertex_action h w).trans (by simp [he])

/-- In a pure phase, the second projection differs by one fixed block permutation. -/
theorem secondProjection_of_pure (k : ℕ) (b : Bool)
    (x : Pure (C := Fin (k + 1)) (Prod.snd : PairState → Bool) b) :
    secondProjection k x.val = relabel (Equiv.mulRight (blockPerm 1 b)) (firstProjection k x.val) := by
  unfold firstProjection secondProjection
  rw [← mapVertices_perm, mapVertices_comp]
  apply mapVertices_congr_of_support
  intro c w hw
  have hb : w.2 = b := by
    by_contra hn
    exact hw (x.property (c, w) hn)
  change w.1 * blockPerm 1 w.2 = w.1 * blockPerm 1 b
  rw [hb]

end AkopyanResearch.PairSourceProjections
