module

public import AkopyanResearch.Completion.PairSourceProjections

/-!
# An actual equivariant nullhomotopy of the original pair-collapse map

The two row projections are fed into the proved full-block nullhomotopy.
Their pair is transformed by the original sphere-pair homeomorphism and
the original collapse. This gives a continuous `PairGroup`-equivariant
path to infinity, constantly infinity on both pure phases.

This is pair-path data for a possible homotopy-fiber comparison target.
It does not assume or prove the global comparison/lifting theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.OriginalPairPath

open scoped OnePoint
open EquivariantJoinStep OriginalJoinBridge OriginalJoinCoordinates
  PairSourceProjections PairSphereAction

def pairedHomotopy (k : ℕ) : PairSourceProjections.Source k × Time → Sphere × Sphere :=
  fun p => (rowNullhomotopy k (firstProjection k p.1, p.2),
    rowNullhomotopy k (secondProjection k p.1, p.2))

theorem continuous_pairedHomotopy (k : ℕ) : Continuous (pairedHomotopy k) :=
  ((continuous_rowNullhomotopy k).comp
    (((continuous_firstProjection k).comp continuous_fst).prodMk continuous_snd)).prodMk
    ((continuous_rowNullhomotopy k).comp
      (((continuous_secondProjection k).comp continuous_fst).prodMk continuous_snd))

theorem pairedHomotopy_equivariant (k : ℕ) (h : PairGroup)
    (x : PairSourceProjections.Source k) (s : Time) :
    pairedHomotopy k (action k h x, s) = pairAction h (pairedHomotopy k (x, s)) := by
  unfold pairedHomotopy
  rw [firstProjection_action, secondProjection_action]
  cases he : h.2.ex
  · simp only [pairAction, he, Bool.false_eq_true, ↓reduceIte]
    exact Prod.ext
      (rowNullhomotopy_right_equivariant k _ (blockPerm_mem _ _) _ s)
      (rowNullhomotopy_right_equivariant k _ (blockPerm_mem _ _) _ s)
  · simp only [pairAction, he, ↓reduceIte]
    exact Prod.ext
      (rowNullhomotopy_right_equivariant k _ (blockPerm_mem _ _) _ s)
      (rowNullhomotopy_right_equivariant k _ (blockPerm_mem _ _) _ s)

/-- The original collapse applied to the two continuously varying single values. -/
def pairPath (k : ℕ) : PairSourceProjections.Source k × Time → OnePoint PairTarget :=
  fun p => pairCollapseMap (spherePairEquiv (pairedHomotopy k p))

theorem continuous_pairPath (k : ℕ) : Continuous (pairPath k) :=
  continuous_pairCollapseMap.comp (spherePairEquiv.continuous.comp (continuous_pairedHomotopy k))

theorem pairPath_equivariant (k : ℕ) (h : PairGroup)
    (x : PairSourceProjections.Source k) (s : Time) :
    pairPath k (action k h x, s) = actOnePoint h (pairPath k (x, s)) := by
  unfold pairPath
  rw [pairedHomotopy_equivariant, spherePairEquiv_equivariant, pairCollapseMap_equivariant]

theorem pairPath_start (k : ℕ) (x : PairSourceProjections.Source k) :
    pairPath k (x, timeZero) = pairCollapseMap (spherePairEquiv
      (rowMap k (firstProjection k x), rowMap k (secondProjection k x))) := by
  unfold pairPath pairedHomotopy
  rw [rowNullhomotopy_start, rowNullhomotopy_start]

theorem pairPath_finish (k : ℕ) (x : PairSourceProjections.Source k) :
    pairPath k (x, timeOne) = ∞ := by
  unfold pairPath pairedHomotopy
  rw [rowNullhomotopy_finish, rowNullhomotopy_finish]
  exact collapse_diagonal anchorS

theorem pairPath_pure (k : ℕ) (b : Bool)
    (x : PhaseExtension.Pure (C := Fin (k + 1)) (Prod.snd : PairState → Bool) b) (s : Time) :
    pairPath k (x.val, s) = ∞ := by
  have hsecond : rowNullhomotopy k (secondProjection k x.val, s) =
      permSphere (blockPerm 1 b) (rowNullhomotopy k (firstProjection k x.val, s)) := by
    rw [secondProjection_of_pure k b x]
    have hi : (blockPerm 1 b)⁻¹ = blockPerm 1 b := by rw [blockPerm_inv, inv_one]
    simpa only [hi] using
      rowNullhomotopy_right_equivariant k (blockPerm 1 b) (blockPerm_mem 1 b)
        (firstProjection k x.val) s
  unfold pairPath pairedHomotopy
  rw [hsecond]
  cases b
  · simp only [blockPerm, Bool.false_eq_true, ↓reduceIte, mul_one, liftPerm4_one, permSphere_one]
    exact collapse_diagonal _
  · simp only [blockPerm, ↓reduceIte, liftPerm4_one, one_mul]
    exact collapse_swap45 _

/-- All homotopy and equivariance properties use the original concrete maps. -/
theorem exists_equivariant_pair_collapse_nullhomotopy (k : ℕ) :
    ∃ P : PairSourceProjections.Source k × Time → OnePoint PairTarget,
      Continuous P ∧
      (∀ x, P (x, timeZero) = pairCollapseMap (spherePairEquiv
        (rowMap k (firstProjection k x), rowMap k (secondProjection k x)))) ∧
      (∀ x, P (x, timeOne) = ∞) ∧
      (∀ h x s, P (action k h x, s) = actOnePoint h (P (x, s))) ∧
      (∀ (b : Bool)
        (x : PhaseExtension.Pure (C := Fin (k + 1)) (Prod.snd : PairState → Bool) b) s,
        P (x.val, s) = ∞) :=
  ⟨pairPath k, continuous_pairPath k, pairPath_start k, pairPath_finish k,
    pairPath_equivariant k, pairPath_pure k⟩

end AkopyanResearch.OriginalPairPath
