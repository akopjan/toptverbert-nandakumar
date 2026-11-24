module

public import AkopyanResearch.Completion.OriginalJoinBridge
public import AkopyanResearch.Completion.IteratedJoinCoordinates
public import AkopyanResearch.Completion.PurePhaseCoordinates
public import AkopyanResearch.Completion.JoinRowAction

/-!
# The original planar map in actual fifteen-color join coordinates

The quotient-join maps are transported through the proved coordinate
homeomorphisms. Coordinatewise inversion also supplies the right row
enumeration convention: changing every row permutation from `sigma` to
`sigma * tau` changes the output by `permSphere tau⁻¹`.

Both the map and its full `4 + 2` block-subgroup nullhomotopy are constructed
without topological hypotheses. The source is the finite colored join of
row permutations, not the simplex of masses and not a safe height table.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.OriginalJoinCoordinates

open EquivariantJoinStep OriginalJoinBridge

attribute [local instance] OriginalJoinBridge.rowTopology
  OriginalJoinBridge.rowDiscreteTopology OriginalJoinBridge.sphereAction
  OriginalJoinBridge.continuous_sphereAction

abbrev Source (k : ℕ) := PhaseExtension.Join (Fin (k + 1)) RowGroup

def coordinateHomeomorph (k : ℕ) : OriginalJoinBridge.Source k ≃ₜ Source k :=
  IteratedJoinCoordinates.finHomeomorph k

theorem coordinateHomeomorph_symm_equivariant (k : ℕ) (a : RowGroup) (x : Source k) :
    (coordinateHomeomorph k).symm (PhaseExtension.relabel (Equiv.mulLeft a) x) =
      a • (coordinateHomeomorph k).symm x := by
  apply (coordinateHomeomorph k).injective
  rw [Homeomorph.apply_symm_apply]
  change PhaseExtension.relabel (Equiv.mulLeft a) x =
    IteratedJoinCoordinates.finHomeomorph k
      (a • (IteratedJoinCoordinates.finHomeomorph k).symm x)
  rw [IteratedJoinCoordinates.finHomeomorph_equivariant, Homeomorph.apply_symm_apply]

def coordinateMap (k : ℕ) : Source k → Target :=
  OriginalJoinBridge.joinMap k ∘ (coordinateHomeomorph k).symm

def coordinateNullhomotopy (k : ℕ) : Source k × Time → Target :=
  fun p => OriginalJoinBridge.blockNullhomotopy k ((coordinateHomeomorph k).symm p.1, p.2)

theorem continuous_coordinateMap (k : ℕ) : Continuous (coordinateMap k) :=
  (OriginalJoinBridge.continuous_joinMap k).comp (coordinateHomeomorph k).symm.continuous

theorem coordinateMap_equivariant (k : ℕ) (a : RowGroup) (x : Source k) :
    coordinateMap k (PhaseExtension.relabel (Equiv.mulLeft a) x) =
      permSphere a (coordinateMap k x) := by
  simp only [coordinateMap, Function.comp_apply, coordinateHomeomorph_symm_equivariant,
    OriginalJoinBridge.joinMap_equivariant]

theorem continuous_coordinateNullhomotopy (k : ℕ) : Continuous (coordinateNullhomotopy k) :=
  (OriginalJoinBridge.continuous_blockNullhomotopy k).comp
    (((coordinateHomeomorph k).symm.continuous.comp continuous_fst).prodMk continuous_snd)

theorem coordinateNullhomotopy_start (k : ℕ) (x : Source k) :
    coordinateNullhomotopy k (x, timeZero) = coordinateMap k x :=
  OriginalJoinBridge.blockNullhomotopy_start k _

theorem coordinateNullhomotopy_finish (k : ℕ) (x : Source k) :
    coordinateNullhomotopy k (x, timeOne) = anchorS :=
  OriginalJoinBridge.blockNullhomotopy_finish k _

theorem coordinateNullhomotopy_equivariant (k : ℕ) (a : RowGroup)
    (ha : a ∈ blockSubgroup) (x : Source k) (s : Time) :
    coordinateNullhomotopy k (PhaseExtension.relabel (Equiv.mulLeft a) x, s) =
      permSphere a (coordinateNullhomotopy k (x, s)) := by
  simp only [coordinateNullhomotopy, coordinateHomeomorph_symm_equivariant]
  exact OriginalJoinBridge.blockNullhomotopy_equivariant k a ha _ s

/-- Inversion is applied to actual vertex-coordinate weights. -/
def invertRows (k : ℕ) : Source k → Source k :=
  PhaseExtension.relabel (Equiv.inv RowGroup)

theorem continuous_invertRows (k : ℕ) : Continuous (invertRows k) :=
  PhaseExtension.continuous_relabel _

theorem invertRows_right (k : ℕ) (a : RowGroup) (x : Source k) :
    invertRows k (PhaseExtension.relabel (Equiv.mulRight a⁻¹) x) =
      PhaseExtension.relabel (Equiv.mulLeft a) (invertRows k x) := by
  apply Subtype.ext
  funext i
  simp [invertRows, PhaseExtension.relabel, mul_inv_rev]

/-- The convention suitable for row-enumeration descent. -/
def rowMap (k : ℕ) : Source k → Target := coordinateMap k ∘ invertRows k

def rowNullhomotopy (k : ℕ) : Source k × Time → Target :=
  fun p => coordinateNullhomotopy k (invertRows k p.1, p.2)

theorem continuous_rowMap (k : ℕ) : Continuous (rowMap k) :=
  (continuous_coordinateMap k).comp (continuous_invertRows k)

theorem continuous_rowNullhomotopy (k : ℕ) : Continuous (rowNullhomotopy k) :=
  (continuous_coordinateNullhomotopy k).comp
    (((continuous_invertRows k).comp continuous_fst).prodMk continuous_snd)

theorem rowMap_right_equivariant (k : ℕ) (a : RowGroup) (x : Source k) :
    rowMap k (PhaseExtension.relabel (Equiv.mulRight a⁻¹) x) = permSphere a (rowMap k x) := by
  simp only [rowMap, Function.comp_apply, invertRows_right, coordinateMap_equivariant]

theorem rowMap_enumeration_change (k : ℕ) (tau : RowGroup) (x : Source k) :
    rowMap k (PhaseExtension.relabel (Equiv.mulRight tau) x) =
      permSphere tau⁻¹ (rowMap k x) := by
  simpa only [inv_inv] using rowMap_right_equivariant k tau⁻¹ x

theorem rowNullhomotopy_start (k : ℕ) (x : Source k) :
    rowNullhomotopy k (x, timeZero) = rowMap k x := coordinateNullhomotopy_start k _

theorem rowNullhomotopy_finish (k : ℕ) (x : Source k) :
    rowNullhomotopy k (x, timeOne) = anchorS := coordinateNullhomotopy_finish k _

theorem rowNullhomotopy_right_equivariant (k : ℕ) (a : RowGroup)
    (ha : a ∈ blockSubgroup) (x : Source k) (s : Time) :
    rowNullhomotopy k (PhaseExtension.relabel (Equiv.mulRight a⁻¹) x, s) =
      permSphere a (rowNullhomotopy k (x, s)) := by
  simp only [rowNullhomotopy, invertRows_right]
  exact coordinateNullhomotopy_equivariant k a ha _ s

/-- Restriction to either actual pure phase of the pair-state coordinate join. -/
def pureMap (k : ℕ) (b : Bool) :
    PurePhaseCoordinates.Pure (C := Fin (k + 1)) (G := RowGroup) b → Target :=
  rowMap k ∘ PurePhaseCoordinates.restrict b

def pureNullhomotopy (k : ℕ) (b : Bool) :
    PurePhaseCoordinates.Pure (C := Fin (k + 1)) (G := RowGroup) b × Time → Target :=
  fun p => rowNullhomotopy k (PurePhaseCoordinates.restrict b p.1, p.2)

theorem continuous_pureMap (k : ℕ) (b : Bool) : Continuous (pureMap k b) :=
  (continuous_rowMap k).comp (PurePhaseCoordinates.continuous_restrict b)

theorem continuous_pureNullhomotopy (k : ℕ) (b : Bool) : Continuous (pureNullhomotopy k b) :=
  (continuous_rowNullhomotopy k).comp
    (((PurePhaseCoordinates.continuous_restrict b).comp continuous_fst).prodMk continuous_snd)

theorem pureNullhomotopy_start (k : ℕ) (b : Bool)
    (x : PurePhaseCoordinates.Pure (C := Fin (k + 1)) (G := RowGroup) b) :
    pureNullhomotopy k b (x, timeZero) = pureMap k b x := rowNullhomotopy_start k _

theorem pureNullhomotopy_finish (k : ℕ) (b : Bool)
    (x : PurePhaseCoordinates.Pure (C := Fin (k + 1)) (G := RowGroup) b) :
    pureNullhomotopy k b (x, timeOne) = anchorS := rowNullhomotopy_finish k _

/-- The real fifteen-color source, with the right row convention and a full
block-subgroup nullhomotopy. No additional topological input is present. -/
theorem exists_fifteen_color_map_with_block_nullhomotopy :
    ∃ F : PhaseExtension.Join (Fin 15) RowGroup → Target,
    ∃ N : PhaseExtension.Join (Fin 15) RowGroup × Time → Target,
      Continuous F ∧
      (∀ a x, F (PhaseExtension.relabel (Equiv.mulRight a⁻¹) x) = permSphere a (F x)) ∧
      Continuous N ∧
      (∀ x, N (x, timeZero) = F x) ∧
      (∀ x, N (x, timeOne) = anchorS) ∧
      (∀ a : RowGroup, a ∈ blockSubgroup → ∀ x s,
        N (PhaseExtension.relabel (Equiv.mulRight a⁻¹) x, s) = permSphere a (N (x, s))) :=
  ⟨rowMap 14, rowNullhomotopy 14, continuous_rowMap 14, rowMap_right_equivariant 14,
    continuous_rowNullhomotopy 14, rowNullhomotopy_start 14, rowNullhomotopy_finish 14,
    rowNullhomotopy_right_equivariant 14⟩

end AkopyanResearch.OriginalJoinCoordinates
