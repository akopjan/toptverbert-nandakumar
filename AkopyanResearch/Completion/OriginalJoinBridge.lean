module

public import AkopyanResearch.PlanarTestJoin
public import AkopyanResearch.Completion.JoinNullIteration

/-!
# The original planar map on finite joins, with a full block-subgroup contraction

The self-map `AkopyanResearch.q0`, its actual nullhomotopy from
`PlanarTestJoin`, and the fixed anchor instantiate the generic join construction.
There are no topological existence hypotheses in the final theorems.

The subgroup consists of all permutations preserving the first four labels;
it is the full `4 + 2` block stabilizer. The sphere action and the discrete
row-group topology are named definitions used as local instances, so this
module does not install a competing global action on the original sphere.

This constructs the single-factor target maps and subgroup nullhomotopies.
It does not assert existence of a safe fifteen-color height table.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.OriginalJoinBridge

open EquivariantJoinStep EquivariantJoinIteration JoinNullhomotopy JoinNullIteration

abbrev RowGroup := Equiv.Perm (Fin 6)
abbrev Target := Metric.sphere (0 : Rep10) 1

/-- The finite row group carries its discrete topology. -/
@[instance_reducible] def rowTopology : TopologicalSpace RowGroup := ⊥
attribute [local instance] rowTopology

theorem rowDiscreteTopology : DiscreteTopology RowGroup := ⟨rfl⟩
attribute [local instance] rowDiscreteTopology

/-- The action is the actual action from `PlanarTestGlobal`. -/
@[instance_reducible] def sphereAction : MulAction RowGroup Target where
  smul := permSphere
  one_smul x := by
    apply Subtype.ext
    exact perm10_one x.1
  mul_smul a b x := by
    apply Subtype.ext
    exact perm10_mul a b x.1
attribute [local instance] sphereAction

theorem continuous_sphereAction : ContinuousSMul RowGroup Target := by
  refine ⟨continuous_prod_of_discrete_left.mpr ?_⟩
  intro a
  exact continuous_permSphere a
attribute [local instance] continuous_sphereAction

/-- The full subgroup preserving the partition `{0,1,2,3} | {4,5}`. -/
def blockSubgroup : Subgroup RowGroup where
  carrier := {a | ∀ i : Fin 6, i.val < 4 ↔ (a i).val < 4}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro a b ha hb i
    exact (hb i).trans (ha (b i))
  inv_mem' := by
    intro a ha i
    simpa using (ha (a⁻¹ i)).symm

theorem mem_blockSubgroup_iff (a : RowGroup) :
    a ∈ blockSubgroup ↔ ∀ i : Fin 6, i.val < 4 ↔ (a i).val < 4 := Iff.rfl

theorem anchor_fixed (a : RowGroup) (ha : a ∈ blockSubgroup) :
    permSphere a anchorS = anchorS :=
  permSphere_anchorS (fun i hi => (ha i).mp hi)

/-- The original, proved nullhomotopy supplies every field of the input data. -/
def originalSelfNullData : SelfNullData RowGroup Target where
  phi := q0
  h := nullHomotopy_q0
  c := anchorS
  continuous_phi := q0.continuous
  continuous_h := nullHomotopy_q0.continuous
  equivariant_phi := q0_equivariant
  start := nullHomotopy_q0_zero
  finish := nullHomotopy_q0_one

/-- `Source k` is the actual quotient join of `k + 1` copies of the row group. -/
abbrev Source (k : ℕ) := IteratedJoin RowGroup RowGroup k

def mapData (k : ℕ) : ExtensionData RowGroup (Source k) Target :=
  iteratedData (seedData originalSelfNullData) k

/-- The continuous equivariant map on the finite join. -/
def joinMap (k : ℕ) : Source k → Target := (mapData k).F

def blockNullData (k : ℕ) : NullData (mapData k) blockSubgroup :=
  iterateNull (seedData originalSelfNullData) blockSubgroup
    (seedNullData originalSelfNullData blockSubgroup anchorS anchor_fixed) k

/-- Its nullhomotopy is equivariant for every permutation of each block. -/
def blockNullhomotopy (k : ℕ) : Source k × Time → Target := (blockNullData k).N

theorem continuous_joinMap (k : ℕ) : Continuous (joinMap k) :=
  (mapData k).continuous_F

theorem joinMap_equivariant (k : ℕ) (a : RowGroup) (x : Source k) :
    joinMap k (a • x) = permSphere a (joinMap k x) :=
  (mapData k).equivariant_F a x

theorem continuous_blockNullhomotopy (k : ℕ) : Continuous (blockNullhomotopy k) :=
  (blockNullData k).continuous_N

theorem blockNullData_endpoint (k : ℕ) : (blockNullData k).c₀ = anchorS := by
  rw [blockNullData, iterated_seed_endpoint]
  exact Function.iterate_fixed q0_anchorS (k + 1)

theorem blockNullhomotopy_start (k : ℕ) (x : Source k) :
    blockNullhomotopy k (x, timeZero) = joinMap k x :=
  (blockNullData k).start x

theorem blockNullhomotopy_finish (k : ℕ) (x : Source k) :
    blockNullhomotopy k (x, timeOne) = anchorS :=
  ((blockNullData k).finish x).trans (blockNullData_endpoint k)

theorem blockNullhomotopy_equivariant (k : ℕ) (a : RowGroup)
    (ha : a ∈ blockSubgroup) (x : Source k) (s : Time) :
    blockNullhomotopy k (a • x, s) = permSphere a (blockNullhomotopy k (x, s)) :=
  (blockNullData k).equivariant a ha x s

/-- No self-map, filling, or subgroup contraction is assumed here. -/
theorem exists_finite_join_map_with_block_nullhomotopy (k : ℕ) :
    ∃ F : Source k → Target, ∃ N : Source k × Time → Target,
      Continuous F ∧
      (∀ (a : RowGroup) (x : Source k), F (a • x) = permSphere a (F x)) ∧
      Continuous N ∧
      (∀ x, N (x, timeZero) = F x) ∧
      (∀ x, N (x, timeOne) = anchorS) ∧
      (∀ a : RowGroup, a ∈ blockSubgroup → ∀ (x : Source k) (s : Time),
        N (a • x, s) = permSphere a (N (x, s))) :=
  ⟨joinMap k, blockNullhomotopy k, continuous_joinMap k, joinMap_equivariant k,
    continuous_blockNullhomotopy k, blockNullhomotopy_start k,
    blockNullhomotopy_finish k, blockNullhomotopy_equivariant k⟩

/-- The fifteen-fold source needed by the planar comparison program. -/
theorem exists_fifteen_join_map_with_block_nullhomotopy :
    ∃ F : Source 14 → Target, ∃ N : Source 14 × Time → Target,
      Continuous F ∧
      (∀ (a : RowGroup) (x : Source 14), F (a • x) = permSphere a (F x)) ∧
      Continuous N ∧
      (∀ x, N (x, timeZero) = F x) ∧
      (∀ x, N (x, timeOne) = anchorS) ∧
      (∀ a : RowGroup, a ∈ blockSubgroup → ∀ (x : Source 14) (s : Time),
        N (a • x, s) = permSphere a (N (x, s))) :=
  exists_finite_join_map_with_block_nullhomotopy 14

end AkopyanResearch.OriginalJoinBridge
