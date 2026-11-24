module

public import AkopyanResearch.Completion.HomotopyPullback

/-!
# Trivialising a path-fibration pullback in a contractible source direction

The contraction acts only in one source factor. The remaining source may
be arbitrary. Restriction to any subspace of the contractible factor is
allowed, which keeps the northern trivialisation compatible with the
overlap in the sphere-cover argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.ContractibleSourcePullback

open ContinuousMap HomotopyPullback

universe w
variable {X Y A T : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace T]

def baseMap (f : C(X × A, Y)) (a : A) : C(X, Y) :=
  f.comp ⟨fun x => (x, a), continuous_id.prodMk continuous_const⟩

def restriction (f : C(X × A, Y)) (j : C(T, A)) : C(X × T, Y) :=
  f.comp ((ContinuousMap.id X).prodMap j)

def projected (g : C(X, Y)) (T : Type w) [TopologicalSpace T] : C(X × T, Y) :=
  g.comp ⟨Prod.fst, continuous_fst⟩

def contractionHomotopy (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (j : C(T, A)) :
    (projected (baseMap f a) T).Homotopy (restriction f j) where
  toFun z := f (z.2.1, c.curve (j z.2.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change f (z.1, c.curve (j z.2, 0)) = f (z.1, a)
    rw [c.curve_zero]
  map_one_left z := by
    change f (z.1, c.curve (j z.2, 1)) = f (z.1, j z.2)
    rw [c.curve_one]

def projectedHomeomorph (g : C(X, Y)) (y₀ : Y) (T : Type w) [TopologicalSpace T] :
    Space (projected g T) y₀ ≃ₜ Space g y₀ × T where
  toFun q := (⟨(q.val.1.1, q.val.2), q.property⟩, q.val.1.2)
  invFun q := ⟨((q.1.val.1, q.2), q.1.val.2), q.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def trivialisation (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (j : C(T, A)) (y₀ : Y) :
    Space (restriction f j) y₀ ≃ₕ Space (baseMap f a) y₀ × T :=
  (HomotopyPullback.homotopyEquiv y₀ (contractionHomotopy f a c j).symm).trans
    (projectedHomeomorph (baseMap f a) y₀ T).toHomotopyEquiv

def projection (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (j : C(T, A)) (y₀ : Y) :
    C(Space (restriction f j) y₀, Space (baseMap f a) y₀) :=
  (⟨Prod.fst, continuous_fst⟩ : C(Space (baseMap f a) y₀ × T, _)).comp
    (trivialisation f a c j y₀).toFun

@[simp]
theorem trivialisation_snd (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (j : C(T, A)) (y₀ : Y)
    (q : Space (restriction f j) y₀) :
    (trivialisation f a c j y₀ q).2 = q.val.1.2 := rfl

@[simp]
theorem projection_fst (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (j : C(T, A)) (y₀ : Y)
    (q : Space (restriction f j) y₀) :
    (projection f a c j y₀ q).val.1 = q.val.1.1 := rfl

def baseInclusion (f : C(X × A, Y)) (a : A) (y₀ : Y) :
    C(Space (baseMap f a) y₀, Space (restriction f (ContinuousMap.id A)) y₀) where
  toFun q := ⟨((q.val.1, a), q.val.2), q.property⟩
  continuous_toFun := by fun_prop

/-- The same append-constant self-equivalence occurs for every chart
contraction fixed at its common basepoint. -/
theorem projection_baseInclusion (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (y₀ : Y) :
    (projection f a c (ContinuousMap.id A) y₀).comp (baseInclusion f a y₀) =
      HomotopyPullback.map y₀ (ContinuousMap.Homotopy.refl (baseMap f a)) := by
  ext q
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  ext t
  change (HomotopyPullback.map y₀ (contractionHomotopy f a c (ContinuousMap.id A)).symm
      (baseInclusion f a y₀ q)).val.2.val t =
    (HomotopyPullback.map y₀ (ContinuousMap.Homotopy.refl (baseMap f a)) q).val.2.val t
  rw [HomotopyPullback.map_curve_apply, HomotopyPullback.map_curve_apply]
  apply Submission.fconcat_congr
  · intro s
    rfl
  · intro s
    change f (q.val.1, c.curve (a, unitInterval.symm s)) = f (q.val.1, a)
    rw [c.curve_base]

variable {T' : Type w} [TopologicalSpace T']

def restrictionMap (f : C(X × A, Y)) (j : C(T, A)) (k : C(T', T)) (y₀ : Y) :
    C(Space (restriction f (j.comp k)) y₀, Space (restriction f j) y₀) where
  toFun q := ⟨((q.val.1.1, k q.val.1.2), q.val.2), q.property⟩
  continuous_toFun := by fun_prop

/-- Restricting the northern chart does not change the fibre coordinate
of its trivialisation. -/
theorem projection_restriction (f : C(X × A, Y)) (a : A)
    (c : Submission.ContractionData A a) (j : C(T, A)) (k : C(T', T)) (y₀ : Y) :
    (projection f a c j y₀).comp (restrictionMap f j k y₀) =
      projection f a c (j.comp k) y₀ := by
  ext q
  apply Subtype.ext
  refine Prod.ext rfl ?_
  apply Subtype.ext
  ext t
  change (HomotopyPullback.map y₀ (contractionHomotopy f a c j).symm
      (restrictionMap f j k y₀ q)).val.2.val t =
    (HomotopyPullback.map y₀ (contractionHomotopy f a c (j.comp k)).symm q).val.2.val t
  rw [HomotopyPullback.map_curve_apply, HomotopyPullback.map_curve_apply]
  apply Submission.fconcat_congr <;> intro s <;> rfl

end AkopyanResearch.ContractibleSourcePullback
