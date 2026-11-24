module

public import AkopyanResearch.Completion.SphereSourceCover

/-!
# The sphere-source cover of a product with based path space

For the projection `X × S → S`, the total homotopy pullback is exactly
`X × PathSpace S`, while its common-base fiber is exactly `X × ΩS`.
The induced inclusion commutes with the literal projections to `X`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.LoopProductGeometry

open ContinuousMap

universe w
variable (X : Type w) [TopologicalSpace X]

def sourceMap (n : ℕ) : C(X × LoopSphereCover.Sphere.{w} n, LoopSphereCover.Sphere n) :=
  ⟨Prod.snd, continuous_snd⟩

abbrev Total (n : ℕ) :=
  SphereSourceCover.Total (sourceMap X n) (LoopSphereCover.basepoint n)

abbrev Base (n : ℕ) :=
  SphereSourceCover.BaseSpace (sourceMap X n) (LoopSphereCover.basepoint n)

def totalHomeomorph (n : ℕ) : Total X n ≃ₜ X × LoopSphereCover.Total n where
  toFun q := (q.val.1.1, q.val.2)
  invFun q := ⟨((q.1, Submission.ev₁ _ _ q.2), q.2), rfl⟩
  left_inv q := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    exact Prod.ext rfl q.property.symm
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def baseHomeomorph (n : ℕ) : Base X n ≃ₜ X × LoopSphereCover.Fibre n where
  toFun q := (q.val.1, ⟨q.val.2, q.property.symm⟩)
  invFun q := ⟨(q.1, q.2.val), q.2.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def totalEquiv (n : ℕ) : Total X n ≃ₕ X :=
  (totalHomeomorph X n).toHomotopyEquiv.trans
    (ProductHemisphereCover.projectionHomotopyEquiv X
      (Submission.PathSpace.const _ (LoopSphereCover.basepoint n)))

def projection (n : ℕ) : C(X × LoopSphereCover.Fibre.{w} n, X) :=
  ⟨Prod.fst, continuous_fst⟩

def constantLoop (n : ℕ) : LoopSphereCover.Fibre.{w} n :=
  ⟨Submission.PathSpace.const _ _, rfl⟩

def sectionMap (n : ℕ) : C(X, X × LoopSphereCover.Fibre.{w} n) :=
  ⟨fun x => (x, constantLoop n), continuous_id.prodMk continuous_const⟩

theorem section_projection (n : ℕ) :
    (projection X n).comp (sectionMap X n) = ContinuousMap.id X := rfl

theorem inclusion_projection (n : ℕ) :
    (totalEquiv X n).toFun.comp
        (SphereSourceCover.baseInclusion (sourceMap X n) (LoopSphereCover.basepoint n)) =
      (projection X n).comp ⟨baseHomeomorph X n, (baseHomeomorph X n).continuous⟩ := rfl

end AkopyanResearch.LoopProductGeometry
