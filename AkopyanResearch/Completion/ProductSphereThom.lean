module

public import AkopyanResearch.Completion.ProductSphereKernel
public import AkopyanResearch.Completion.ProductZeroSphereKernel

/-!
# The homology shift for the kernel of product-sphere projection

Iterating the actual Mayer--Vietoris connecting isomorphism and the actual
two-point base case computes the kernel of projection in every degree.
Below the sphere dimension the kernel vanishes. In and above that dimension
it is the ordinary homology of the base with the corresponding degree shift.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ProductSphereKernel

open CategoryTheory CategoryTheory.Limits

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (Z : Type w) [TopologicalSpace Z] (R : C)

/-- The reduced summand of product-sphere homology, with the exact degree
shift and without any connectedness hypothesis on the base. -/
def suspensionIso (r i : ℕ) :
    Kernel Z R r (r + i) ≅ homology R i (TopCat.of Z) := by
  induction r with
  | zero => simpa only [Nat.zero_add] using zeroSphereKernelIso Z R i
  | succ r ih =>
      rw [Nat.succ_add]
      exact (recurrenceIso Z R r (r + i)).trans ih

/-- The degree formulation used in relative Thom calculations. -/
def degreeShiftIso (r i : ℕ) (hri : r ≤ i) :
    Kernel Z R r i ≅ homology R (i - r) (TopCat.of Z) := by
  have h := suspensionIso Z R r (i - r)
  simpa only [Nat.add_sub_of_le hri] using h

theorem isZero_kernel_below (r i : ℕ) (hi : i < r) : IsZero (Kernel Z R r i) := by
  induction r generalizing i with
  | zero => omega
  | succ r ih =>
      cases i with
      | zero => exact isZero_kernel_zero Z R r
      | succ i =>
          exact (ih i (Nat.lt_of_succ_lt_succ hi)).of_iso (recurrenceIso Z R r i)

theorem isZero_kernel_of_homology (r i : ℕ)
    (h : IsZero (homology R i (TopCat.of Z))) : IsZero (Kernel Z R r (r + i)) :=
  h.of_iso (suspensionIso Z R r i)

/-- The two normal ranks required by the matching arrangement, stated as
their sphere dimensions nine and thirteen. -/
def codimTenKernelIso (i : ℕ) :
    Kernel Z R 9 (9 + i) ≅ homology R i (TopCat.of Z) := suspensionIso Z R 9 i

def codimFourteenKernelIso (i : ℕ) :
    Kernel Z R 13 (13 + i) ≅ homology R i (TopCat.of Z) := suspensionIso Z R 13 i

end AkopyanResearch.ProductSphereKernel
