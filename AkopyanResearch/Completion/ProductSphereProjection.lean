module

public import Hatcher.Singular.Homology
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The reduced part of product-sphere homology

This file specifies the actual projection whose categorical kernel is used
in the Thom calculation. No vanishing or homology decomposition is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ProductSphereKernel

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

abbrev sphereProduct (Z : Type w) [TopologicalSpace Z] (r : ℕ) : TopCat.{w} :=
  TopCat.of (Z × (TopCat.sphere.{w} r : Type w))

abbrev homologyFunctor (R : C) (i : ℕ) : TopCat.{w} ⥤ C :=
  (singularHomologyFunctor C i).obj R

abbrev homology (R : C) (i : ℕ) (T : TopCat.{w}) : C :=
  (homologyFunctor R i).obj T

def projection (Z : Type w) [TopologicalSpace Z] (r : ℕ) :
    sphereProduct Z r ⟶ TopCat.of Z := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

def projectionMap (Z : Type w) [TopologicalSpace Z] (R : C) (r i : ℕ) :
    homology R i (sphereProduct Z r) ⟶ homology R i (TopCat.of Z) :=
  (homologyFunctor R i).map (projection Z r)

abbrev Kernel (Z : Type w) [TopologicalSpace Z] (R : C) (r i : ℕ) : C :=
  kernel (projectionMap Z R r i)

end AkopyanResearch.ProductSphereKernel
