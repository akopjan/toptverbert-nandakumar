module

public import AkopyanResearch.Completion.ProductSphereProjection
public import AkopyanResearch.Completion.ProductHemisphereCover
public import Hatcher.Sphere.RadialDeformationRetract
public import Hatcher.Singular.Relative
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Relative normal-pair homology and the product-sphere projection kernel

The connecting map in the actual singular-homology sequence of a pair
identifies relative homology with an inclusion kernel whenever the preceding
inclusion map is onto. We apply this to the product of a base with a punctured
normal ball, keeping the projections and their homotopies explicit.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.ProductNormalPairKernel

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open ProductSphereKernel
open scoped Topology ContinuousMap

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The connecting morphism in the actual pair sequence lands in the
kernel of the actual inclusion. -/
theorem pairConnecting_comp_inclusion (P : TopPair.{w}) (R : C) (i : ℕ) :
    Hatcher.Relative.pairConnecting P R (i + 1) i rfl ≫
      (homologyFunctor R i).map P.map = 0 :=
  (Hatcher.Relative.pairSequence_exact P R (i + 1) i rfl).toIsComplex.zero 2

/-- Surjectivity of the preceding inclusion makes the connecting map
injective. This is deduced from the genuine pair long exact sequence. -/
theorem mono_pairConnecting_of_epi (P : TopPair.{w}) (R : C) (i : ℕ)
    (hepi : Epi ((homologyFunctor R (i + 1)).map P.map)) :
    Mono (Hatcher.Relative.pairConnecting P R (i + 1) i rfl) := by
  let hs := Hatcher.Relative.pairSequence_exact P R (i + 1) i rfl
  let T : ShortComplex C := hs.sc 0
  have : Epi T.f := hepi
  have hz : T.g = 0 := zero_of_epi_comp T.f T.zero
  exact (hs.exact 1).mono_g hz

def pairBoundaryShortComplex (P : TopPair.{w}) (R : C) (i : ℕ) : ShortComplex C :=
  ShortComplex.mk (Hatcher.Relative.pairConnecting P R (i + 1) i rfl)
    ((homologyFunctor R i).map P.map) (pairConnecting_comp_inclusion P R i)

theorem pairBoundaryShortComplex_exact (P : TopPair.{w}) (R : C) (i : ℕ) :
    (pairBoundaryShortComplex P R i).Exact :=
  (Hatcher.Relative.pairSequence_exact P R (i + 1) i rfl).exact 2

/-- Relative homology is the actual inclusion kernel when the preceding
inclusion is onto. The forward map is induced by the pair boundary. -/
def pairBoundaryKernelIso (P : TopPair.{w}) (R : C) (i : ℕ)
    (hepi : Epi ((homologyFunctor R (i + 1)).map P.map)) :
    (Hatcher.Relative.homologyFunctor R (i + 1)).obj P ≅
      kernel ((homologyFunctor R i).map P.map) := by
  have := mono_pairConnecting_of_epi P R i hepi
  have : Epi (kernel.lift ((homologyFunctor R i).map P.map)
      (Hatcher.Relative.pairConnecting P R (i + 1) i rfl)
      (pairConnecting_comp_inclusion P R i)) :=
    (pairBoundaryShortComplex_exact P R i).epi_kernelLift
  have : IsIso (kernel.lift ((homologyFunctor R i).map P.map)
      (Hatcher.Relative.pairConnecting P R (i + 1) i rfl)
      (pairConnecting_comp_inclusion P R i)) := isIso_of_mono_of_epi _
  exact asIso (kernel.lift ((homologyFunctor R i).map P.map)
    (Hatcher.Relative.pairConnecting P R (i + 1) i rfl)
    (pairConnecting_comp_inclusion P R i))

@[reassoc (attr := simp)]
theorem pairBoundaryKernelIso_hom_comp_ι (P : TopPair.{w}) (R : C) (i : ℕ)
    (hepi : Epi ((homologyFunctor R (i + 1)).map P.map)) :
    (pairBoundaryKernelIso P R i hepi).hom ≫ kernel.ι ((homologyFunctor R i).map P.map) =
      Hatcher.Relative.pairConnecting P R (i + 1) i rfl := by
  simp [pairBoundaryKernelIso]

/-- A section over a homology equivalence makes the inclusion onto in
every degree. The section is a map into the actual subspace. -/
theorem epi_inclusion_of_section (P : TopPair.{w}) {B : TopCat.{w}}
    (p : P.fst ⟶ B) (s : B ⟶ P.snd) (hs : s ≫ P.map ≫ p = 𝟙 B)
    (R : C) (i : ℕ) [IsIso ((homologyFunctor R i).map p)] :
    Epi ((homologyFunctor R i).map P.map) := by
  let F := homologyFunctor R i
  have h : (F.map p ≫ F.map s) ≫ F.map P.map = 𝟙 _ := by
    apply (cancel_mono (F.map p)).1
    simp only [Category.assoc, Category.id_comp]
    rw [← F.map_comp, ← F.map_comp, hs, F.map_id, Category.comp_id]
  exact epi_of_epi_fac h

/-- The zero-degree endpoint of the same relative calculation. -/
theorem isZero_relative_zero_of_epi_inclusion (P : TopPair.{w}) (R : C)
    (hepi : Epi ((homologyFunctor R 0).map P.map)) :
    IsZero ((Hatcher.Relative.homologyFunctor R 0).obj P) := by
  let Q := Hatcher.Relative.singularPairFunctor.obj P
  have hz : Q.homologyπ R 0 = 0 :=
    zero_of_epi_comp ((homologyFunctor R 0).map P.map)
      (Q.homologyMap_hom_homologyπ R 0)
  exact IsZero.of_epi_eq_zero (Q.homologyπ R 0) hz

section NormalGeometry

variable (Z : Type w) [TopologicalSpace Z]
variable (E : Type w) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev NormalBall := Metric.ball (0 : E) 1
abbrev PuncturedBall := {x : NormalBall E // x.val ≠ 0}

/-- The actual product normal pair, with the zero section removed. -/
abbrev normalBallPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (Z × NormalBall E)) {p | p.2.val ≠ 0}

omit [FiniteDimensional ℝ E] in
theorem unitBall_eq_zero_iff (x : E) :
    (Homeomorph.unitBall x : E) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply (Homeomorph.unitBall : E ≃ₜ NormalBall E).injective
    apply Subtype.ext
    simpa only [Homeomorph.coe_unitBall_apply_zero] using hx
  · rintro rfl
    exact Homeomorph.coe_unitBall_apply_zero

/-- Radial compression identifies the punctured unit ball with the
punctured vector space, and preserves the deleted zero section exactly. -/
def puncturedBallHomeomorph : PuncturedBall E ≃ₜ ({0}ᶜ : Set E) :=
  ((Homeomorph.unitBall : E ≃ₜ NormalBall E).subtype (fun x => by
    change x ≠ 0 ↔ (Homeomorph.unitBall x : E) ≠ 0
    exact not_congr (unitBall_eq_zero_iff E x).symm)).symm

def puncturedProductHomeomorph :
    (normalBallPair Z E).snd ≃ₜ Z × ({0}ᶜ : Set E) :=
  (show (normalBallPair Z E).snd ≃ₜ Z × PuncturedBall E from {
    toFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
    invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }).trans
      ((Homeomorph.refl Z).prodCongr (puncturedBallHomeomorph E))

/-- Coordinates from an orthonormal basis identify a normal unit sphere
with Mathlib's universe-lifted sphere of the specified dimension. -/
def normalSphereHomeomorph (r : ℕ) (h : Module.finrank ℝ E = r + 1) :
    Metric.sphere (0 : E) 1 ≃ₜ (TopCat.sphere.{w} r : Type w) := by
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + 1)) := by
    rw [← h]
    exact (stdOrthonormalBasis ℝ E).repr
  exact (e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph, e.norm_map])).trans
      Homeomorph.ulift.symm

/-- The ambient normal-ball projection is the forward map of this
homotopy equivalence. -/
def ambientProjectionEquiv : (normalBallPair Z E).fst ≃ₕ Z := by
  let : ContractibleSpace (NormalBall E) := Metric.contractibleSpace_ball (by norm_num)
  exact ProductHemisphereCover.projectionHomotopyEquiv Z ⟨0, by simp⟩

/-- The punctured normal-ball product retracts to the product with the
actual standard sphere. -/
def puncturedSphereEquiv [Nontrivial E] (r : ℕ) (h : Module.finrank ℝ E = r + 1) :
    (normalBallPair Z E).snd ≃ₕ (sphereProduct Z r : Type w) :=
  (puncturedProductHomeomorph Z E).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl Z).prodCongr
      ((Hatcher.Sphere.spherePuncturedStrongDeformationRetract
        (E := E) 1 (by norm_num)).toHomotopyEquiv.trans
          (normalSphereHomeomorph E r h).toHomotopyEquiv))

omit [FiniteDimensional ℝ E] in
@[simp]
theorem ambientProjectionEquiv_apply (x : (normalBallPair Z E).fst) :
    ambientProjectionEquiv Z E x = x.1 := rfl

@[simp]
theorem puncturedSphereEquiv_fst [Nontrivial E] (r : ℕ)
    (h : Module.finrank ℝ E = r + 1) (x : (normalBallPair Z E).snd) :
    (puncturedSphereEquiv Z E r h x).1 = x.val.1 := rfl

def ambientProjection : (normalBallPair Z E).fst ⟶ TopCat.of Z :=
  TopCat.ofHom (ambientProjectionEquiv Z E).toFun

def puncturedToSphere [Nontrivial E] (r : ℕ) (h : Module.finrank ℝ E = r + 1) :
    (normalBallPair Z E).snd ⟶ sphereProduct Z r :=
  TopCat.ofHom (puncturedSphereEquiv Z E r h).toFun

theorem puncturedToSphere_comp_projection [Nontrivial E] (r : ℕ)
    (h : Module.finrank ℝ E = r + 1) :
    puncturedToSphere Z E r h ≫ projection Z r =
      (normalBallPair Z E).map ≫ ambientProjection Z E := rfl

def ambientHomologyIso (R : C) (i : ℕ) :
    homology R i (normalBallPair Z E).fst ≅ homology R i (TopCat.of Z) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (ambientProjectionEquiv Z E) R i

def puncturedHomologyIso [Nontrivial E] (r : ℕ) (h : Module.finrank ℝ E = r + 1)
    (R : C) (i : ℕ) :
    homology R i (normalBallPair Z E).snd ≅ homology R i (sphereProduct Z r) :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv (puncturedSphereEquiv Z E r h) R i

theorem inclusion_comp_ambientHomologyIso [Nontrivial E] (r : ℕ)
    (h : Module.finrank ℝ E = r + 1) (R : C) (i : ℕ) :
    (homologyFunctor R i).map (normalBallPair Z E).map ≫
      (ambientHomologyIso Z E R i).hom =
    (puncturedHomologyIso Z E r h R i).hom ≫ projectionMap Z R r i := by
  change (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _ =
    (homologyFunctor R i).map _ ≫ (homologyFunctor R i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- A fixed nonzero normal vector gives a section into the punctured
ball over every point of the base. -/
def puncturedBallPoint [Nontrivial E] : PuncturedBall E := by
  let x : E := Classical.choose (exists_ne (0 : E))
  have hx : x ≠ 0 := Classical.choose_spec (exists_ne (0 : E))
  exact ⟨Homeomorph.unitBall x, fun h => hx ((unitBall_eq_zero_iff E x).mp h)⟩

def normalSection [Nontrivial E] : TopCat.of Z ⟶ (normalBallPair Z E).snd :=
  TopCat.ofHom ⟨fun z => ⟨(z, (puncturedBallPoint E).val),
    (puncturedBallPoint E).property⟩, by fun_prop⟩

omit [FiniteDimensional ℝ E] in
theorem normalSection_comp_projection [Nontrivial E] :
    normalSection Z E ≫ (normalBallPair Z E).map ≫ ambientProjection Z E =
      𝟙 (TopCat.of Z) := rfl

omit [FiniteDimensional ℝ E] in
/-- The inclusion of the actual punctured normal-ball product is onto on
homology in every degree. -/
theorem normalInclusion_epi [Nontrivial E] (R : C) (i : ℕ) :
    Epi ((homologyFunctor R i).map (normalBallPair Z E).map) := by
  have : IsIso ((homologyFunctor R i).map (ambientProjection Z E)) :=
    (ambientHomologyIso Z E R i).isIso_hom
  exact epi_inclusion_of_section (normalBallPair Z E) (ambientProjection Z E)
    (normalSection Z E) (normalSection_comp_projection Z E) R i

/-- The actual relative homology of the normal pair is the actual
projection kernel for the sphere product. -/
def normalBallKernelIso [Nontrivial E] (r : ℕ) (h : Module.finrank ℝ E = r + 1)
    (R : C) (i : ℕ) :
    (Hatcher.Relative.homologyFunctor R (i + 1)).obj (normalBallPair Z E) ≅
      Kernel Z R r i :=
  pairBoundaryKernelIso (normalBallPair Z E) R i (normalInclusion_epi Z E R (i + 1)) ≪≫
    kernel.mapIso ((homologyFunctor R i).map (normalBallPair Z E).map)
      (projectionMap Z R r i) (puncturedHomologyIso Z E r h R i)
      (ambientHomologyIso Z E R i) (inclusion_comp_ambientHomologyIso Z E r h R i)

/-- The normal-pair isomorphism is induced by the genuine relative
boundary followed by the radial homotopy equivalence. -/
@[reassoc]
theorem normalBallKernelIso_hom_comp_ι [Nontrivial E] (r : ℕ)
    (h : Module.finrank ℝ E = r + 1) (R : C) (i : ℕ) :
    (normalBallKernelIso Z E r h R i).hom ≫ kernel.ι (projectionMap Z R r i) =
      Hatcher.Relative.pairConnecting (normalBallPair Z E) R (i + 1) i rfl ≫
        (puncturedHomologyIso Z E r h R i).hom := by
  simp [normalBallKernelIso]

omit [FiniteDimensional ℝ E] in
theorem isZero_normalBall_relative_zero [Nontrivial E] (R : C) :
    IsZero ((Hatcher.Relative.homologyFunctor R 0).obj (normalBallPair Z E)) :=
  isZero_relative_zero_of_epi_inclusion (normalBallPair Z E) R (normalInclusion_epi Z E R 0)

end NormalGeometry

end AkopyanResearch.ProductNormalPairKernel
