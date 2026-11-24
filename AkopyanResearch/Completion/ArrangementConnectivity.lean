module

public import Submission.Approximation.Boundary
public import Submission.ForMathlib.HomotopyGroup.Contractible
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Connectivity of finite linear arrangement complements

The finite grid approximation is the Kuhn interpolation of Vasily Ilin, ported
from homotopy-groups-lean.  The general-position argument below uses the existing
algebraic finite-subspace avoidance theorem of this project.
-/

@[expose] public section
noncomputable section

open scoped unitInterval Topology Topology.Homotopy
open Module Set Submission

namespace AkopyanResearch.ArrangementConnectivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
variable {n N : ℕ}

/-- Finite proper linear subspaces cannot cover a real vector space.
This is the algebraic argument used in `Surgery.Avoid`, with narrow imports. -/
theorem exists_avoiding_subspaces {κ : Type*} (s : Finset κ)
    (P : κ → Submodule ℝ E) (hP : ∀ i ∈ s, P i ≠ ⊤) :
    ∃ p : E, ∀ i ∈ s, p ∉ P i := by
  classical
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (K := ℝ)
    (Finset.univ : Finset s) (fun i => P i) (fun i => hP i i.2)
    (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)
  obtain ⟨p, -, hp⟩ := exists_of_ssubset hss
  exact ⟨p, fun i hi hpi => hp (mem_iUnion₂.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hpi⟩)⟩

/-- A segment from an admissible point to a generic apex avoids the subspace.
This is the segment calculation of `Surgery.Avoid`. -/
theorem segment_avoids_subspace {L : Submodule ℝ E} {a p : E} (ha : a ∉ L)
    (hp : p ∉ L ⊔ Submodule.span ℝ {a}) :
    ∀ x ∈ segment ℝ a p, x ∉ L := by
  rintro x ⟨u, v, hu, hv, huv, rfl⟩ hx
  rcases eq_or_lt_of_le hv with hzero | hpos
  · subst hzero
    have huone : u = 1 := by linarith
    exact ha (by simpa only [huone, one_smul, zero_smul, add_zero] using hx)
  · apply hp
    have heq : p = v⁻¹ • (u • a + v • p) + (-(v⁻¹ * u)) • a := by
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      rw [neg_smul]
      abel
    rw [heq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (L.smul_mem _ hx))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)))

/-- The actual complement of a finite family of linear subspaces. -/
abbrev Complement (L : ι → Submodule ℝ E) := {x : E // ∀ i, x ∉ L i}

/-- Linear span of the sampled values on one grid simplex. -/
def simplexSpan (N : ℕ) (g : C(I^ Fin n, E)) (S : Finset (Fin n → ℕ)) :
    Submodule ℝ E :=
  Submodule.span ℝ ((fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ)))

theorem finrank_simplexSpan_le (N : ℕ) (g : C(I^ Fin n, E))
    (S : Finset (Fin n → ℕ)) : finrank ℝ (simplexSpan N g S) ≤ S.card := by
  classical
  have himg : (fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ)) =
      ((S.image fun v => g (gridVertex N v) : Finset E) : Set E) :=
    (Finset.coe_image).symm
  unfold simplexSpan
  rw [himg]
  exact (finrank_span_finset_le_card (R := ℝ) _).trans Finset.card_image_le

theorem sup_simplexSpan_ne_top (L : Submodule ℝ E) (g : C(I^ Fin n, E))
    (hdim : finrank ℝ L + n + 1 < finrank ℝ E)
    {S : Finset (Fin n → ℕ)} (hS : S ∈ gridSimplices n N) :
    L ⊔ simplexSpan N g S ≠ ⊤ := by
  have hcard := card_le_of_mem_gridSimplices hS
  have hrank := finrank_simplexSpan_le N g S
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq L (simplexSpan N g S)
  intro htop
  rw [htop, finrank_top] at hsup
  omega

theorem cubeGridAffineApprox_mem_simplexSpan (hN : 1 ≤ N)
    (g : C(I^ Fin n, E)) (y : I^ Fin n) :
    cubeGridAffineApprox n N g y ∈ simplexSpan N g (activeVerts N y) := by
  exact affineSpan_le_toAffineSubspace_span
    (convexHull_subset_affineSpan _ (cubeGridAffineApprox_mem_convexHull hN g y))

/-- A PL cube of dimension `n` avoiding subspaces of codimension at least `n+2`
admits one common cone apex which still avoids all those subspaces. -/
theorem exists_gridCone_apex (L : ι → Submodule ℝ E) (hN : 1 ≤ N)
    (g : C(I^ Fin n, E))
    (hdim : ∀ i, finrank ℝ (L i) + n + 1 < finrank ℝ E)
    (havoid : ∀ y i, cubeGridAffineApprox n N g y ∉ L i) :
    ∃ p : E, ∀ y, ∀ x ∈ segment ℝ (cubeGridAffineApprox n N g y) p,
      ∀ i, x ∉ L i := by
  classical
  let D : Finset (ι × Finset (Fin n → ℕ)) := Finset.univ ×ˢ gridSimplices n N
  let K : (ι × Finset (Fin n → ℕ)) → Submodule ℝ E :=
    fun j => L j.1 ⊔ simplexSpan N g j.2
  obtain ⟨p, hp⟩ := exists_avoiding_subspaces D K (by
    intro j hj
    exact sup_simplexSpan_ne_top (L j.1) g (hdim j.1) (Finset.mem_product.mp hj).2)
  refine ⟨p, fun y x hx i => ?_⟩
  apply segment_avoids_subspace (havoid y i) ?_ x hx
  intro hp'
  apply hp (i, activeVerts N y)
    (Finset.mem_product.mpr ⟨Finset.mem_univ i, activeVerts_mem_gridSimplices hN y⟩)
  apply (sup_le_sup_left ?_ (L i)) hp'
  rw [Submodule.span_le]
  intro a ha
  have ha' : a = cubeGridAffineApprox n N g y := by simpa using ha
  rw [ha']
  exact cubeGridAffineApprox_mem_simplexSpan hN g y

/-- The arrangement complement is open in the ambient vector space. -/
theorem isOpen_complement (L : ι → Submodule ℝ E) :
    IsOpen {x : E | ∀ i, x ∉ L i} := by
  have heq : {x : E | ∀ i, x ∉ L i} = ⋂ i, (L i : Set E)ᶜ := by
    ext x
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i => (L i).closed_of_finiteDimensional.isOpen_compl

/-- A sufficiently fine grid approximation and its straight-line homotopy stay
inside the arrangement complement. -/
theorem exists_gridApprox_avoiding (L : ι → Submodule ℝ E)
    (g : C(I^ Fin n, E)) (hg : ∀ y i, g y ∉ L i) :
    ∃ N, 1 ≤ N ∧ ∀ (t : I) (y : I^ Fin n) i,
      cubeGridAffineApproxHomotopy n N g (t, y) ∉ L i := by
  let U : Set E := {x | ∀ i, x ∉ L i}
  have hU : IsOpen U := isOpen_complement L
  have hsub : Set.range g ⊆ U := by
    rintro x ⟨y, rfl⟩
    exact hg y
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_range g.continuous).exists_cthickening_subset_open hU hsub
  obtain ⟨N, hN, hdist⟩ := exists_cubeGridAffineApprox_dist_le n g hδ
  refine ⟨N, hN, fun t y => ?_⟩
  apply hδU
  exact Metric.mem_cthickening_of_dist_le _ (g y) δ _ ⟨y, rfl⟩
    (cubeGridAffineApproxHomotopy_dist_le g hdist t y)

/-- The union of the segments from a map's values to one common apex. -/
def coneRange {X : Type*} (g : X → E) (p : E) : Set E :=
  ⋃ y, segment ℝ (g y) p

theorem mem_coneRange {X : Type*} (g : X → E) (p : E) (y : X) :
    g y ∈ coneRange g p :=
  Set.mem_iUnion.mpr ⟨y, left_mem_segment ℝ _ _⟩

theorem starConvex_coneRange {X : Type*} (g : X → E) (p : E) :
    StarConvex ℝ p (coneRange g p) :=
  starConvex_iUnion fun y => (convex_segment (g y) p).starConvex (right_mem_segment ℝ _ _)

/-- Every positive-dimensional based cube in a finite arrangement complement is
nullhomotopic below the smallest codimension minus one. -/
theorem homotopyGroup_eq_one (L : ι → Submodule ℝ E) [Nonempty (Fin n)]
    (hdim : ∀ i, finrank ℝ (L i) + n + 1 < finrank ℝ E)
    (b : Complement L) (f : Ω^ (Fin n) (Complement L) b) :
    (⟦f⟧ : HomotopyGroup (Fin n) (Complement L) b) =
      (1 : HomotopyGroup (Fin n) (Complement L) b) := by
  let F : C(I^ Fin n, E) :=
    ⟨fun y => (f y).1, continuous_subtype_val.comp f.1.continuous⟩
  have hFbd : ∀ z ∈ Cube.boundary (Fin n), F z = b.1 := by
    intro z hz
    exact congrArg Subtype.val (_root_.GenLoop.boundary f z hz)
  obtain ⟨N, hN, hHavoid⟩ := exists_gridApprox_avoiding L F (fun y => (f y).2)
  have hGavoid : ∀ y i, cubeGridAffineApprox n N F y ∉ L i := by
    intro y i
    simpa only [cubeGridAffineApproxHomotopy_one] using hHavoid 1 y i
  have hGbd : ∀ z ∈ Cube.boundary (Fin n), cubeGridAffineApprox n N F z = b.1 :=
    fun z hz => cubeGridAffineApprox_eq_of_mem_boundary hN F hFbd hz
  let g : Ω^ (Fin n) (Complement L) b :=
    ⟨⟨fun y => ⟨cubeGridAffineApprox n N F y, hGavoid y⟩,
      (cubeGridAffineApprox n N F).continuous.subtype_mk _⟩,
      fun z hz => Subtype.ext (hGbd z hz)⟩
  have hfg : _root_.GenLoop.Homotopic f g := by
    refine ⟨{
      toFun := fun ty => ⟨cubeGridAffineApproxHomotopy n N F ty, hHavoid ty.1 ty.2⟩
      continuous_toFun := (cubeGridAffineApproxHomotopy n N F).continuous.subtype_mk _
      map_zero_left := fun y => Subtype.ext (cubeGridAffineApproxHomotopy_zero F y)
      map_one_left := fun y => Subtype.ext (cubeGridAffineApproxHomotopy_one F y)
      prop' := ?_ }⟩
    intro t z hz
    apply Subtype.ext
    change (1 - (t : ℝ)) • F z + (t : ℝ) • cubeGridAffineApprox n N F z = F z
    rw [hFbd z hz, hGbd z hz, ← add_smul]
    simp
  obtain ⟨p, hp⟩ := exists_gridCone_apex L hN F hdim hGavoid
  let C : Set E := coneRange (cubeGridAffineApprox n N F) p
  have hC : ∀ x ∈ C, ∀ i, x ∉ L i := by
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
    exact hp y x hy
  have hgC : ∀ y, cubeGridAffineApprox n N F y ∈ C :=
    mem_coneRange _ _
  have hbC : b.1 ∈ C := by
    obtain ⟨j⟩ := ‹Nonempty (Fin n)›
    have hy : (fun _ : Fin n => (0 : I)) ∈ Cube.boundary (Fin n) := ⟨j, Or.inl rfl⟩
    rw [← hGbd _ hy]
    exact hgC _
  let bC : C := ⟨b.1, hbC⟩
  let gC : Ω^ (Fin n) C bC :=
    ⟨⟨fun y => ⟨cubeGridAffineApprox n N F y, hgC y⟩,
      (cubeGridAffineApprox n N F).continuous.subtype_mk _⟩,
      fun z hz => Subtype.ext (hGbd z hz)⟩
  let incl : C(C, Complement L) :=
    ⟨fun x => ⟨x.1, hC x.1 x.2⟩, continuous_subtype_val.subtype_mk _⟩
  letI : ContractibleSpace C :=
    (starConvex_coneRange (cubeGridAffineApprox n N F) p).contractibleSpace ⟨b.1, hbC⟩
  have htriv : Subsingleton (HomotopyGroup (Fin n) C bC) :=
    Submission.subsingleton_homotopyGroup_of_contractible bC
  have hmap : Submission.GenLoop.map incl (rfl : incl bC = b) gC = g :=
    _root_.GenLoop.ext _ _ fun y => rfl
  have heq := congrArg (Submission.HomotopyGroup.map incl (rfl : incl bC = b))
    (htriv.elim (⟦gC⟧ : HomotopyGroup (Fin n) C bC) 1)
  rw [Submission.HomotopyGroup.map_mk, hmap, Submission.HomotopyGroup.map_one] at heq
  exact (Quotient.sound hfg).trans heq

/-- Formulation as vanishing of the actual Mathlib homotopy group. -/
theorem subsingleton_homotopyGroup (L : ι → Submodule ℝ E) (hn : 0 < n)
    (hdim : ∀ i, finrank ℝ (L i) + n + 1 < finrank ℝ E)
    (b : Complement L) : Subsingleton (HomotopyGroup.Pi n (Complement L) b) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨fun a c => Quotient.inductionOn₂ a c fun f g => ?_⟩
  exact (homotopyGroup_eq_one L hdim b f).trans (homotopyGroup_eq_one L hdim b g).symm

/-- A finite arrangement of codimension at least two has a path-connected
complement.  The paths consist of two straight segments through a generic apex. -/
theorem pathConnectedSpace_complement (L : ι → Submodule ℝ E)
    (hdim : ∀ i, finrank ℝ (L i) + 1 < finrank ℝ E) :
    PathConnectedSpace (Complement L) := by
  classical
  have hsup : ∀ (i : ι) (a : E), L i ⊔ Submodule.span ℝ {a} ≠ ⊤ := by
    intro i a htop
    have hs : finrank ℝ (Submodule.span ℝ ({a} : Set E)) ≤ 1 := by
      exact finrank_span_le_card ({a} : Set E)
    have h := Submodule.finrank_add_le_finrank_add_finrank
      (L i) (Submodule.span ℝ {a})
    rw [htop, finrank_top] at h
    have hi := hdim i
    omega
  have hL : ∀ i, L i ≠ ⊤ := by
    intro i htop
    have h := hdim i
    rw [htop, finrank_top] at h
    omega
  obtain ⟨a, ha⟩ := exists_avoiding_subspaces Finset.univ L (fun i _ => hL i)
  refine ⟨⟨⟨a, fun i => ha i (Finset.mem_univ i)⟩⟩, fun x y => ?_⟩
  let K : ι × Bool → Submodule ℝ E :=
    fun j => L j.1 ⊔ Submodule.span ℝ {if j.2 then x.1 else y.1}
  obtain ⟨p, hp⟩ := exists_avoiding_subspaces Finset.univ K
    (fun j _ => hsup j.1 _)
  have hxp : ∀ z ∈ segment ℝ x.1 p, ∀ i, z ∉ L i := by
    intro z hz i
    apply segment_avoids_subspace (x.2 i) ?_ z hz
    simpa [K] using hp (i, true) (Finset.mem_univ _)
  have hyp : ∀ z ∈ segment ℝ y.1 p, ∀ i, z ∉ L i := by
    intro z hz i
    apply segment_avoids_subspace (y.2 i) ?_ z hz
    simpa [K] using hp (i, false) (Finset.mem_univ _)
  have hxjoined : JoinedIn {z : E | ∀ i, z ∉ L i} x.1 p :=
    JoinedIn.of_segment_subset hxp
  have hyjoined : JoinedIn {z : E | ∀ i, z ∉ L i} y.1 p :=
    JoinedIn.of_segment_subset hyp
  exact (hxjoined.trans hyjoined.symm).joined_subtype

/-- Codimension formulation, including path components in dimension zero. -/
theorem subsingleton_homotopyGroup_of_codim (L : ι → Submodule ℝ E)
    (n : ℕ) (hdim : ∀ i, n + 2 ≤ finrank ℝ (E ⧸ L i))
    (b : Complement L) : Subsingleton (HomotopyGroup.Pi n (Complement L) b) := by
  have hrank : ∀ i, finrank ℝ (L i) + n + 1 < finrank ℝ E := by
    intro i
    have hi := hdim i
    have hq := (L i).finrank_quotient_add_finrank
    omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · letI : PathConnectedSpace (Complement L) := pathConnectedSpace_complement L (by
      intro i
      simpa using hrank i)
    exact (HomotopyGroup.pi0EquivZerothHomotopy (x := b)).subsingleton
  · exact subsingleton_homotopyGroup L hn hrank b

end AkopyanResearch.ArrangementConnectivity
