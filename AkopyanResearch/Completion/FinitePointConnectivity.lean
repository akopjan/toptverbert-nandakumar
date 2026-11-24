module

public import AkopyanResearch.Completion.ArrangementConnectivity
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Connectivity of finite point complements

A fine Kuhn interpolation stays in the open complement. A common cone
apex is chosen outside finitely many affine spans of a forbidden point
and a grid simplex. Their directions have dimension at most `n+1`, so
they are proper when `n+2 ≤ finrank ℝ E`. The actual based homotopy
groups therefore vanish in the stated range.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped unitInterval Topology Topology.Homotopy
open Module Set Submission

namespace AkopyanResearch.FinitePointConnectivity

open ArrangementConnectivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
variable {n N : ℕ}

abbrev PointComplement (p : ι → E) := {x : E // ∀ i, x ≠ p i}

omit [FiniteDimensional ℝ E] in
theorem dense_complement_submodule (L : Submodule ℝ E) (hL : L ≠ ⊤) :
    Dense (L : Set E)ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl]
  exact Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
    hL (L.eq_top_of_nonempty_interior' ⟨x, hx⟩)

/-- Finite proper affine subspaces do not cover a finite-dimensional real
normed space. This also applies to an empty family. -/
theorem exists_avoiding_translates {κ : Type*} (s : Finset κ)
    (p : κ → E) (L : κ → Submodule ℝ E) (hL : ∀ i ∈ s, L i ≠ ⊤) :
    ∃ a : E, ∀ i ∈ s, a - p i ∉ L i := by
  classical
  let U : s → Set E := fun i => {x | x - p i ∉ L i}
  have ho : ∀ i, IsOpen (U i) := fun i =>
    (L i).closed_of_finiteDimensional.isOpen_compl.preimage
      (continuous_id.sub continuous_const)
  have hd : ∀ i, Dense (U i) := fun i =>
    (dense_complement_submodule (L i) (hL i i.property)).preimage
      (Homeomorph.subRight (p i)).isOpenMap
  obtain ⟨a, ha⟩ := (dense_iInter_of_isOpen ho hd).nonempty
  exact ⟨a, fun i hi => Set.mem_iInter.mp ha ⟨i, hi⟩⟩

theorem segment_avoids_point {a q p : E} (ha : a ≠ p)
    (hq : q - p ∉ Submodule.span ℝ {a - p}) :
    ∀ x ∈ segment ℝ a q, x ≠ p := by
  rintro x ⟨u, v, hu, hv, huv, rfl⟩ hx
  have hzero : u • (a - p) + v • (q - p) = 0 := by
    rw [smul_sub, smul_sub]
    calc
      u • a - u • p + (v • q - v • p) =
          (u • a + v • q) - (u + v) • p := by rw [add_smul]; abel
      _ = 0 := by rw [hx, huv, one_smul, sub_self]
  have havoid := segment_avoids_subspace (L := (⊥ : Submodule ℝ E))
    (a := a - p) (p := q - p)
    (by simpa only [Submodule.mem_bot, sub_eq_zero] using ha)
    (by simpa only [bot_sup_eq] using hq)
  exact havoid (u • (a - p) + v • (q - p))
    ⟨u, v, hu, hv, huv, rfl⟩ (by simpa only [Submodule.mem_bot] using hzero)

def shiftedMap (p : E) (g : C(I^Fin n, E)) : C(I^Fin n, E) :=
  ⟨fun y => g y - p, g.continuous.sub continuous_const⟩

def simplexShiftSpan (p : E) (N : ℕ) (g : C(I^Fin n, E))
    (T : Finset (Fin n → ℕ)) : Submodule ℝ E :=
  simplexSpan N (shiftedMap p g) T

theorem simplexShiftSpan_ne_top (p : E) (g : C(I^Fin n, E))
    (hdim : n + 2 ≤ finrank ℝ E) {T : Finset (Fin n → ℕ)}
    (hT : T ∈ gridSimplices n N) : simplexShiftSpan p N g T ≠ ⊤ := by
  have hc := card_le_of_mem_gridSimplices hT
  have hr := finrank_simplexSpan_le N (shiftedMap p g) T
  intro ht
  change finrank ℝ (simplexShiftSpan p N g T) ≤ T.card at hr
  rw [ht, finrank_top] at hr
  omega

theorem gridApprox_sub_mem (p : E) (hN : 1 ≤ N) (g : C(I^Fin n, E))
    (y : I^Fin n) :
    cubeGridAffineApprox n N g y - p ∈ simplexShiftSpan p N g (activeVerts N y) := by
  let K := simplexShiftSpan p N g (activeVerts N y)
  have hc : Convex ℝ {x : E | x - p ∈ K} := by
    intro a ha b hb u v hu hv huv
    change u • a + v • b - p ∈ K
    have he : u • a + v • b - p = u • (a - p) + v • (b - p) := by
      rw [smul_sub, smul_sub]
      calc
        u • a + v • b - p = (u • a + v • b) - (u + v) • p := by rw [huv, one_smul]
        _ = _ := by rw [add_smul]; abel
    rw [he]
    exact K.add_mem (K.smul_mem u ha) (K.smul_mem v hb)
  apply (convexHull_min ?_ hc) (cubeGridAffineApprox_mem_convexHull hN g y)
  rintro x ⟨v, hv, rfl⟩
  exact Submodule.subset_span ⟨v, hv, rfl⟩

theorem exists_gridCone_apex (p : ι → E) (hN : 1 ≤ N)
    (g : C(I^Fin n, E)) (hdim : n + 2 ≤ finrank ℝ E)
    (havoid : ∀ y i, cubeGridAffineApprox n N g y ≠ p i) :
    ∃ a : E, ∀ y, ∀ x ∈ segment ℝ (cubeGridAffineApprox n N g y) a,
      ∀ i, x ≠ p i := by
  classical
  let D : Finset (ι × Finset (Fin n → ℕ)) := Finset.univ ×ˢ gridSimplices n N
  let K : (ι × Finset (Fin n → ℕ)) → Submodule ℝ E :=
    fun j => simplexShiftSpan (p j.1) N g j.2
  obtain ⟨a, ha⟩ := exists_avoiding_translates D (fun j => p j.1) K (by
    intro j hj
    exact simplexShiftSpan_ne_top (p j.1) g hdim (Finset.mem_product.mp hj).2)
  refine ⟨a, fun y x hx i => segment_avoids_point (havoid y i) ?_ x hx⟩
  intro hm
  apply ha (i, activeVerts N y)
    (Finset.mem_product.mpr ⟨Finset.mem_univ i, activeVerts_mem_gridSimplices hN y⟩)
  apply (Submodule.span_le.mpr ?_) hm
  intro z hz
  have hz' : z = cubeGridAffineApprox n N g y - p i := by simpa using hz
  rw [hz']
  exact gridApprox_sub_mem (p i) hN g y

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isOpen_pointComplement (p : ι → E) : IsOpen {x : E | ∀ i, x ≠ p i} := by
  have he : {x : E | ∀ i, x ≠ p i} = ⋂ i, ({p i} : Set E)ᶜ := by ext x; simp
  rw [he]
  exact isOpen_iInter_of_finite fun _ => isClosed_singleton.isOpen_compl

omit [FiniteDimensional ℝ E] in
theorem exists_gridApprox_avoiding (p : ι → E) (g : C(I^Fin n, E))
    (hg : ∀ y i, g y ≠ p i) :
    ∃ N, 1 ≤ N ∧ ∀ (t : I) (y : I^Fin n) i,
      cubeGridAffineApproxHomotopy n N g (t, y) ≠ p i := by
  let U : Set E := {x | ∀ i, x ≠ p i}
  have hU : IsOpen U := isOpen_pointComplement p
  have hsub : Set.range g ⊆ U := by rintro x ⟨y, rfl⟩; exact hg y
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_range g.continuous).exists_cthickening_subset_open hU hsub
  obtain ⟨N, hN, hdist⟩ := exists_cubeGridAffineApprox_dist_le n g hδ
  refine ⟨N, hN, fun t y => ?_⟩
  apply hδU
  exact Metric.mem_cthickening_of_dist_le _ (g y) δ _ ⟨y, rfl⟩
    (cubeGridAffineApproxHomotopy_dist_le g hdist t y)

/-- Every based cube in the indicated dimension is nullhomotopic in the
actual finite point complement. -/
theorem homotopyGroup_eq_one (p : ι → E) [Nonempty (Fin n)]
    (hdim : n + 2 ≤ finrank ℝ E)
    (b : PointComplement p) (f : Ω^ (Fin n) (PointComplement p) b) :
    (⟦f⟧ : HomotopyGroup (Fin n) (PointComplement p) b) =
      (1 : HomotopyGroup (Fin n) (PointComplement p) b) := by
  let F : C(I^Fin n, E) :=
    ⟨fun y => (f y).val, continuous_subtype_val.comp f.1.continuous⟩
  have hFbd : ∀ z ∈ Cube.boundary (Fin n), F z = b.val := by
    intro z hz
    exact congrArg Subtype.val (_root_.GenLoop.boundary f z hz)
  obtain ⟨N, hN, hHavoid⟩ := exists_gridApprox_avoiding p F (fun y => (f y).property)
  have hGavoid : ∀ y i, cubeGridAffineApprox n N F y ≠ p i := by
    intro y i
    simpa only [cubeGridAffineApproxHomotopy_one] using hHavoid 1 y i
  have hGbd : ∀ z ∈ Cube.boundary (Fin n), cubeGridAffineApprox n N F z = b.val :=
    fun z hz => cubeGridAffineApprox_eq_of_mem_boundary hN F hFbd hz
  let g : Ω^ (Fin n) (PointComplement p) b :=
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
  obtain ⟨a, ha⟩ := exists_gridCone_apex p hN F hdim hGavoid
  let C : Set E := coneRange (cubeGridAffineApprox n N F) a
  have hC : ∀ x ∈ C, ∀ i, x ≠ p i := by
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
    exact ha y x hy
  have hgC : ∀ y, cubeGridAffineApprox n N F y ∈ C := mem_coneRange _ _
  have hbC : b.val ∈ C := by
    obtain ⟨j⟩ := ‹Nonempty (Fin n)›
    have hy : (fun _ : Fin n => (0 : I)) ∈ Cube.boundary (Fin n) := ⟨j, Or.inl rfl⟩
    rw [← hGbd _ hy]
    exact hgC _
  let bC : C := ⟨b.val, hbC⟩
  let gC : Ω^ (Fin n) C bC :=
    ⟨⟨fun y => ⟨cubeGridAffineApprox n N F y, hgC y⟩,
      (cubeGridAffineApprox n N F).continuous.subtype_mk _⟩,
      fun z hz => Subtype.ext (hGbd z hz)⟩
  let incl : C(C, PointComplement p) :=
    ⟨fun x => ⟨x.val, hC x.val x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let : ContractibleSpace C :=
    (starConvex_coneRange (cubeGridAffineApprox n N F) a).contractibleSpace ⟨b.val, hbC⟩
  have htriv : Subsingleton (HomotopyGroup (Fin n) C bC) :=
    Submission.subsingleton_homotopyGroup_of_contractible bC
  have hmap : Submission.GenLoop.map incl (rfl : incl bC = b) gC = g :=
    _root_.GenLoop.ext _ _ fun y => rfl
  have heq := congrArg (Submission.HomotopyGroup.map incl (rfl : incl bC = b))
    (htriv.elim (⟦gC⟧ : HomotopyGroup (Fin n) C bC) 1)
  rw [Submission.HomotopyGroup.map_mk, hmap, Submission.HomotopyGroup.map_one] at heq
  exact (Quotient.sound hfg).trans heq

/-- A finite point complement is path-connected when the real dimension
is at least two. Its paths consist of two straight segments. -/
theorem pathConnectedSpace_pointComplement (p : ι → E) (hdim : 2 ≤ finrank ℝ E) :
    PathConnectedSpace (PointComplement p) := by
  classical
  have hbot : (⊥ : Submodule ℝ E) ≠ ⊤ := by
    intro he
    have hh := congrArg (fun L : Submodule ℝ E => finrank ℝ L) he
    simp only [finrank_bot, finrank_top] at hh
    omega
  obtain ⟨a, ha⟩ := exists_avoiding_translates Finset.univ p (fun _ => (⊥ : Submodule ℝ E))
    (fun _ _ => hbot)
  have hane : ∀ i, a ≠ p i := fun i => by
    simpa only [Submodule.mem_bot, sub_eq_zero] using ha i (Finset.mem_univ i)
  refine ⟨⟨⟨a, hane⟩⟩, fun x y => ?_⟩
  let K : ι × Bool → Submodule ℝ E := fun j =>
    Submodule.span ℝ {if j.2 then x.val - p j.1 else y.val - p j.1}
  have hK : ∀ j, K j ≠ ⊤ := by
    intro j ht
    have hr : finrank ℝ (K j) ≤ 1 :=
      finrank_span_le_card ({if j.2 then x.val - p j.1 else y.val - p j.1} : Set E)
    rw [ht, finrank_top] at hr
    omega
  obtain ⟨q, hq⟩ := exists_avoiding_translates Finset.univ (fun j : ι × Bool => p j.1) K
    (fun j _ => hK j)
  have hxq : ∀ z ∈ segment ℝ x.val q, ∀ i, z ≠ p i := by
    intro z hz i
    apply segment_avoids_point (x.property i) ?_ z hz
    simpa [K] using hq (i, true) (Finset.mem_univ _)
  have hyq : ∀ z ∈ segment ℝ y.val q, ∀ i, z ≠ p i := by
    intro z hz i
    apply segment_avoids_point (y.property i) ?_ z hz
    simpa [K] using hq (i, false) (Finset.mem_univ _)
  have hxjoined : JoinedIn {z : E | ∀ i, z ≠ p i} x.val q :=
    JoinedIn.of_segment_subset hxq
  have hyjoined : JoinedIn {z : E | ∀ i, z ≠ p i} y.val q :=
    JoinedIn.of_segment_subset hyq
  exact (hxjoined.trans hyjoined.symm).joined_subtype

/-- Vanishing of the actual Mathlib homotopy groups, including path
components in dimension zero. -/
theorem subsingleton_homotopyGroup (p : ι → E) (n : ℕ)
    (hdim : n + 2 ≤ finrank ℝ E) (b : PointComplement p) :
    Subsingleton (HomotopyGroup.Pi n (PointComplement p) b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let : PathConnectedSpace (PointComplement p) := pathConnectedSpace_pointComplement p hdim
    exact (HomotopyGroup.pi0EquivZerothHomotopy (x := b)).subsingleton
  · let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨fun a c => Quotient.inductionOn₂ a c fun f g => ?_⟩
    exact (homotopyGroup_eq_one p hdim b f).trans (homotopyGroup_eq_one p hdim b g).symm

end AkopyanResearch.FinitePointConnectivity
