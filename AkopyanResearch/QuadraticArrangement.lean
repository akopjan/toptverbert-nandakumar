module

public import AkopyanResearch.SafeQuadraticRealization
public import AkopyanResearch.DiskCylinderRetraction
public import AkopyanResearch.MatchingProjection
public import AkopyanResearch.QuadraticRank
public import AkopyanResearch.QuadraticNaturality
public import AkopyanResearch.CoxeterTriangulation

@[expose] public section

/-!
# Quadratic subspace arrangements, codimension bounds, Kuhn PL extension, and comparison bridge

1. Simplex faces `FaceSimplex S`, boundaries `FaceBoundary S`, unit cubes `UnitCube d`, and explicit
   radial homeomorphisms `cubeHomeoBall` and `faceSimplexHomeoBall`.
2. Face quadratic spaces `QuadSpace S`, matching kernels `L_M S m`, arrangement complements
   `QuadComplement S`, face lifting `liftFace` / `liftFaceCompl`, and exact codimension bounds
   `10` (single matching), `≥ 14` (pair of distinct matchings), and `≥ 18` (triple of distinct matchings).
3. Ball homotopy extension `homotopy_extension_ball_with_homotopy` and `homotopy_extension_ball`
   from `DiskCylinderRetraction`.
4. Global Choquet-Kuhn PL weights `kuhnWeight` on subdivided unit cubes and sequential general-position
   perturbation `exists_extension_ball_complement`, yielding `exists_extension_quadComplement_of_card_le_nine`.
5. Legacy conditional comparison structures `ComparisonTarget` and `CoherentComparison`, skeleton induction
   `exists_safe_compatible_quadratic_table_of_coherent_comparison`, and final bridge
   `exists_almostSix_of_coherent_comparison`.

The legacy comparison interface assumes universal boundary extension in its
target. Combined with its lifting field, this would extend every boundary map
into the arrangement complement. It is therefore too strong for the intended
nine-sphere comparison. `Completion.ComparisonContract` proves this consequence,
and `Completion.QuadraticLink` constructs an actual linking nine-sphere retract.
`Completion.RelativeComparison` supplies the corrected interface, which tracks
a homotopy to one chosen natural target section and extends that homotopy too.
The legacy conditional implications below are retained as mathematical statements;
they do not assert that such a comparison exists.
-/

noncomputable section

open scoped BigOperators
open Metric AkopyanQuadratic

namespace AkopyanResearch

local instance (priority := 2000) (S : Finset (Fin 15)) : DecidableEq (S → Fin 6) :=
  Classical.decEq _

/-! ### 1. Simplex faces, unit cubes, and homeomorphisms to Euclidean balls -/

section FacesAndBalls

abbrev FaceSimplex (S : Finset (Fin 15)) :=
  {z : MassSimplex // ∀ i, i ∉ S → z.val i = 0}

abbrev FaceBoundary (S : Finset (Fin 15)) :=
  {z : FaceSimplex S // ∃ i ∈ S, z.1.val i = 0}

def faceIncl {T S : Finset (Fin 15)} (hTS : T ⊆ S) (z : FaceSimplex T) : FaceSimplex S :=
  ⟨z.1, fun i hi => z.2 i (fun h => hi (hTS h))⟩

lemma continuous_faceIncl {T S : Finset (Fin 15)} (hTS : T ⊆ S) :
    Continuous (faceIncl hTS) :=
  Continuous.subtype_mk continuous_subtype_val _

@[simp] lemma faceIncl_refl (S : Finset (Fin 15)) (z : FaceSimplex S) :
    faceIncl (Finset.Subset.refl S) z = z := rfl

@[simp] lemma faceIncl_comp {R T S : Finset (Fin 15)} (hRT : R ⊆ T) (hTS : T ⊆ S)
    (z : FaceSimplex R) :
    faceIncl hTS (faceIncl hRT z) = faceIncl (hRT.trans hTS) z := rfl

lemma faceSimplex_sum_eq_one {S : Finset (Fin 15)} (z : FaceSimplex S) :
    ∑ i ∈ S, z.1.val i = 1 := by
  have htot : ∑ i : Fin 15, z.1.val i = 1 := z.1.property.2
  rw [← htot]
  exact Finset.sum_subset (Finset.subset_univ S) fun i _ hi => z.2 i hi

abbrev UnitCube (d : ℕ) :=
  {x : Fin d → ℝ // ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

abbrev UnitCubeBoundary (d : ℕ) :=
  {x : UnitCube d // ∃ j, x.1 j = 0 ∨ x.1 j = 1}

instance compactSpaceUnitCube (d : ℕ) : CompactSpace (UnitCube d) := by
  have heq : {x : Fin d → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} =
      Set.Icc (0 : Fin d → ℝ) 1 := by
    ext x
    simp [Set.mem_Icc, Pi.le_def, forall_and]
  have hcomp : IsCompact {x : Fin d → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} := by
    rw [heq]; exact isCompact_Icc
  exact isCompact_iff_compactSpace.mp hcomp

instance compactSpaceUnitCubeBoundary (d : ℕ) : CompactSpace (UnitCubeBoundary d) := by
  have hclosed : IsClosed {x : UnitCube d | ∃ j : Fin d, x.1 j = 0 ∨ x.1 j = 1} := by
    have heq : {x : UnitCube d | ∃ j : Fin d, x.1 j = 0 ∨ x.1 j = 1} =
        ⋃ j : Fin d, ({x : UnitCube d | x.1 j = 0} ∪ {x : UnitCube d | x.1 j = 1}) := by
      ext x; simp
    rw [heq]
    refine isClosed_iUnion_of_finite fun j => IsClosed.union ?_ ?_
    · exact isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const
    · exact isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

def radialToL2 (d : ℕ) (y : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  if y = 0 then 0 else (‖y‖ / ‖WithLp.toLp 2 y‖) • WithLp.toLp 2 y

def radialFromL2 (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ :=
  if z = 0 then 0 else (‖z‖ / ‖WithLp.ofLp z‖) • WithLp.ofLp z

lemma norm_radialToL2 (d : ℕ) (y : Fin d → ℝ) : ‖radialToL2 d y‖ = ‖y‖ := by
  by_cases hy : y = 0
  · simp [radialToL2, hy]
  · have h2 : WithLp.toLp 2 y ≠ 0 := fun h => hy (congrArg WithLp.ofLp h)
    have hpos : 0 < ‖WithLp.toLp 2 y‖ := norm_pos_iff.mpr h2
    simp only [radialToL2, hy, ↓reduceIte, norm_smul,
      Real.norm_of_nonneg (div_nonneg (norm_nonneg y) hpos.le),
      div_mul_cancel₀ _ hpos.ne']

lemma norm_radialFromL2 (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) : ‖radialFromL2 d z‖ = ‖z‖ := by
  by_cases hz : z = 0
  · simp [radialFromL2, hz]
  · have h2 : WithLp.ofLp z ≠ 0 := fun h => hz (congrArg (WithLp.toLp 2) h)
    have hpos : 0 < ‖WithLp.ofLp z‖ := norm_pos_iff.mpr h2
    simp only [radialFromL2, hz, ↓reduceIte, norm_smul,
      Real.norm_of_nonneg (div_nonneg (norm_nonneg z) hpos.le),
      div_mul_cancel₀ _ hpos.ne']

lemma radialFromL2_radialToL2 (d : ℕ) (y : Fin d → ℝ) :
    radialFromL2 d (radialToL2 d y) = y := by
  by_cases hy : y = 0
  · simp [radialToL2, radialFromL2, hy]
  · have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hz : radialToL2 d y ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_radialToL2]; exact hny.ne'
    have h2 : 0 < ‖WithLp.toLp 2 y‖ := norm_pos_iff.mpr fun h => hy (congrArg WithLp.ofLp h)
    have hc_pos : 0 < ‖y‖ / ‖WithLp.toLp 2 y‖ := div_pos hny h2
    simp only [radialFromL2, hz, ↓reduceIte, norm_radialToL2]
    have hof : WithLp.ofLp (radialToL2 d y) = (‖y‖ / ‖WithLp.toLp 2 y‖) • y := by
      simp [radialToL2, hy]
    rw [hof, norm_smul, Real.norm_of_nonneg hc_pos.le, smul_smul]
    have hmul : (‖y‖ / ((‖y‖ / ‖WithLp.toLp 2 y‖) * ‖y‖)) * (‖y‖ / ‖WithLp.toLp 2 y‖) = 1 := by
      field_simp [hny.ne', h2.ne']
    rw [hmul, one_smul]

lemma radialToL2_radialFromL2 (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    radialToL2 d (radialFromL2 d z) = z := by
  by_cases hz : z = 0
  · simp [radialToL2, radialFromL2, hz]
  · have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hy : radialFromL2 d z ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_radialFromL2]; exact hnz.ne'
    have h2 : 0 < ‖WithLp.ofLp z‖ := norm_pos_iff.mpr fun h => hz (congrArg (WithLp.toLp 2) h)
    have hc_pos : 0 < ‖z‖ / ‖WithLp.ofLp z‖ := div_pos hnz h2
    simp only [radialToL2, hy, ↓reduceIte, norm_radialFromL2]
    have hto : WithLp.toLp 2 (radialFromL2 d z) = (‖z‖ / ‖WithLp.ofLp z‖) • z := by
      simp [radialFromL2, hz]
    rw [hto, norm_smul, Real.norm_of_nonneg hc_pos.le, smul_smul]
    have hmul : (‖z‖ / ((‖z‖ / ‖WithLp.ofLp z‖) * ‖z‖)) * (‖z‖ / ‖WithLp.ofLp z‖) = 1 := by
      field_simp [hnz.ne', h2.ne']
    rw [hmul, one_smul]

lemma continuous_radialToL2 (d : ℕ) : Continuous (radialToL2 d) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  by_cases hy₀ : y₀ = 0
  · subst hy₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    have h0 : radialToL2 d 0 = 0 := by simp [radialToL2]
    rw [h0, dist_zero_right, norm_radialToL2]
    simpa [dist_zero_right] using hy
  · have h2 : ‖WithLp.toLp 2 y₀‖ ≠ 0 :=
      norm_ne_zero_iff.mpr fun h => hy₀ (congrArg WithLp.ofLp h)
    have hcont : ContinuousAt
        (fun y : Fin d → ℝ => (‖y‖ / ‖WithLp.toLp 2 y‖) • WithLp.toLp 2 y) y₀ := by
      have hc1 : Continuous (fun y : Fin d → ℝ => ‖y‖) := continuous_norm
      have hc2 : Continuous (fun y : Fin d → ℝ => ‖WithLp.toLp 2 y‖) :=
        continuous_norm.comp (PiLp.continuous_toLp 2 _)
      have hc3 : Continuous (fun y : Fin d → ℝ => WithLp.toLp 2 y) :=
        PiLp.continuous_toLp 2 _
      exact (hc1.continuousAt.div hc2.continuousAt h2).smul hc3.continuousAt
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hy₀] with y hy
    simp [radialToL2, hy]

lemma continuous_radialFromL2 (d : ℕ) : Continuous (radialFromL2 d) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  by_cases hz₀ : z₀ = 0
  · subst hz₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun z hz => ?_⟩
    have h0 : radialFromL2 d 0 = 0 := by simp [radialFromL2]
    rw [h0, dist_zero_right, norm_radialFromL2]
    simpa [dist_zero_right] using hz
  · have h2 : ‖WithLp.ofLp z₀‖ ≠ 0 :=
      norm_ne_zero_iff.mpr fun h => hz₀ (congrArg (WithLp.toLp 2) h)
    have hcont : ContinuousAt
        (fun z : EuclideanSpace ℝ (Fin d) => (‖z‖ / ‖WithLp.ofLp z‖) • WithLp.ofLp z) z₀ := by
      have hc1 : Continuous (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖) := continuous_norm
      have hc2 : Continuous (fun z : EuclideanSpace ℝ (Fin d) => ‖WithLp.ofLp z‖) :=
        continuous_norm.comp (PiLp.continuous_ofLp 2 _)
      have hc3 : Continuous (fun z : EuclideanSpace ℝ (Fin d) => WithLp.ofLp z) :=
        PiLp.continuous_ofLp 2 _
      exact (hc1.continuousAt.div hc2.continuousAt h2).smul hc3.continuousAt
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hz₀] with z hz
    simp [radialFromL2, hz]

def cubeHomeoBall (d : ℕ) :
    UnitCube d ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 where
  toFun x :=
    ⟨radialToL2 d (fun j => 2 * x.1 j - 1), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_radialToL2]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
      rw [Real.norm_eq_abs, abs_le]
      have hx := x.2 j
      constructor <;> linarith [hx.1, hx.2]⟩
  invFun z :=
    ⟨fun j => (radialFromL2 d z.1 j + 1) / 2, fun j => by
      have hnorm : ‖radialFromL2 d z.1‖ ≤ 1 := by
        rw [norm_radialFromL2]
        exact mem_closedBall_zero_iff.mp z.2
      have hj : |radialFromL2 d z.1 j| ≤ 1 := by
        simpa [Real.norm_eq_abs] using (norm_le_pi_norm (radialFromL2 d z.1) j).trans hnorm
      rw [abs_le] at hj
      constructor <;> linarith⟩
  left_inv x := by
    apply Subtype.ext
    ext j
    change (radialFromL2 d (radialToL2 d (fun j => 2 * x.1 j - 1)) j + 1) / 2 = x.1 j
    rw [radialFromL2_radialToL2]
    ring
  right_inv z := by
    apply Subtype.ext
    have heq : (fun j => 2 * ((radialFromL2 d z.1 j + 1) / 2) - 1) = radialFromL2 d z.1 := by
      ext j; ring
    change radialToL2 d (fun j => 2 * ((radialFromL2 d z.1 j + 1) / 2) - 1) = z.1
    rw [heq, radialToL2_radialFromL2]
  continuous_toFun := by
    refine Continuous.subtype_mk ((continuous_radialToL2 d).comp ?_) _
    refine continuous_pi fun j => ?_
    exact (continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)).sub continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    exact (((continuous_apply j).comp ((continuous_radialFromL2 d).comp continuous_subtype_val)).add
      continuous_const).div_const 2

lemma cubeHomeoBall_norm_eq_one_iff (d : ℕ) (x : UnitCube d) :
    ‖(cubeHomeoBall d x).1‖ = 1 ↔ ∃ j : Fin d, x.1 j = 0 ∨ x.1 j = 1 := by
  change ‖radialToL2 d (fun j => 2 * x.1 j - 1)‖ = 1 ↔ _
  rw [norm_radialToL2]
  let y : Fin d → ℝ := fun j => 2 * x.1 j - 1
  have hy_le : ∀ j, ‖y j‖ ≤ 1 := fun j => by
    rw [Real.norm_eq_abs, abs_le]
    have hx := x.2 j
    constructor <;> linarith [hx.1, hx.2]
  have hnorm_le : ‖y‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hy_le
  constructor
  · intro h1
    by_contra hno
    push_neg at hno
    have hlt : ∀ j, ‖y j‖ < 1 := fun j => by
      rw [Real.norm_eq_abs, abs_lt]
      have hx := x.2 j
      have hne := hno j
      have h0 : 0 < x.1 j := lt_of_le_of_ne hx.1 (Ne.symm hne.1)
      have h1' : x.1 j < 1 := lt_of_le_of_ne hx.2 hne.2
      constructor <;> linarith
    have : ‖y‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr hlt
    linarith
  · rintro ⟨j, hj⟩
    have hj1 : 1 ≤ ‖y j‖ := by
      rw [Real.norm_eq_abs]
      rcases hj with h0 | h1
      · simp [y, h0]
      · simp [y, h1]; norm_num
    exact le_antisymm hnorm_le (hj1.trans (norm_le_pi_norm y j))

def sumSEuc (S : Finset (Fin 15)) : EuclideanSpace ℝ S →ₗ[ℝ] ℝ where
  toFun x := ∑ i : S, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

def Z_S (S : Finset (Fin 15)) : Submodule ℝ (EuclideanSpace ℝ S) :=
  LinearMap.ker (sumSEuc S)

lemma finrank_Z_S (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Module.finrank ℝ ↥(Z_S S) = S.card - 1 := by
  have h1 := (sumSEuc S).finrank_range_add_finrank_ker
  let i₀ : S := ⟨hS.choose, hS.choose_spec⟩
  have hsurj : Function.Surjective (sumSEuc S) := fun c => by
    refine ⟨WithLp.toLp 2 (fun i : S => if i = i₀ then c else 0), ?_⟩
    simp [sumSEuc]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    finrank_euclideanSpace, Fintype.card_coe] at h1
  change 1 + Module.finrank ℝ ↥(Z_S S) = S.card at h1
  omega

def isoZ_S (S : Finset (Fin 15)) (hS : S.Nonempty) :
    ↥(Z_S S) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (S.card - 1)) :=
  ((stdOrthonormalBasis ℝ ↥(Z_S S)).reindex (finCongr (finrank_Z_S S hS))).repr

theorem univNonemptyS (S : Finset (Fin 15)) (hS : S.Nonempty) :
    (Finset.univ : Finset S).Nonempty :=
  ⟨⟨hS.choose, hS.choose_spec⟩, Finset.mem_univ _⟩

def gaugeS (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) : ℝ :=
  Finset.univ.sup' (univNonemptyS S hS) (fun i : S => -(S.card : ℝ) * x.1 i)

lemma continuous_finset_sup' {α X : Type*} [TopologicalSpace X]
    (s : Finset α) (hs : s.Nonempty) (f : α → X → ℝ) (hf : ∀ a ∈ s, Continuous (f a)) :
    Continuous (fun x => s.sup' hs (fun a => f a x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hf a (Finset.mem_singleton_self a)
  | cons a t hat hne ih =>
    simp_rw [Finset.sup'_cons hne]
    exact (hf a (Finset.mem_cons_self a t)).max
      (ih fun b hb => hf b (Finset.mem_cons_of_mem hb))

lemma continuous_gaugeS (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Continuous (gaugeS S hS) := by
  refine continuous_finset_sup' Finset.univ (univNonemptyS S hS) _ fun i _ => ?_
  exact continuous_const.mul ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)

lemma gaugeS_nonneg (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    0 ≤ gaugeS S hS x := by
  by_contra hlt
  have hlt' : gaugeS S hS x < 0 := not_le.mp hlt
  have hforall : ∀ i ∈ (Finset.univ : Finset S), -(S.card : ℝ) * x.1 i < 0 := fun i hi =>
    (Finset.le_sup' (fun j : S => -(S.card : ℝ) * x.1 j) hi).trans_lt hlt'
  have hsum_neg : ∑ i : S, (-(S.card : ℝ) * x.1 i) < ∑ _i : S, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty (univNonemptyS S hS) hforall
  have hsum_zero : ∑ i : S, (-(S.card : ℝ) * x.1 i) = 0 := by
    rw [← Finset.mul_sum, show (∑ i : S, x.1 i) = 0 from x.2, mul_zero]
  rw [hsum_zero, Finset.sum_const_zero] at hsum_neg
  exact lt_irrefl 0 hsum_neg

lemma gaugeS_zero (S : Finset (Fin 15)) (hS : S.Nonempty) :
    gaugeS S hS 0 = 0 := by
  simp [gaugeS]

lemma gaugeS_smul (S : Finset (Fin 15)) (hS : S.Nonempty) {c : ℝ} (hc : 0 ≤ c) (x : ↥(Z_S S)) :
    gaugeS S hS (c • x) = c * gaugeS S hS x := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simp [gaugeS_zero]
  · apply le_antisymm
    · refine Finset.sup'_le _ _ fun i hi => ?_
      change -(S.card : ℝ) * (c * x.1 i) ≤ c * gaugeS S hS x
      rw [show -(S.card : ℝ) * (c * x.1 i) = c * (-(S.card : ℝ) * x.1 i) by ring]
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun j : S => -(S.card : ℝ) * x.1 j) hi) hc
    · rw [← le_div_iff₀' hc_pos]
      refine Finset.sup'_le _ _ fun i hi => ?_
      rw [le_div_iff₀' hc_pos]
      have h1 := Finset.le_sup' (fun j : S => -(S.card : ℝ) * (c • x).1 j) hi
      change -(S.card : ℝ) * (c * x.1 i) ≤ gaugeS S hS (c • x) at h1
      linarith

lemma gaugeS_le_card_mul_norm (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    gaugeS S hS x ≤ (S.card : ℝ) * ‖x‖ := by
  have hm : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hi : |x.1 i| ≤ ‖x.1‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x.1 i
  have hneg : -x.1 i ≤ |x.1 i| := neg_le_abs (x.1 i)
  calc -(S.card : ℝ) * x.1 i = (S.card : ℝ) * (-x.1 i) := by ring
    _ ≤ (S.card : ℝ) * ‖x.1‖ := mul_le_mul_of_nonneg_left (hneg.trans hi) hm
    _ = (S.card : ℝ) * ‖x‖ := rfl

lemma norm_le_card_mul_gaugeS (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    ‖x‖ ≤ (S.card : ℝ) * gaugeS S hS x := by
  have hm_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hm_one : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  let g := gaugeS S hS x
  have hg0 : 0 ≤ g := gaugeS_nonneg S hS x
  have hcoord : ∀ i : S, |x.1 i| ≤ g := fun i => by
    have hlow : -x.1 i ≤ g / S.card := by
      rw [le_div_iff₀' hm_pos]
      have hsup : -(S.card : ℝ) * x.1 i ≤ g :=
        Finset.le_sup' (fun j : S => -(S.card : ℝ) * x.1 j) (Finset.mem_univ i)
      linarith
    have hlow' : -x.1 i ≤ g := hlow.trans (div_le_self hg0 hm_one)
    have hhigh : x.1 i ≤ g := by
      have hsum : x.1 i + ∑ j ∈ Finset.univ.erase i, x.1 j = 0 := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        exact x.2
      have hxi : x.1 i = ∑ j ∈ Finset.univ.erase i, (-x.1 j) := by
        rw [Finset.sum_neg_distrib]
        linarith
      rw [hxi]
      calc ∑ j ∈ Finset.univ.erase i, (-x.1 j)
          ≤ ∑ _j ∈ Finset.univ.erase i, (g / S.card) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [le_div_iff₀' hm_pos]
            have hsup : -(S.card : ℝ) * x.1 j ≤ g :=
              Finset.le_sup' (fun k : S => -(S.card : ℝ) * x.1 k) (Finset.mem_univ j)
            linarith
        _ = ((Finset.univ.erase i).card : ℝ) * (g / S.card) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (S.card : ℝ) * (g / S.card) := by
            refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hg0 hm_pos.le)
            have : (Finset.univ.erase i).card ≤ S.card := by
              have hcard_u : (Finset.univ : Finset S).card = S.card := by simp
              rw [Finset.card_erase_of_mem (Finset.mem_univ i), hcard_u]
              exact Nat.sub_le _ _
            exact_mod_cast this
        _ = g := mul_div_cancel₀ g hm_pos.ne'
    exact abs_le.mpr ⟨by linarith, hhigh⟩
  have hsq : ‖x‖ ^ 2 ≤ ((S.card : ℝ) * g) ^ 2 := by
    change ‖x.1‖ ^ 2 ≤ _
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : S, ‖x.1 i‖ ^ 2
        ≤ ∑ _i : S, g ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hg0] using hcoord i)
      _ = (S.card : ℝ) * g ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) ^ 2 * g ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg g)
          nlinarith
      _ = ((S.card : ℝ) * g) ^ 2 := (mul_pow _ _ 2).symm
  nlinarith [norm_nonneg x, mul_nonneg hm_pos.le hg0]

lemma gaugeS_eq_zero_iff (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    gaugeS S hS x = 0 ↔ x = 0 := by
  constructor
  · intro h0
    have hle := norm_le_card_mul_gaugeS S hS x
    rw [h0, mul_zero] at hle
    exact norm_le_zero_iff.mp hle
  · rintro rfl
    exact gaugeS_zero S hS

def zToBall (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    EuclideanSpace ℝ (Fin (S.card - 1)) :=
  if x = 0 then 0 else (gaugeS S hS x / ‖isoZ_S S hS x‖) • isoZ_S S hS x

def ballToZ (S : Finset (Fin 15)) (hS : S.Nonempty)
    (v : EuclideanSpace ℝ (Fin (S.card - 1))) : ↥(Z_S S) :=
  if v = 0 then 0
  else (‖v‖ / gaugeS S hS ((isoZ_S S hS).symm v)) • (isoZ_S S hS).symm v

lemma norm_zToBall (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    ‖zToBall S hS x‖ = gaugeS S hS x := by
  by_cases hx : x = 0
  · simp [zToBall, hx, gaugeS_zero]
  · have hpos : 0 < ‖isoZ_S S hS x‖ := by
      rw [(isoZ_S S hS).norm_map]
      exact norm_pos_iff.mpr hx
    simp only [zToBall, hx, ↓reduceIte, norm_smul,
      Real.norm_of_nonneg (div_nonneg (gaugeS_nonneg S hS x) hpos.le),
      div_mul_cancel₀ _ hpos.ne']

lemma gaugeS_ballToZ (S : Finset (Fin 15)) (hS : S.Nonempty)
    (v : EuclideanSpace ℝ (Fin (S.card - 1))) :
    gaugeS S hS (ballToZ S hS v) = ‖v‖ := by
  by_cases hv : v = 0
  · simp [ballToZ, hv, gaugeS_zero]
  · have hx : (isoZ_S S hS).symm v ≠ 0 :=
      (LinearEquiv.map_ne_zero_iff (isoZ_S S hS).symm.toLinearEquiv).mpr hv
    have hg : 0 < gaugeS S hS ((isoZ_S S hS).symm v) :=
      lt_of_le_of_ne (gaugeS_nonneg S hS _)
        (Ne.symm ((gaugeS_eq_zero_iff S hS _).not.mpr hx))
    simp only [ballToZ, hv, ↓reduceIte]
    rw [gaugeS_smul S hS (div_nonneg (norm_nonneg v) hg.le), div_mul_cancel₀ _ hg.ne']

lemma ballToZ_zToBall (S : Finset (Fin 15)) (hS : S.Nonempty) (x : ↥(Z_S S)) :
    ballToZ S hS (zToBall S hS x) = x := by
  by_cases hx : x = 0
  · simp [zToBall, ballToZ, hx]
  · have hg : 0 < gaugeS S hS x :=
      lt_of_le_of_ne (gaugeS_nonneg S hS x) (Ne.symm ((gaugeS_eq_zero_iff S hS x).not.mpr hx))
    have hnorm : 0 < ‖isoZ_S S hS x‖ := by
      rw [(isoZ_S S hS).norm_map]; exact norm_pos_iff.mpr hx
    have hv : zToBall S hS x ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_zToBall]; exact hg.ne'
    have hc : 0 < gaugeS S hS x / ‖isoZ_S S hS x‖ := div_pos hg hnorm
    simp only [ballToZ, hv, ↓reduceIte, norm_zToBall]
    have hsymm : (isoZ_S S hS).symm (zToBall S hS x) =
        (gaugeS S hS x / ‖isoZ_S S hS x‖) • x := by
      simp [zToBall, hx, map_smul]
    rw [hsymm, gaugeS_smul S hS hc.le, smul_smul]
    have hmul : (gaugeS S hS x / ((gaugeS S hS x / ‖isoZ_S S hS x‖) * gaugeS S hS x)) *
        (gaugeS S hS x / ‖isoZ_S S hS x‖) = 1 := by
      field_simp [hg.ne', hnorm.ne']
    rw [hmul, one_smul]

lemma zToBall_ballToZ (S : Finset (Fin 15)) (hS : S.Nonempty)
    (v : EuclideanSpace ℝ (Fin (S.card - 1))) :
    zToBall S hS (ballToZ S hS v) = v := by
  by_cases hv : v = 0
  · simp [zToBall, ballToZ, hv]
  · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hx0 : (isoZ_S S hS).symm v ≠ 0 :=
      (LinearEquiv.map_ne_zero_iff (isoZ_S S hS).symm.toLinearEquiv).mpr hv
    have hg : 0 < gaugeS S hS ((isoZ_S S hS).symm v) :=
      lt_of_le_of_ne (gaugeS_nonneg S hS _) (Ne.symm ((gaugeS_eq_zero_iff S hS _).not.mpr hx0))
    have hx : ballToZ S hS v ≠ 0 := by
      intro h0
      have := gaugeS_ballToZ S hS v
      rw [h0, gaugeS_zero] at this
      linarith
    have hc : 0 < ‖v‖ / gaugeS S hS ((isoZ_S S hS).symm v) := div_pos hnv hg
    simp only [zToBall, hx, ↓reduceIte, gaugeS_ballToZ]
    have hiso : isoZ_S S hS (ballToZ S hS v) =
        (‖v‖ / gaugeS S hS ((isoZ_S S hS).symm v)) • v := by
      simp [ballToZ, hv, map_smul]
    rw [hiso, norm_smul, Real.norm_of_nonneg hc.le, smul_smul]
    have hmul : (‖v‖ / ((‖v‖ / gaugeS S hS ((isoZ_S S hS).symm v)) * ‖v‖)) *
        (‖v‖ / gaugeS S hS ((isoZ_S S hS).symm v)) = 1 := by
      field_simp [hnv.ne', hg.ne']
    rw [hmul, one_smul]

lemma continuous_zToBall (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Continuous (zToBall S hS) := by
  have hm_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : x₀ = 0
  · subst hx₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / S.card, div_pos hε hm_pos, fun x hx => ?_⟩
    have h0 : zToBall S hS 0 = 0 := by simp [zToBall]
    rw [dist_zero_right] at hx
    rw [h0, dist_zero_right, norm_zToBall]
    calc gaugeS S hS x ≤ (S.card : ℝ) * ‖x‖ := gaugeS_le_card_mul_norm S hS x
      _ < (S.card : ℝ) * (ε / S.card) := mul_lt_mul_of_pos_left hx hm_pos
      _ = ε := mul_div_cancel₀ ε hm_pos.ne'
  · have hnorm : ‖isoZ_S S hS x₀‖ ≠ 0 := by
      rw [(isoZ_S S hS).norm_map]; exact norm_ne_zero_iff.mpr hx₀
    have hcont : ContinuousAt
        (fun x : ↥(Z_S S) => (gaugeS S hS x / ‖isoZ_S S hS x‖) • isoZ_S S hS x) x₀ := by
      have hc1 : Continuous (fun x : ↥(Z_S S) => gaugeS S hS x) := continuous_gaugeS S hS
      have hc2 : Continuous (fun x : ↥(Z_S S) => ‖isoZ_S S hS x‖) :=
        continuous_norm.comp (isoZ_S S hS).continuous
      have hc3 : Continuous (fun x : ↥(Z_S S) => isoZ_S S hS x) := (isoZ_S S hS).continuous
      exact (hc1.continuousAt.div hc2.continuousAt hnorm).smul hc3.continuousAt
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hx₀] with x hx
    simp [zToBall, hx]

lemma continuous_ballToZ (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Continuous (ballToZ S hS) := by
  have hm_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  rw [continuous_iff_continuousAt]
  intro v₀
  by_cases hv₀ : v₀ = 0
  · subst hv₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / S.card, div_pos hε hm_pos, fun v hv => ?_⟩
    have h0 : ballToZ S hS 0 = 0 := by simp [ballToZ]
    rw [dist_zero_right] at hv
    rw [h0, dist_zero_right]
    calc ‖ballToZ S hS v‖
        ≤ (S.card : ℝ) * gaugeS S hS (ballToZ S hS v) := norm_le_card_mul_gaugeS S hS _
      _ = (S.card : ℝ) * ‖v‖ := by rw [gaugeS_ballToZ]
      _ < (S.card : ℝ) * (ε / S.card) := mul_lt_mul_of_pos_left hv hm_pos
      _ = ε := mul_div_cancel₀ ε hm_pos.ne'
  · have hx0 : (isoZ_S S hS).symm v₀ ≠ 0 :=
      (LinearEquiv.map_ne_zero_iff (isoZ_S S hS).symm.toLinearEquiv).mpr hv₀
    have hg : gaugeS S hS ((isoZ_S S hS).symm v₀) ≠ 0 :=
      (gaugeS_eq_zero_iff S hS _).not.mpr hx0
    have hcont : ContinuousAt
        (fun v : EuclideanSpace ℝ (Fin (S.card - 1)) =>
          (‖v‖ / gaugeS S hS ((isoZ_S S hS).symm v)) • (isoZ_S S hS).symm v) v₀ := by
      have hc1 : Continuous (fun v : EuclideanSpace ℝ (Fin (S.card - 1)) => ‖v‖) := continuous_norm
      have hc2 : Continuous (fun v : EuclideanSpace ℝ (Fin (S.card - 1)) =>
          gaugeS S hS ((isoZ_S S hS).symm v)) :=
        (continuous_gaugeS S hS).comp (isoZ_S S hS).symm.continuous
      have hc3 : Continuous (fun v : EuclideanSpace ℝ (Fin (S.card - 1)) =>
          (isoZ_S S hS).symm v) := (isoZ_S S hS).symm.continuous
      exact (hc1.continuousAt.div hc2.continuousAt hg).smul hc3.continuousAt
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hv₀] with v hv
    simp [ballToZ, hv]

def simplexToZ (S : Finset (Fin 15)) (hS : S.Nonempty) (z : FaceSimplex S) : ↥(Z_S S) :=
  ⟨WithLp.toLp 2 (fun i : S => z.1.val i.1 - (S.card : ℝ)⁻¹), by
    have hm : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
    change ∑ i : S, (z.1.val i.1 - (S.card : ℝ)⁻¹) = 0
    have hattach : (∑ i : S, z.1.val i.1) = ∑ i ∈ S, z.1.val i := by
      change (∑ i ∈ S.attach, z.1.val i.1) = ∑ i ∈ S, z.1.val i
      exact Finset.sum_attach S (fun i => z.1.val i)
    rw [Finset.sum_sub_distrib, hattach, faceSimplex_sum_eq_one z]
    simp [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hm]⟩

lemma gaugeS_simplexToZ_le_one (S : Finset (Fin 15)) (hS : S.Nonempty) (z : FaceSimplex S) :
    gaugeS S hS (simplexToZ S hS z) ≤ 1 := by
  have hm_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hi : 0 ≤ z.1.val i.1 := z.1.property.1 i.1
  change -(S.card : ℝ) * (z.1.val i.1 - (S.card : ℝ)⁻¹) ≤ 1
  have : -(S.card : ℝ) * (z.1.val i.1 - (S.card : ℝ)⁻¹) =
      1 - (S.card : ℝ) * z.1.val i.1 := by
    field_simp [hm_pos.ne']
    ring
  rw [this]
  nlinarith

def zToSimplex (S : Finset (Fin 15)) (hS : S.Nonempty)
    (x : {x : ↥(Z_S S) // gaugeS S hS x ≤ 1}) : FaceSimplex S :=
  ⟨⟨fun i : Fin 15 => if hi : i ∈ S then x.1.1 ⟨i, hi⟩ + (S.card : ℝ)⁻¹ else 0, by
      have hm_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
      constructor
      · intro i
        by_cases hi : i ∈ S
        · simp only [hi, ↓reduceDIte]
          have hle : -(S.card : ℝ) * x.1.1 ⟨i, hi⟩ ≤ 1 :=
            (Finset.le_sup' (fun j : S => -(S.card : ℝ) * x.1.1 j)
              (Finset.mem_univ ⟨i, hi⟩)).trans x.2
          have h1 : -1 ≤ x.1.1 ⟨i, hi⟩ * (S.card : ℝ) := by linarith
          have h2 : -(S.card : ℝ)⁻¹ ≤ x.1.1 ⟨i, hi⟩ := by
            have := (div_le_iff₀ hm_pos).mpr h1
            linarith [show (-1 : ℝ) / S.card = -(S.card : ℝ)⁻¹ by ring]
          linarith
        · simp [hi]
      · rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
        have hattach : (∑ i ∈ S, (if hi : i ∈ S then x.1.1 ⟨i, hi⟩ + (S.card : ℝ)⁻¹ else 0)) =
            ∑ i : S, (x.1.1 i + (S.card : ℝ)⁻¹) := by
          rw [← Finset.sum_attach S]
          refine Finset.sum_congr rfl fun i _ => by simp [i.2]
        rw [hattach, Finset.sum_add_distrib, show (∑ i : S, x.1.1 i) = 0 from x.1.2]
        simp [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hm_pos.ne']⟩,
    fun i hi => by simp [hi]⟩

def faceSimplexHomeoBall (S : Finset (Fin 15)) (hS : S.Nonempty) :
    FaceSimplex S ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (S.card - 1))) 1 where
  toFun z :=
    ⟨zToBall S hS (simplexToZ S hS z), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_zToBall]
      exact gaugeS_simplexToZ_le_one S hS z⟩
  invFun v :=
    zToSimplex S hS ⟨ballToZ S hS v.1, by
      rw [gaugeS_ballToZ]
      exact mem_closedBall_zero_iff.mp v.2⟩
  left_inv z := by
    apply Subtype.ext; apply Subtype.ext; ext i
    simp only [zToSimplex, ballToZ_zToBall]
    by_cases hi : i ∈ S
    · simp [hi, simplexToZ]
    · simp [hi, z.2 i hi]
  right_inv v := by
    apply Subtype.ext
    have hsim : simplexToZ S hS (zToSimplex S hS ⟨ballToZ S hS v.1, by
        rw [gaugeS_ballToZ]; exact mem_closedBall_zero_iff.mp v.2⟩) =
        ballToZ S hS v.1 := by
      apply Subtype.ext; ext i
      simp [simplexToZ, zToSimplex]
    change zToBall S hS (simplexToZ S hS (zToSimplex S hS ⟨ballToZ S hS v.1, by
        rw [gaugeS_ballToZ]; exact mem_closedBall_zero_iff.mp v.2⟩)) = v.1
    rw [hsim, zToBall_ballToZ]
  continuous_toFun := by
    refine Continuous.subtype_mk ((continuous_zToBall S hS).comp ?_) _
    have hvec : Continuous (fun z : FaceSimplex S =>
        WithLp.toLp 2 (fun i : S => z.1.val i.1 - (S.card : ℝ)⁻¹)) :=
      (PiLp.continuous_toLp 2 (fun _ : S => ℝ)).comp (continuous_pi fun i : S =>
        (((continuous_apply i.1).comp (continuous_subtype_val.comp continuous_subtype_val)).sub
          continuous_const))
    exact Continuous.subtype_mk hvec _
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (continuous_pi fun i => ?_) _) _
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceDIte]
      exact (((PiLp.continuous_apply 2 _ ⟨i, hi⟩).comp
        (continuous_subtype_val.comp ((continuous_ballToZ S hS).comp continuous_subtype_val))).add
        continuous_const)
    · simp only [hi, ↓reduceDIte]
      exact continuous_const

lemma faceSimplexHomeoBall_norm_eq_one_iff (S : Finset (Fin 15)) (hS : S.Nonempty)
    (z : FaceSimplex S) :
    ‖(faceSimplexHomeoBall S hS z).1‖ = 1 ↔ ∃ i ∈ S, z.1.val i = 0 := by
  have hm_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  change ‖zToBall S hS (simplexToZ S hS z)‖ = 1 ↔ _
  rw [norm_zToBall]
  have hle : gaugeS S hS (simplexToZ S hS z) ≤ 1 := gaugeS_simplexToZ_le_one S hS z
  have hterm : ∀ i : S, -(S.card : ℝ) * (simplexToZ S hS z).1 i =
      1 - (S.card : ℝ) * z.1.val i.1 := fun i => by
    change -(S.card : ℝ) * (z.1.val i.1 - (S.card : ℝ)⁻¹) = _
    field_simp [hm_pos.ne']
    ring
  constructor
  · intro h1
    obtain ⟨i, _, hi_eq⟩ :=
      Finset.exists_mem_eq_sup' (univNonemptyS S hS) (fun j : S => -(S.card : ℝ) * (simplexToZ S hS z).1 j)
    change gaugeS S hS (simplexToZ S hS z) = -(S.card : ℝ) * (simplexToZ S hS z).1 i at hi_eq
    rw [h1] at hi_eq
    rw [hterm i] at hi_eq
    have hmul : (S.card : ℝ) * z.1.val i.1 = 0 := by linarith
    refine ⟨i.1, i.2, (mul_eq_zero.mp hmul).resolve_left hm_pos.ne'⟩
  · rintro ⟨i, hiS, hzi⟩
    have h1 : 1 ≤ gaugeS S hS (simplexToZ S hS z) := by
      have := Finset.le_sup' (fun j : S => -(S.card : ℝ) * (simplexToZ S hS z).1 j)
        (Finset.mem_univ (⟨i, hiS⟩ : S))
      rw [hterm ⟨i, hiS⟩, hzi, mul_zero, sub_zero] at this
      exact this
    exact le_antisymm hle h1

end FacesAndBalls

/-! ### 2. Face quadratic spaces, matching kernels, and codimensions `10`, `14`, `18` -/

section MatchingCodimension

abbrev QuadSpace (S : Finset (Fin 15)) :=
  Fin 2 → AkopyanQuadratic.quadraticLabelSpace S (Fin 6)

def finsetIncl {T S : Finset (Fin 15)} (hTS : T ⊆ S) (x : T) : S :=
  ⟨x.1, hTS x.2⟩

def liftFace {T S : Finset (Fin 15)} (hTS : T ⊆ S) :
    QuadSpace T →ₗ[ℝ] QuadSpace S where
  toFun H := fun t =>
    ⟨fun w => (H t).1 (w ∘ finsetIncl hTS),
      color_duplication_mem_quadratic (finsetIncl hTS) (H t).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma continuous_liftFace {T S : Finset (Fin 15)} (hTS : T ⊆ S) :
    Continuous (liftFace hTS) :=
  (liftFace hTS).continuous_of_finiteDimensional

@[simp] lemma liftFace_refl (S : Finset (Fin 15)) (H : QuadSpace S) :
    liftFace (Finset.Subset.refl S) H = H := rfl

@[simp] lemma liftFace_comp {R T S : Finset (Fin 15)} (hRT : R ⊆ T) (hTS : T ⊆ S)
    (H : QuadSpace R) :
    liftFace hTS (liftFace hRT H) = liftFace (hRT.trans hTS) H := rfl

def liftToFull (S : Finset (Fin 15)) (H : QuadSpace S) : TableWords → Fin 2 → ℝ :=
  fun w t => (H t).1 (fun i : S => w i.1)

lemma liftToFull_mem_quadratic (S : Finset (Fin 15)) (H : QuadSpace S) (t : Fin 2) :
    (fun w => liftToFull S H w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6) :=
  color_duplication_mem_quadratic (Subtype.val : S → Fin 15) (H t).2

lemma ignoresColor_liftToFull (S : Finset (Fin 15)) (H : QuadSpace S)
    {i : Fin 15} (hi : i ∉ S) (t : Fin 2) :
    IgnoresColor (fun w => liftToFull S H w t) i := by
  intro w a
  dsimp [liftToFull]
  have hfun : (fun j : S => Function.update w i a j.1) = (fun j : S => w j.1) := by
    funext j
    have hne : j.1 ≠ i := fun h => hi (h ▸ j.2)
    exact Function.update_of_ne hne a w
  rw [hfun]

def L_M (S : Finset (Fin 15)) (m : Finset (S → Fin 6)) : Submodule ℝ (QuadSpace S) where
  carrier := {H | ∀ u ∈ m, ∀ v ∈ m, ∀ t : Fin 2, (H t).1 u = (H t).1 v}
  add_mem' {H₁ H₂} h₁ h₂ u hu v hv t := by
    change (H₁ t).1 u + (H₂ t).1 u = (H₁ t).1 v + (H₂ t).1 v
    rw [h₁ u hu v hv t, h₂ u hu v hv t]
  zero_mem' _ _ _ _ _ := rfl
  smul_mem' c {H} h u hu v hv t := by
    change c * (H t).1 u = c * (H t).1 v
    rw [h u hu v hv t]

abbrev QuadComplement (S : Finset (Fin 15)) :=
  {H : QuadSpace S // ∀ m : Finset (S → Fin 6), SixMatching m → H ∉ L_M S m}

def liftFaceCompl {T S : Finset (Fin 15)} (hT : T.Nonempty) (hTS : T ⊆ S)
    (H : QuadComplement T) : QuadComplement S :=
  ⟨liftFace hTS H.1, fun m hm hmem => by
    let i₀ : T := ⟨hT.choose, hT.choose_spec⟩
    have hmT : SixMatching (projectMatching (finsetIncl hTS) m) :=
      hm.project (finsetIncl hTS) i₀
    apply H.2 (projectMatching (finsetIncl hTS) m) hmT
    intro u' hu' v' hv' t
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hv'
    exact hmem u hu v hv t⟩

lemma continuous_liftFaceCompl {T S : Finset (Fin 15)} (hT : T.Nonempty) (hTS : T ⊆ S) :
    Continuous (liftFaceCompl hT hTS) :=
  Continuous.subtype_mk ((continuous_liftFace hTS).comp continuous_subtype_val) _

@[simp] lemma liftFaceCompl_refl (S : Finset (Fin 15)) (hS : S.Nonempty) (H : QuadComplement S) :
    liftFaceCompl hS (Finset.Subset.refl S) H = H := by
  apply Subtype.ext; rfl

@[simp] lemma liftFaceCompl_comp {R T S : Finset (Fin 15)} (hR : R.Nonempty) (hT : T.Nonempty)
    (hRT : R ⊆ T) (hTS : T ⊆ S) (H : QuadComplement R) :
    liftFaceCompl hT hTS (liftFaceCompl hR hRT H) = liftFaceCompl hR (hRT.trans hTS) H := by
  apply Subtype.ext; rfl

lemma codim_comap_of_surjective {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (ev : E →ₗ[ℝ] F) (hev : Function.Surjective ev) (K : Submodule ℝ F) :
    Module.finrank ℝ (E ⧸ K.comap ev) = Module.finrank ℝ F - Module.finrank ℝ K := by
  let f : E →ₗ[ℝ] (F ⧸ K) := K.mkQ.comp ev
  have hf_surj : Function.Surjective f := K.mkQ_surjective.comp hev
  have hker : LinearMap.ker f = K.comap ev := by
    ext x
    simp [f, LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hequiv : (E ⧸ K.comap ev) ≃ₗ[ℝ] (F ⧸ K) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf_surj)
  have hsum := K.finrank_quotient_add_finrank
  rw [hequiv.finrank_eq]
  omega

def constOnSubmodule {W : Type*} (u : Finset W) (ms : List (Finset W)) :
    Submodule ℝ ({w // w ∈ u} → Fin 2 → ℝ) where
  carrier := {g | ∀ m ∈ ms, ∀ a ∈ m, ∀ b ∈ m, (ha : a ∈ u) → (hb : b ∈ u) →
    g ⟨a, ha⟩ = g ⟨b, hb⟩}
  add_mem' {g₁ g₂} h₁ h₂ m hm a ha b hb hau hbu := by
    ext t
    exact congrArg₂ (· + ·) (congrFun (h₁ m hm a ha b hb hau hbu) t)
      (congrFun (h₂ m hm a ha b hb hau hbu) t)
  zero_mem' _ _ _ _ _ _ _ _ := rfl
  smul_mem' c {g} h m hm a ha b hb hau hbu := by
    ext t
    exact congrArg (c * ·) (congrFun (h m hm a ha b hb hau hbu) t)

lemma finrank_arrow_fin2 {W : Type*} (u : Finset W) :
    Module.finrank ℝ ({w // w ∈ u} → Fin 2 → ℝ) = 2 * u.card := by
  rw [Module.finrank_pi_fintype]
  simp [Finset.sum_const, mul_comm]

theorem codim_L_M_eq_ten (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m : Finset (S → Fin 6)) (hm : SixMatching m) :
    Module.finrank ℝ (QuadSpace S ⧸ L_M S m) = 10 := by
  let i₀ : S := ⟨hS.choose, hS.choose_spec⟩
  have h3 := three_matchings_fiber_card_le_three m m m i₀
    (hm.coordinateInjectiveOn i₀) (hm.coordinateInjectiveOn i₀) (hm.coordinateInjectiveOn i₀)
  have hU : @Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _))
      (@Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _)) m m) m = m := by
    ext x; simp
  rw [hU] at h3
  have hev : Function.Surjective (vectorEvaluation (K := Fin 2) m) :=
    vectorEvaluation_surjective m i₀ h3
  let K := constOnSubmodule m [m]
  have hcomap : K.comap (vectorEvaluation (K := Fin 2) m) = L_M S m := by
    ext H
    simp only [Submodule.mem_comap, K, constOnSubmodule, List.mem_singleton, forall_eq,
      L_M, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
      vectorEvaluation, LinearMap.coe_mk, AddHom.coe_mk, funext_iff]
    constructor
    · intro h u hu v hv t; exact h u hu v hv hu hv t
    · intro h u hu v hv _ _ t; exact h u hu v hv t
  have hcard_pos : 0 < m.card := by rw [hm.1]; norm_num
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hcard_pos
  let equivK : K ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun g => g.1 ⟨u₀, hu₀⟩
      invFun := fun c => ⟨fun _ => c, fun _ _ _ _ _ _ _ _ => rfl⟩
      left_inv := fun g => by
        apply Subtype.ext; funext ⟨w, hw⟩
        exact (g.2 m (List.mem_singleton_self m) w hw u₀ hu₀ hw hu₀).symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hK_dim : Module.finrank ℝ K = 2 := by
    rw [equivK.finrank_eq, Module.finrank_fin_fun]
  rw [← hcomap, codim_comap_of_surjective _ hev K, finrank_arrow_fin2, hm.1, hK_dim]

theorem codim_L_M_inf_two_ge_fourteen (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m₁ m₂ : Finset (S → Fin 6)) (hm₁ : SixMatching m₁) (hm₂ : SixMatching m₂)
    (hne : m₁ ≠ m₂) :
    14 ≤ Module.finrank ℝ (QuadSpace S ⧸ (L_M S m₁ ⊓ L_M S m₂)) := by
  let i₀ : S := ⟨hS.choose, hS.choose_spec⟩
  have h3 := three_matchings_fiber_card_le_three m₁ m₂ m₂ i₀
    (hm₁.coordinateInjectiveOn i₀) (hm₂.coordinateInjectiveOn i₀) (hm₂.coordinateInjectiveOn i₀)
  have hU : @Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _))
      (@Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _)) m₁ m₂) m₂ = m₁ ∪ m₂ := by
    ext x; simp
  rw [hU] at h3
  have hev : Function.Surjective (vectorEvaluation (K := Fin 2) (m₁ ∪ m₂)) :=
    vectorEvaluation_surjective (m₁ ∪ m₂) i₀ h3
  let K := constOnSubmodule (m₁ ∪ m₂) [m₁, m₂]
  have hcomap : K.comap (vectorEvaluation (K := Fin 2) (m₁ ∪ m₂)) = L_M S m₁ ⊓ L_M S m₂ := by
    ext H
    simp only [Submodule.mem_comap, K, constOnSubmodule, List.mem_cons, List.not_mem_nil,
      or_false, Submodule.mem_inf, L_M, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, vectorEvaluation, LinearMap.coe_mk,
      AddHom.coe_mk, funext_iff]
    constructor
    · intro h
      refine ⟨fun a ha b hb t => h m₁ (Or.inl rfl) a ha b hb (Finset.mem_union_left _ ha)
          (Finset.mem_union_left _ hb) t,
        fun a ha b hb t => h m₂ (Or.inr rfl) a ha b hb (Finset.mem_union_right _ ha)
          (Finset.mem_union_right _ hb) t⟩
    · rintro ⟨h₁, h₂⟩ m (rfl | rfl) a ha b hb _ _ t
      · exact h₁ a ha b hb t
      · exact h₂ a ha b hb t
  obtain ⟨w₁, hw₁⟩ := Finset.card_pos.mp (by rw [hm₁.1]; norm_num : 0 < m₁.card)
  obtain ⟨w₂, hw₂⟩ := Finset.card_pos.mp (by rw [hm₂.1]; norm_num : 0 < m₂.card)
  have hw₁u : w₁ ∈ m₁ ∪ m₂ := Finset.mem_union_left _ hw₁
  have hw₂u : w₂ ∈ m₁ ∪ m₂ := Finset.mem_union_right _ hw₂
  have hcodim_eq := codim_comap_of_surjective (vectorEvaluation (K := Fin 2) (m₁ ∪ m₂)) hev K
  rw [hcomap, finrank_arrow_fin2] at hcodim_eq
  rw [hcodim_eq]
  by_cases hinter : (m₁ ∩ m₂).Nonempty
  · obtain ⟨w₀, hw₀⟩ := hinter
    have hw₀1 : w₀ ∈ m₁ := (Finset.mem_inter.mp hw₀).1
    have hw₀2 : w₀ ∈ m₂ := (Finset.mem_inter.mp hw₀).2
    have hw₀u : w₀ ∈ m₁ ∪ m₂ := Finset.mem_union_left _ hw₀1
    let proj1 : K →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun g => g.1 ⟨w₀, hw₀u⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj1 := fun g₁ g₂ h => by
      have h_eq : g₁.1 ⟨w₀, hw₀u⟩ = g₂.1 ⟨w₀, hw₀u⟩ := h
      apply Subtype.ext; funext ⟨w, hwu⟩
      rcases Finset.mem_union.mp hwu with h1 | h2
      · rw [g₁.2 m₁ (by simp) w h1 w₀ hw₀1 hwu hw₀u,
          g₂.2 m₁ (by simp) w h1 w₀ hw₀1 hwu hw₀u, h_eq]
      · rw [g₁.2 m₂ (by simp) w h2 w₀ hw₀2 hwu hw₀u,
          g₂.2 m₂ (by simp) w h2 w₀ hw₀2 hwu hw₀u, h_eq]
    have hK_le : Module.finrank ℝ K ≤ 2 := by
      have := LinearMap.finrank_le_finrank_of_injective hinj
      simpa using this
    have hinter_le := distinct_sixMatchings_inter_card_le_four m₁ m₂ i₀ hm₁ hm₂ hne
    have hcards := Finset.card_union_add_card_inter m₁ m₂
    have hm1c := hm₁.1
    have hm2c := hm₂.1
    have hu_ge : 8 ≤ (m₁ ∪ m₂).card := by omega
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hinter
    let proj2 : K →ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
      { toFun := fun g => (g.1 ⟨w₁, hw₁u⟩, g.1 ⟨w₂, hw₂u⟩)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj2 := fun g₁ g₂ h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      apply Subtype.ext; funext ⟨w, hwu⟩
      rcases Finset.mem_union.mp hwu with hw_m1 | hw_m2
      · rw [g₁.2 m₁ (by simp) w hw_m1 w₁ hw₁ hwu hw₁u,
          g₂.2 m₁ (by simp) w hw_m1 w₁ hw₁ hwu hw₁u, h1]
      · rw [g₁.2 m₂ (by simp) w hw_m2 w₂ hw₂ hwu hw₂u,
          g₂.2 m₂ (by simp) w hw_m2 w₂ hw₂ hwu hw₂u, h2]
    have hK_le : Module.finrank ℝ K ≤ 4 := by
      have := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [Module.finrank_prod] using this
    have hcards := Finset.card_union_add_card_inter m₁ m₂
    rw [hinter, Finset.card_empty] at hcards
    have hm1c := hm₁.1
    have hm2c := hm₂.1
    have hu_eq : (m₁ ∪ m₂).card = 12 := by omega
    omega

lemma finrank_constOn_three_le_four_of_inter {W : Type*} [DecidableEq W]
    (m₁ m₂ m₃ : Finset W)
    (w₁ : W) (hw₁ : w₁ ∈ m₁) (w₂ : W) (hw₂ : w₂ ∈ m₂) (w₃ : W) (hw₃ : w₃ ∈ m₃)
    (h12 : (m₁ ∩ m₂).Nonempty) :
    Module.finrank ℝ (constOnSubmodule (m₁ ∪ m₂ ∪ m₃) [m₁, m₂, m₃]) ≤ 4 := by
  let u := m₁ ∪ m₂ ∪ m₃
  obtain ⟨c, hc⟩ := h12
  have hc1 : c ∈ m₁ := (Finset.mem_inter.mp hc).1
  have hc2 : c ∈ m₂ := (Finset.mem_inter.mp hc).2
  have hcu : c ∈ u := Finset.mem_union_left _ (Finset.mem_union_left _ hc1)
  have hw₁u : w₁ ∈ u := Finset.mem_union_left _ (Finset.mem_union_left _ hw₁)
  have hw₂u : w₂ ∈ u := Finset.mem_union_left _ (Finset.mem_union_right _ hw₂)
  have hw₃u : w₃ ∈ u := Finset.mem_union_right _ hw₃
  let K := constOnSubmodule u [m₁, m₂, m₃]
  let proj : K →ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
    { toFun := fun g => (g.1 ⟨c, hcu⟩, g.1 ⟨w₃, hw₃u⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective proj := fun g₁ g₂ h => by
    rcases Prod.mk.inj h with ⟨hc_eq, h3_eq⟩
    apply Subtype.ext; funext ⟨w, hwu⟩
    rcases Finset.mem_union.mp hwu with h12u | h3u
    · rcases Finset.mem_union.mp h12u with h1u | h2u
      · rw [g₁.2 m₁ (by simp) w h1u c hc1 hwu hcu,
          g₂.2 m₁ (by simp) w h1u c hc1 hwu hcu, hc_eq]
      · rw [g₁.2 m₂ (by simp) w h2u c hc2 hwu hcu,
          g₂.2 m₂ (by simp) w h2u c hc2 hwu hcu, hc_eq]
    · rw [g₁.2 m₃ (by simp) w h3u w₃ hw₃ hwu hw₃u,
        g₂.2 m₃ (by simp) w h3u w₃ hw₃ hwu hw₃u, h3_eq]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod] using this

theorem codim_L_M_inf_three_ge_eighteen (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m₁ m₂ m₃ : Finset (S → Fin 6))
    (hm₁ : SixMatching m₁) (hm₂ : SixMatching m₂) (hm₃ : SixMatching m₃)
    (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃) :
    18 ≤ Module.finrank ℝ (QuadSpace S ⧸ (L_M S m₁ ⊓ L_M S m₂ ⊓ L_M S m₃)) := by
  let i₀ : S := ⟨hS.choose, hS.choose_spec⟩
  have h3 := three_matchings_fiber_card_le_three m₁ m₂ m₃ i₀
    (hm₁.coordinateInjectiveOn i₀) (hm₂.coordinateInjectiveOn i₀) (hm₃.coordinateInjectiveOn i₀)
  have hU : @Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _))
      (@Union.union (Finset (S → Fin 6)) (@Finset.instUnion _ (Classical.decEq _)) m₁ m₂) m₃ = m₁ ∪ m₂ ∪ m₃ := by
    ext x; simp
  rw [hU] at h3
  have hev : Function.Surjective (vectorEvaluation (K := Fin 2) (m₁ ∪ m₂ ∪ m₃)) :=
    vectorEvaluation_surjective (m₁ ∪ m₂ ∪ m₃) i₀ h3
  let K := constOnSubmodule (m₁ ∪ m₂ ∪ m₃) [m₁, m₂, m₃]
  have hcomap : K.comap (vectorEvaluation (K := Fin 2) (m₁ ∪ m₂ ∪ m₃)) =
      L_M S m₁ ⊓ L_M S m₂ ⊓ L_M S m₃ := by
    ext H
    simp only [Submodule.mem_comap, K, constOnSubmodule, List.mem_cons, List.not_mem_nil,
      or_false, Submodule.mem_inf, L_M, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, vectorEvaluation, LinearMap.coe_mk,
      AddHom.coe_mk, funext_iff]
    constructor
    · intro h
      refine ⟨⟨fun a ha b hb t => h m₁ (Or.inl rfl) a ha b hb
          (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
          (Finset.mem_union_left _ (Finset.mem_union_left _ hb)) t,
        fun a ha b hb t => h m₂ (Or.inr (Or.inl rfl)) a ha b hb
          (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
          (Finset.mem_union_left _ (Finset.mem_union_right _ hb)) t⟩,
        fun a ha b hb t => h m₃ (Or.inr (Or.inr rfl)) a ha b hb
          (Finset.mem_union_right _ ha) (Finset.mem_union_right _ hb) t⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩ m (rfl | rfl | rfl) a ha b hb _ _ t
      · exact h₁ a ha b hb t
      · exact h₂ a ha b hb t
      · exact h₃ a ha b hb t
  obtain ⟨w₁, hw₁⟩ := Finset.card_pos.mp (by rw [hm₁.1]; norm_num : 0 < m₁.card)
  obtain ⟨w₂, hw₂⟩ := Finset.card_pos.mp (by rw [hm₂.1]; norm_num : 0 < m₂.card)
  obtain ⟨w₃, hw₃⟩ := Finset.card_pos.mp (by rw [hm₃.1]; norm_num : 0 < m₃.card)
  have hw₁u : w₁ ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_left _ (Finset.mem_union_left _ hw₁)
  have hw₂u : w₂ ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_left _ (Finset.mem_union_right _ hw₂)
  have hw₃u : w₃ ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hw₃
  have hcodim_eq := codim_comap_of_surjective (vectorEvaluation (K := Fin 2) (m₁ ∪ m₂ ∪ m₃)) hev K
  rw [hcomap, finrank_arrow_fin2] at hcodim_eq
  rw [hcodim_eq]
  have hu_ge_ten : 10 ≤ (m₁ ∪ m₂ ∪ m₃).card :=
    three_distinct_sixMatchings_union_card_ge_ten m₁ m₂ m₃ i₀ hm₁ hm₂ hm₃ h12 h13 h23
  by_cases hI12 : (m₁ ∩ m₂).Nonempty <;>
    by_cases hI13 : (m₁ ∩ m₃).Nonempty <;>
    by_cases hI23 : (m₂ ∩ m₃).Nonempty
  · -- all 3 pairs intersect: connected (1 component)
    obtain ⟨c12, hc12⟩ := hI12
    obtain ⟨c13, hc13⟩ := hI13
    have hc12_1 := (Finset.mem_inter.mp hc12).1
    have hc12_2 := (Finset.mem_inter.mp hc12).2
    have hc13_1 := (Finset.mem_inter.mp hc13).1
    have hc13_3 := (Finset.mem_inter.mp hc13).2
    have hc12u : c12 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_left _ (Finset.mem_union_left _ hc12_1)
    have hc13u : c13 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc13_3
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun g => g.1 ⟨w₁, hw₁u⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      apply Subtype.ext; funext ⟨w, hwu⟩
      have h_w1 : g₁.1 ⟨w₁, hw₁u⟩ = g₂.1 ⟨w₁, hw₁u⟩ := h
      have h_c12 : g₁.1 ⟨c12, hc12u⟩ = g₂.1 ⟨c12, hc12u⟩ := by
        rw [g₁.2 m₁ (by simp) c12 hc12_1 w₁ hw₁ hc12u hw₁u,
          g₂.2 m₁ (by simp) c12 hc12_1 w₁ hw₁ hc12u hw₁u, h_w1]
      have h_c13 : g₁.1 ⟨c13, hc13u⟩ = g₂.1 ⟨c13, hc13u⟩ := by
        rw [g₁.2 m₁ (by simp) c13 hc13_1 w₁ hw₁ hc13u hw₁u,
          g₂.2 m₁ (by simp) c13 hc13_1 w₁ hw₁ hc13u hw₁u, h_w1]
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u,
            g₂.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u, h_w1]
        · rw [g₁.2 m₂ (by simp) w h2u c12 hc12_2 hwu hc12u,
            g₂.2 m₂ (by simp) w h2u c12 hc12_2 hwu hc12u, h_c12]
      · rw [g₁.2 m₃ (by simp) w h3u c13 hc13_3 hwu hc13u,
          g₂.2 m₃ (by simp) w h3u c13 hc13_3 hwu hc13u, h_c13]
    have hK_le : Module.finrank ℝ K ≤ 2 := by
      simpa using LinearMap.finrank_le_finrank_of_injective hinj
    omega
  · -- hI12, hI13: connected (1 component via m₁)
    obtain ⟨c12, hc12⟩ := hI12
    obtain ⟨c13, hc13⟩ := hI13
    have hc12_1 := (Finset.mem_inter.mp hc12).1
    have hc12_2 := (Finset.mem_inter.mp hc12).2
    have hc13_1 := (Finset.mem_inter.mp hc13).1
    have hc13_3 := (Finset.mem_inter.mp hc13).2
    have hc12u : c12 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_left _ (Finset.mem_union_left _ hc12_1)
    have hc13u : c13 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc13_3
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun g => g.1 ⟨w₁, hw₁u⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      have h_w1 : g₁.1 ⟨w₁, hw₁u⟩ = g₂.1 ⟨w₁, hw₁u⟩ := h
      apply Subtype.ext; funext ⟨w, hwu⟩
      have h_c12 : g₁.1 ⟨c12, hc12u⟩ = g₂.1 ⟨c12, hc12u⟩ := by
        rw [g₁.2 m₁ (by simp) c12 hc12_1 w₁ hw₁ hc12u hw₁u,
          g₂.2 m₁ (by simp) c12 hc12_1 w₁ hw₁ hc12u hw₁u, h_w1]
      have h_c13 : g₁.1 ⟨c13, hc13u⟩ = g₂.1 ⟨c13, hc13u⟩ := by
        rw [g₁.2 m₁ (by simp) c13 hc13_1 w₁ hw₁ hc13u hw₁u,
          g₂.2 m₁ (by simp) c13 hc13_1 w₁ hw₁ hc13u hw₁u, h_w1]
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u,
            g₂.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u, h_w1]
        · rw [g₁.2 m₂ (by simp) w h2u c12 hc12_2 hwu hc12u,
            g₂.2 m₂ (by simp) w h2u c12 hc12_2 hwu hc12u, h_c12]
      · rw [g₁.2 m₃ (by simp) w h3u c13 hc13_3 hwu hc13u,
          g₂.2 m₃ (by simp) w h3u c13 hc13_3 hwu hc13u, h_c13]
    have hK_le : Module.finrank ℝ K ≤ 2 := by
      simpa using LinearMap.finrank_le_finrank_of_injective hinj
    omega
  · -- hI12, hI23: connected (1 component via m₂)
    obtain ⟨c12, hc12⟩ := hI12
    obtain ⟨c23, hc23⟩ := hI23
    have hc12_1 := (Finset.mem_inter.mp hc12).1
    have hc12_2 := (Finset.mem_inter.mp hc12).2
    have hc23_2 := (Finset.mem_inter.mp hc23).1
    have hc23_3 := (Finset.mem_inter.mp hc23).2
    have hc12u : c12 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_left _ (Finset.mem_union_left _ hc12_1)
    have hc23u : c23 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc23_3
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun g => g.1 ⟨w₂, hw₂u⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      have h_w2 : g₁.1 ⟨w₂, hw₂u⟩ = g₂.1 ⟨w₂, hw₂u⟩ := h
      apply Subtype.ext; funext ⟨w, hwu⟩
      have h_c12 : g₁.1 ⟨c12, hc12u⟩ = g₂.1 ⟨c12, hc12u⟩ := by
        rw [g₁.2 m₂ (by simp) c12 hc12_2 w₂ hw₂ hc12u hw₂u,
          g₂.2 m₂ (by simp) c12 hc12_2 w₂ hw₂ hc12u hw₂u, h_w2]
      have h_c23 : g₁.1 ⟨c23, hc23u⟩ = g₂.1 ⟨c23, hc23u⟩ := by
        rw [g₁.2 m₂ (by simp) c23 hc23_2 w₂ hw₂ hc23u hw₂u,
          g₂.2 m₂ (by simp) c23 hc23_2 w₂ hw₂ hc23u hw₂u, h_w2]
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u c12 hc12_1 hwu hc12u,
            g₂.2 m₁ (by simp) w h1u c12 hc12_1 hwu hc12u, h_c12]
        · rw [g₁.2 m₂ (by simp) w h2u w₂ hw₂ hwu hw₂u,
            g₂.2 m₂ (by simp) w h2u w₂ hw₂ hwu hw₂u, h_w2]
      · rw [g₁.2 m₃ (by simp) w h3u c23 hc23_3 hwu hc23u,
          g₂.2 m₃ (by simp) w h3u c23 hc23_3 hwu hc23u, h_c23]
    have hK_le : Module.finrank ℝ K ≤ 2 := by
      simpa using LinearMap.finrank_le_finrank_of_injective hinj
    omega
  · -- ONLY hI12: m₃ is disjoint from m₁ ∪ m₂
    rw [Finset.not_nonempty_iff_eq_empty] at hI13 hI23
    have hK_le : Module.finrank ℝ K ≤ 4 :=
      finrank_constOn_three_le_four_of_inter m₁ m₂ m₃ w₁ hw₁ w₂ hw₂ w₃ hw₃ hI12
    have h12_inter := distinct_sixMatchings_inter_card_le_four m₁ m₂ i₀ hm₁ hm₂ h12
    have h12_cards := Finset.card_union_add_card_inter m₁ m₂
    have hdisj : (m₁ ∪ m₂) ∩ m₃ = ∅ := by
      rw [Finset.union_inter_distrib_right, hI13, hI23, Finset.union_empty]
    have hu_cards := Finset.card_union_add_card_inter (m₁ ∪ m₂) m₃
    rw [hdisj, Finset.card_empty] at hu_cards
    have hm1c := hm₁.1; have hm2c := hm₂.1; have hm3c := hm₃.1
    have hu_ge : 14 ≤ (m₁ ∪ m₂ ∪ m₃).card := by omega
    omega
  · -- hI13, hI23: connected (1 component via m₃)
    obtain ⟨c13, hc13⟩ := hI13
    obtain ⟨c23, hc23⟩ := hI23
    have hc13_1 := (Finset.mem_inter.mp hc13).1
    have hc13_3 := (Finset.mem_inter.mp hc13).2
    have hc23_2 := (Finset.mem_inter.mp hc23).1
    have hc23_3 := (Finset.mem_inter.mp hc23).2
    have hc13u : c13 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc13_3
    have hc23u : c23 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc23_3
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun g => g.1 ⟨w₃, hw₃u⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      have h_w3 : g₁.1 ⟨w₃, hw₃u⟩ = g₂.1 ⟨w₃, hw₃u⟩ := h
      apply Subtype.ext; funext ⟨w, hwu⟩
      have h_c13 : g₁.1 ⟨c13, hc13u⟩ = g₂.1 ⟨c13, hc13u⟩ := by
        rw [g₁.2 m₃ (by simp) c13 hc13_3 w₃ hw₃ hc13u hw₃u,
          g₂.2 m₃ (by simp) c13 hc13_3 w₃ hw₃ hc13u hw₃u, h_w3]
      have h_c23 : g₁.1 ⟨c23, hc23u⟩ = g₂.1 ⟨c23, hc23u⟩ := by
        rw [g₁.2 m₃ (by simp) c23 hc23_3 w₃ hw₃ hc23u hw₃u,
          g₂.2 m₃ (by simp) c23 hc23_3 w₃ hw₃ hc23u hw₃u, h_w3]
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u c13 hc13_1 hwu hc13u,
            g₂.2 m₁ (by simp) w h1u c13 hc13_1 hwu hc13u, h_c13]
        · rw [g₁.2 m₂ (by simp) w h2u c23 hc23_2 hwu hc23u,
            g₂.2 m₂ (by simp) w h2u c23 hc23_2 hwu hc23u, h_c23]
      · rw [g₁.2 m₃ (by simp) w h3u w₃ hw₃ hwu hw₃u,
          g₂.2 m₃ (by simp) w h3u w₃ hw₃ hwu hw₃u, h_w3]
    have hK_le : Module.finrank ℝ K ≤ 2 := by
      simpa using LinearMap.finrank_le_finrank_of_injective hinj
    omega
  · -- ONLY hI13: m₂ is disjoint from m₁ ∪ m₃
    rw [Finset.not_nonempty_iff_eq_empty] at hI12 hI23
    obtain ⟨c13, hc13⟩ := hI13
    have hc13_1 := (Finset.mem_inter.mp hc13).1
    have hc13_3 := (Finset.mem_inter.mp hc13).2
    have hc13u : c13 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc13_3
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
      { toFun := fun g => (g.1 ⟨c13, hc13u⟩, g.1 ⟨w₂, hw₂u⟩)
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      rcases Prod.mk.inj h with ⟨hc_eq, h2_eq⟩
      apply Subtype.ext; funext ⟨w, hwu⟩
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u c13 hc13_1 hwu hc13u,
            g₂.2 m₁ (by simp) w h1u c13 hc13_1 hwu hc13u, hc_eq]
        · rw [g₁.2 m₂ (by simp) w h2u w₂ hw₂ hwu hw₂u,
            g₂.2 m₂ (by simp) w h2u w₂ hw₂ hwu hw₂u, h2_eq]
      · rw [g₁.2 m₃ (by simp) w h3u c13 hc13_3 hwu hc13u,
          g₂.2 m₃ (by simp) w h3u c13 hc13_3 hwu hc13u, hc_eq]
    have hK_le : Module.finrank ℝ K ≤ 4 := by
      have := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [Module.finrank_prod] using this
    have h13_inter := distinct_sixMatchings_inter_card_le_four m₁ m₃ i₀ hm₁ hm₃ h13
    have h12_cards := Finset.card_union_add_card_inter m₁ m₂
    rw [hI12, Finset.card_empty] at h12_cards
    have h123_inter : ((m₁ ∪ m₂) ∩ m₃).card ≤ 4 := by
      rw [Finset.union_inter_distrib_right, hI23, Finset.union_empty]
      exact h13_inter
    have hu_cards := Finset.card_union_add_card_inter (m₁ ∪ m₂) m₃
    have hm1c := hm₁.1; have hm2c := hm₂.1; have hm3c := hm₃.1
    omega
  · -- ONLY hI23: m₁ is disjoint from m₂ ∪ m₃
    rw [Finset.not_nonempty_iff_eq_empty] at hI12 hI13
    obtain ⟨c23, hc23⟩ := hI23
    have hc23_2 := (Finset.mem_inter.mp hc23).1
    have hc23_3 := (Finset.mem_inter.mp hc23).2
    have hc23u : c23 ∈ m₁ ∪ m₂ ∪ m₃ := Finset.mem_union_right _ hc23_3
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
      { toFun := fun g => (g.1 ⟨w₁, hw₁u⟩, g.1 ⟨c23, hc23u⟩)
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      rcases Prod.mk.inj h with ⟨h1_eq, hc_eq⟩
      apply Subtype.ext; funext ⟨w, hwu⟩
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u,
            g₂.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u, h1_eq]
        · rw [g₁.2 m₂ (by simp) w h2u c23 hc23_2 hwu hc23u,
            g₂.2 m₂ (by simp) w h2u c23 hc23_2 hwu hc23u, hc_eq]
      · rw [g₁.2 m₃ (by simp) w h3u c23 hc23_3 hwu hc23u,
          g₂.2 m₃ (by simp) w h3u c23 hc23_3 hwu hc23u, hc_eq]
    have hK_le : Module.finrank ℝ K ≤ 4 := by
      have := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [Module.finrank_prod] using this
    have h23_inter := distinct_sixMatchings_inter_card_le_four m₂ m₃ i₀ hm₂ hm₃ h23
    have h12_cards := Finset.card_union_add_card_inter m₁ m₂
    rw [hI12, Finset.card_empty] at h12_cards
    have h123_inter : ((m₁ ∪ m₂) ∩ m₃).card ≤ 4 := by
      rw [Finset.union_inter_distrib_right, hI13, Finset.empty_union]
      exact h23_inter
    have hu_cards := Finset.card_union_add_card_inter (m₁ ∪ m₂) m₃
    have hm1c := hm₁.1; have hm2c := hm₂.1; have hm3c := hm₃.1
    omega
  · -- pairwise disjoint
    rw [Finset.not_nonempty_iff_eq_empty] at hI12 hI13 hI23
    let proj : K →ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
      { toFun := fun g => (g.1 ⟨w₁, hw₁u⟩, g.1 ⟨w₂, hw₂u⟩, g.1 ⟨w₃, hw₃u⟩)
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := fun g₁ g₂ h => by
      rcases Prod.mk.inj h with ⟨h1_eq, h23_eq⟩
      rcases Prod.mk.inj h23_eq with ⟨h2_eq, h3_eq⟩
      apply Subtype.ext; funext ⟨w, hwu⟩
      rcases Finset.mem_union.mp hwu with (h12u | h3u)
      · rcases Finset.mem_union.mp h12u with (h1u | h2u)
        · rw [g₁.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u,
            g₂.2 m₁ (by simp) w h1u w₁ hw₁ hwu hw₁u, h1_eq]
        · rw [g₁.2 m₂ (by simp) w h2u w₂ hw₂ hwu hw₂u,
            g₂.2 m₂ (by simp) w h2u w₂ hw₂ hwu hw₂u, h2_eq]
      · rw [g₁.2 m₃ (by simp) w h3u w₃ hw₃ hwu hw₃u,
          g₂.2 m₃ (by simp) w h3u w₃ hw₃ hwu hw₃u, h3_eq]
    have hK_le : Module.finrank ℝ K ≤ 6 := by
      have := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [Module.finrank_prod] using this
    have h12_cards := Finset.card_union_add_card_inter m₁ m₂
    rw [hI12, Finset.card_empty] at h12_cards
    have hdisj : (m₁ ∪ m₂) ∩ m₃ = ∅ := by
      rw [Finset.union_inter_distrib_right, hI13, hI23, Finset.union_empty]
    have hu_cards := Finset.card_union_add_card_inter (m₁ ∪ m₂) m₃
    rw [hdisj, Finset.card_empty] at hu_cards
    have hm1c := hm₁.1; have hm2c := hm₂.1; have hm3c := hm₃.1
    omega

end MatchingCodimension

/-! ### 3. Ball homotopy extension via `DiskCylinderRetraction` -/

section HomotopyExtension

theorem homotopy_extension_ball_with_homotopy {d : ℕ} {X : Type*} [TopologicalSpace X]
    (g₀ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 → X) (hg₀ : Continuous g₀)
    (H : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → X) (hH : Continuous H)
    (hagree : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      H (0, x) = g₀ ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right,
        mem_sphere_zero_iff_norm.mp x.2]⟩) :
    ∃ G : unitInterval × Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 → X,
      Continuous G ∧
      (∀ x, G (0, x) = g₀ x) ∧
      (∀ (t : unitInterval) (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        G (t, ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right,
          mem_sphere_zero_iff_norm.mp x.2]⟩) = H (t, x)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let Cyl := unitInterval × Metric.closedBall (0 : E) 1
  let toEProd (p : Cyl) : E × ℝ := (p.2.1, (p.1 : ℝ))
  have hto_cont : Continuous toEProd :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)
  have hto_mem : ∀ p : Cyl, toEProd p ∈ closedDiskCylinder (E := E) := fun p => by
    refine ⟨?_, p.1.2.1, p.1.2.2⟩
    exact mem_closedBall_zero_iff.mp p.2.2
  let ret (p : Cyl) : E × ℝ := diskCylinderRetraction (toEProd p)
  have hret_cont : Continuous ret :=
    continuousOn_diskCylinderRetraction.comp_continuous hto_cont hto_mem
  have hret_mem : ∀ p : Cyl, ret p ∈ closedDiskCylinder (E := E) := fun p =>
    diskCylinderRetraction_mem (hto_mem p)
  let B0 : Set Cyl := {p | (ret p).2 = 0}
  let S1 : Set Cyl := {p | ‖(ret p).1‖ = 1}
  have hB0_closed : IsClosed B0 := isClosed_eq (continuous_snd.comp hret_cont) continuous_const
  have hS1_closed : IsClosed S1 :=
    isClosed_eq (continuous_norm.comp (continuous_fst.comp hret_cont)) continuous_const
  have hcover : B0 ∪ S1 = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true, B0, S1, Set.mem_ofPred_eq]
    exact diskCylinderRetraction_bottom_or_side (hto_mem p)
  let projBall (p : Cyl) : Metric.closedBall (0 : E) 1 :=
    ⟨(ret p).1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hret_mem p).1⟩
  have hprojBall_cont : Continuous projBall :=
    Continuous.subtype_mk (continuous_fst.comp hret_cont) _
  let projTime (p : Cyl) : unitInterval :=
    ⟨(ret p).2, (hret_mem p).2.1, (hret_mem p).2.2⟩
  have hprojTime_cont : Continuous projTime :=
    Continuous.subtype_mk (continuous_snd.comp hret_cont) _
  have hside_norm : ∀ p : Cyl, (ret p).2 ≠ 0 → ‖(ret p).1‖ = 1 := fun p hne =>
    (diskCylinderRetraction_bottom_or_side (hto_mem p)).resolve_left hne
  let G (p : Cyl) : X :=
    if h0 : (ret p).2 = 0 then g₀ (projBall p)
    else H (projTime p, ⟨(ret p).1, mem_sphere_zero_iff_norm.mpr (hside_norm p h0)⟩)
  have hG_on_B0 : ContinuousOn G B0 := by
    have hcont : ContinuousOn (fun p : Cyl => g₀ (projBall p)) B0 :=
      (hg₀.comp hprojBall_cont).continuousOn
    refine hcont.congr fun p hp => ?_
    have hp0 : (ret p).2 = 0 := hp
    simp [G, hp0]
  have hG_on_S1 : ContinuousOn G S1 := by
    let mapS1 (p : S1) : unitInterval × Metric.sphere (0 : E) 1 :=
      (projTime p.1, ⟨(ret p.1).1, mem_sphere_zero_iff_norm.mpr p.2⟩)
    have hmapS1_cont : Continuous mapS1 := by
      refine (hprojTime_cont.comp continuous_subtype_val).prodMk ?_
      exact Continuous.subtype_mk ((continuous_fst.comp hret_cont).comp continuous_subtype_val) _
    have hH_S1 : ContinuousOn (fun p : Cyl =>
        if h1 : ‖(ret p).1‖ = 1 then
          H (projTime p, ⟨(ret p).1, mem_sphere_zero_iff_norm.mpr h1⟩)
        else g₀ (projBall p)) S1 := by
      rw [continuousOn_iff_continuous_restrict]
      refine (hH.comp hmapS1_cont).congr fun p => ?_
      have hp1 : ‖(ret p.1).1‖ = 1 := p.2
      change H (projTime p.1, ⟨(ret p.1).1, mem_sphere_zero_iff_norm.mpr hp1⟩) =
        if h1 : ‖(ret p.1).1‖ = 1 then
          H (projTime p.1, ⟨(ret p.1).1, mem_sphere_zero_iff_norm.mpr h1⟩)
        else g₀ (projBall p.1)
      rw [dif_pos hp1]
    refine hH_S1.congr fun p hp => ?_
    have hp1 : ‖(ret p).1‖ = 1 := hp
    by_cases hp0 : (ret p).2 = 0
    · have ht0 : projTime p = 0 := Subtype.ext hp0
      simp only [G, hp0, hp1, ↓reduceDIte, ht0]
      exact (hagree ⟨(ret p).1, mem_sphere_zero_iff_norm.mpr hp1⟩).symm
    · simp [G, hp0, hp1]
  have hG_cont : Continuous G := by
    rw [← continuousOn_univ, ← hcover]
    exact hG_on_B0.union_of_isClosed hG_on_S1 hB0_closed hS1_closed
  refine ⟨G, hG_cont, ?_, ?_⟩
  · intro x
    have hret0 : ret (0, x) = (x.1, 0) :=
      diskCylinderRetraction_fixes_bottom x.1 (mem_closedBall_zero_iff.mp x.2)
    have h2 : (ret (0, x)).2 = 0 := by rw [hret0]
    have hball : projBall (0, x) = x := by
      apply Subtype.ext
      change (ret (0, x)).1 = x.1
      rw [hret0]
    simp [G, h2, hball]
  · intro t x
    let xb : Metric.closedBall (0 : E) 1 :=
      ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.mp x.2]⟩
    have hret_side : ret (t, xb) = (x.1, (t : ℝ)) :=
      diskCylinderRetraction_fixes_side x.1 (t : ℝ) (mem_sphere_zero_iff_norm.mp x.2) t.2.1
    change G (t, xb) = H (t, x)
    by_cases ht0 : (t : ℝ) = 0
    · have h2 : (ret (t, xb)).2 = 0 := by rw [hret_side]; exact ht0
      have hball : projBall (t, xb) = xb := by
        apply Subtype.ext; change (ret (t, xb)).1 = x.1; rw [hret_side]
      have ht_eq : t = 0 := Subtype.ext ht0
      dsimp only [G]
      rw [dif_pos h2, hball, ht_eq]
      exact (hagree x).symm
    · have h2 : (ret (t, xb)).2 ≠ 0 := by rw [hret_side]; exact ht0
      have htime : projTime (t, xb) = t := by
        apply Subtype.ext; change (ret (t, xb)).2 = (t : ℝ); rw [hret_side]
      have hsph : (⟨(ret (t, xb)).1, mem_sphere_zero_iff_norm.mpr (hside_norm (t, xb) h2)⟩ :
          Metric.sphere (0 : E) 1) = x := by
        apply Subtype.ext; change (ret (t, xb)).1 = x.1; rw [hret_side]
      dsimp only [G]
      rw [dif_neg h2, htime, hsph]

theorem homotopy_extension_ball {d : ℕ} {X : Type*} [TopologicalSpace X]
    (g₀ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 → X) (hg₀ : Continuous g₀)
    (H : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → X) (hH : Continuous H)
    (hagree : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      H (0, x) = g₀ ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right,
        mem_sphere_zero_iff_norm.mp x.2]⟩) :
    ∃ g₁ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 → X,
      Continuous g₁ ∧
      ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        g₁ ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right,
          mem_sphere_zero_iff_norm.mp x.2]⟩ = H (1, x) := by
  obtain ⟨G, hG_cont, _, hG_side⟩ :=
    homotopy_extension_ball_with_homotopy g₀ hg₀ H hH hagree
  exact ⟨fun x => G (1, x), hG_cont.comp (continuous_const.prodMk continuous_id),
    fun x => hG_side 1 x⟩

end HomotopyExtension

/-! ### 4. Kuhn PL approximation and extension in the complement of subspaces of codim `≥ d + 1` -/

section KuhnPLExtension

def foldMin {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  Finset.univ.fold min 1 a

def foldMax {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  Finset.univ.fold max 0 a

lemma foldMin_le_one {d : ℕ} (a : Fin d → ℝ) : foldMin a ≤ 1 := by
  simpa [foldMin] using (Finset.fold_min_le (s := (Finset.univ : Finset (Fin d)))
    (b := (1 : ℝ)) (f := a) (c := 1)).mpr (Or.inl le_rfl)

lemma foldMin_le_apply {d : ℕ} (a : Fin d → ℝ) (i : Fin d) : foldMin a ≤ a i := by
  simpa [foldMin] using (Finset.fold_min_le (s := (Finset.univ : Finset (Fin d)))
    (b := (1 : ℝ)) (f := a) (c := a i)).mpr (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)

lemma le_foldMin_iff {d : ℕ} {a : Fin d → ℝ} {c : ℝ} :
    c ≤ foldMin a ↔ c ≤ 1 ∧ ∀ i : Fin d, c ≤ a i := by
  simpa [foldMin] using (Finset.le_fold_min (s := (Finset.univ : Finset (Fin d)))
    (b := (1 : ℝ)) (f := a) (c := c))

lemma zero_le_foldMax {d : ℕ} (a : Fin d → ℝ) : 0 ≤ foldMax a := by
  simpa [foldMax] using (Finset.le_fold_max (s := (Finset.univ : Finset (Fin d)))
    (b := (0 : ℝ)) (f := a) (c := 0)).mpr (Or.inl le_rfl)

lemma apply_le_foldMax {d : ℕ} (a : Fin d → ℝ) (i : Fin d) : a i ≤ foldMax a := by
  simpa [foldMax] using (Finset.le_fold_max (s := (Finset.univ : Finset (Fin d)))
    (b := (0 : ℝ)) (f := a) (c := a i)).mpr (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)

lemma foldMax_le_iff {d : ℕ} {a : Fin d → ℝ} {c : ℝ} :
    foldMax a ≤ c ↔ 0 ≤ c ∧ ∀ i : Fin d, a i ≤ c := by
  simpa [foldMax] using (Finset.fold_max_le (s := (Finset.univ : Finset (Fin d)))
    (b := (0 : ℝ)) (f := a) (c := c))

lemma continuous_fold_min {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    (s : Finset ι) (b : ℝ) (f : ι → X → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => s.fold min b (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | @insert a s ha ih =>
    simp_rw [Finset.fold_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).min
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma continuous_fold_max {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    (s : Finset ι) (b : ℝ) (f : ι → X → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => s.fold max b (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | @insert a s ha ih =>
    simp_rw [Finset.fold_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).max
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

def kuhnUpper {d : ℕ} (N : ℕ) (v : Fin d → Fin (N + 1)) (x : UnitCube d) : ℝ :=
  foldMin (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ))

def kuhnLower {d : ℕ} (N : ℕ) (v : Fin d → Fin (N + 1)) (x : UnitCube d) : ℝ :=
  foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ))

def kuhnWeight {d : ℕ} (N : ℕ) (v : Fin d → Fin (N + 1)) (x : UnitCube d) : ℝ :=
  max 0 (kuhnUpper N v x - kuhnLower N v x)

lemma kuhnWeight_nonneg {d : ℕ} (N : ℕ) (v : Fin d → Fin (N + 1)) (x : UnitCube d) :
    0 ≤ kuhnWeight N v x :=
  le_max_left 0 _

lemma continuous_kuhnWeight {d : ℕ} (N : ℕ) (v : Fin d → Fin (N + 1)) :
    Continuous (kuhnWeight N v) := by
  have hup : Continuous (kuhnUpper N v) := by
    refine continuous_fold_min (Finset.univ : Finset (Fin d)) 1
      (fun (j : Fin d) (x : UnitCube d) => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) fun j _ => ?_
    exact (continuous_const.add (continuous_const.mul ((continuous_apply j).comp continuous_subtype_val))).sub
      continuous_const
  have hlo : Continuous (kuhnLower N v) := by
    refine continuous_fold_max (Finset.univ : Finset (Fin d)) 0
      (fun (j : Fin d) (x : UnitCube d) => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) fun j _ => ?_
    exact (continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)).sub continuous_const
  exact continuous_const.max (hup.sub hlo)

def gridPoint {d : ℕ} {N : ℕ} (hN : 0 < N) (v : Fin d → Fin (N + 1)) : UnitCube d :=
  ⟨fun j => ((v j : ℕ) : ℝ) / (N : ℝ), fun j => by
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hv_le : ((v j : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (v j).isLt
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNpos.le, (div_le_one hNpos).mpr hv_le⟩⟩

lemma gridPoint_mem_boundary_of_active {d : ℕ} {N : ℕ} (hN : 0 < N)
    {v : Fin d → Fin (N + 1)} {x : UnitCube d}
    (hx : ∃ j : Fin d, x.1 j = 0 ∨ x.1 j = 1) (hw : 0 < kuhnWeight N v x) :
    ∃ j : Fin d, (gridPoint hN v).1 j = 0 ∨ (gridPoint hN v).1 j = 1 := by
  rcases hx with ⟨j, hj0 | hj1⟩
  · refine ⟨j, Or.inl ?_⟩
    have hup_lo : kuhnLower N v x < kuhnUpper N v x := by
      simp only [kuhnWeight] at hw
      linarith [lt_max_iff.mp hw |>.resolve_left (lt_irrefl 0)]
    have h0_le : 0 ≤ kuhnLower N v x := zero_le_foldMax _
    have hup_le : kuhnUpper N v x ≤ 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) :=
      foldMin_le_apply _ j
    rw [hj0, mul_zero, add_zero] at hup_le
    have hv_lt : ((v j : ℕ) : ℝ) < 1 := by linarith
    have hv_zero : (v j : ℕ) = 0 := by
      have : (v j : ℕ) < 1 := by exact_mod_cast hv_lt
      omega
    change ((v j : ℕ) : ℝ) / (N : ℝ) = 0
    rw [hv_zero, Nat.cast_zero, zero_div]
  · refine ⟨j, Or.inr ?_⟩
    have hup_lo : kuhnLower N v x < kuhnUpper N v x := by
      simp only [kuhnWeight] at hw
      linarith [lt_max_iff.mp hw |>.resolve_left (lt_irrefl 0)]
    have hup_le1 : kuhnUpper N v x ≤ 1 := foldMin_le_one _
    have hlo_ge : (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) ≤ kuhnLower N v x :=
      apply_le_foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) j
    rw [hj1, mul_one] at hlo_ge
    have hv_gt : (N : ℝ) - 1 < ((v j : ℕ) : ℝ) := by linarith
    have hv_eq : (v j : ℕ) = N := by
      have h1 : N < (v j : ℕ) + 1 := by
        have : (N : ℝ) < ((v j : ℕ) : ℝ) + 1 := by linarith
        exact_mod_cast this
      have h2 := (v j).isLt
      omega
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    change ((v j : ℕ) : ℝ) / (N : ℝ) = 1
    rw [hv_eq, div_self hN_ne]

lemma dist_gridPoint_le_of_active {d : ℕ} {N : ℕ} (hN : 0 < N)
    {v : Fin d → Fin (N + 1)} {x : UnitCube d} (hw : 0 < kuhnWeight N v x) :
    dist (gridPoint hN v) x ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hup_lo : kuhnLower N v x < kuhnUpper N v x := by
    simp only [kuhnWeight] at hw
    linarith [lt_max_iff.mp hw |>.resolve_left (lt_irrefl 0)]
  have h0_le : 0 ≤ kuhnLower N v x := zero_le_foldMax _
  have hup_le1 : kuhnUpper N v x ≤ 1 := foldMin_le_one _
  change ‖(gridPoint hN v).1 - x.1‖ ≤ 1 / (N : ℝ)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  have hlo_j : (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) ≤ kuhnLower N v x :=
    apply_le_foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) j
  have hup_j : kuhnUpper N v x ≤ 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) :=
    foldMin_le_apply (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) j
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  change -(1 / (N : ℝ)) ≤ ((v j : ℕ) : ℝ) / (N : ℝ) - x.1 j ∧
    ((v j : ℕ) : ℝ) / (N : ℝ) - x.1 j ≤ 1 / (N : ℝ)
  have h1 : -1 ≤ ((v j : ℕ) : ℝ) - (N : ℝ) * x.1 j := by linarith
  have h2 : ((v j : ℕ) : ℝ) - (N : ℝ) * x.1 j ≤ 1 := by linarith
  have hdiv : ((v j : ℕ) : ℝ) / (N : ℝ) - x.1 j =
      (((v j : ℕ) : ℝ) - (N : ℝ) * x.1 j) / (N : ℝ) := by
    field_simp [hNpos.ne']
  rw [hdiv, ← neg_div, div_le_div_iff_of_pos_right hNpos, div_le_div_iff_of_pos_right hNpos]
  exact ⟨h1, h2⟩

def baseCellCoord {d : ℕ} (N : ℕ) (x : UnitCube d) (j : Fin d) : ℕ :=
  min (N - 1) ⌊(N : ℝ) * x.1 j⌋₊

lemma baseCellCoord_bounds {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d) (j : Fin d) :
    baseCellCoord N x j + 1 ≤ N ∧
    ((baseCellCoord N x j : ℕ) : ℝ) ≤ (N : ℝ) * x.1 j ∧
    (N : ℝ) * x.1 j ≤ ((baseCellCoord N x j : ℕ) : ℝ) + 1 := by
  have h1 : baseCellCoord N x j ≤ N - 1 := min_le_left _ _
  have h1' : baseCellCoord N x j + 1 ≤ N := by omega
  have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hxj0 : 0 ≤ (N : ℝ) * x.1 j := mul_nonneg hNpos (x.2 j).1
  have hxjN : (N : ℝ) * x.1 j ≤ (N : ℝ) := by
    calc (N : ℝ) * x.1 j ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left (x.2 j).2 hNpos
      _ = (N : ℝ) := mul_one _
  refine ⟨h1', ?_, ?_⟩
  · rcases le_total (N - 1) ⌊(N : ℝ) * x.1 j⌋₊ with hle | hle
    · have heq : baseCellCoord N x j = N - 1 := min_eq_left hle
      rw [heq]
      have hleR : ((N - 1 : ℕ) : ℝ) ≤ ((⌊(N : ℝ) * x.1 j⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr hle
      exact hleR.trans (Nat.floor_le hxj0)
    · have heq : baseCellCoord N x j = ⌊(N : ℝ) * x.1 j⌋₊ := min_eq_right hle
      rw [heq]
      exact Nat.floor_le hxj0
  · rcases le_total (N - 1) ⌊(N : ℝ) * x.1 j⌋₊ with hle | hle
    · have heq : baseCellCoord N x j = N - 1 := min_eq_left hle
      rw [heq]
      have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        exact_mod_cast (show (N - 1) + 1 = N by omega)
      linarith
    · have heq : baseCellCoord N x j = ⌊(N : ℝ) * x.1 j⌋₊ := min_eq_right hle
      rw [heq]
      exact (Nat.lt_floor_add_one _).le

def kuhnChainVertex {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d)
    (σ : Equiv.Perm (Fin d)) (r : Fin (d + 1)) (j : Fin d) : Fin (N + 1) :=
  ⟨baseCellCoord N x j + (if r.1 ≤ (σ⁻¹ j).1 then 1 else 0), by
    have hb := (baseCellCoord_bounds hN x j).1
    split_ifs <;> omega⟩

lemma kuhnChainVertex_injective {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d)
    (σ : Equiv.Perm (Fin d)) :
    Function.Injective (kuhnChainVertex hN x σ) := by
  intro r₁ r₂ heq
  by_contra hne
  have hval_ne : r₁.1 ≠ r₂.1 := Fin.val_injective.ne hne
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · let i : Fin d := ⟨r₁.1, by have := r₂.isLt; omega⟩
    have hval := congrArg Fin.val (congrFun heq (σ i))
    have hinv : (σ.symm (σ i)).1 = r₁.1 := by simp [i]
    dsimp [kuhnChainVertex] at hval
    have h1 : r₁.1 ≤ (σ.symm (σ i)).1 := by omega
    have h2 : ¬ r₂.1 ≤ (σ.symm (σ i)).1 := by omega
    rw [if_pos h1, if_neg h2] at hval
    omega
  · let i : Fin d := ⟨r₂.1, by have := r₁.isLt; omega⟩
    have hval := congrArg Fin.val (congrFun heq (σ i))
    have hinv : (σ.symm (σ i)).1 = r₂.1 := by simp [i]
    dsimp [kuhnChainVertex] at hval
    have h1 : ¬ r₁.1 ≤ (σ.symm (σ i)).1 := by omega
    have h2 : r₂.1 ≤ (σ.symm (σ i)).1 := by omega
    rw [if_neg h1, if_pos h2] at hval
    omega

lemma kuhnWeight_eq_zero_of_not_mem_chain {d : ℕ} {N : ℕ} (hN : 0 < N)
    (x : UnitCube d) (v : Fin d → Fin (N + 1))
    (hnot : ∀ r : Fin (d + 1),
      v ≠ kuhnChainVertex hN x (Tuple.sort (fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ))) r) :
    kuhnWeight N v x = 0 := by
  let k := baseCellCoord N x
  let f : Fin d → ℝ := fun j => (N : ℝ) * x.1 j - (k j : ℝ)
  let σ : Equiv.Perm (Fin d) := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hf_bounds : ∀ j, 0 ≤ f j ∧ f j ≤ 1 := fun j => by
    have hb := baseCellCoord_bounds hN x j
    exact ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
  by_contra hpos
  have hw_pos : 0 < kuhnWeight N v x :=
    lt_of_le_of_ne (kuhnWeight_nonneg N v x) (Ne.symm hpos)
  have hup_lo : kuhnLower N v x < kuhnUpper N v x := by
    simp only [kuhnWeight] at hw_pos
    linarith [lt_max_iff.mp hw_pos |>.resolve_left (lt_irrefl 0)]
  have h0_le_lo : 0 ≤ kuhnLower N v x := zero_le_foldMax _
  have hup_le_1 : kuhnUpper N v x ≤ 1 := foldMin_le_one _
  have hv_in_cell : ∀ j : Fin d, (v j : ℕ) = k j ∨ (v j : ℕ) = k j + 1 := fun j => by
    have hlo_j : (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) ≤ kuhnLower N v x :=
      apply_le_foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) j
    have hup_j : kuhnUpper N v x ≤ 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) :=
      foldMin_le_apply (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) j
    have hfj := hf_bounds j
    have h1 : ((k j : ℕ) : ℝ) - 1 < ((v j : ℕ) : ℝ) := by linarith
    have h2 : ((v j : ℕ) : ℝ) < ((k j : ℕ) : ℝ) + 2 := by linarith
    have h1' : k j < (v j : ℕ) + 1 := by
      have : ((k j : ℕ) : ℝ) < ((v j : ℕ) : ℝ) + 1 := by linarith
      exact_mod_cast this
    have h2' : (v j : ℕ) < k j + 2 := by exact_mod_cast h2
    omega
  have horder : ∀ i₁ i₂ : Fin d,
      (v (σ i₁) : ℕ) = k (σ i₁) + 1 → (v (σ i₂) : ℕ) = k (σ i₂) → i₂.1 < i₁.1 := by
    intro i₁ i₂ hv1 hv2
    have hup1 : kuhnUpper N v x ≤ f (σ i₁) := by
      have := foldMin_le_apply (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) (σ i₁)
      have hcast : ((v (σ i₁) : ℕ) : ℝ) = ((k (σ i₁) : ℕ) : ℝ) + 1 := by exact_mod_cast hv1
      dsimp [kuhnUpper, f] at this ⊢
      linarith
    have hlo2 : f (σ i₂) ≤ kuhnLower N v x := by
      have := apply_le_foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) (σ i₂)
      have hcast : ((v (σ i₂) : ℕ) : ℝ) = ((k (σ i₂) : ℕ) : ℝ) := by exact_mod_cast hv2
      dsimp [kuhnLower, f] at this ⊢
      linarith
    have hlt_f : f (σ i₂) < f (σ i₁) := by linarith
    by_contra hge
    have hle_i : i₁ ≤ i₂ := Fin.le_def.mpr (not_lt.mp hge)
    have hle_f : f (σ i₁) ≤ f (σ i₂) := hmono hle_i
    linarith
  by_cases hex : ∃ n < d, ∃ hn : n < d, (v (σ ⟨n, hn⟩) : ℕ) = k (σ ⟨n, hn⟩) + 1
  · let r₀ := Nat.find hex
    obtain ⟨hr₀_lt, hr₀_lt', hvr₀⟩ := Nat.find_spec hex
    apply hnot ⟨r₀, Nat.lt_succ_of_lt hr₀_lt⟩
    ext j
    let i := σ⁻¹ j
    have hij : σ i = j := Equiv.apply_symm_apply σ j
    change (v j : ℕ) = k j + (if r₀ ≤ i.1 then 1 else 0)
    by_cases hle : r₀ ≤ i.1
    · rw [if_pos hle, ← hij]
      rcases hv_in_cell (σ i) with hv0 | hv1
      · exfalso
        have hlt : i.1 < r₀ := horder ⟨r₀, hr₀_lt'⟩ i hvr₀ hv0
        omega
      · exact hv1
    · rw [if_neg hle, add_zero, ← hij]
      have hlt : i.1 < r₀ := Nat.lt_of_not_le hle
      have hmin := Nat.find_min hex hlt
      rcases hv_in_cell (σ i) with hv0 | hv1
      · exact hv0
      · exfalso; exact hmin ⟨i.isLt, i.isLt, hv1⟩
  · push_neg at hex
    apply hnot ⟨d, Nat.lt_succ_self d⟩
    ext j
    let i := σ⁻¹ j
    have hij : σ i = j := Equiv.apply_symm_apply σ j
    change (v j : ℕ) = k j + (if d ≤ i.1 then 1 else 0)
    rw [if_neg (not_le.mpr i.isLt), add_zero, ← hij]
    exact (hv_in_cell (σ i)).resolve_right (hex i.1 i.isLt i.isLt)

def kuhnCutpoint {d : ℕ} (N : ℕ) (x : UnitCube d) (m : ℕ) : ℝ :=
  let f : Fin d → ℝ := fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ)
  let σ : Equiv.Perm (Fin d) := Tuple.sort f
  if m = 0 then 0
  else if hd : m - 1 < d then f (σ ⟨m - 1, hd⟩)
  else 1

lemma kuhnUpper_chainVertex {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d)
    (r : Fin (d + 1)) :
    kuhnUpper N
      (kuhnChainVertex hN x
        (Tuple.sort (fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ))) r) x =
      kuhnCutpoint N x (r.1 + 1) := by
  let k := baseCellCoord N x
  let f : Fin d → ℝ := fun j => (N : ℝ) * x.1 j - (k j : ℝ)
  let σ : Equiv.Perm (Fin d) := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hf_bounds : ∀ j, 0 ≤ f j ∧ f j ≤ 1 := fun j => by
    have hb := baseCellCoord_bounds hN x j
    exact ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
  let v := kuhnChainVertex hN x σ r
  have hterm : ∀ j : Fin d,
      1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) =
        if r.1 ≤ (σ⁻¹ j).1 then f j else 1 + f j := fun j => by
    change 1 + (N : ℝ) * x.1 j - ((k j + (if r.1 ≤ (σ⁻¹ j).1 then 1 else 0) : ℕ) : ℝ) = _
    split_ifs <;> push_cast <;> dsimp [f] <;> ring
  by_cases hrd : r.1 < d
  · have hcut : kuhnCutpoint N x (r.1 + 1) = f (σ ⟨r.1, hrd⟩) := by
      simp [kuhnCutpoint, hrd, f, σ, k]
    rw [hcut]
    apply le_antisymm
    · have h1 := foldMin_le_apply (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) (σ ⟨r.1, hrd⟩)
      rw [hterm (σ ⟨r.1, hrd⟩)] at h1
      have hinv : r.1 ≤ (σ⁻¹ (σ ⟨r.1, hrd⟩)).1 := by simp
      rw [if_pos hinv] at h1
      exact h1
    · change f (σ ⟨r.1, hrd⟩) ≤ foldMin (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ))
      rw [le_foldMin_iff]
      refine ⟨(hf_bounds (σ ⟨r.1, hrd⟩)).2, fun j => ?_⟩
      rw [hterm j]
      split_ifs with hle
      · have hle' : (⟨r.1, hrd⟩ : Fin d) ≤ σ⁻¹ j := Fin.le_def.mpr hle
        have hm := hmono hle'
        simpa [Function.comp] using hm
      · linarith [(hf_bounds (σ ⟨r.1, hrd⟩)).2, (hf_bounds j).1]
  · have hr_eq : r.1 = d := by have := r.isLt; omega
    have hcut : kuhnCutpoint N x (r.1 + 1) = 1 := by
      simp [kuhnCutpoint, hr_eq]
    rw [hcut]
    apply le_antisymm (foldMin_le_one _)
    change (1 : ℝ) ≤ foldMin (fun j => 1 + (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ))
    rw [le_foldMin_iff]
    refine ⟨le_rfl, fun j => ?_⟩
    rw [hterm j, hr_eq, if_neg (not_le.mpr (σ⁻¹ j).isLt)]
    linarith [(hf_bounds j).1]

lemma kuhnLower_chainVertex {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d)
    (r : Fin (d + 1)) :
    kuhnLower N
      (kuhnChainVertex hN x
        (Tuple.sort (fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ))) r) x =
      kuhnCutpoint N x r.1 := by
  let k := baseCellCoord N x
  let f : Fin d → ℝ := fun j => (N : ℝ) * x.1 j - (k j : ℝ)
  let σ : Equiv.Perm (Fin d) := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hf_bounds : ∀ j, 0 ≤ f j ∧ f j ≤ 1 := fun j => by
    have hb := baseCellCoord_bounds hN x j
    exact ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
  let v := kuhnChainVertex hN x σ r
  have hterm : ∀ j : Fin d,
      (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ) =
        if r.1 ≤ (σ⁻¹ j).1 then f j - 1 else f j := fun j => by
    change (N : ℝ) * x.1 j - ((k j + (if r.1 ≤ (σ⁻¹ j).1 then 1 else 0) : ℕ) : ℝ) = _
    split_ifs <;> push_cast <;> dsimp [f] <;> ring
  by_cases hr0 : r.1 = 0
  · have hcut : kuhnCutpoint N x r.1 = 0 := by simp [kuhnCutpoint, hr0]
    rw [hcut]
    apply le_antisymm _ (zero_le_foldMax _)
    change foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) ≤ 0
    rw [foldMax_le_iff]
    refine ⟨le_rfl, fun j => ?_⟩
    rw [hterm j, hr0, if_pos (Nat.zero_le _)]
    linarith [(hf_bounds j).2]
  · have hprev : r.1 - 1 < d := by have := r.isLt; omega
    have hcut : kuhnCutpoint N x r.1 = f (σ ⟨r.1 - 1, hprev⟩) := by
      simp [kuhnCutpoint, hr0, hprev, f, σ, k]
    rw [hcut]
    apply le_antisymm
    · change foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) ≤ f (σ ⟨r.1 - 1, hprev⟩)
      rw [foldMax_le_iff]
      refine ⟨(hf_bounds (σ ⟨r.1 - 1, hprev⟩)).1, fun j => ?_⟩
      rw [hterm j]
      split_ifs with hle
      · linarith [(hf_bounds j).2, (hf_bounds (σ ⟨r.1 - 1, hprev⟩)).1]
      · have hle' : σ⁻¹ j ≤ (⟨r.1 - 1, hprev⟩ : Fin d) := by
          rw [Fin.le_def]
          change (σ⁻¹ j).1 ≤ r.1 - 1
          omega
        have hm := hmono hle'
        simpa [Function.comp] using hm
    · have h1 := apply_le_foldMax (fun j => (N : ℝ) * x.1 j - ((v j : ℕ) : ℝ)) (σ ⟨r.1 - 1, hprev⟩)
      rw [hterm (σ ⟨r.1 - 1, hprev⟩)] at h1
      have hinv : ¬ r.1 ≤ (σ⁻¹ (σ ⟨r.1 - 1, hprev⟩)).1 := by
        have hval : (σ⁻¹ (σ ⟨r.1 - 1, hprev⟩)).1 = r.1 - 1 := by simp
        omega
      rw [if_neg hinv] at h1
      exact h1

lemma kuhnCutpoint_le_succ {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d) (r : Fin (d + 1)) :
    kuhnCutpoint N x r.1 ≤ kuhnCutpoint N x (r.1 + 1) := by
  let k := baseCellCoord N x
  let f : Fin d → ℝ := fun j => (N : ℝ) * x.1 j - (k j : ℝ)
  let σ : Equiv.Perm (Fin d) := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hf_bounds : ∀ j, 0 ≤ f j ∧ f j ≤ 1 := fun j => by
    have hb := baseCellCoord_bounds hN x j
    exact ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
  by_cases hr0 : r.1 = 0
  · by_cases hd : 0 < d
    · simp only [kuhnCutpoint, hr0, ↓reduceIte, zero_add,
        Nat.one_ne_zero, hd, ↓reduceDIte]
      exact (hf_bounds _).1
    · have hd0 : d = 0 := by omega
      simp [kuhnCutpoint, hr0, hd0]
  · have hprev : r.1 - 1 < d := by have := r.isLt; omega
    by_cases hrd : r.1 < d
    · simp only [kuhnCutpoint, hr0, ↓reduceIte, hprev, ↓reduceDIte,
        Nat.add_one_ne_zero, add_tsub_cancel_right, hrd]
      refine hmono ?_
      rw [Fin.le_def]
      change r.1 - 1 ≤ r.1
      omega
    · simp only [kuhnCutpoint, hr0, ↓reduceIte, hprev, ↓reduceDIte,
        Nat.add_one_ne_zero, add_tsub_cancel_right, hrd]
      exact (hf_bounds _).2

lemma kuhnWeight_chainVertex {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d)
    (r : Fin (d + 1)) :
    kuhnWeight N
      (kuhnChainVertex hN x
        (Tuple.sort (fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ))) r) x =
      kuhnCutpoint N x (r.1 + 1) - kuhnCutpoint N x r.1 := by
  rw [kuhnWeight, kuhnUpper_chainVertex hN x r, kuhnLower_chainVertex hN x r,
    max_eq_right (sub_nonneg.mpr (kuhnCutpoint_le_succ hN x r))]

lemma sum_kuhnWeight_eq_one {d : ℕ} {N : ℕ} (hN : 0 < N) (x : UnitCube d) :
    ∑ v : Fin d → Fin (N + 1), kuhnWeight N v x = 1 := by
  let σ := Tuple.sort (fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ))
  let chainSet : Finset (Fin d → Fin (N + 1)) := Finset.univ.image (kuhnChainVertex hN x σ)
  have hsub : (∑ v : Fin d → Fin (N + 1), kuhnWeight N v x) =
      ∑ v ∈ chainSet, kuhnWeight N v x := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
    refine kuhnWeight_eq_zero_of_not_mem_chain hN x v fun r hr => hv ?_
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr.symm⟩
  rw [hsub, Finset.sum_image (fun r₁ _ r₂ _ h => kuhnChainVertex_injective hN x σ h)]
  have hterm_eq : ∀ r : Fin (d + 1),
      kuhnWeight N (kuhnChainVertex hN x σ r) x =
        kuhnCutpoint N x (r.1 + 1) - kuhnCutpoint N x r.1 :=
    fun r => kuhnWeight_chainVertex hN x r
  simp_rw [hterm_eq]
  rw [Fin.sum_univ_eq_sum_range (fun m => kuhnCutpoint N x (m + 1) - kuhnCutpoint N x m) (d + 1),
    Finset.sum_range_sub (fun m => kuhnCutpoint N x m) (d + 1)]
  have h0 : kuhnCutpoint N x 0 = 0 := by simp [kuhnCutpoint]
  have hd : kuhnCutpoint N x (d + 1) = 1 := by
    dsimp [kuhnCutpoint]
    exact dif_neg (Nat.lt_irrefl d)
  rw [h0, hd, sub_zero]

lemma finrank_sup_span_image_le {E V : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq V]
    (L : Submodule ℝ E) (val : V → E) (B : Finset V) :
    Module.finrank ℝ ↥(L ⊔ Submodule.span ℝ ((B.image val : Finset E) : Set E)) ≤
      Module.finrank ℝ L + B.card := by
  induction B using Finset.induction_on with
  | empty =>
    rw [Finset.image_empty, Finset.coe_empty, Submodule.span_empty, sup_bot_eq,
      Finset.card_empty, add_zero]
  | @insert b B hb ih =>
    have hsup : L ⊔ Submodule.span ℝ (((insert b B).image val : Finset E) : Set E) =
        (L ⊔ Submodule.span ℝ ((B.image val : Finset E) : Set E)) ⊔ (ℝ ∙ val b) := by
      rw [Finset.image_insert, Finset.coe_insert, Submodule.span_insert, sup_assoc,
        sup_comm (ℝ ∙ val b), ← sup_assoc]
    rw [hsup]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (L ⊔ Submodule.span ℝ ((B.image val : Finset E) : Set E)) (ℝ ∙ val b)
    have h2 : Module.finrank ℝ ↥(ℝ ∙ val b) ≤ 1 := by
      by_cases hv : val b = 0
      · rw [hv, Submodule.span_zero_singleton, finrank_bot]
        omega
      · rw [finrank_span_singleton hv]
    rw [Finset.card_insert_of_notMem hb]
    omega

theorem exists_general_position_vertex_table {V E ι : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (d : ℕ) (L : ι → Submodule ℝ E)
    (hcodim : ∀ i : ι, d + 1 ≤ Module.finrank ℝ (E ⧸ L i))
    (S : Finset V) (val₀ : V → E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ val : V → E,
      (∀ v : V, ‖val v - val₀ v‖ < δ) ∧
      ∀ B ⊆ S, B.card ≤ d + 1 → ∀ i : ι, ∀ w : V → ℝ,
        ∑ b ∈ B, w b = 1 → (∑ b ∈ B, w b • val b) ∉ L i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨val₀, fun v => by simp [hδ], fun B hB _ i w hw => ?_⟩
    rw [Finset.subset_empty.mp hB, Finset.sum_empty] at hw
    norm_num at hw
  | @insert v₀ S hv₀ ih =>
    obtain ⟨val, hval_close, hval_gp⟩ := ih
    let idxSet : Finset (ι × Finset V) :=
      Finset.univ ×ˢ (S.powerset.filter (fun B => B.card ≤ d))
    let W : ι × Finset V → Submodule ℝ E := fun p =>
      L p.1 ⊔ Submodule.span ℝ ((p.2.image val : Finset E) : Set E)
    have hW_proper : ∀ p ∈ idxSet, W p ≠ ⊤ := by
      intro p hp htop
      have hcard : p.2.card ≤ d := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
      have hle := finrank_sup_span_image_le (L p.1) val p.2
      change Module.finrank ℝ ↥(W p) ≤ Module.finrank ℝ (L p.1) + p.2.card at hle
      rw [htop, finrank_top] at hle
      have hq := (L p.1).finrank_quotient_add_finrank
      have hc := hcodim p.1
      omega
    obtain ⟨u, hu⟩ := exists_notMem_biUnion_proper_subspaces idxSet W hW_proper
    let bad : ι × Finset V → Finset ℝ := fun p =>
      if h : ∃ c : ℝ, val₀ v₀ + c • u ∈ W p then {h.choose} else ∅
    let BadScalars : Finset ℝ := idxSet.biUnion bad
    let Nmax : ℕ := (BadScalars.image (fun r : ℝ => ⌊(δ / (2 * (‖u‖ + 1))) / |r|⌋₊)).sup id
    let c : ℝ := (δ / (2 * (‖u‖ + 1))) / ((Nmax : ℝ) + 1)
    have hu_pos : 0 < ‖u‖ + 1 := by positivity
    have hN_pos : (0 : ℝ) < (Nmax : ℝ) + 1 := by positivity
    have hc_pos : 0 < c := div_pos (div_pos hδ (by positivity)) hN_pos
    have hc_notMem : c ∉ BadScalars := by
      intro hc_mem
      have habs : |c| = c := abs_of_pos hc_pos
      have hdiv_eq : (δ / (2 * (‖u‖ + 1))) / |c| = (Nmax : ℝ) + 1 := by
        rw [habs]
        dsimp [c]
        have hnum_ne : δ / (2 * (‖u‖ + 1)) ≠ 0 := (div_pos hδ (by positivity)).ne'
        field_simp [hnum_ne, hN_pos.ne']
      have hfloor : ⌊(δ / (2 * (‖u‖ + 1))) / |c|⌋₊ = Nmax + 1 := by
        rw [hdiv_eq]
        exact_mod_cast Nat.floor_natCast (Nmax + 1)
      have hle : ⌊(δ / (2 * (‖u‖ + 1))) / |c|⌋₊ ≤ Nmax :=
        Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hc_mem)
      omega
    have hpert_avoid : ∀ p ∈ idxSet, val₀ v₀ + c • u ∉ W p := by
      intro p hp hmem
      have hex : ∃ c' : ℝ, val₀ v₀ + c' • u ∈ W p := ⟨c, hmem⟩
      let c' := hex.choose
      have hc'_mem : val₀ v₀ + c' • u ∈ W p := hex.choose_spec
      have hc'_in : c' ∈ BadScalars :=
        Finset.mem_biUnion.mpr ⟨p, hp, by simp [bad, hex, c']⟩
      have hne : c - c' ≠ 0 := sub_ne_zero.mpr (fun h => hc_notMem (h ▸ hc'_in))
      have hdiff : (c - c') • u ∈ W p := by
        have : (c - c') • u = (val₀ v₀ + c • u) - (val₀ v₀ + c' • u) := by
          rw [sub_smul]; abel
        rw [this]
        exact (W p).sub_mem hmem hc'_mem
      exact hu p hp (by simpa [hne] using (W p).smul_mem (c - c')⁻¹ hdiff)
    let val' : V → E := Function.update val v₀ (val₀ v₀ + c • u)
    refine ⟨val', ?_, ?_⟩
    · intro v
      by_cases hv : v = v₀
      · subst hv
        simp only [val', Function.update_self, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hc_pos.le]
        have hc_le : c ≤ δ / (2 * (‖u‖ + 1)) :=
          div_le_self (div_nonneg hδ.le (by positivity)) (by linarith)
        calc c * ‖u‖ ≤ (δ / (2 * (‖u‖ + 1))) * ‖u‖ :=
              mul_le_mul_of_nonneg_right hc_le (norm_nonneg u)
          _ < (δ / (2 * (‖u‖ + 1))) * (2 * (‖u‖ + 1)) :=
              mul_lt_mul_of_pos_left (by linarith [norm_nonneg u]) (div_pos hδ (by positivity))
          _ = δ := div_mul_cancel₀ δ (by positivity)
      · simp only [val', Function.update_of_ne hv]
        exact hval_close v
    · intro B hB hBcard i w hw
      by_cases hvB : v₀ ∈ B
      · by_cases hw0 : w v₀ = 0
        · have hsum_eq : (∑ b ∈ B, w b • val' b) = ∑ b ∈ B.erase v₀, w b • val b := by
            rw [← Finset.add_sum_erase B (fun b => w b • val' b) hvB, hw0, zero_smul, zero_add]
            refine Finset.sum_congr rfl fun b hb => ?_
            have hne : b ≠ v₀ := (Finset.mem_erase.mp hb).1
            simp [val', Function.update_of_ne hne]
          have hw_eq : ∑ b ∈ B.erase v₀, w b = 1 := by
            rw [← hw, ← Finset.add_sum_erase B w hvB, hw0, zero_add]
          have hsub : B.erase v₀ ⊆ S := fun b hb =>
            (Finset.mem_insert.mp (hB (Finset.mem_of_mem_erase hb))).resolve_left
              (Finset.mem_erase.mp hb).1
          have hcard' : (B.erase v₀).card ≤ d + 1 :=
            (Finset.card_erase_le).trans hBcard
          rw [hsum_eq]
          exact hval_gp (B.erase v₀) hsub hcard' i w hw_eq
        · intro hmem
          let B' := B.erase v₀
          have hB'_sub : B' ⊆ S := fun b hb =>
            (Finset.mem_insert.mp (hB (Finset.mem_of_mem_erase hb))).resolve_left
              (Finset.mem_erase.mp hb).1
          have hB'_card : B'.card ≤ d := by
            have : B'.card + 1 = B.card := Finset.card_erase_add_one hvB
            omega
          have hp_mem : (i, B') ∈ idxSet := by
            refine Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_filter.mpr ⟨?_, hB'_card⟩⟩
            exact Finset.mem_powerset.mpr hB'_sub
          apply hpert_avoid (i, B') hp_mem
          have hsplit : (∑ b ∈ B, w b • val' b) =
              w v₀ • (val₀ v₀ + c • u) + ∑ b ∈ B', w b • val b := by
            rw [← Finset.add_sum_erase B (fun b => w b • val' b) hvB]
            congr 1
            · simp [val']
            · refine Finset.sum_congr rfl fun b hb => ?_
              have hne : b ≠ v₀ := (Finset.mem_erase.mp hb).1
              simp [val', Function.update_of_ne hne]
          have h1 : w v₀ • (val₀ v₀ + c • u) + ∑ b ∈ B', w b • val b ∈ W (i, B') :=
            Submodule.mem_sup_left (hsplit ▸ hmem)
          have h2 : ∑ b ∈ B', w b • val b ∈ W (i, B') := by
            refine Submodule.mem_sup_right (Submodule.sum_mem _ fun b hb => ?_)
            exact Submodule.smul_mem _ _ (Submodule.subset_span
              (Finset.mem_coe.mpr (Finset.mem_image_of_mem val hb)))
          have h3 : w v₀ • (val₀ v₀ + c • u) ∈ W (i, B') := by
            have : w v₀ • (val₀ v₀ + c • u) =
                (w v₀ • (val₀ v₀ + c • u) + ∑ b ∈ B', w b • val b) - ∑ b ∈ B', w b • val b := by
              abel
            rw [this]
            exact (W (i, B')).sub_mem h1 h2
          simpa [hw0] using (W (i, B')).smul_mem (w v₀)⁻¹ h3
      · have hB_sub : B ⊆ S := fun b hb =>
          (Finset.mem_insert.mp (hB hb)).resolve_left (fun h => hvB (h ▸ hb))
        have hsum_eq : (∑ b ∈ B, w b • val' b) = ∑ b ∈ B, w b • val b := by
          refine Finset.sum_congr rfl fun b hb => ?_
          have hne : b ≠ v₀ := fun h => hvB (h ▸ hb)
          simp [val', Function.update_of_ne hne]
        rw [hsum_eq]
        exact hval_gp B hB_sub hBcard i w hw

lemma exists_margin_avoiding_subspace {X E : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℝ E) (f : X → E) (hf : Continuous f) (havoid : ∀ x : X, f x ∉ L) :
    ∃ ε > 0, ∀ x : X, ∀ y : E, ‖y - f x‖ < ε → y ∉ L := by
  by_cases hX : Nonempty X
  · let k := Module.finrank ℝ (E ⧸ L)
    let e : (E ⧸ L) ≃ₗ[ℝ] (Fin k → ℝ) :=
      LinearEquiv.ofFinrankEq (E ⧸ L) (Fin k → ℝ) (by simp [k])
    let q : E →L[ℝ] (Fin k → ℝ) := (e.toLinearMap.comp L.mkQ).toContinuousLinearMap
    have hq_zero : ∀ y : E, y ∈ L ↔ q y = 0 := fun y => by
      change y ∈ L ↔ e (L.mkQ y) = 0
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hcont : Continuous (fun x : X => ‖q (f x)‖) :=
      continuous_norm.comp (q.continuous.comp hf)
    obtain ⟨x₀, _, hx₀_min⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
    have hm_pos : 0 < ‖q (f x₀)‖ :=
      norm_pos_iff.mpr (fun h0 => havoid x₀ ((hq_zero (f x₀)).mpr h0))
    have hq_pos : 0 < ‖q‖ + 1 := by positivity
    refine ⟨‖q (f x₀)‖ / (‖q‖ + 1), div_pos hm_pos hq_pos, fun x y hy hyL => ?_⟩
    have hqy : q y = 0 := (hq_zero y).mp hyL
    have hmin : ‖q (f x₀)‖ ≤ ‖q (f x)‖ := hx₀_min (Set.mem_univ x)
    have hle : ‖q (f x)‖ ≤ ‖q‖ * ‖y - f x‖ := by
      have hq_eq : q (f x) = -q (y - f x) := by
        rw [map_sub, hqy, zero_sub, neg_neg]
      rw [hq_eq, norm_neg]
      exact q.le_opNorm (y - f x)
    have hlt : ‖q‖ * ‖y - f x‖ < (‖q‖ + 1) * (‖q (f x₀)‖ / (‖q‖ + 1)) := by
      calc ‖q‖ * ‖y - f x‖ ≤ ‖q‖ * (‖q (f x₀)‖ / (‖q‖ + 1)) :=
            mul_le_mul_of_nonneg_left hy.le (norm_nonneg q)
        _ < (‖q‖ + 1) * (‖q (f x₀)‖ / (‖q‖ + 1)) :=
            mul_lt_mul_of_pos_right (by linarith) (div_pos hm_pos hq_pos)
    rw [mul_div_cancel₀ _ hq_pos.ne'] at hlt
    linarith
  · refine ⟨1, zero_lt_one, fun x => (hX ⟨x⟩).elim⟩

lemma exists_margin_avoiding_subspaces {X E ι : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset ι) (L : ι → Submodule ℝ E)
    (f : X → E) (hf : Continuous f) (havoid : ∀ i ∈ s, ∀ x : X, f x ∉ L i) :
    ∃ ε > 0, ∀ i ∈ s, ∀ x : X, ∀ y : E, ‖y - f x‖ < ε → y ∉ L i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i₀ s hi₀ ih =>
    obtain ⟨ε₁, hε₁, h1⟩ := ih (fun i hi => havoid i (Finset.mem_insert_of_mem hi))
    obtain ⟨ε₂, hε₂, h2⟩ := exists_margin_avoiding_subspace (L i₀) f hf
      (havoid i₀ (Finset.mem_insert_self i₀ s))
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun i hi x y hy => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | his
    · exact h2 x y (hy.trans_le (min_le_right _ _))
    · exact h1 i his x y (hy.trans_le (min_le_left _ _))

theorem exists_extension_ball_complement {d : ℕ} {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (L : ι → Submodule ℝ E)
    (hcodim : ∀ i : ι, d + 1 ≤ Module.finrank ℝ (E ⧸ L i))
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      {y : E // ∀ i : ι, y ∉ L i})
    (hg : Continuous g) :
    ∃ G : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 →
      {y : E // ∀ i : ι, y ∉ L i},
      Continuous G ∧
      ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        G ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right,
          mem_sphere_zero_iff_norm.mp x.2]⟩ = g x := by
  let bdryToSphere : UnitCubeBoundary d → Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    fun x => ⟨(cubeHomeoBall d x.1).1, by
      rw [mem_sphere_zero_iff_norm, cubeHomeoBall_norm_eq_one_iff]
      exact x.2⟩
  have hbdryToSphere_cont : Continuous bdryToSphere :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp ((cubeHomeoBall d).continuous.comp continuous_subtype_val)) _
  let f₀ : UnitCubeBoundary d → E := fun x => (g (bdryToSphere x)).1
  have hf₀_cont : Continuous f₀ := continuous_subtype_val.comp (hg.comp hbdryToSphere_cont)
  have hf₀_avoid : ∀ i ∈ (Finset.univ : Finset ι), ∀ x : UnitCubeBoundary d, f₀ x ∉ L i :=
    fun i _ x => (g (bdryToSphere x)).2 i
  obtain ⟨ε, hε, hmargin⟩ :=
    exists_margin_avoiding_subspaces Finset.univ L f₀ hf₀_cont hf₀_avoid
  have hf₀_ucont : UniformContinuous f₀ :=
    CompactSpace.uniformContinuous_of_continuous hf₀_cont
  rw [Metric.uniformContinuous_iff] at hf₀_ucont
  obtain ⟨δ, hδ, hδ_uc⟩ := hf₀_ucont (ε / 2) (half_pos hε)
  let N : ℕ := ⌊1 / δ⌋₊ + 1
  have hN : 0 < N := Nat.succ_pos _
  have h1N_lt_δ : 1 / (N : ℝ) < δ := by
    have hgt : 1 / δ < (N : ℝ) := by
      dsimp [N]
      push_cast
      exact Nat.lt_floor_add_one (1 / δ)
    exact (div_lt_iff₀ (Nat.cast_pos.mpr hN)).mpr
      ((div_lt_iff₀ hδ).mp hgt |>.trans_eq (mul_comm _ _))
  let val₀ : (Fin d → Fin (N + 1)) → E := fun v =>
    if hv : ∃ j : Fin d, (gridPoint hN v).1 j = 0 ∨ (gridPoint hN v).1 j = 1 then
      f₀ ⟨gridPoint hN v, hv⟩
    else 0
  obtain ⟨val, hval_close, hval_gp⟩ :=
    exists_general_position_vertex_table d L hcodim Finset.univ val₀ (by positivity : 0 < ε / 4)
  let F_cube : UnitCube d → E := fun x =>
    ∑ v : Fin d → Fin (N + 1), kuhnWeight N v x • val v
  have hF_cube_cont : Continuous F_cube := by
    refine continuous_finsetSum Finset.univ fun v _ => ?_
    exact (continuous_kuhnWeight N v).smul continuous_const
  have hF_cube_avoid : ∀ x : UnitCube d, ∀ i : ι, F_cube x ∉ L i := by
    intro x i
    let σ := Tuple.sort (fun j => (N : ℝ) * x.1 j - (baseCellCoord N x j : ℝ))
    let B : Finset (Fin d → Fin (N + 1)) := Finset.univ.image (kuhnChainVertex hN x σ)
    have hB_card : B.card ≤ d + 1 :=
      Finset.card_image_le.trans (by simp)
    have hsum_B : ∑ b ∈ B, kuhnWeight N b x = 1 := by
      rw [← sum_kuhnWeight_eq_one hN x]
      refine Finset.sum_subset (Finset.subset_univ B) fun v _ hv => ?_
      refine kuhnWeight_eq_zero_of_not_mem_chain hN x v fun r hr => hv ?_
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr.symm⟩
    have hF_eq : F_cube x = ∑ b ∈ B, kuhnWeight N b x • val b := by
      symm
      refine Finset.sum_subset (Finset.subset_univ B) fun v _ hv => ?_
      have hw0 : kuhnWeight N v x = 0 :=
        kuhnWeight_eq_zero_of_not_mem_chain hN x v fun r hr => hv
          (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr.symm⟩)
      rw [hw0, zero_smul]
    rw [hF_eq]
    exact hval_gp B (Finset.subset_univ B) hB_card i (fun v => kuhnWeight N v x) hsum_B
  have hbdry_dist : ∀ x : UnitCubeBoundary d, ‖F_cube x.1 - f₀ x‖ < ε := by
    intro x
    have hdiff : F_cube x.1 - f₀ x =
        ∑ v : Fin d → Fin (N + 1), kuhnWeight N v x.1 • (val v - f₀ x) := by
      simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
        sum_kuhnWeight_eq_one hN x.1, one_smul]
      rfl
    have hterm_le : ∀ v : Fin d → Fin (N + 1),
        ‖kuhnWeight N v x.1 • (val v - f₀ x)‖ ≤ kuhnWeight N v x.1 * (3 * ε / 4) := by
      intro v
      rcases eq_or_lt_of_le (kuhnWeight_nonneg N v x.1) with hw0 | hw
      · rw [← hw0, zero_smul, norm_zero, zero_mul]
      · have hv_bdry : ∃ j : Fin d, (gridPoint hN v).1 j = 0 ∨ (gridPoint hN v).1 j = 1 :=
          gridPoint_mem_boundary_of_active hN x.2 hw
        have hval₀_eq : val₀ v = f₀ ⟨gridPoint hN v, hv_bdry⟩ := dif_pos hv_bdry
        have hdist_grid : dist (⟨gridPoint hN v, hv_bdry⟩ : UnitCubeBoundary d) x < δ :=
          (dist_gridPoint_le_of_active hN hw).trans_lt h1N_lt_δ
        have h1 : ‖val v - val₀ v‖ < ε / 4 := hval_close v
        have h2 : ‖val₀ v - f₀ x‖ < ε / 2 := by
          rw [hval₀_eq, ← dist_eq_norm]
          exact hδ_uc hdist_grid
        have hnorm_le : ‖val v - f₀ x‖ ≤ 3 * ε / 4 := by
          calc ‖val v - f₀ x‖ = ‖(val v - val₀ v) + (val₀ v - f₀ x)‖ := by congr 1; abel
            _ ≤ ‖val v - val₀ v‖ + ‖val₀ v - f₀ x‖ := norm_add_le _ _
            _ ≤ ε / 4 + ε / 2 := add_le_add h1.le h2.le
            _ = 3 * ε / 4 := by ring
        rw [norm_smul, Real.norm_of_nonneg hw.le]
        exact mul_le_mul_of_nonneg_left hnorm_le hw.le
    calc ‖F_cube x.1 - f₀ x‖
        = ‖∑ v : Fin d → Fin (N + 1), kuhnWeight N v x.1 • (val v - f₀ x)‖ := by rw [hdiff]
      _ ≤ ∑ v : Fin d → Fin (N + 1), ‖kuhnWeight N v x.1 • (val v - f₀ x)‖ := norm_sum_le _ _
      _ ≤ ∑ v : Fin d → Fin (N + 1), kuhnWeight N v x.1 * (3 * ε / 4) :=
          Finset.sum_le_sum fun v _ => hterm_le v
      _ = (∑ v : Fin d → Fin (N + 1), kuhnWeight N v x.1) * (3 * ε / 4) :=
          (Finset.sum_mul _ _ _).symm
      _ = 3 * ε / 4 := by rw [sum_kuhnWeight_eq_one hN x.1, one_mul]
      _ < ε := by linarith
  let g₀ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 →
      {y : E // ∀ i : ι, y ∉ L i} :=
    fun z => ⟨F_cube ((cubeHomeoBall d).symm z), hF_cube_avoid ((cubeHomeoBall d).symm z)⟩
  have hg₀_cont : Continuous g₀ :=
    Continuous.subtype_mk (hF_cube_cont.comp (cubeHomeoBall d).symm.continuous) _
  let sphToBall (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.mp x.2]⟩
  have hsphToBall_cont : Continuous sphToBall :=
    Continuous.subtype_mk continuous_subtype_val _
  have hsph_bdry : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∃ j : Fin d, ((cubeHomeoBall d).symm (sphToBall x)).1 j = 0 ∨
        ((cubeHomeoBall d).symm (sphToBall x)).1 j = 1 := by
    intro x
    rw [← cubeHomeoBall_norm_eq_one_iff, (cubeHomeoBall d).apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp x.2
  let H : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      {y : E // ∀ i : ι, y ∉ L i} :=
    fun p =>
      ⟨(1 - (p.1 : ℝ)) • (g₀ (sphToBall p.2)).1 + (p.1 : ℝ) • (g p.2).1, fun i => by
        let xB : UnitCubeBoundary d := ⟨(cubeHomeoBall d).symm (sphToBall p.2), hsph_bdry p.2⟩
        have hbdry_eq : bdryToSphere xB = p.2 := by
          apply Subtype.ext
          change ((cubeHomeoBall d) ((cubeHomeoBall d).symm (sphToBall p.2))).1 = p.2.1
          rw [(cubeHomeoBall d).apply_symm_apply]
        have hfxB : f₀ xB = (g p.2).1 := by
          change (g (bdryToSphere xB)).1 = (g p.2).1
          rw [hbdry_eq]
        have hg₀_eq : (g₀ (sphToBall p.2)).1 = F_cube xB.1 := rfl
        have hdiff_eq : ((1 - (p.1 : ℝ)) • (g₀ (sphToBall p.2)).1 + (p.1 : ℝ) • (g p.2).1) - f₀ xB =
            (1 - (p.1 : ℝ)) • (F_cube xB.1 - f₀ xB) := by
          rw [hg₀_eq, ← hfxB]
          module
        have h1_nonneg : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
        have h1_le_one : 1 - (p.1 : ℝ) ≤ 1 := sub_le_self 1 p.1.2.1
        have hnorm_lt : ‖((1 - (p.1 : ℝ)) • (g₀ (sphToBall p.2)).1 + (p.1 : ℝ) • (g p.2).1) - f₀ xB‖ < ε := by
          rw [hdiff_eq, norm_smul, Real.norm_of_nonneg h1_nonneg]
          calc (1 - (p.1 : ℝ)) * ‖F_cube xB.1 - f₀ xB‖
              ≤ 1 * ‖F_cube xB.1 - f₀ xB‖ := mul_le_mul_of_nonneg_right h1_le_one (norm_nonneg _)
            _ = ‖F_cube xB.1 - f₀ xB‖ := one_mul _
            _ < ε := hbdry_dist xB
        exact hmargin i (Finset.mem_univ i) xB _ hnorm_lt⟩
  have hH_cont : Continuous H := by
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous (fun p : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous (fun p : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        (g₀ (sphToBall p.2)).1) :=
      continuous_subtype_val.comp (hg₀_cont.comp (hsphToBall_cont.comp continuous_snd))
    have h3 : Continuous (fun p : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have h4 : Continuous (fun p : unitInterval × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        (g p.2).1) :=
      continuous_subtype_val.comp (hg.comp continuous_snd)
    exact (h1.smul h2).add (h3.smul h4)
  have hagree : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      H (0, x) = g₀ (sphToBall x) := by
    intro x
    apply Subtype.ext
    change (1 - (0 : ℝ)) • (g₀ (sphToBall x)).1 + (0 : ℝ) • (g x).1 = (g₀ (sphToBall x)).1
    simp
  obtain ⟨g₁, hg₁_cont, hg₁_bdry⟩ := homotopy_extension_ball g₀ hg₀_cont H hH_cont hagree
  refine ⟨g₁, hg₁_cont, fun x => ?_⟩
  rw [hg₁_bdry x]
  apply Subtype.ext
  change (1 - (1 : ℝ)) • (g₀ (sphToBall x)).1 + (1 : ℝ) • (g x).1 = (g x).1
  simp

theorem exists_extension_quadComplement_of_card_le_nine
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card ≤ 9)
    (g : FaceBoundary S → QuadComplement S) (hg : Continuous g) :
    ∃ G : FaceSimplex S → QuadComplement S,
      Continuous G ∧
      ∀ z : FaceBoundary S, G z.1 = g z := by
  classical
  let d := S.card - 1
  let ι := {m : Finset (S → Fin 6) // SixMatching m}
  let L : ι → Submodule ℝ (QuadSpace S) := fun m => L_M S m.1
  have hcodim : ∀ m : ι, d + 1 ≤ Module.finrank ℝ (QuadSpace S ⧸ L m) := fun m => by
    have h1 : Module.finrank ℝ (QuadSpace S ⧸ L m) = 10 := codim_L_M_eq_ten S hS m.1 m.2
    omega
  let sphToBdry (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) : FaceBoundary S :=
    ⟨(faceSimplexHomeoBall S hS).symm
        ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.mp x.2]⟩,
      by
        rw [← faceSimplexHomeoBall_norm_eq_one_iff S hS, (faceSimplexHomeoBall S hS).apply_symm_apply]
        exact mem_sphere_zero_iff_norm.mp x.2⟩
  have hsphToBdry_cont : Continuous sphToBdry := by
    refine Continuous.subtype_mk ((faceSimplexHomeoBall S hS).symm.continuous.comp ?_) _
    exact Continuous.subtype_mk continuous_subtype_val _
  let g_sph : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      {H : QuadSpace S // ∀ m : ι, H ∉ L m} :=
    fun x => ⟨(g (sphToBdry x)).1, fun m => (g (sphToBdry x)).2 m.1 m.2⟩
  have hg_sph_cont : Continuous g_sph :=
    Continuous.subtype_mk (continuous_subtype_val.comp (hg.comp hsphToBdry_cont)) _
  obtain ⟨G_ball, hG_ball_cont, hG_ball_bdry⟩ :=
    exists_extension_ball_complement L hcodim g_sph hg_sph_cont
  let G : FaceSimplex S → QuadComplement S :=
    fun z =>
      ⟨(G_ball (faceSimplexHomeoBall S hS z)).1,
        fun m hm => (G_ball (faceSimplexHomeoBall S hS z)).2 ⟨m, hm⟩⟩
  have hG_cont : Continuous G :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp (hG_ball_cont.comp (faceSimplexHomeoBall S hS).continuous)) _
  refine ⟨G, hG_cont, fun z => ?_⟩
  let x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨(faceSimplexHomeoBall S hS z.1).1, by
      rw [mem_sphere_zero_iff_norm, faceSimplexHomeoBall_norm_eq_one_iff S hS]
      exact z.2⟩
  have hball_eq : faceSimplexHomeoBall S hS z.1 =
      ⟨x.1, by simp [Metric.mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.mp x.2]⟩ :=
    rfl
  have hbdry_eq : sphToBdry x = z := by
    apply Subtype.ext
    change (faceSimplexHomeoBall S hS).symm (faceSimplexHomeoBall S hS z.1) = z.1
    exact (faceSimplexHomeoBall S hS).symm_apply_apply z.1
  apply Subtype.ext
  change (G_ball (faceSimplexHomeoBall S hS z.1)).1 = (g z).1
  rw [hball_eq, hG_ball_bdry x]
  change (g (sphToBdry x)).1 = (g z).1
  rw [hbdry_eq]

end KuhnPLExtension

/-! ### 5. Coherent comparison structures, skeleton induction, and almost-6-embedding bridge -/

section CoherentComparisonBridge

structure CompatibleSkeletonTable (k : ℕ) where
  table : ∀ (S : Finset (Fin 15)), S.Nonempty → S.card ≤ k →
    FaceSimplex S → QuadComplement S
  continuous_table : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hk : S.card ≤ k),
    Continuous (table S hS hk)
  compatible : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hS : S.Nonempty)
    (hkT : T.card ≤ k) (hkS : S.card ≤ k) (hTS : T ⊆ S) (z : FaceSimplex T),
    table S hS hkS (faceIncl hTS z) = liftFaceCompl hT hTS (table T hT hkT z)

lemma faceSimplex_closed_cover (S : Finset (Fin 15)) (i : Fin 15) :
    IsClosed {z : FaceSimplex S | z.1.val i = 0} :=
  isClosed_eq
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
    continuous_const

def projectToBoundaryFacet {S : Finset (Fin 15)} {i : Fin 15}
    (z : FaceSimplex S) (hzi : z.1.val i = 0) :
    FaceSimplex (S.erase i) :=
  ⟨z.1, fun j hj => by
    by_cases hji : j = i
    · subst hji; exact hzi
    · exact z.2 j (fun hjS => hj (Finset.mem_erase.mpr ⟨hji, hjS⟩))⟩

lemma faceIncl_projectToBoundaryFacet {S : Finset (Fin 15)} {i : Fin 15} (_hi : i ∈ S)
    (z : FaceSimplex S) (hzi : z.1.val i = 0) :
    faceIncl (Finset.erase_subset i S) (projectToBoundaryFacet z hzi) = z := by
  apply Subtype.ext; rfl

def extendSkeletonBoundary {k : ℕ} (sk : CompatibleSkeletonTable k)
    (S : Finset (Fin 15)) (_hS : S.Nonempty) (hcard : S.card = k + 1)
    (hk_pos : 1 ≤ k) :
    FaceBoundary S → QuadComplement S :=
  fun z =>
    let i := z.2.choose
    have hiS : i ∈ S := z.2.choose_spec.1
    have hzi : z.1.1.val i = 0 := z.2.choose_spec.2
    have hTi : (S.erase i).Nonempty := by
      have hcard_erase : (S.erase i).card = k := by
        rw [Finset.card_erase_of_mem hiS, hcard]; omega
      exact Finset.card_pos.mp (by omega)
    have hkTi : (S.erase i).card ≤ k := by
      rw [Finset.card_erase_of_mem hiS, hcard]; omega
    liftFaceCompl hTi (Finset.erase_subset i S)
      (sk.table (S.erase i) hTi hkTi (projectToBoundaryFacet z.1 hzi))

lemma extendSkeletonBoundary_eq_of_zero {k : ℕ} (sk : CompatibleSkeletonTable k)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1) (hk_pos : 1 ≤ k)
    (z : FaceBoundary S) (j : Fin 15) (hjS : j ∈ S) (hzj : z.1.1.val j = 0)
    (hTj : (S.erase j).Nonempty) (hkTj : (S.erase j).card ≤ k) :
    extendSkeletonBoundary sk S hS hcard hk_pos z =
      liftFaceCompl hTj (Finset.erase_subset j S)
        (sk.table (S.erase j) hTj hkTj (projectToBoundaryFacet z.1 hzj)) := by
  let i := z.2.choose
  have hiS : i ∈ S := z.2.choose_spec.1
  have hzi : z.1.1.val i = 0 := z.2.choose_spec.2
  have hTi : (S.erase i).Nonempty := by
    have : (S.erase i).card = k := by rw [Finset.card_erase_of_mem hiS, hcard]; omega
    exact Finset.card_pos.mp (by omega)
  have hkTi : (S.erase i).card ≤ k := by
    rw [Finset.card_erase_of_mem hiS, hcard]; omega
  change liftFaceCompl hTi (Finset.erase_subset i S)
      (sk.table (S.erase i) hTi hkTi (projectToBoundaryFacet z.1 hzi)) = _
  by_cases hij : i = j
  · subst hij; rfl
  · let R := (S.erase i).erase j
    have hR : R.Nonempty := by
      by_contra hR_empty
      rw [Finset.not_nonempty_iff_eq_empty] at hR_empty
      have htot := faceSimplex_sum_eq_one z.1
      have hsum0 : ∑ m ∈ S, z.1.1.val m = 0 := by
        refine Finset.sum_eq_zero fun m hmS => ?_
        by_cases hmi : m = i
        · subst hmi; exact hzi
        · by_cases hmj : m = j
          · subst hmj; exact hzj
          · have hmR : m ∈ R :=
              Finset.mem_erase.mpr ⟨hmj, Finset.mem_erase.mpr ⟨hmi, hmS⟩⟩
            rw [hR_empty] at hmR
            exact (Finset.notMem_empty m hmR).elim
      linarith
    have hkR : R.card ≤ k :=
      (Finset.card_erase_le.trans (Finset.card_erase_of_mem hiS).le).trans (by omega)
    let zR : FaceSimplex R :=
      ⟨z.1.1, fun m hmR => by
        by_cases hmi : m = i
        · subst hmi; exact hzi
        · by_cases hmj : m = j
          · subst hmj; exact hzj
          · exact z.1.2 m (fun hmS =>
              hmR (Finset.mem_erase.mpr ⟨hmj, Finset.mem_erase.mpr ⟨hmi, hmS⟩⟩))⟩
    have hR_sub_i : R ⊆ S.erase i := Finset.erase_subset j (S.erase i)
    have hR_sub_j : R ⊆ S.erase j := by
      intro m hmR
      have hm1 := Finset.mem_erase.mp hmR
      have hm2 := Finset.mem_erase.mp hm1.2
      exact Finset.mem_erase.mpr ⟨hm1.1, hm2.2⟩
    have hzi_eq : projectToBoundaryFacet z.1 hzi = faceIncl hR_sub_i zR := by
      apply Subtype.ext; rfl
    have hzj_eq : projectToBoundaryFacet z.1 hzj = faceIncl hR_sub_j zR := by
      apply Subtype.ext; rfl
    rw [hzi_eq, hzj_eq, sk.compatible hR hTi hkR hkTi hR_sub_i zR,
      sk.compatible hR hTj hkR hkTj hR_sub_j zR, liftFaceCompl_comp, liftFaceCompl_comp]

lemma continuousOn_biUnion_of_isClosed {X Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [DecidableEq ι]
    (s : Finset ι) (A : ι → Set X) (f : X → Y)
    (hclosed : ∀ i ∈ s, IsClosed (A i))
    (hcont : ∀ i ∈ s, ContinuousOn f (A i)) :
    ContinuousOn f (⋃ i ∈ s, A i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert i₀ s hi₀ ih =>
    rw [Finset.set_biUnion_insert]
    exact (hcont i₀ (Finset.mem_insert_self i₀ s)).union_of_isClosed
      (ih (fun i hi => hclosed i (Finset.mem_insert_of_mem hi))
          (fun i hi => hcont i (Finset.mem_insert_of_mem hi)))
      (hclosed i₀ (Finset.mem_insert_self i₀ s))
      (s.finite_toSet.isClosed_biUnion fun i hi => hclosed i (Finset.mem_insert_of_mem hi))

lemma continuous_extendSkeletonBoundary {k : ℕ} (sk : CompatibleSkeletonTable k)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1) (hk_pos : 1 ≤ k) :
    Continuous (extendSkeletonBoundary sk S hS hcard hk_pos) := by
  let A : Fin 15 → Set (FaceBoundary S) := fun j =>
    if j ∈ S then {z : FaceBoundary S | z.1.1.val j = 0} else ∅
  have hA_closed : ∀ j ∈ (Finset.univ : Finset (Fin 15)), IsClosed (A j) := fun j _ => by
    dsimp [A]
    split_ifs with hjS
    · exact isClosed_eq
        ((continuous_apply j).comp (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_subtype_val)))
        continuous_const
    · exact isClosed_empty
  have hA_cover : (⋃ j ∈ (Finset.univ : Finset (Fin 15)), A j) = Set.univ := by
    ext z
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hjS, hzj⟩ := z.2
    refine ⟨j, ?_⟩
    simp [A, hjS, hzj]
  rw [← continuousOn_univ, ← hA_cover]
  refine continuousOn_biUnion_of_isClosed Finset.univ A _ hA_closed fun j _ => ?_
  dsimp [A]
  split_ifs with hjS
  · have hTj : (S.erase j).Nonempty := by
      have : (S.erase j).card = k := by rw [Finset.card_erase_of_mem hjS, hcard]; omega
      exact Finset.card_pos.mp (by omega)
    have hkTj : (S.erase j).card ≤ k := by
      rw [Finset.card_erase_of_mem hjS, hcard]; omega
    let E_j : {z : FaceBoundary S // z.1.1.val j = 0} → FaceSimplex (S.erase j) :=
      fun z => projectToBoundaryFacet z.1.1 z.2
    have hEj_cont : Continuous E_j := by
      have h1 : Continuous (fun z : {z : FaceBoundary S // z.1.1.val j = 0} => z.1) :=
        continuous_subtype_val
      have h2 : Continuous (fun z : FaceBoundary S => z.1) :=
        continuous_subtype_val
      have h3 : Continuous (fun z : FaceSimplex S => z.1) :=
        continuous_subtype_val
      exact Continuous.subtype_mk (h3.comp (h2.comp h1)) _
    let F_j : {z : FaceBoundary S // z.1.1.val j = 0} → QuadComplement S :=
      fun z => liftFaceCompl hTj (Finset.erase_subset j S)
        (sk.table (S.erase j) hTj hkTj (E_j z))
    have hFj_cont : Continuous F_j :=
      (continuous_liftFaceCompl hTj (Finset.erase_subset j S)).comp
        ((sk.continuous_table (S.erase j) hTj hkTj).comp hEj_cont)
    rw [continuousOn_iff_continuous_domRestrict]
    refine hFj_cont.congr fun z => ?_
    exact (extendSkeletonBoundary_eq_of_zero sk S hS hcard hk_pos z.1 j hjS z.2 hTj hkTj).symm
  · exact continuousOn_empty _

def extendSkeletonStep {k : ℕ} (sk : CompatibleSkeletonTable k) (hk_pos : 1 ≤ k)
    (ext : ∀ (S : Finset (Fin 15)) (_hS : S.Nonempty) (_hcard : S.card = k + 1),
      FaceSimplex S → QuadComplement S)
    (hext_cont : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1),
      Continuous (ext S hS hcard))
    (hext_bdry : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1)
      (z : FaceBoundary S),
      ext S hS hcard z.1 = extendSkeletonBoundary sk S hS hcard hk_pos z) :
    CompatibleSkeletonTable (k + 1) where
  table S hS hkS :=
    if hle : S.card ≤ k then sk.table S hS hle
    else ext S hS (by omega)
  continuous_table S hS hkS := by
    split_ifs with hle
    · exact sk.continuous_table S hS hle
    · exact hext_cont S hS (by omega)
  compatible {T S} hT hS hkT hkS hTS z := by
    split_ifs with hleS hleT hleT
    · exact sk.compatible hT hS hleT hleS hTS z
    · exfalso
      have := Finset.card_le_card hTS
      omega
    · have hcardS : S.card = k + 1 := by omega
      have hne_diff : (S \ T).Nonempty := by
        apply Finset.nonempty_of_ne_empty
        intro hempty
        have hST : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hempty
        have := Finset.card_le_card hST
        omega
      let j := hne_diff.choose
      have hj_diff : j ∈ S \ T := hne_diff.choose_spec
      have hjS : j ∈ S := (Finset.mem_sdiff.mp hj_diff).1
      have hjT : j ∉ T := (Finset.mem_sdiff.mp hj_diff).2
      have hzj : (faceIncl hTS z).1.val j = 0 := z.2 j hjT
      let zB : FaceBoundary S := ⟨faceIncl hTS z, ⟨j, hjS, hzj⟩⟩
      have hTj : (S.erase j).Nonempty := by
        have : (S.erase j).card = k := by rw [Finset.card_erase_of_mem hjS, hcardS]; omega
        exact Finset.card_pos.mp (by omega)
      have hkTj : (S.erase j).card ≤ k := by
        rw [Finset.card_erase_of_mem hjS, hcardS]; omega
      have hT_sub_Tj : T ⊆ S.erase j := fun m hmT =>
        Finset.mem_erase.mpr ⟨fun hmj => hjT (hmj ▸ hmT), hTS hmT⟩
      have hproj_eq : projectToBoundaryFacet zB.1 hzj = faceIncl hT_sub_Tj z := by
        apply Subtype.ext; rfl
      change ext S hS hcardS zB.1 = liftFaceCompl hT hTS (sk.table T hT hleT z)
      rw [hext_bdry S hS hcardS zB,
        extendSkeletonBoundary_eq_of_zero sk S hS hcardS hk_pos zB j hjS hzj hTj hkTj,
        hproj_eq, sk.compatible hT hTj hleT hkTj hT_sub_Tj z, liftFaceCompl_comp]
    · have hcardT : T.card = k + 1 := by omega
      have hcardS : S.card = k + 1 := by omega
      have hTS_eq : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
      subst hTS_eq
      rw [faceIncl_refl, liftFaceCompl_refl]

lemma nonempty_quadComplement (S : Finset (Fin 15)) (hS : S.Nonempty) :
    Nonempty (QuadComplement S) := by
  classical
  let s : Finset {m : Finset (S → Fin 6) // SixMatching m} := Finset.univ
  let W : {m : Finset (S → Fin 6) // SixMatching m} → Submodule ℝ (QuadSpace S) :=
    fun m => L_M S m.1
  have hW : ∀ m ∈ s, W m ≠ ⊤ := by
    intro m _ htop
    have hc : Module.finrank ℝ (QuadSpace S ⧸ L_M S m.1) = 10 :=
      codim_L_M_eq_ten S hS m.1 m.2
    have hq : Module.finrank ℝ (QuadSpace S ⧸ L_M S m.1) + Module.finrank ℝ (L_M S m.1) =
        Module.finrank ℝ (QuadSpace S) :=
      (L_M S m.1).finrank_quotient_add_finrank
    have htop_eq : Module.finrank ℝ (L_M S m.1) = Module.finrank ℝ (QuadSpace S) := by
      change L_M S m.1 = ⊤ at htop
      rw [htop]
      exact finrank_top ℝ (QuadSpace S)
    omega
  obtain ⟨H, hH⟩ := exists_notMem_biUnion_proper_subspaces s W hW
  exact ⟨⟨H, fun m hm => hH ⟨m, hm⟩ (Finset.mem_univ _)⟩⟩

def baseSkeletonTable1 : CompatibleSkeletonTable 1 where
  table S hS _ := fun _ => (nonempty_quadComplement S hS).some
  continuous_table _ _ _ := continuous_const
  compatible {T S} hT hS hkT hkS hTS z := by
    have hT_pos : 1 ≤ T.card := hT.card_pos
    have hTS_eq : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
    subst hTS_eq
    exact (liftFaceCompl_refl T hT (nonempty_quadComplement T hT).some).symm

def compatibleSkeletonTableNine : CompatibleSkeletonTable 9 :=
  let hstep (k : ℕ) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (sk : CompatibleSkeletonTable k) :
      CompatibleSkeletonTable (k + 1) :=
    let hex (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = k + 1) :=
      exists_extension_quadComplement_of_card_le_nine S hS (by omega)
        (extendSkeletonBoundary sk S hS hcard hk1)
        (continuous_extendSkeletonBoundary sk S hS hcard hk1)
    extendSkeletonStep sk hk1
      (fun S hS hcard => (hex S hS hcard).choose)
      (fun S hS hcard => (hex S hS hcard).choose_spec.1)
      (fun S hS hcard z => (hex S hS hcard).choose_spec.2 z)
  let sk1 := baseSkeletonTable1
  let sk2 := hstep 1 (by omega) (by omega) sk1
  let sk3 := hstep 2 (by omega) (by omega) sk2
  let sk4 := hstep 3 (by omega) (by omega) sk3
  let sk5 := hstep 4 (by omega) (by omega) sk4
  let sk6 := hstep 5 (by omega) (by omega) sk5
  let sk7 := hstep 6 (by omega) (by omega) sk6
  let sk8 := hstep 7 (by omega) (by omega) sk7
  hstep 8 (by omega) (by omega) sk8

/-- Legacy universal-extension target. For the intended `k = 9` application,
use the chosen-section relative interface in `Completion.RelativeComparison`.
Existence of this structure is not proved here. -/
structure ComparisonTarget (k : ℕ) where
  Space : Finset (Fin 15) → Type
  topSpace : ∀ S, TopologicalSpace (Space S)
  lift : ∀ {T S : Finset (Fin 15)}, T.Nonempty → T ⊆ S → Space T → Space S
  continuous_lift : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hTS : T ⊆ S),
    @Continuous _ _ (topSpace T) (topSpace S) (lift hT hTS)
  lift_refl : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (x : Space S),
    lift hS (Finset.Subset.refl S) x = x
  lift_comp : ∀ {R T S : Finset (Fin 15)} (hR : R.Nonempty) (hT : T.Nonempty)
    (hRT : R ⊆ T) (hTS : T ⊆ S) (x : Space R),
    lift hT hTS (lift hR hRT x) = lift hR (hRT.trans hTS) x
  extend_high : ∀ (S : Finset (Fin 15)) (_hS : S.Nonempty), k + 1 ≤ S.card →
    ∀ g : FaceBoundary S → Space S,
      @Continuous _ _ _ (topSpace S) g →
      ∃ G : FaceSimplex S → Space S,
        @Continuous _ _ _ (topSpace S) G ∧
        ∀ z : FaceBoundary S, G z.1 = g z

attribute [instance] ComparisonTarget.topSpace

/-- Legacy conditional comparison. Its existence, together with the target's
universal extension field, is stronger than the intended lifting argument. -/
structure CoherentComparison (k : ℕ) (P : ComparisonTarget k) where
  comp : ∀ (S : Finset (Fin 15)), S.Nonempty → QuadComplement S → P.Space S
  continuous_comp : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty),
    Continuous (comp S hS)
  natural_comp : ∀ {T S : Finset (Fin 15)} (hT : T.Nonempty) (hS : S.Nonempty)
    (hTS : T ⊆ S) (H : QuadComplement T),
    comp S hS (liftFaceCompl hT hTS H) = P.lift hT hTS (comp T hT H)
  lift_ball_along_comp : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty), k + 1 ≤ S.card →
    ∀ (g : FaceBoundary S → QuadComplement S), Continuous g →
    ∀ (F : FaceSimplex S → P.Space S), Continuous F →
      (∀ z : FaceBoundary S, F z.1 = comp S hS (g z)) →
      ∃ G : FaceSimplex S → QuadComplement S,
        Continuous G ∧
        ∀ z : FaceBoundary S, G z.1 = g z

def extendSkeletonTableOfCoherentComparison {k : ℕ} (hk_pos : 1 ≤ k)
    (P : ComparisonTarget k) (C : CoherentComparison k P)
    (sk : CompatibleSkeletonTable k) (m : ℕ) :
    CompatibleSkeletonTable (k + m) := by
  induction m with
  | zero => exact sk
  | succ m ih =>
    have hk_m_pos : 1 ≤ k + m := by omega
    have hex : ∀ (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = (k + m) + 1),
        ∃ G : FaceSimplex S → QuadComplement S,
          Continuous G ∧
          ∀ z : FaceBoundary S, G z.1 = extendSkeletonBoundary ih S hS hcard hk_m_pos z := by
      intro S hS hcard
      let g := extendSkeletonBoundary ih S hS hcard hk_m_pos
      have hg_cont : Continuous g := continuous_extendSkeletonBoundary ih S hS hcard hk_m_pos
      have hcard_ge : k + 1 ≤ S.card := by omega
      obtain ⟨F, hF_cont, hF_bdry⟩ :=
        P.extend_high S hS hcard_ge (fun z => C.comp S hS (g z))
          ((C.continuous_comp S hS).comp hg_cont)
      exact C.lift_ball_along_comp S hS hcard_ge g hg_cont F hF_cont hF_bdry
    let ext (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = (k + m) + 1) :
        FaceSimplex S → QuadComplement S :=
      (hex S hS hcard).choose
    have hext_cont (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = (k + m) + 1) :
        Continuous (ext S hS hcard) :=
      (hex S hS hcard).choose_spec.1
    have hext_bdry (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : S.card = (k + m) + 1)
        (z : FaceBoundary S) :
        ext S hS hcard z.1 = extendSkeletonBoundary ih S hS hcard hk_m_pos z :=
      (hex S hS hcard).choose_spec.2 z
    exact extendSkeletonStep ih hk_m_pos ext hext_cont hext_bdry

theorem exists_safe_compatible_quadratic_table_of_coherent_comparison
    (P : ComparisonTarget 9) (C : CoherentComparison 9 P) :
    ∃ H : MassSimplex → TableWords → Fin 2 → ℝ,
      Continuous H ∧
      (∀ z t, (fun w => H z w t) ∈ quadraticLabelSpace (Fin 15) (Fin 6)) ∧
      (∀ z i, z.val i = 0 → ∀ t, IgnoresColor (fun w => H z w t) i) ∧
      (∀ z : MassSimplex, ∀ σ : MatchingColumns,
        ∃ j, H z (fun i => σ i j) ≠ H z (fun i => σ i 0)) := by
  classical
  let sk9 := compatibleSkeletonTableNine
  let sk15 : CompatibleSkeletonTable 15 :=
    extendSkeletonTableOfCoherentComparison (by norm_num : 1 ≤ 9) P C sk9 6
  let U : Finset (Fin 15) := Finset.univ
  have hU : U.Nonempty := Finset.univ_nonempty
  have hU_card : U.card ≤ 15 := by simp [U]
  let toFaceU (z : MassSimplex) : FaceSimplex U :=
    ⟨z, fun i hi => (hi (Finset.mem_univ i)).elim⟩
  have htoFaceU_cont : Continuous toFaceU :=
    Continuous.subtype_mk continuous_id _
  let G_univ : MassSimplex → QuadComplement U :=
    fun z => sk15.table U hU hU_card (toFaceU z)
  have hG_univ_cont : Continuous G_univ :=
    (sk15.continuous_table U hU hU_card).comp htoFaceU_cont
  let H : MassSimplex → TableWords → Fin 2 → ℝ :=
    fun z => liftToFull U (G_univ z).1
  have hlift_linear : Continuous (liftToFull U) := by
    refine continuous_pi fun w => continuous_pi fun t => ?_
    have hproj : Continuous (fun Q : QuadSpace U => (Q t).1 (fun i : U => w i.1)) :=
      (continuous_apply (fun i : U => w i.1)).comp
        (continuous_subtype_val.comp (continuous_apply t))
    exact hproj
  have hH_cont : Continuous H :=
    hlift_linear.comp (continuous_subtype_val.comp hG_univ_cont)
  refine ⟨H, hH_cont, ?_, ?_, ?_⟩
  · intro z t
    exact liftToFull_mem_quadratic U (G_univ z).1 t
  · intro z i hzi t
    let T : Finset (Fin 15) := U.erase i
    have hT : T.Nonempty := by
      have : T.card = 14 := by simp [T, U]
      exact Finset.card_pos.mp (by omega)
    have hT_card : T.card ≤ 15 := by simp [T, U]
    have hTU : T ⊆ U := Finset.erase_subset i U
    let zT : FaceSimplex T :=
      ⟨z, fun j hjT => by
        by_cases hji : j = i
        · subst hji; exact hzi
        · exact (hjT (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)).elim⟩
    have hinc : faceIncl hTU zT = toFaceU z := by
      apply Subtype.ext; rfl
    have hcompat := sk15.compatible hT hU hT_card hU_card hTU zT
    rw [hinc] at hcompat
    have hG_eq : G_univ z = liftFaceCompl hT hTU (sk15.table T hT hT_card zT) := hcompat
    have hH_eq : H z = liftToFull T (sk15.table T hT hT_card zT).1 := by
      funext w s
      change ((G_univ z).1 s).1 (fun j : U => w j.1) = _
      rw [hG_eq]
      rfl
    rw [hH_eq]
    exact ignoresColor_liftToFull T (sk15.table T hT hT_card zT).1 (Finset.notMem_erase i U) t
  · intro z σ
    let f : Fin 6 → (U → Fin 6) := fun j => fun i : U => σ i.1 j
    let m : Finset (U → Fin 6) := Finset.univ.image f
    have hf_inj : Function.Injective f := by
      intro j₁ j₂ h
      exact (σ 0).injective (congrFun h ⟨0, Finset.mem_univ 0⟩)
    have hm : SixMatching m := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injective Finset.univ hf_inj, Finset.card_univ, Fintype.card_fin]
      · intro i u hu v hv huv
        obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hv
        have hj : j₁ = j₂ := (σ i.1).injective huv
        rw [hj]
      · intro i a
        exact ⟨f ((σ i.1).symm a), Finset.mem_image_of_mem f (Finset.mem_univ _),
          (σ i.1).apply_symm_apply a⟩
    have hnot_mem : (G_univ z).1 ∉ L_M U m := (G_univ z).2 m hm
    by_contra hno
    push Not at hno
    apply hnot_mem
    intro u hu v hv t
    obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hv
    have h1 : H z (fun i => σ i j₁) = H z (fun i => σ i 0) := hno j₁
    have h2 : H z (fun i => σ i j₂) = H z (fun i => σ i 0) := hno j₂
    exact congrFun (h1.trans h2.symm) t

theorem exists_almostSix_of_coherent_comparison
    (P : ComparisonTarget 9) (C : CoherentComparison 9 P) :
    ∃ g : (Fin 90 → ℝ) → (Fin 16 → ℝ), Continuous g ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ j, x j ∈ coordinateSimplex (Fin 90)) → SixDisjointSupports x →
        ∃ j, g (x j) ≠ g (x 0) := by
  obtain ⟨H, hH, hq, hcompat, hsafe⟩ :=
    exists_safe_compatible_quadratic_table_of_coherent_comparison P C
  exact exists_almostSix_of_safe_compatible_quadratic_table H hH hq hcompat hsafe

end CoherentComparisonBridge

end AkopyanResearch




