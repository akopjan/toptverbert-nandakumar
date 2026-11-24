module

public import Submission.Homotopy.CubePair
public import Submission.WhiteheadTheorem.HEP.Cube

/-!
# Removing pauses from a prescribed boundary homotopy

A homotopy on a cube whose boundary is a fixed reparametrisation of the
prescribed homotopy can be corrected without changing either endpoint.
The correction is pasted on the full boundary of the cylinder and then
extended by the actual cubical homotopy extension property.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.CubicalHomotopyRectification

open ContinuousMap
open scoped unitInterval Topology

abbrev Domain (n : ℕ) := Fin n → I
abbrev Boundary (n : ℕ) := {x : Domain n // x ∈ Cube.boundary (Fin n)}

def fullTime {n : ℕ} : C(Boundary (n + 1), I) :=
  ⟨fun x => (Cube.splitAtLast x.val).1,
    continuous_fst.comp (Cube.splitAtLast.continuous.comp continuous_subtype_val)⟩

def fullPoint {n : ℕ} : C(Boundary (n + 1), Domain n) :=
  ⟨fun x => (Cube.splitAtLast x.val).2,
    continuous_snd.comp (Cube.splitAtLast.continuous.comp continuous_subtype_val)⟩

def interpolate (r : C(I, I)) : C(I × I, I) :=
  ⟨fun z => Set.Icc.convexComb (r z.2) z.2 z.1, by fun_prop⟩

@[simp] theorem interpolate_zero (r : C(I, I)) (t : I) : interpolate r (0, t) = r t := by
  simp [interpolate]
@[simp] theorem interpolate_one (r : C(I, I)) (t : I) : interpolate r (1, t) = t := by
  simp [interpolate]

theorem interpolate_at_zero (r : C(I, I)) (hr : r 0 = 0) (u : I) :
    interpolate r (u, 0) = 0 := by simp [interpolate, hr]
theorem interpolate_at_one (r : C(I, I)) (hr : r 1 = 1) (u : I) :
    interpolate r (u, 1) = 1 := by simp [interpolate, hr]

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
variable (f₀ f₁ : C(Domain n, Y)) (eta : C(Boundary n, C(I, Y))) (r : C(I, I))

def correction (z : Boundary (n + 1) × I) : Y := by
  classical
  exact if hs : fullPoint z.1 ∈ Cube.boundary (Fin n) then
    eta ⟨fullPoint z.1, hs⟩ (interpolate r (z.2, fullTime z.1))
  else if fullTime z.1 = 0 then f₀ (fullPoint z.1) else f₁ (fullPoint z.1)

theorem correction_side (z : Boundary (n + 1) × I)
    (hs : fullPoint z.1 ∈ Cube.boundary (Fin n)) :
    correction f₀ f₁ eta r z = eta ⟨fullPoint z.1, hs⟩ (interpolate r (z.2, fullTime z.1)) := by
  rw [correction, dite_eq_left hs]

variable (h₀ : ∀ a : Boundary n, eta a 0 = f₀ a.val)
  (h₁ : ∀ a : Boundary n, eta a 1 = f₁ a.val)
  (hr₀ : r 0 = 0) (hr₁ : r 1 = 1)

include h₀ hr₀ in
theorem correction_bottom (z : Boundary (n + 1) × I) (hz : fullTime z.1 = 0) :
    correction f₀ f₁ eta r z = f₀ (fullPoint z.1) := by
  by_cases hs : fullPoint z.1 ∈ Cube.boundary (Fin n)
  · rw [correction_side f₀ f₁ eta r z hs, hz, interpolate_at_zero r hr₀]
    exact h₀ _
  · rw [correction, dite_eq_right hs, ite_eq_left hz]

include h₁ hr₁ in
theorem correction_top (z : Boundary (n + 1) × I) (hz : fullTime z.1 = 1) :
    correction f₀ f₁ eta r z = f₁ (fullPoint z.1) := by
  by_cases hs : fullPoint z.1 ∈ Cube.boundary (Fin n)
  · rw [correction_side f₀ f₁ eta r z hs, hz, interpolate_at_one r hr₁]
    exact h₁ _
  · rw [correction, dite_eq_right hs, ite_eq_right (by rw [hz]; exact one_ne_zero)]

theorem isClosed_boundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have h := isClosed_iUnion_of_finite (fun j : Fin n =>
    (isClosed_eq (continuous_apply j : Continuous (fun x : Domain n => x j))
      (continuous_const : Continuous (fun _ : Domain n => (0 : I)))).union
      (isClosed_eq (continuous_apply j : Continuous (fun x : Domain n => x j))
        (continuous_const : Continuous (fun _ : Domain n => (1 : I)))))
  convert h using 1
  ext x
  simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]

include h₀ h₁ hr₀ hr₁ in
theorem continuous_correction : Continuous (correction f₀ f₁ eta r) := by
  let A : Set (Boundary (n + 1) × I) := {z | fullPoint z.1 ∈ Cube.boundary (Fin n)}
  let B : Set (Boundary (n + 1) × I) := {z | fullTime z.1 = 0}
  let D : Set (Boundary (n + 1) × I) := {z | fullTime z.1 = 1}
  have hA : IsClosed A := (isClosed_boundary n).preimage (fullPoint.continuous.comp continuous_fst)
  have hB : IsClosed B := isClosed_eq (fullTime.continuous.comp continuous_fst) continuous_const
  have hD : IsClosed D := isClosed_eq (fullTime.continuous.comp continuous_fst) continuous_const
  have hcover : (A ∪ B) ∪ D = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hz := Submission.mem_boundary_iff_splitAtLast.mp z.1.property
    change _ ∨ _ ∨ _ at hz
    rcases hz with hz | hz | hz
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
    · exact Or.inl (Or.inl hz)
  have hcA : ContinuousOn (correction f₀ f₁ eta r) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    let q : C(A, Boundary n) := ⟨fun z => ⟨fullPoint z.val.1, z.property⟩, by fun_prop⟩
    have hc : Continuous (fun z : A => eta (q z) (interpolate r (z.val.2, fullTime z.val.1))) :=
      Continuous.eval (eta.continuous.comp q.continuous)
        ((interpolate r).continuous.comp ((continuous_snd.comp continuous_subtype_val).prodMk
          (fullTime.continuous.comp (continuous_fst.comp continuous_subtype_val))))
    exact hc.congr (fun z => (correction_side f₀ f₁ eta r z.val z.property).symm)
  have hcB : ContinuousOn (correction f₀ f₁ eta r) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (f₀.continuous.comp (fullPoint.continuous.comp
      (continuous_fst.comp continuous_subtype_val))).congr
        (fun z => (correction_bottom f₀ f₁ eta r h₀ hr₀ z.val z.property).symm)
  have hcD : ContinuousOn (correction f₀ f₁ eta r) D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (f₁.continuous.comp (fullPoint.continuous.comp
      (continuous_fst.comp continuous_subtype_val))).congr
        (fun z => (correction_top f₀ f₁ eta r h₁ hr₁ z.val z.property).symm)
  rw [← continuousOn_univ, ← hcover]
  exact (continuousOn_union_iff_of_isClosed (hA.union hB) hD).mpr
    ⟨(continuousOn_union_iff_of_isClosed hA hB).mpr ⟨hcA, hcB⟩, hcD⟩

include h₀ h₁ hr₀ hr₁ in
/-- Correct a boundary reparametrisation while retaining the two exact
endpoint maps on the whole cube. -/
theorem rectify (H : C(I × Domain n, Y))
    (hH₀ : ∀ x, H (0, x) = f₀ x) (hH₁ : ∀ x, H (1, x) = f₁ x)
    (hHb : ∀ (a : Boundary n) t, H (t, a.val) = eta a (r t)) :
    ∃ K : C(I × Domain n, Y),
      (∀ x, K (0, x) = f₀ x) ∧ (∀ x, K (1, x) = f₁ x) ∧
        ∀ (a : Boundary n) t, K (t, a.val) = eta a t := by
  let F : C(Domain (n + 1), Y) := H.comp ⟨Cube.splitAtLast, Cube.splitAtLast.continuous⟩
  let C : C(Boundary (n + 1) × I, Y) :=
    ⟨correction f₀ f₁ eta r, continuous_correction f₀ f₁ eta r h₀ h₁ hr₀ hr₁⟩
  have hinit : F ∘ Cube.boundaryIncl (n + 1) = C ∘ (·, 0) := by
    funext a
    change F a.val = C (a, 0)
    have ha := Submission.mem_boundary_iff_splitAtLast.mp a.property
    rcases ha with ha | ha | ha
    · rw [show C (a, 0) = f₀ (fullPoint a) from correction_bottom f₀ f₁ eta r h₀ hr₀ _ ha]
      change H (fullTime a, fullPoint a) = _
      rw [show fullTime a = 0 from ha, hH₀]
    · rw [show C (a, 0) = f₁ (fullPoint a) from correction_top f₀ f₁ eta r h₁ hr₁ _ ha]
      change H (fullTime a, fullPoint a) = _
      rw [show fullTime a = 1 from ha, hH₁]
    · rw [show C (a, 0) = eta ⟨fullPoint a, ha⟩ (r (fullTime a)) by
        exact (correction_side f₀ f₁ eta r (a, 0) ha).trans (congrArg (eta ⟨fullPoint a, ha⟩) (interpolate_zero r _))]
      exact hHb ⟨fullPoint a, ha⟩ (fullTime a)
  obtain ⟨L, _, hL⟩ := Cube.boundaryIncl_hasHEP (n + 1) Y F C hinit
  let K : C(I × Domain n, Y) :=
    ⟨fun z => L (Cube.splitAtLast.symm z, 1), by fun_prop⟩
  have hLapply (a : Boundary (n + 1)) : K (Cube.splitAtLast a.val) = C (a, 1) := by
    change L (Cube.splitAtLast.symm (Cube.splitAtLast a.val), 1) = C (a, 1)
    rw [Cube.splitAtLast.symm_apply_apply]
    exact (congrFun hL (a, 1)).symm
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x
    let a : Boundary (n + 1) := ⟨Cube.splitAtLast.symm (0, x),
      Submission.mem_boundary_iff_splitAtLast.mpr (by simp)⟩
    have htime : fullTime a = 0 := congrArg Prod.fst (Cube.splitAtLast.apply_symm_apply (0, x))
    have hpoint : fullPoint a = x := congrArg Prod.snd (Cube.splitAtLast.apply_symm_apply (0, x))
    rw [← Cube.splitAtLast.apply_symm_apply (0, x), hLapply a]
    exact (correction_bottom f₀ f₁ eta r h₀ hr₀ _ htime).trans (congrArg f₀ hpoint)
  · intro x
    let a : Boundary (n + 1) := ⟨Cube.splitAtLast.symm (1, x),
      Submission.mem_boundary_iff_splitAtLast.mpr (by simp)⟩
    have htime : fullTime a = 1 := congrArg Prod.fst (Cube.splitAtLast.apply_symm_apply (1, x))
    have hpoint : fullPoint a = x := congrArg Prod.snd (Cube.splitAtLast.apply_symm_apply (1, x))
    rw [← Cube.splitAtLast.apply_symm_apply (1, x), hLapply a]
    exact (correction_top f₀ f₁ eta r h₁ hr₁ _ htime).trans (congrArg f₁ hpoint)
  · intro b t
    let a : Boundary (n + 1) := ⟨Cube.splitAtLast.symm (t, b.val),
      Submission.mem_boundary_iff_splitAtLast.mpr (by simp [b.property])⟩
    have htime : fullTime a = t := congrArg Prod.fst (Cube.splitAtLast.apply_symm_apply (t, b.val))
    have hpoint : fullPoint a = b.val := congrArg Prod.snd (Cube.splitAtLast.apply_symm_apply (t, b.val))
    have hb : fullPoint a ∈ Cube.boundary (Fin n) := hpoint.symm ▸ b.property
    rw [← Cube.splitAtLast.apply_symm_apply (t, b.val), hLapply a]
    change correction f₀ f₁ eta r (a, 1) = _
    rw [correction_side f₀ f₁ eta r _ hb, interpolate_one, htime]
    exact congrArg (fun q : Boundary n => eta q t) (Subtype.ext hpoint)

end AkopyanResearch.CubicalHomotopyRectification
