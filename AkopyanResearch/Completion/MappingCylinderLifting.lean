module

public import AkopyanResearch.Completion.MappingCylinderCompression
public import AkopyanResearch.Completion.CubicalHomotopyRectification

/-!
# Exact relative lifting from bounded mapping-cylinder connectivity

The boundary homotopy is part of the prescribed data. An initial homotopy
extension makes the mapping-cylinder square strict; relative compression
then gives a lift. The pauses introduced by concatenating these homotopies
are removed on the full boundary of the cylinder by cubical HEP.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingCylinderLifting

open CategoryTheory TopCat ContinuousMap
open CubicalHomotopyRectification
open scoped unitInterval Topology

/-- The pause introduced by the two concatenations in the compression
construction. -/
def pause : C(I, I) :=
  ⟨fun t => ⟨max 0 (4 * (t : ℝ) - 3),
    ⟨le_max_left _ _, max_le zero_le_one (by linarith [t.property.2])⟩⟩,
    by fun_prop⟩

@[simp] theorem pause_zero : pause 0 = 0 := by ext; norm_num [pause]
@[simp] theorem pause_one : pause 1 = 1 := by ext; norm_num [pause]

theorem pause_eq_zero {t : I} (ht : (t : ℝ) ≤ 3 / 4) : pause t = 0 := by
  apply Subtype.ext
  change max 0 (4 * (t : ℝ) - 3) = 0
  exact max_eq_left (by linarith)

variable {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
  (g : C(Boundary n, X)) (p : C(Domain n, Y))
  (eta : C(Boundary n, C(I, Y)))
  (h₀ : ∀ a : Boundary n, eta a 0 = f (g a))
  (h₁ : ∀ a : Boundary n, eta a 1 = p a.val)

/-- The specified boundary homotopy in uncurried form. -/
def boundaryHomotopy : (f.hom.comp g).Homotopy (p.comp (Cube.boundaryIncl n)) where
  toContinuousMap := eta.uncurry.argSwap
  map_zero_left := h₀
  map_one_left := h₁

/-- The actual vertical cylinder path over the boundary map. -/
def vertical :
    ((MapCyl.inl f).hom.comp (f.hom.comp g)).Homotopy ((MapCyl.domIncl f).hom.comp g) where
  toFun z := MapCyl.inr f (g z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left a := (ConcreteCategory.congr_hom (MapCyl.condition f) (g a)).symm
  map_one_left _ := rfl

/-- Boundary path from the given target map to the top of the cylinder. -/
def boundaryLift :
    ((MapCyl.inl f).hom.comp (p.comp (Cube.boundaryIncl n))).Homotopy
      ((MapCyl.domIncl f).hom.comp g) :=
  ((Homotopy.refl (MapCyl.inl f).hom).comp
    (boundaryHomotopy f g p eta h₀ h₁).symm).trans (vertical f g)

theorem retr_vertical (t : I) (a : Boundary n) :
    MapCyl.retr f (vertical f g (t, a)) = f (g a) := by
  change (MapCyl.inr f ≫ MapCyl.retr f) (g a, t) = _
  simp only [MapCyl.retr, MapCyl.inr, CategoryTheory.Limits.pushout.inr_desc]
  rfl

/-- Boundary trace of the reverse initial homotopy, after retracting the
mapping cylinder to its base. -/
theorem retr_boundaryLift_symm (t : I) (a : Boundary n) :
    MapCyl.retr f ((boundaryLift f g p eta h₀ h₁).symm (t, a)) =
      if ht : (t : ℝ) ≤ 1 / 2 then f (g a)
      else eta a ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.mpr ⟨(not_le.mp ht).le, t.property.2⟩⟩ := by
  change MapCyl.retr f (boundaryLift f g p eta h₀ h₁ (σ t, a)) = _
  rw [boundaryLift, Homotopy.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [dite_eq_left ht]
    by_cases hs : (σ t : ℝ) ≤ 1 / 2
    · rw [dite_eq_left hs]
      have heq : (t : ℝ) = 1 / 2 := by
        simp only [unitInterval.coe_symm_eq] at hs
        linarith
      change MapCyl.retr f (MapCyl.inl f (eta a (σ _))) = f (g a)
      rw [show (MapCyl.retr f) (MapCyl.inl f (eta a (σ _))) = eta a (σ _) from
        ConcreteCategory.congr_hom (MapCyl.inl_retr_eq_id f) _]
      have hz : (σ (⟨2 * (σ t : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨(σ t).property.1, hs⟩⟩ : I)) = 0 := by
        apply Subtype.ext
        norm_num [unitInterval.coe_symm_eq, heq]
      rw [hz, h₀]
    · rw [dite_eq_right hs]
      exact retr_vertical f g _ a
  · rw [dite_eq_right ht]
    have hs : (σ t : ℝ) ≤ 1 / 2 := by
      simp only [unitInterval.coe_symm_eq]
      linarith
    rw [dite_eq_left hs]
    change MapCyl.retr f (MapCyl.inl f (eta a (σ _))) = _
    rw [show (MapCyl.retr f) (MapCyl.inl f (eta a (σ _))) = eta a (σ _) from
      ConcreteCategory.congr_hom (MapCyl.inl_retr_eq_id f) _]
    congr 1
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq]
    ring

include h₀ h₁ in
/-- Extend a boundary map together with its exact prescribed homotopy,
through any dimension covered by mapping-cylinder connectivity. -/
theorem extend [PathConnectedSpace X] {N : ℕ}
    (h : Submission.IsNConnectedPair N (MapCyl f) (MapCyl.top f)) (hn : n ≤ N) :
    ∃ G : C(Domain n, X), ∃ H : C(Domain n, C(I, Y)),
      (∀ a : Boundary n, G a.val = g a) ∧
      (∀ a : Boundary n, H a.val = eta a) ∧
      (∀ x, H x 0 = f (G x)) ∧ (∀ x, H x 1 = p x) := by
  let B := boundaryLift f g p eta h₀ h₁
  obtain ⟨K, hK₀, hKb⟩ := Cube.boundaryIncl_hasHEP n (MapCyl f)
    ((MapCyl.inl f).hom.comp p) B.toContinuousMap.argSwap (by
      funext a
      exact (B.apply_zero a).symm)
  let F : C(Domain n, MapCyl f) := ⟨fun x => K (x, 1), by fun_prop⟩
  have hKside (a : Boundary n) (t : I) : K (a.val, t) = B (t, a) :=
    (congrFun hKb (a, t)).symm
  have hF (a : Boundary n) : F a.val = MapCyl.domIncl f (g a) :=
    (hKside a 1).trans (B.apply_one a)
  obtain ⟨G, hG, ⟨J⟩⟩ := MappingCylinderCompression.cube f h hn F g hF
  let K' : ((MapCyl.inl f).hom.comp p).Homotopy F :=
    { toContinuousMap := K.argSwap
      map_zero_left := fun x => (congrFun hK₀ x).symm
      map_one_left := fun _ => rfl }
  let L := (Homotopy.refl (MapCyl.retr f).hom).comp
    (J.toHomotopy.symm.trans K'.symm)
  have hL₀ (x) : L (0, x) = f (G x) := by
    rw [L.apply_zero]
    exact ConcreteCategory.congr_hom (MapCyl.domIncl_retr_eq f) (G x)
  have hL₁ (x) : L (1, x) = p x := by
    rw [L.apply_one]
    exact ConcreteCategory.congr_hom (MapCyl.inl_retr_eq_id f) (p x)
  have hLb (a : Boundary n) (t : I) : L (t, a.val) = eta a (pause t) := by
    change MapCyl.retr f ((J.toHomotopy.symm.trans K'.symm) (t, a.val)) = _
    rw [Homotopy.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [dite_eq_left ht]
      let v : I := ⟨2 * (t : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨t.property.1, ht⟩⟩
      change MapCyl.retr f (J (σ v, a.val)) = _
      have hJ : J (σ v, a.val) = F a.val := J.prop' (σ v) a.val a.property
      rw [hJ, hF]
      rw [show MapCyl.retr f (MapCyl.domIncl f (g a)) = f (g a) from
        ConcreteCategory.congr_hom (MapCyl.domIncl_retr_eq f) (g a)]
      rw [pause_eq_zero (by linarith), h₀]
    · rw [dite_eq_right ht]
      let u : I := ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.mpr ⟨(not_le.mp ht).le, t.property.2⟩⟩
      change MapCyl.retr f (K (a.val, σ u)) = _
      rw [hKside]
      change MapCyl.retr f ((boundaryLift f g p eta h₀ h₁).symm (u, a)) = _
      rw [retr_boundaryLift_symm]
      by_cases hu : (u : ℝ) ≤ 1 / 2
      · rw [dite_eq_left hu, pause_eq_zero (by dsimp [u] at hu; linarith), h₀]
      · rw [dite_eq_right hu]
        congr 1
        apply Subtype.ext
        change 2 * (2 * (t : ℝ) - 1) - 1 = max 0 (4 * (t : ℝ) - 3)
        rw [max_eq_right (by dsimp [u] at hu; linarith)]
        ring
  obtain ⟨L', hL'₀, hL'₁, hL'b⟩ := CubicalHomotopyRectification.rectify
    (f.hom.comp G) p eta pause (fun a => (h₀ a).trans (congrArg f (hG a).symm))
      h₁ pause_zero pause_one L.toContinuousMap hL₀ hL₁ hLb
  refine ⟨G, L'.argSwap.curry, hG, ?_, hL'₀, hL'₁⟩
  intro a
  ext t
  exact hL'b a t

end AkopyanResearch.MappingCylinderLifting
