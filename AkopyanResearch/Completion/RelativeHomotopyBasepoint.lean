module

public import Submission.WhiteheadTheorem.Compressible.Disk
public import Submission.WhiteheadTheorem.HEP.Cofibration

/-!
# Restoring the basepoint in a homotopy of pairs

The restriction of a free pair homotopy to a contractible jar is a loop
of maps into the subspace. Contract the jar, kill the resulting loop by
simple connectedness, and extend the correction twice by HEP. Following
the other three edges of the correction square gives a based homotopy.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.RelativeHomotopyBasepoint

open ContinuousMap
open scoped Topology unitInterval Topology.Homotopy

universe u

theorem loop_null_of_pi1 {X : Type u} [TopologicalSpace X] (x : X)
    (h : Subsingleton (HomotopyGroup.Pi 1 X x)) (p : Path x x) :
    p.Homotopic (Path.refl x) := by
  have : Subsingleton (HomotopyGroup.Pi 1 X x) := h
  have : Subsingleton (FundamentalGroup X x) :=
    (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).symm.subsingleton
  have : Subsingleton (Path.Homotopic.Quotient x x) :=
    (CategoryTheory.End.homEquiv (X := FundamentalGroupoid.mk x)).symm.subsingleton
  exact Path.Homotopic.Quotient.eq.mp (Subsingleton.elim _ _)

section General

variable {J B K X : Type u}
variable [TopologicalSpace J] [TopologicalSpace B] [TopologicalSpace K]
variable [TopologicalSpace X] [ContractibleSpace J]
variable (j : C(J, B)) (i : C(B, K)) (A : Set X) (a : A)

def PairCondition (f : C(K, X)) : Prop := ∀ b, f (i b) ∈ A

def BasedPairCondition (f : C(K, X)) : Prop :=
  PairCondition i A f ∧ ∀ z, f (i (j z)) = a

def boundaryMap (f : C(K, X)) (hf : PairCondition i A f) : C(B, A) :=
  ⟨fun b => ⟨f (i b), hf b⟩, by fun_prop⟩

omit [ContractibleSpace J] in
theorem extend_jar_homotopy
    (hJ : HasHomotopyExtensionProperty j A)
    (hB : HasHomotopyExtensionProperty i X)
    (f : C(K, X)) (hf : PairCondition i A f)
    (h : Homotopy ((boundaryMap i A f hf).comp j) (ContinuousMap.const J a)) :
    ∃ g : C(K, X), BasedPairCondition j i A a g ∧
      ∃ H : HomotopyWith f g (PairCondition i A),
        ∀ t z, H (t, i (j z)) = (h (t, z) : X) := by
  obtain ⟨G₁, hG₁zero, hG₁side⟩ := hJ (boundaryMap i A f hf)
    h.toContinuousMap.argSwap (by funext z; exact (h.apply_zero z).symm)
  let side : C(B × I, X) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp G₁
  obtain ⟨G, hGzero, hGside⟩ := hB f side (by
    funext b
    exact congrArg Subtype.val (congrFun hG₁zero b))
  have hboundary (b : B) (s : I) : G (i b, s) ∈ A := by
    have he := congrFun hGside (b, s)
    change (G₁ (b, s)).val = G (i b, s) at he
    rw [← he]
    exact (G₁ (b, s)).property
  have hjar (z : J) (s : I) : G (i (j z), s) = (h (s, z) : X) := by
    have he := congrFun hGside (j z, s)
    change (G₁ (j z, s)).val = G (i (j z), s) at he
    rw [← he]
    exact congrArg Subtype.val (congrFun hG₁side (z, s)).symm
  let g : C(K, X) := ⟨fun x => G (x, 1), by fun_prop⟩
  refine ⟨g, ⟨fun b => hboundary b 1, ?_⟩, ?_⟩
  · intro z
    exact (hjar z 1).trans (congrArg Subtype.val (h.apply_one z))
  · refine ⟨{
      toFun := fun sx => G (sx.2, sx.1)
      continuous_toFun := by fun_prop
      map_zero_left x := (congrFun hGzero x).symm
      map_one_left _ := rfl
      prop' s b := hboundary b s }, ?_⟩
    exact fun t z => hjar z t

theorem based_representative [PathConnectedSpace A]
    (hJ : HasHomotopyExtensionProperty j A)
    (hB : HasHomotopyExtensionProperty i X)
    (f : C(K, X)) (hf : PairCondition i A f) :
    ∃ g : C(K, X), BasedPairCondition j i A a g ∧
      f.HomotopicWith g (PairCondition i A) := by
  let fb : C(B, A) := ⟨fun b => ⟨f (i b), hf b⟩, by fun_prop⟩
  let fj := fb.comp j
  obtain ⟨z₀, hc⟩ := (contractible_iff_id_nullhomotopic J).mp inferInstance
  let c := hc.some
  let p := (PathConnectedSpace.joined (fj z₀) a).somePath
  let h₀ : Homotopy fj (ContinuousMap.const J (fj z₀)) :=
    (Homotopy.refl fj).comp c
  let h₁ : Homotopy (ContinuousMap.const J (fj z₀)) (ContinuousMap.const J a) := {
    toFun := fun sz => p sz.1
    continuous_toFun := by fun_prop
    map_zero_left _ := p.source
    map_one_left _ := p.target }
  let h := h₀.trans h₁
  obtain ⟨G₁, hG₁zero, hG₁side⟩ := hJ fb h.toContinuousMap.argSwap (by
    funext z
    exact (h.apply_zero z).symm)
  let side : C(B × I, X) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp G₁
  obtain ⟨G, hGzero, hGside⟩ := hB f side (by
    funext b
    exact congrArg Subtype.val (congrFun hG₁zero b))
  have hboundary (b : B) (s : I) : G (i b, s) ∈ A := by
    have he := congrFun hGside (b, s)
    change (G₁ (b, s)).val = G (i b, s) at he
    rw [← he]
    exact (G₁ (b, s)).property
  let g : C(K, X) := ⟨fun x => G (x, 1), by fun_prop⟩
  refine ⟨g, ⟨fun b => hboundary b 1, ?_⟩, ?_⟩
  · intro z
    have he := congrFun hGside (j z, 1)
    change (G₁ (j z, 1)).val = g (i (j z)) at he
    rw [← he]
    have he' := congrFun hG₁side (z, 1)
    change h (1, z) = G₁ (j z, 1) at he'
    rw [← he']
    exact congrArg Subtype.val (h.apply_one z)
  · exact ⟨{
      toFun := fun sx => G (sx.2, sx.1)
      continuous_toFun := by fun_prop
      map_zero_left x := (congrFun hGzero x).symm
      map_one_left _ := rfl
      prop' s b := hboundary b s }⟩

theorem repair_free_homotopy
    (hJ : HasHomotopyExtensionProperty (j.prodMap (ContinuousMap.id I)) A)
    (hB : HasHomotopyExtensionProperty (i.prodMap (ContinuousMap.id I)) X)
    (hπ : Subsingleton (HomotopyGroup.Pi 1 A a))
    {f g : C(K, X)} (hf : BasedPairCondition j i A a f)
    (hg : BasedPairCondition j i A a g)
    (h : f.HomotopicWith g (PairCondition i A)) :
    f.HomotopicWith g (BasedPairCondition j i A a) := by
  let H := h.some
  obtain ⟨z₀, hc⟩ := (contractible_iff_id_nullhomotopic J).mp inferInstance
  let c := hc.some
  let hb : C(B × I, A) :=
    ⟨fun bt => ⟨H (bt.2, i bt.1), H.prop' bt.2 bt.1⟩, by fun_prop⟩
  let hj : C(J × I, A) := hb.comp (j.prodMap (ContinuousMap.id I))
  let p : Path a a := {
    toFun := fun t => hj (z₀, t)
    continuous_toFun := by fun_prop
    source' := by apply Subtype.ext; exact (H.apply_zero _).trans (hf.2 z₀)
    target' := by apply Subtype.ext; exact (H.apply_one _).trans (hg.2 z₀) }
  let q : C(J × I, A) := ⟨fun zt => p zt.2, by fun_prop⟩
  let P : C(J × I, A) → Prop := fun v => ∀ z t, t = 0 ∨ t = 1 → v (z, t) = a
  have hj_end (z : J) (t : I) (ht : t = 0 ∨ t = 1) : hj (z, t) = a := by
    apply Subtype.ext
    rcases ht with rfl | rfl
    · exact (H.apply_zero _).trans (hf.2 z)
    · exact (H.apply_one _).trans (hg.2 z)
  let K₀ : HomotopyWith hj q P := {
    toFun := fun st => hj (c (st.1, st.2.1), st.2.2)
    continuous_toFun := by fun_prop
    map_zero_left zt := by simp only [c, Homotopy.apply_zero, id_apply]
    map_one_left zt := by simp only [c, Homotopy.apply_one, const_apply]; rfl
    prop' s z t ht := hj_end (c (s, z)) t ht }
  let N := (loop_null_of_pi1 a hπ p).some
  let K₁ : HomotopyWith q (ContinuousMap.const _ a) P := {
    toFun := fun st => N (st.1, st.2.2)
    continuous_toFun := by fun_prop
    map_zero_left zt := N.apply_zero zt.2
    map_one_left zt := N.apply_one zt.2
    prop' s z t ht := by
      rcases ht with rfl | rfl
      · exact N.source s
      · exact N.target s }
  let C := K₀.trans K₁
  let ch : C((J × I) × I, A) := C.toHomotopy.toContinuousMap.argSwap
  have hcompat : hb ∘ (j.prodMap (ContinuousMap.id I)) = ch ∘ (·, 0) := by
    funext zt
    exact (C.apply_zero zt).symm
  obtain ⟨G₁, hG₁zero, hG₁side⟩ := hJ hb ch hcompat
  let bottom : C(K × I, X) := ⟨fun xt => H (xt.2, xt.1), by fun_prop⟩
  let side : C((B × I) × I, X) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp G₁
  have hcompat₂ : bottom ∘ (i.prodMap (ContinuousMap.id I)) = side ∘ (·, 0) := by
    funext bt
    exact congrArg Subtype.val (congrFun hG₁zero bt)
  obtain ⟨G, hGzero, hGside⟩ := hB bottom side hcompat₂
  have hG_boundary (b : B) (t s : I) : G ((i b, t), s) ∈ A := by
    have he := congrFun hGside ((b, t), s)
    change (G₁ ((b, t), s)).val = G ((i b, t), s) at he
    rw [← he]
    exact (G₁ ((b, t), s)).property
  have hG_jar (z : J) (t s : I) (hts : (t = 0 ∨ t = 1) ∨ s = 1) :
      G ((i (j z), t), s) = a := by
    have he := congrFun hGside ((j z, t), s)
    change (G₁ ((j z, t), s)).val = G ((i (j z), t), s) at he
    rw [← he]
    have he' := congrFun hG₁side ((z, t), s)
    change C (s, (z, t)) = G₁ ((j z, t), s) at he'
    rw [← he']
    rcases hts with ht | rfl
    · exact congrArg Subtype.val (C.prop' s z t ht)
    · exact congrArg Subtype.val (C.apply_one (z, t))
  let f₁ : C(K, X) := ⟨fun x => G ((x, 0), 1), by fun_prop⟩
  let g₁ : C(K, X) := ⟨fun x => G ((x, 1), 1), by fun_prop⟩
  have hff : f.HomotopicWith f₁ (BasedPairCondition j i A a) := ⟨{
    toFun := fun sx => G ((sx.2, 0), sx.1)
    continuous_toFun := by fun_prop
    map_zero_left x := by
      have he := congrFun hGzero (x, 0)
      change H (0, x) = G ((x, 0), 0) at he
      exact he.symm.trans (H.apply_zero x)
    map_one_left _ := rfl
    prop' s := ⟨fun b => hG_boundary b 0 s,
      fun z => hG_jar z 0 s (Or.inl (Or.inl rfl))⟩ }⟩
  have hfg : f₁.HomotopicWith g₁ (BasedPairCondition j i A a) := ⟨{
    toFun := fun tx => G ((tx.2, tx.1), 1)
    continuous_toFun := by fun_prop
    map_zero_left _ := rfl
    map_one_left _ := rfl
    prop' t := ⟨fun b => hG_boundary b t 1,
      fun z => hG_jar z t 1 (Or.inr rfl)⟩ }⟩
  have hgg : g.HomotopicWith g₁ (BasedPairCondition j i A a) := ⟨{
    toFun := fun sx => G ((sx.2, 1), sx.1)
    continuous_toFun := by fun_prop
    map_zero_left x := by
      have he := congrFun hGzero (x, 1)
      change H (1, x) = G ((x, 1), 0) at he
      exact he.symm.trans (H.apply_one x)
    map_one_left _ := rfl
    prop' s := ⟨fun b => hG_boundary b 1 s,
      fun z => hG_jar z 1 s (Or.inl (Or.inr rfl))⟩ }⟩
  exact hff.trans hfg |>.trans hgg.symm

end General

open TopCat

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {A : Set X} (a : A)

theorem cube_jar_isCofibration :
    IsCofibration (cubeBoundaryJarInclToBoundary.{u} (n + 1)) :=
  (IsCofibration.iff_hasHomotopyExtensionProperty _).mpr
    (fun Y => cubeBoundaryJarInclToBoundary_hasHEP n Y)

def cubeJarMap (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) :
    C(Cube.boundaryJar (n + 1), A) :=
  ⟨fun y => ⟨f y.val, hf y.val (Cube.boundaryJar_subset_boundary _ y.property)⟩,
    by fun_prop⟩

theorem normalize_with_jar_homotopy
    (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f)
    (h : Homotopy (cubeJarMap f hf) (ContinuousMap.const _ a)) :
    ∃ g : RelGenLoop (n + 1) X A a,
      ∃ H : HomotopyWith f g.val (Cube.IsMapOfPairs X A),
        ∀ t y, H (t, y.val) = (h (t, y) : X) := by
  let j := (cubeBoundaryJarInclToBoundary.{u} (n + 1)).hom
  let i := (cubeBoundaryIncl.{u} (n + 1)).hom
  let f' : C(cube.{u} (n + 1), X) := f.comp ⟨ULift.down, continuous_uliftDown⟩
  let hf' : PairCondition i A f' := fun b => hf b.down.val b.down.property
  let h' : Homotopy ((boundaryMap i A f' hf').comp j)
      (ContinuousMap.const (cubeBoundaryJar.{u} (n + 1)) a) := {
    toFun := fun ty => h (ty.1, ty.2.down)
    continuous_toFun := by fun_prop
    map_zero_left y := h.apply_zero y.down
    map_one_left y := h.apply_one y.down }
  obtain ⟨g', hg', H', hH'⟩ := extend_jar_homotopy j i A a
    (cubeBoundaryJarInclToBoundary_hasHEP n A)
    (cubeBoundaryIncl_hasHEP (n + 1) X) f' hf' h'
  let g : RelGenLoop (n + 1) X A a := ⟨
    g'.comp ⟨ULift.up, continuous_uliftUp⟩,
    ⟨fun y hy => hg'.1 ⟨⟨y, hy⟩⟩, fun y hy => hg'.2 ⟨⟨y, hy⟩⟩⟩⟩
  refine ⟨g, {
    toFun := fun ty => H' (ty.1, ⟨ty.2⟩)
    continuous_toFun := by fun_prop
    map_zero_left y := H'.apply_zero ⟨y⟩
    map_one_left y := H'.apply_one ⟨y⟩
    prop' t y hy := H'.prop' t ⟨⟨y, hy⟩⟩ }, ?_⟩
  exact fun t y => hH' t ⟨y⟩

theorem exists_relGenLoop_at_fixed_base [PathConnectedSpace A]
    (f : C(I^Fin (n + 1), X)) (hf : Cube.IsMapOfPairs X A f) :
    ∃ g : RelGenLoop (n + 1) X A a,
      f.HomotopicWith g.val (Cube.IsMapOfPairs X A) := by
  let j := (cubeBoundaryJarInclToBoundary.{u} (n + 1)).hom
  let i := (cubeBoundaryIncl.{u} (n + 1)).hom
  have : ContractibleSpace (cubeBoundaryJar.{u} (n + 1)) :=
    (Homeomorph.ulift : cubeBoundaryJar.{u} (n + 1) ≃ₜ Cube.boundaryJar (n + 1)).contractibleSpace
  let f' : C(cube.{u} (n + 1), X) :=
    f.comp ⟨ULift.down, continuous_uliftDown⟩
  obtain ⟨g', hg', H'⟩ := based_representative j i A a
    (cubeBoundaryJarInclToBoundary_hasHEP n A)
    (cubeBoundaryIncl_hasHEP (n + 1) X) f'
    (fun b => hf b.down.val b.down.property)
  let g : RelGenLoop (n + 1) X A a := ⟨
    g'.comp ⟨ULift.up, continuous_uliftUp⟩,
    ⟨fun y hy => hg'.1 ⟨⟨y, hy⟩⟩, fun y hy => hg'.2 ⟨⟨y, hy⟩⟩⟩⟩
  refine ⟨g, ⟨?_⟩⟩
  exact {
    toFun := fun ty => H'.some (ty.1, ⟨ty.2⟩)
    continuous_toFun := by fun_prop
    map_zero_left y := H'.some.apply_zero ⟨y⟩
    map_one_left y := H'.some.apply_one ⟨y⟩
    prop' t y hy := H'.some.prop' t ⟨⟨y, hy⟩⟩ }

theorem relGenLoop_homotopic_of_free
    (hπ : Subsingleton (HomotopyGroup.Pi 1 A a))
    (f g : RelGenLoop (n + 1) X A a)
    (h : f.val.HomotopicWith g.val (Cube.IsMapOfPairs X A)) :
    RelGenLoop.Homotopic f g := by
  let j := (cubeBoundaryJarInclToBoundary.{u} (n + 1)).hom
  let i := (cubeBoundaryIncl.{u} (n + 1)).hom
  have : ContractibleSpace (cubeBoundaryJar.{u} (n + 1)) :=
    (Homeomorph.ulift : cubeBoundaryJar.{u} (n + 1) ≃ₜ Cube.boundaryJar (n + 1)).contractibleSpace
  have : IsCofibration (cubeBoundaryJarInclToBoundary.{u} (n + 1)) := cube_jar_isCofibration
  have hJ : HasHomotopyExtensionProperty (j.prodMap (ContinuousMap.id I)) A :=
    (IsCofibration.iff_hasHomotopyExtensionProperty _).mp
      (IsCofibration.prod_unitInterval (cubeBoundaryJarInclToBoundary (n + 1))) (TopCat.of A)
  let f' : C(cube.{u} (n + 1), X) := f.val.comp ⟨ULift.down, continuous_uliftDown⟩
  let g' : C(cube.{u} (n + 1), X) := g.val.comp ⟨ULift.down, continuous_uliftDown⟩
  have hf' : BasedPairCondition j i A a f' :=
    ⟨fun b => f.property.1 b.down.val b.down.property,
      fun z => f.property.2 z.down.val z.down.property⟩
  have hg' : BasedPairCondition j i A a g' :=
    ⟨fun b => g.property.1 b.down.val b.down.property,
      fun z => g.property.2 z.down.val z.down.property⟩
  have h' : f'.HomotopicWith g' (PairCondition i A) := ⟨{
    toFun := fun ty => h.some (ty.1, ty.2.down)
    continuous_toFun := by fun_prop
    map_zero_left y := h.some.apply_zero y.down
    map_one_left y := h.some.apply_one y.down
    prop' t b := h.some.prop' t b.down.val b.down.property }⟩
  obtain ⟨H⟩ := repair_free_homotopy j i A a hJ
    (cubeBoundaryIncl_prod_unitInterval_hasHEP (n + 1) X) hπ hf' hg' h'
  exact ⟨{
    toFun := fun ty => H (ty.1, ⟨ty.2⟩)
    continuous_toFun := by fun_prop
    map_zero_left y := H.apply_zero ⟨y⟩
    map_one_left y := H.apply_one ⟨y⟩
    prop' t := ⟨fun y hy => (H.prop' t).1 ⟨⟨y, hy⟩⟩,
      fun y hy => (H.prop' t).2 ⟨⟨y, hy⟩⟩⟩ }⟩

end AkopyanResearch.RelativeHomotopyBasepoint
