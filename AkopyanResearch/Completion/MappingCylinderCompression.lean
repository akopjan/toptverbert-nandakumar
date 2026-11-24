module

public import Submission.Homotopy.Connected
public import Submission.ForMathlib.HomotopyGroup.Basic
public import Submission.WhiteheadTheorem.Compressible.Disk
public import Submission.WhiteheadTheorem.Shapes.DiskHomeoCube

/-!
# Bounded compression into the top of a mapping cylinder

Vanishing of the actual relative homotopy groups gives compression of
cubical maps relative to their full boundary. The zero-dimensional case
uses the path connected source and the actual component-surjectivity map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AkopyanResearch.MappingCylinderCompression

open CategoryTheory TopCat ContinuousMap
open scoped unitInterval Topology

variable {X Y : TopCat} (f : X ⟶ Y) [PathConnectedSpace X]

/-- Actual disk compression through every degree covered by relative
connectivity. -/
theorem disk_top {N n : ℕ}
    (h : Submission.IsNConnectedPair N (MapCyl f) (MapCyl.top f)) (hn : n ≤ N) :
    IsCompressible (diskBoundaryIncl n) (ofHom (MapCyl.domInclFromTop f)) := by
  cases n with
  | zero =>
    let : PathConnectedSpace (MapCyl.top f) := (MapCyl.domHomeoTop f).pathConnectedSpace
    let a : MapCyl.top f := Classical.choice inferInstance
    have : Subsingleton (HomotopyGroup (Fin 0) (MapCyl.top f) a) :=
      Submission.subsingleton_homotopyGroup_zero a
    exact disk.isCompressible_zero_subtype_val_of_bijective_iStar_zero
      (MapCyl f) (MapCyl.top f) a
        ⟨fun _ _ _ => Subsingleton.elim _ _, h.surjective_iStar_zero a⟩
  | succ n =>
    exact disk.isCompressible_subtype_val_of_unique_pi n
      (MapCyl f) (MapCyl.top f) (h.unique_piRel n hn)

abbrev Domain (n : ℕ) := Fin n → I
abbrev Boundary (n : ℕ) := {x : Domain n // x ∈ Cube.boundary (Fin n)}

/-- Compression relative to the complete boundary of a cube. -/
theorem cube {N n : ℕ}
    (h : Submission.IsNConnectedPair N (MapCyl f) (MapCyl.top f)) (hn : n ≤ N)
    (F : C(Domain n, MapCyl f)) (g : C(Boundary n, X))
    (hg : ∀ a : Boundary n, F a.val = MapCyl.domIncl f (g a)) :
    ∃ G : C(Domain n, X), (∀ a : Boundary n, G a.val = g a) ∧
      Nonempty (F.HomotopyRel ((MapCyl.domIncl f).hom.comp G) (Cube.boundary (Fin n))) := by
  let e := diskHomeoCube n
  let b := diskBoundaryHomeoCubeBoundary n
  have he (a : diskBoundary n) : e (diskBoundaryIncl n a) = (b a).val := rfl
  have heb (a : Boundary n) : e.symm a.val = diskBoundaryIncl n (b.symm a) := by
    apply e.injective
    rw [e.apply_symm_apply, he, b.apply_symm_apply]
  let Fd : disk n ⟶ MapCyl f := ofHom (F.comp ⟨e, e.continuous⟩)
  let gd : diskBoundary n ⟶ TopCat.of (MapCyl.top f) :=
    ofHom ((MapCyl.domInclToTop f).comp (g.comp ⟨b, b.continuous⟩))
  have sq : CommSq gd (diskBoundaryIncl n) (ofHom (MapCyl.domInclFromTop f)) Fd := by
    constructor
    ext a
    exact (hg (b a)).symm
  let l := (disk_top f h hn).sq_hasLift sq |>.hasLift.some
  let G : C(Domain n, X) :=
    ⟨fun x => (MapCyl.domHomeoTop f).symm (l.l (e.symm x)), by fun_prop⟩
  have hG (a : Boundary n) : G a.val = g a := by
    change (MapCyl.domHomeoTop f).symm (l.l (e.symm a.val)) = g a
    rw [heb]
    have hl := ConcreteCategory.congr_hom l.fac_left (b.symm a)
    change l.l (diskBoundaryIncl n (b.symm a)) =
      MapCyl.domInclToTop f (g (b (b.symm a))) at hl
    rw [hl, b.apply_symm_apply]
    exact (MapCyl.domHomeoTop f).symm_apply_apply (g a)
  refine ⟨G, hG, ⟨?_⟩⟩
  refine
    { toFun := fun z => l.H.some (z.1, e.symm z.2)
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro x
    change l.H.some (0, e.symm x) = F x
    rw [ContinuousMap.HomotopyWith.apply_zero]
    change F (e (e.symm x)) = F x
    rw [e.apply_symm_apply]
  · intro x
    change l.H.some (1, e.symm x) = MapCyl.domIncl f (G x)
    rw [ContinuousMap.HomotopyWith.apply_one]
    change (l.l (e.symm x)).val =
      MapCyl.domInclFromTop f (MapCyl.domInclToTop f
        ((MapCyl.domHomeoTop f).symm (l.l (e.symm x))))
    rw [show MapCyl.domInclToTop f =
      (⟨MapCyl.domHomeoTop f, (MapCyl.domHomeoTop f).continuous⟩ : C(X, MapCyl.top f)) from rfl]
    simp only [ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]
    rfl
  · intro t x hx
    have hb : e.symm x ∈ Set.range (diskBoundaryIncl n) :=
      ⟨b.symm ⟨x, hx⟩, (heb ⟨x, hx⟩).symm⟩
    have hl := l.H.some.prop' t (e.symm x) hb
    change l.H.some (t, e.symm x) = F x
    exact hl.trans (congrArg F (e.apply_symm_apply x))

end AkopyanResearch.MappingCylinderCompression
