module
public import AkopyanResearch.Completion.JoinCoordinates
public import AkopyanResearch.Completion.EquivariantJoinIteration
public import Mathlib.Algebra.Group.Units.Equiv

@[expose] public section

/-!
# Iterated quotient joins in finite colored coordinates

Binary quotient joins preserve homeomorphisms of both factors. Recursively
using the actual binary coordinate homeomorphism and its one-color base
identifies every finite iterated join with the coordinate colored join.
The colors can then be relabeled by `Fin (k+1)`. Vertex permutations and the
regular left group action are respected exactly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AkopyanResearch.IteratedJoinCoordinates

open EquivariantJoinStep EquivariantJoinIteration

section Binary
variable {A B A' B' : Type*}

def joinMap (f : A → A') (g : B → B') : Join A B → Join A' B' :=
  Quot.map (fun p => (p.1, f p.2.1, g p.2.2)) (by
    intro p q h
    rcases h with ⟨ht, hs, hx⟩ | ⟨ht, hs, hy⟩
    · exact Or.inl ⟨ht, hs, congrArg f hx⟩
    · exact Or.inr ⟨ht, hs, congrArg g hy⟩)

@[simp] theorem joinMap_mk (f : A → A') (g : B → B') (t : Time) (x : A) (y : B) :
    joinMap f g (joinMk t x y) = joinMk t (f x) (g y) := rfl

variable [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace A'] [TopologicalSpace B']

theorem continuous_joinMap (f : A → A') (g : B → B')
    (hf : Continuous f) (hg : Continuous g) : Continuous (joinMap f g) := by
  apply continuous_quot_map
  exact continuous_fst.prodMk ((hf.comp continuous_snd.fst).prodMk
    (hg.comp continuous_snd.snd))

def joinCongr (f : A ≃ₜ A') (g : B ≃ₜ B') : Join A B ≃ₜ Join A' B' where
  toFun := joinMap f g
  invFun := joinMap f.symm g.symm
  left_inv z := by
    induction z using Quot.inductionOn with
    | h p =>
      rcases p with ⟨t, x, y⟩
      change joinMk t (f.symm (f x)) (g.symm (g y)) = joinMk t x y
      rw [f.symm_apply_apply, g.symm_apply_apply]
  right_inv z := by
    induction z using Quot.inductionOn with
    | h p =>
      rcases p with ⟨t, x, y⟩
      change joinMk t (f (f.symm x)) (g (g.symm y)) = joinMk t x y
      rw [f.apply_symm_apply, g.apply_symm_apply]
  continuous_toFun := continuous_joinMap f g f.continuous g.continuous
  continuous_invFun := continuous_joinMap f.symm g.symm f.symm.continuous g.symm.continuous

end Binary

section ColorChange
universe u v w
variable {C : Type u} {D : Type v} {V : Type w}
variable [Fintype C] [Fintype D] [Fintype V]

def colorMap (e : C ≃ D) (x : PhaseExtension.Join C V) : PhaseExtension.Join D V :=
  ⟨fun i => x.val (e.symm i.1, i.2), by
    refine ⟨fun i => x.property.1 _, ?_, ?_⟩
    · exact (Equiv.sum_comp (Equiv.prodCongr e.symm (Equiv.refl V)) x.val).trans x.property.2.1
    · intro d a b ha hb
      exact x.property.2.2 (e.symm d) a b ha hb⟩

theorem continuous_colorMap (e : C ≃ D) : Continuous (colorMap (V := V) e) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (e.symm i.1, i.2)).comp continuous_subtype_val

def colorHomeomorph (e : C ≃ D) : PhaseExtension.Join C V ≃ₜ PhaseExtension.Join D V where
  toFun := colorMap e
  invFun := colorMap e.symm
  left_inv x := by
    apply Subtype.ext
    funext i
    change x.val (e.symm (e i.1), i.2) = x.val i
    rw [e.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    funext i
    change x.val (e (e.symm i.1), i.2) = x.val i
    rw [e.apply_symm_apply]
  continuous_toFun := continuous_colorMap e
  continuous_invFun := continuous_colorMap e.symm

theorem colorMap_relabel (e : C ≃ D) (p : Equiv.Perm V) (x : PhaseExtension.Join C V) :
    colorMap e (PhaseExtension.relabel p x) = PhaseExtension.relabel p (colorMap e x) := by
  apply Subtype.ext
  rfl

end ColorChange

/-- One new color for each binary join with a vertex set. -/
def Colors : ℕ → Type
  | 0 => Unit
  | k + 1 => Colors k ⊕ Unit

instance colorsFintype (k : ℕ) : Fintype (Colors k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Colors k ⊕ Unit))

instance colorsNonempty (k : ℕ) : Nonempty (Colors k) := by
  cases k with
  | zero => exact ⟨()⟩
  | succ k => exact ⟨Sum.inr ()⟩

theorem card_colors (k : ℕ) : Fintype.card (Colors k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change Fintype.card (Colors k ⊕ Unit) = (k + 1) + 1
      simp only [Fintype.card_sum, Fintype.card_unique, ih]

def colorsEquivFin (k : ℕ) : Colors k ≃ Fin (k + 1) := by
  classical
  exact (Fintype.equivFin (Colors k)).trans (finCongr (card_colors k))

universe u
variable {G : Type u} [Fintype G] [Nonempty G] [TopologicalSpace G] [DiscreteTopology G]

/-- Every step uses the actual quotient-to-coordinate homeomorphism. -/
def homeomorph : (k : ℕ) → IteratedJoin G G k ≃ₜ PhaseExtension.Join (Colors k) G
  | 0 => JoinCoordinates.unitHomeomorph (V := G)
  | k + 1 =>
      (joinCongr (homeomorph k) (JoinCoordinates.unitHomeomorph (V := G))).trans JoinCoordinates.homeomorph

/-- The same homeomorphism with the standard `Fin (k+1)` color indexing. -/
def finHomeomorph (k : ℕ) : IteratedJoin G G k ≃ₜ PhaseExtension.Join (Fin (k + 1)) G :=
  (homeomorph k).trans (colorHomeomorph (colorsEquivFin k))

@[simp] theorem homeomorph_zero (g : G) :
    homeomorph 0 g = JoinCoordinates.vertex () g := rfl

@[simp] theorem homeomorph_succ_mk (k : ℕ) (t : Time) (x : IteratedJoin G G k) (g : G) :
    homeomorph (k + 1) (joinMk t x g) =
      JoinCoordinates.mix (t, homeomorph k x, JoinCoordinates.vertex () g) := rfl

omit [Nonempty G] [TopologicalSpace G] [DiscreteTopology G] in
theorem vertex_relabel (p : Equiv.Perm G) (g : G) :
    PhaseExtension.relabel p (JoinCoordinates.vertex () g) = JoinCoordinates.vertex () (p g) := by
  classical
  apply Subtype.ext
  funext i
  rcases i with ⟨c, v⟩
  cases c
  simp [PhaseExtension.relabel, JoinCoordinates.vertex, Equiv.symm_apply_eq]

section Action
variable [Group G]

/-- The regular left action agrees with the actual permutation action on
vertex-coordinate weights. -/
theorem homeomorph_equivariant (k : ℕ) (a : G) (x : IteratedJoin G G k) :
    homeomorph k (a • x) = PhaseExtension.relabel (Equiv.mulLeft a) (homeomorph k x) := by
  induction k with
  | zero =>
      change JoinCoordinates.vertex () (a * (show G from x)) =
        PhaseExtension.relabel (Equiv.mulLeft a) (JoinCoordinates.vertex () (show G from x))
      simpa only [Equiv.coe_mulLeft] using (vertex_relabel (Equiv.mulLeft a) (show G from x)).symm
  | succ k ih =>
      induction x using Quot.inductionOn with
      | h p =>
          rcases p with ⟨t, y, g⟩
          change JoinCoordinates.mix (t, homeomorph k (a • y), JoinCoordinates.vertex () (a * g)) =
            PhaseExtension.relabel (Equiv.mulLeft a)
              (JoinCoordinates.mix (t, homeomorph k y, JoinCoordinates.vertex () g))
          have hv := vertex_relabel (Equiv.mulLeft a) g
          simp only [Equiv.coe_mulLeft] at hv
          rw [ih, ← hv]
          exact JoinCoordinates.toCoordinates_relabel (Equiv.mulLeft a)
            (joinMk t (homeomorph k y) (JoinCoordinates.vertex () g))

theorem finHomeomorph_equivariant (k : ℕ) (a : G) (x : IteratedJoin G G k) :
    finHomeomorph k (a • x) = PhaseExtension.relabel (Equiv.mulLeft a) (finHomeomorph k x) := by
  change colorMap (colorsEquivFin k) (homeomorph k (a • x)) =
    PhaseExtension.relabel (Equiv.mulLeft a) (colorMap (colorsEquivFin k) (homeomorph k x))
  rw [homeomorph_equivariant, colorMap_relabel]

end Action
end AkopyanResearch.IteratedJoinCoordinates

#print axioms AkopyanResearch.IteratedJoinCoordinates.homeomorph
#print axioms AkopyanResearch.IteratedJoinCoordinates.finHomeomorph
#print axioms AkopyanResearch.IteratedJoinCoordinates.finHomeomorph_equivariant

end
