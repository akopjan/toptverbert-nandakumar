module
public import AkopyanResearch.Completion.PhaseExtension
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# Pure phases of a product-labeled colored join

A pure phase of the coordinate join with vertices `G × Bool` is exactly the
coordinate join with vertices `G`. Both inverse maps are explicit coordinate
restriction/insertion, and both are continuous. The homeomorphism is natural
for a permutation of `G` and a permutation of the two phases.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AkopyanResearch.PurePhaseCoordinates

universe u v
variable {C : Type u} {G : Type v} [Fintype C] [Fintype G]

abbrev Pure (b : Bool) := PhaseExtension.Pure (C := C) (Prod.snd : G × Bool → Bool) b

def restrict (b : Bool) (x : Pure (C := C) (G := G) b) : PhaseExtension.Join C G :=
  ⟨fun i => x.val.val (i.1, (i.2, b)), by
    refine ⟨fun i => x.val.property.1 (i.1, (i.2, b)), ?_, ?_⟩
    · have hzero : ∀ c : C, ∀ g : G, x.val.val (c, (g, !b)) = 0 := by
        intro c g
        apply x.property
        change (!b) ≠ b
        cases b <;> decide
      cases b with
      | false =>
        have hz : ∀ c : C, ∀ g : G, x.val.val (c, (g, true)) = 0 := hzero
        simpa only [Fintype.sum_prod_type, Fintype.sum_bool, hz, zero_add]
          using x.val.property.2.1
      | true =>
        have hz : ∀ c : C, ∀ g : G, x.val.val (c, (g, false)) = 0 := hzero
        simpa only [Fintype.sum_prod_type, Fintype.sum_bool, hz, add_zero]
          using x.val.property.2.1
    · intro c a d ha hd
      exact congrArg Prod.fst (x.val.property.2.2 c (a, b) (d, b) ha hd)⟩

def insert (b : Bool) (x : PhaseExtension.Join C G) : Pure (C := C) (G := G) b :=
  ⟨⟨fun i => if i.2.2 = b then x.val (i.1, i.2.1) else 0, by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change 0 ≤ (if i.2.2 = b then x.val (i.1, i.2.1) else 0)
      split_ifs
      · exact x.property.1 _
      · exact le_rfl
    · cases b <;>
        simpa [Fintype.sum_prod_type, Fintype.sum_bool] using x.property.2.1
    · intro c a d ha hd
      have haPhase : a.2 = b := by
        by_contra h
        simp [h] at ha
      have hdPhase : d.2 = b := by
        by_contra h
        simp [h] at hd
      apply Prod.ext
      · apply x.property.2.2 c a.1 d.1
        · simpa only [haPhase, ite_true] using ha
        · simpa only [hdPhase, ite_true] using hd
      · exact haPhase.trans hdPhase.symm⟩, by
    intro i hi
    exact ite_eq_right hi⟩

theorem restrict_insert (b : Bool) (x : PhaseExtension.Join C G) :
    restrict b (insert b x) = x := by
  apply Subtype.ext
  funext i
  change (if b = b then x.val i else 0) = x.val i
  simp

theorem insert_restrict (b : Bool) (x : Pure (C := C) (G := G) b) :
    insert b (restrict b x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  rcases i with ⟨c, g, b'⟩
  change (if b' = b then x.val.val (c, (g, b)) else 0) = x.val.val (c, (g, b'))
  by_cases hb : b' = b
  · subst b'
    simp
  · simp [hb, x.property (c, (g, b')) hb]

theorem continuous_restrict (b : Bool) :
    Continuous (restrict (C := C) (G := G) b) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (i.1, (i.2, b))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_insert (b : Bool) :
    Continuous (insert (C := C) (G := G) b) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact continuous_if_const (i.2.2 = b)
    (fun _ => (continuous_apply (i.1, i.2.1)).comp continuous_subtype_val)
    (fun _ => continuous_const)

/-- Exact coordinate homeomorphism, valid without any nonemptiness assumption. -/
def homeomorph (b : Bool) : Pure (C := C) (G := G) b ≃ₜ PhaseExtension.Join C G where
  toFun := restrict b
  invFun := insert b
  left_inv := insert_restrict b
  right_inv := restrict_insert b
  continuous_toFun := continuous_restrict b
  continuous_invFun := continuous_insert b

@[simp] theorem homeomorph_apply (b : Bool) (x : Pure (C := C) (G := G) b) :
    homeomorph b x = restrict b x := rfl

variable (e : Equiv.Perm G) (ε : Equiv.Perm Bool)

/-- Permuting labels and optionally exchanging phases commutes with restriction. -/
theorem restrict_relabel (b : Bool) (x : Pure (C := C) (G := G) b) :
    restrict (ε b) (PhaseExtension.relabelPure (Prod.snd : G × Bool → Bool)
      (Equiv.prodCongr e ε) ε (fun _ => rfl) b x) =
      PhaseExtension.relabel e (restrict b x) := by
  apply Subtype.ext
  funext i
  change x.val.val (i.1, (e.symm i.2, ε.symm (ε b))) =
    x.val.val (i.1, (e.symm i.2, b))
  rw [ε.symm_apply_apply]

theorem insert_relabel (b : Bool) (x : PhaseExtension.Join C G) :
    PhaseExtension.relabelPure (Prod.snd : G × Bool → Bool)
      (Equiv.prodCongr e ε) ε (fun _ => rfl) b (insert b x) =
      insert (ε b) (PhaseExtension.relabel e x) := by
  apply (homeomorph (ε b)).injective
  change restrict (ε b) _ = restrict (ε b) _
  rw [restrict_relabel, restrict_insert, restrict_insert]

end AkopyanResearch.PurePhaseCoordinates

#print axioms AkopyanResearch.PurePhaseCoordinates.homeomorph
#print axioms AkopyanResearch.PurePhaseCoordinates.restrict_relabel
#print axioms AkopyanResearch.PurePhaseCoordinates.insert_relabel

end
