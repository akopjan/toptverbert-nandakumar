module

public import AkopyanResearch.Completion.ArrangementLink
public import AkopyanResearch.Completion.ComparisonContract

/-!
# Actual linking nine-spheres in the quadratic arrangement complement

Every matching subspace has codimension ten. Distinct matching subspaces
intersect in codimension at least fourteen, so none contains another.
The general local-link construction therefore gives a continuous section and
retraction between the complement and the ordinary unit nine-sphere.

The last theorem makes the overstrong consequence of the original comparison
interface concrete: it would extend every boundary map into this sphere.
No noncontractibility theorem for spheres is assumed or introduced here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch

open AkopyanQuadratic LocalLink

abbrev MatchingIndex (S : Finset (Fin 15)) :=
  {m : Finset (S → Fin 6) // SixMatching m}

/-- The local linking `S⁹` is an actual retract of the complement. -/
theorem exists_matching_sphere_retract
    (S : Finset (Fin 15)) (hS : S.Nonempty)
    (m : Finset (S → Fin 6)) (hm : SixMatching m) :
    ∃ (s : UnitSphere (EuclideanSpace ℝ (Fin 10)) → QuadComplement S)
      (r : QuadComplement S → UnitSphere (EuclideanSpace ℝ (Fin 10))),
      Continuous s ∧ Continuous r ∧ Function.LeftInverse r s := by
  classical
  letI : Fintype (MatchingIndex S) := Fintype.ofFinite _
  let K : MatchingIndex S → Submodule ℝ (QuadSpace S) := fun j => L_M S j.1
  let i : MatchingIndex S := ⟨m, hm⟩
  have hirredundant : ∀ j : MatchingIndex S, j ≠ i → ¬ K i ≤ K j := by
    intro j hji hle
    have hne : m ≠ j.1 := fun h => hji (Subtype.ext h.symm)
    have hpair := codim_L_M_inf_two_ge_fourteen S hS m j.1 hm j.2 hne
    have hinf : L_M S m ⊓ L_M S j.1 = L_M S m := inf_eq_left.mpr hle
    rw [hinf, codim_L_M_eq_ten S hS m hm] at hpair
    omega
  obtain ⟨s₀, r₀, hs₀, hr₀, hleft⟩ := ArrangementLink.exists_sphere_retract
    K i hirredundant 10 (codim_L_M_eq_ten S hS m hm)
  let forward : ArrangementLink.Complement K → QuadComplement S :=
    fun x => ⟨x.1, fun j hj => x.2 ⟨j, hj⟩⟩
  let backward : QuadComplement S → ArrangementLink.Complement K :=
    fun x => ⟨x.1, fun j => x.2 j.1 j.2⟩
  have hf : Continuous forward := continuous_subtype_val.subtype_mk _
  have hb : Continuous backward := continuous_subtype_val.subtype_mk _
  refine ⟨fun y => forward (s₀ y), fun x => r₀ (backward x),
    hf.comp hs₀, hr₀.comp hb, ?_⟩
  intro y
  exact hleft y

/-- The universal extension consequence holds for the standard nine-sphere,
not only for an abstract retract with unspecified topology. -/
theorem CoherentComparison.extends_boundary_into_nine_sphere
    {P : ComparisonTarget 9} (C : CoherentComparison 9 P)
    (S : Finset (Fin 15)) (hS : S.Nonempty) (hcard : 10 ≤ S.card)
    (m : Finset (S → Fin 6)) (hm : SixMatching m)
    (f : FaceBoundary S → UnitSphere (EuclideanSpace ℝ (Fin 10)))
    (hf : Continuous f) :
    ∃ F : FaceSimplex S → UnitSphere (EuclideanSpace ℝ (Fin 10)),
      Continuous F ∧ ∀ z : FaceBoundary S, F z.1 = f z := by
  obtain ⟨s, r, hs, hr, hleft⟩ := exists_matching_sphere_retract S hS m hm
  exact C.extends_boundary_into_retract S hS hcard s r hs hr hleft f hf

end AkopyanResearch
