module

public import AkopyanResearch.Completion.LocalLink
public import RequestProject.Surgery.Avoid

/-!
# Linking spheres are retracts of finite arrangement complements

For any selected subspace which is not contained in another member of a finite
real linear arrangement, the sphere in its normal quotient is a retract of the
complement. Both maps are constructed; the generic centre is obtained by avoiding
a finite union of proper subspaces inside the selected subspace.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.ArrangementLink

open LocalLink

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev Complement {ι : Type*} (K : ι → Submodule ℝ E) :=
  {x : E // ∀ j, x ∉ K j}

/-- A linear normal quotient with values in standard Euclidean space. -/
def normalMap (K : Submodule ℝ E) (n : ℕ)
    (hcodim : Module.finrank ℝ (E ⧸ K) = n) :
    E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    ((LinearEquiv.ofFinrankEq (E ⧸ K) (EuclideanSpace ℝ (Fin n)) (by
      simpa only [finrank_euclideanSpace_fin] using hcodim)).toLinearMap.comp K.mkQ)

theorem normalMap_eq_zero_iff (K : Submodule ℝ E) (n : ℕ)
    (hcodim : Module.finrank ℝ (E ⧸ K) = n) (x : E) :
    normalMap K n hcodim x = 0 ↔ x ∈ K := by
  change (LinearEquiv.ofFinrankEq (E ⧸ K) (EuclideanSpace ℝ (Fin n)) _ :
    (E ⧸ K) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (K.mkQ x) = 0 ↔ x ∈ K
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero K

theorem normalMap_surjective (K : Submodule ℝ E) (n : ℕ)
    (hcodim : Module.finrank ℝ (E ⧸ K) = n) :
    Function.Surjective (normalMap K n hcodim) :=
  (LinearEquiv.ofFinrankEq (E ⧸ K) (EuclideanSpace ℝ (Fin n)) (by
    simpa only [finrank_euclideanSpace_fin] using hcodim)).surjective.comp K.mkQ_surjective

theorem exists_sphere_retract {ι : Type*} [Fintype ι]
    (K : ι → Submodule ℝ E) (i : ι)
    (hirredundant : ∀ j, j ≠ i → ¬ K i ≤ K j)
    (n : ℕ) (hcodim : Module.finrank ℝ (E ⧸ K i) = n) :
    ∃ (s : UnitSphere (EuclideanSpace ℝ (Fin n)) → Complement K)
      (r : Complement K → UnitSphere (EuclideanSpace ℝ (Fin n))),
      Continuous s ∧ Continuous r ∧ Function.LeftInverse r s := by
  classical
  let others : Finset ι := Finset.univ.erase i
  obtain ⟨a, ha, hother⟩ := Surgery.exists_mem_not_mem_finset_submodule
    (K i) others K (fun j hj => hirredundant j (Finset.mem_erase.mp hj).1)
  let U : Set E := {x | ∀ j, j ≠ i → x ∉ K j}
  have hU : IsOpen U := by
    have heq : U = ⋂ j : ι, ⋂ (_ : j ≠ i), (K j : Set E)ᶜ := by
      ext x
      simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      (K j).closed_of_finiteDimensional.isOpen_compl
  have haU : a ∈ U := by
    intro j hji
    exact hother j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
  let Q := normalMap (K i) n hcodim
  have hQsurj : Function.Surjective Q := normalMap_surjective (K i) n hcodim
  obtain ⟨L₀, hL₀⟩ := Q.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hQsurj)
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] E := LinearMap.toContinuousLinearMap L₀
  have hL : Function.LeftInverse Q L := by
    intro y
    exact LinearMap.congr_fun hL₀ y
  have hQa : Q a = 0 := (normalMap_eq_zero_iff (K i) n hcodim a).mpr ha
  obtain ⟨s₀, hs₀, hrs₀⟩ := exists_linking_sphere_retract Q L hL U hU a haU hQa
  let forward : PuncturedNeighbourhood Q U → Complement K := fun x =>
    ⟨x.1, fun j => by
      by_cases hji : j = i
      · subst j
        exact fun h => x.2.2 ((normalMap_eq_zero_iff (K i) n hcodim x.1).mpr h)
      · exact x.2.1 j hji⟩
  let backward : Complement K → PuncturedNeighbourhood Q U := fun x =>
    ⟨x.1, fun j _ => x.2 j,
      fun h => x.2 i ((normalMap_eq_zero_iff (K i) n hcodim x.1).mp h)⟩
  have hforward : Continuous forward := continuous_subtype_val.subtype_mk _
  have hbackward : Continuous backward := continuous_subtype_val.subtype_mk _
  refine ⟨fun y => forward (s₀ y), fun x => normalProjection Q U (backward x),
    hforward.comp hs₀, (continuous_normalProjection Q U).comp hbackward, ?_⟩
  intro y
  exact hrs₀ y

end AkopyanResearch.ArrangementLink
