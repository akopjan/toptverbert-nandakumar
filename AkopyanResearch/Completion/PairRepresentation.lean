module

public import AkopyanResearch.Completion.PairSourceProjections
public import AkopyanResearch.Completion.MatchingSphereMap
public import Mathlib.Data.Fintype.Sum

/-!
# Coverage of four-common-word matching pairs by the actual pair source

This finite construction uses the actual `PairState`, `firstVertex`,
`secondVertex`, and `matchingWords` definitions. It does not assume an orbit
classification or a topological comparison theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AkopyanResearch.PairRepresentation

open scoped Classical
open AkopyanQuadratic OriginalJoinBridge PairSphereAction PairSourceProjections
open MatchingSphereMap

theorem exists_enumeration_extending_four {β : Type*} [DecidableEq β]
    (m : Finset β) (hm : m.card = 6) (f : Fin 4 ↪ β)
    (hf : ∀ i, f i ∈ m) :
    ∃ e : Fin 6 ≃ m, ∀ i : Fin 4, (e (i.castAdd 2)).val = f i := by
  let f' : Fin 6 → β := fun j =>
    Fin.addCases (m := 4) (n := 2) (fun i => f i) (fun _ => f 0) j
  let s : Set (Fin 6) := Set.range (fun i : Fin 4 => i.castAdd 2)
  have hmap : Set.MapsTo f' s m := by
    rintro _ ⟨i, rfl⟩
    simpa [f'] using hf i
  have hinj : Set.InjOn f' s := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have h : i = j := f.injective (by simpa [f'] using hij)
    exact congrArg (fun k : Fin 4 => k.castAdd 2) h
  obtain ⟨e, he⟩ := hmap.exists_equiv_extend_of_card_eq
    (by simpa only [Fintype.card_fin] using hm.symm) hinj
  refine ⟨e, fun i => ?_⟩
  simpa [f'] using he (i.castAdd 2) ⟨i, rfl⟩

def enumerationPermutation {I : Type*} {m : Finset (I → Fin 6)}
    (hm : SixMatching m) (e : Fin 6 ≃ m) (c : I) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (fun j => (e j).val c) (by
    constructor
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hm.2.1 c _ (e i).property _ (e j).property hij
    · intro a
      obtain ⟨u, hu, hua⟩ := hm.2.2 c a
      refine ⟨e.symm ⟨u, hu⟩, ?_⟩
      simpa only [e.apply_symm_apply] using hua)

@[simp] theorem enumerationPermutation_apply {I : Type*}
    {m : Finset (I → Fin 6)} (hm : SixMatching m) (e : Fin 6 ≃ m)
    (c : I) (j : Fin 6) : enumerationPermutation hm e c j = (e j).val c := rfl

theorem matchingWords_enumeration {S : Finset (Fin 15)}
    {m : Finset (S → Fin 6)} (hm : SixMatching m) (e : Fin 6 ≃ m) :
    matchingWords (enumerationPermutation hm e) = m := by
  ext u
  constructor
  · intro hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact (e j).property
  · intro hu
    apply Finset.mem_image.mpr
    refine ⟨e.symm ⟨u, hu⟩, Finset.mem_univ _, ?_⟩
    change (fun c => (e (e.symm ⟨u, hu⟩)).val c) = u
    simp only [e.apply_symm_apply]

theorem permutation_fixing_four (ρ : Equiv.Perm (Fin 6))
    (hρ : ∀ i : Fin 4, ρ (i.castAdd 2) = i.castAdd 2) :
    ∃ b : Bool, ρ = blockPerm 1 b := by
  have h0 : ρ 0 = 0 := hρ 0
  have h1 : ρ 1 = 1 := hρ 1
  have h2 : ρ 2 = 2 := hρ 2
  have h3 : ρ 3 = 3 := hρ 3
  have hlarge (i : Fin 6) (hi : 4 ≤ i.val) : 4 ≤ (ρ i).val := by
    by_contra h
    let j : Fin 4 := ⟨(ρ i).val, by omega⟩
    have he : ρ i = ρ (j.castAdd 2) := by
      rw [hρ j]
      apply Fin.ext
      rfl
    have he' := congrArg Fin.val (ρ.injective he)
    change i.val = j.val at he'
    have hj := j.isLt
    omega
  have h4 : ρ 4 = 4 ∨ ρ 4 = 5 := by
    have := hlarge 4 (by decide)
    omega
  have h5 : ρ 5 = 4 ∨ ρ 5 = 5 := by
    have := hlarge 5 (by decide)
    omega
  have hne : ρ 4 ≠ ρ 5 := ρ.injective.ne (by decide)
  rcases h4 with h4 | h4
  · have h5 : ρ 5 = 5 := by
      rcases h5 with h5 | h5
      · exact False.elim (hne (h4.trans h5.symm))
      · exact h5
    refine ⟨false, ?_⟩
    apply Equiv.ext
    intro i
    fin_cases i <;> simp [h0, h1, h2, h3, h4, h5, blockPerm, liftPerm4_one]
  · have h5 : ρ 5 = 4 := by
      rcases h5 with h5 | h5
      · exact h5
      · exact False.elim (hne (h4.trans h5.symm))
    refine ⟨true, ?_⟩
    apply Equiv.ext
    intro i
    fin_cases i <;>
      simp [h0, h1, h2, h3, h4, h5, blockPerm, liftPerm4_one, swap45] <;> decide

/-- Every pair of six-matchings with four common words is represented by
the actual two row projections of a family of `PairState`s. -/
theorem exists_pair_labels {S : Finset (Fin 15)}
    (m n : Finset (S → Fin 6)) (hm : SixMatching m) (hn : SixMatching n)
    (hcommon : (m ∩ n).card = 4) :
    ∃ ω : S → PairState,
      matchingWords (firstVertex ∘ ω) = m ∧
      matchingWords (secondVertex ∘ ω) = n := by
  let ec : Fin 4 ≃ ↥(m ∩ n) :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hcommon)).symm
  let f : Fin 4 ↪ (S → Fin 6) :=
    ⟨fun i => (ec i).val, fun i j hij => ec.injective (Subtype.ext hij)⟩
  obtain ⟨em, hem⟩ := exists_enumeration_extending_four m hm.1 f
    (fun i => (Finset.mem_inter.mp (ec i).property).1)
  obtain ⟨en, hen⟩ := exists_enumeration_extending_four n hn.1 f
    (fun i => (Finset.mem_inter.mp (ec i).property).2)
  let σ : S → Equiv.Perm (Fin 6) := enumerationPermutation hm em
  let τ : S → Equiv.Perm (Fin 6) := enumerationPermutation hn en
  have hfix (c : S) (i : Fin 4) :
      ((σ c)⁻¹ * τ c) (i.castAdd 2) = i.castAdd 2 := by
    change (σ c).symm (τ c (i.castAdd 2)) = i.castAdd 2
    apply (σ c).injective
    simp only [Equiv.apply_symm_apply]
    change (en (i.castAdd 2)).val c = (em (i.castAdd 2)).val c
    rw [hen i, hem i]
  have hb (c : S) : ∃ b : Bool, (σ c)⁻¹ * τ c = blockPerm 1 b :=
    permutation_fixing_four _ (hfix c)
  choose b hb using hb
  have hτ (c : S) : τ c = σ c * blockPerm 1 (b c) := by
    simpa only [mul_inv_cancel_left] using congrArg (fun q => σ c * q) (hb c)
  let ω : S → PairState := fun c => (σ c, b c)
  refine ⟨ω, ?_, ?_⟩
  · exact matchingWords_enumeration hm em
  · have he : secondVertex ∘ ω = τ := by
      funext c
      exact (hτ c).symm
    rw [he]
    exact matchingWords_enumeration hn en

end AkopyanResearch.PairRepresentation
