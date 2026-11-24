module

public import AkopyanResearch.Completion.TableRealization
public import AkopyanResearch.Completion.SimplexEmbedding

/-!
# The fifteen-colour continuous-table reduction

This theorem removes the quadratic ansatz from the realization step. It is
conditional on an actual continuous, compatible, safe table. It does not
prove that such a table exists, nor the convex-partition counterexample.
-/

@[expose] public section

set_option autoImplicit false

namespace AkopyanResearch.TableToEmbedding

abbrev PlanarTable := TableRealization.HeightTable (Fin 15) (Fin 6) (Fin 2)

/-- Any continuous compatible safe table on fifteen colours gives an almost-six
map from the simplex with ninety vertices to sixteen-dimensional space.
No polynomial-degree hypothesis appears. -/
theorem exists_almostSix_of_continuous_table (H : PlanarTable)
    (hH : Continuous H) (hcompat : TableRealization.Compatible H)
    (hsafe : TableRealization.Safe 0 H) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ,
      ContinuousOn g (SimplexEmbedding.simplexSet (Fin 90)) ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ r : Fin 6, x r ∈ SimplexEmbedding.simplexSet (Fin 90)) →
        SimplexEmbedding.DisjointSupports x →
        ∃ r : Fin 6, g (x r) ≠ g (x 0) := by
  obtain ⟨h, hh, hs⟩ := TableRealization.exists_height_separating_equal_mass
    H hH hcompat 0 hsafe
  apply SimplexEmbedding.exists_almostSix_of_height_separates_equal_mass h hh
  intro x hd hm
  apply hs x hd
  intro j
  apply Subtype.ext
  funext c
  exact hm j c

/-- The same conclusion with a continuous extension to the entire ambient
coordinate space, obtained by the Tietze extension theorem. -/
theorem exists_continuous_almostSix_of_continuous_table (H : PlanarTable)
    (hH : Continuous H) (hcompat : TableRealization.Compatible H)
    (hsafe : TableRealization.Safe 0 H) :
    ∃ g : (Fin 90 → ℝ) → Fin 16 → ℝ,
      Continuous g ∧
      ∀ x : Fin 6 → Fin 90 → ℝ,
        (∀ r : Fin 6, x r ∈ SimplexEmbedding.simplexSet (Fin 90)) →
        SimplexEmbedding.DisjointSupports x →
        ∃ r : Fin 6, g (x r) ≠ g (x 0) := by
  obtain ⟨h, hh, hs⟩ := TableRealization.exists_height_separating_equal_mass
    H hH hcompat 0 hsafe
  apply SimplexEmbedding.exists_continuous_almostSix_of_height_separates_equal_mass h hh
  intro x hd hm
  apply hs x hd
  intro j
  apply Subtype.ext
  funext c
  exact hm j c

end AkopyanResearch.TableToEmbedding

