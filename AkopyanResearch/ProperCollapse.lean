module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Constructions


@[expose] public section

/-!
# Extension of a proper map by the point at infinity

This elementary lemma is the continuity ingredient for the explicit pair
collapse. It does not assert the existence of the normal chart or a tubular
neighborhood. The open set and its proper coordinate map are inputs.
-/

noncomputable section

namespace AkopyanResearch

open Set
open scoped OnePoint

variable {X Y : Type*}

def properCollapse (U : Set X) (f : U → Y) (x : X) : OnePoint Y := by
  classical
  exact if hx : x ∈ U then (f ⟨x, hx⟩ : OnePoint Y) else ∞

@[simp] theorem properCollapse_of_mem {U : Set X} (f : U → Y)
    {x : X} (hx : x ∈ U) : properCollapse U f x = (f ⟨x, hx⟩ : OnePoint Y) := by
  simp [properCollapse, hx]

@[simp] theorem properCollapse_of_notMem {U : Set X} (f : U → Y)
    {x : X} (hx : x ∉ U) : properCollapse U f x = ∞ := by
  simp [properCollapse, hx]

theorem properCollapse_preimage_of_notMem {U : Set X} (f : U → Y)
    {s : Set (OnePoint Y)} (hs : ∞ ∉ s) :
    properCollapse U f ⁻¹' s =
      Subtype.val '' (f ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' s)) := by
  ext x
  constructor
  · intro hx
    by_cases hu : x ∈ U
    · exact ⟨⟨x, hu⟩, by simpa [properCollapse, hu] using hx, rfl⟩
    · exact False.elim (hs (by simpa [properCollapse, hu] using hx))
  · rintro ⟨y, hy, rfl⟩
    simpa [properCollapse, y.property] using hy

theorem properCollapse_compl_preimage_of_mem {U : Set X} (f : U → Y)
    {s : Set (OnePoint Y)} (hs : ∞ ∈ s) :
    (properCollapse U f ⁻¹' s)ᶜ =
      Subtype.val '' (f ⁻¹' ((((↑) : Y → OnePoint Y) ⁻¹' s)ᶜ)) := by
  simpa only [preimage_compl] using
    properCollapse_preimage_of_notMem f (s := sᶜ) (by simpa using hs)

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- A proper coordinate on an open subset extends continuously by infinity. -/
theorem continuous_properCollapse [T2Space X] {U : Set X}
    (hU : IsOpen U) (f : U → Y) (hf : IsProperMap f) :
    Continuous (properCollapse U f) := by
  apply continuous_def.mpr
  intro s hs
  by_cases hi : ∞ ∈ s
  · have hcompact : IsCompact ((((↑) : Y → OnePoint Y) ⁻¹' s)ᶜ) :=
      (OnePoint.isOpen_def.mp hs).1 hi
    have hc : IsCompact (Subtype.val ''
        (f ⁻¹' ((((↑) : Y → OnePoint Y) ⁻¹' s)ᶜ))) :=
      (hf.isCompact_preimage hcompact).image continuous_subtype_val
    have hclosed : IsClosed (properCollapse U f ⁻¹' s)ᶜ := by
      rw [properCollapse_compl_preimage_of_mem f hi]
      exact hc.isClosed
    exact isClosed_compl_iff.mp hclosed
  · rw [properCollapse_preimage_of_notMem f hi]
    apply hU.isOpenMap_subtype_val
    exact hf.continuous.isOpen_preimage _ ((OnePoint.isOpen_def.mp hs).2)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The fiber coordinate of a product chart with compact base is proper.
This is the continuity statement used after trivializing the pair normal bundle. -/
theorem continuous_compact_chart_collapse [T2Space X] {U : Set X}
    (hU : IsOpen U) (e : U ≃ₜ K × Y) :
    Continuous (properCollapse U (fun x => (e x).2)) := by
  apply continuous_properCollapse hU
  exact isProperMap_snd_of_compactSpace.comp e.isProperMap

end AkopyanResearch
