module

public import AkopyanResearch.Completion.ArrangementConnectivity
public import AkopyanResearch.QuadraticArrangement

/-!
# Homotopy connectivity of the actual quadratic arrangement complement

The matching kernels have codimension ten. Consequently the actual complement
is path connected and its Mathlib homotopy groups vanish in dimensions zero
through eight. These statements concern the ordinary subspace topology.
-/

@[expose] public section
noncomputable section

open scoped Topology Topology.Homotopy

namespace AkopyanResearch

open AkopyanQuadratic ArrangementConnectivity

/-- The two equivalent ways of indexing the actual matching-kernel complement. -/
def quadraticComplementHomeomorph (S : Finset (Fin 15)) :
    QuadComplement S ≃ₜ
      ArrangementConnectivity.Complement
        (fun m : {m : Finset (S → Fin 6) // SixMatching m} => L_M S m.1) where
  toFun x := ⟨x.1, fun m => x.2 m.1 m.2⟩
  invFun x := ⟨x.1, fun m hm => x.2 ⟨m, hm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The complement of all matching kernels is path connected. -/
theorem pathConnectedSpace_quadComplement (S : Finset (Fin 15)) (hS : S.Nonempty) :
    PathConnectedSpace (QuadComplement S) := by
  classical
  let L := fun m : {m : Finset (S → Fin 6) // SixMatching m} => L_M S m.1
  letI : PathConnectedSpace (ArrangementConnectivity.Complement L) :=
    ArrangementConnectivity.pathConnectedSpace_complement L (by
      intro m
      have hq := (L m).finrank_quotient_add_finrank
      have hc := codim_L_M_eq_ten S hS m.1 m.2
      change Module.finrank ℝ (QuadSpace S ⧸ L m) = 10 at hc
      omega)
  exact (quadraticComplementHomeomorph S).symm.surjective.pathConnectedSpace
    (quadraticComplementHomeomorph S).symm.continuous

/-- Every actual based homotopy group in dimensions at most eight is trivial. -/
theorem subsingleton_homotopyGroup_quadComplement (S : Finset (Fin 15))
    (hS : S.Nonempty) (n : ℕ) (hn : n ≤ 8) (b : QuadComplement S) :
    Subsingleton (HomotopyGroup.Pi n (QuadComplement S) b) := by
  classical
  let L := fun m : {m : Finset (S → Fin 6) // SixMatching m} => L_M S m.1
  let e := quadraticComplementHomeomorph S
  have htriv : Subsingleton (HomotopyGroup.Pi n (ArrangementConnectivity.Complement L) (e b)) :=
    ArrangementConnectivity.subsingleton_homotopyGroup_of_codim L n (by
      intro m
      have hc := codim_L_M_eq_ten S hS m.1 m.2
      change n + 2 ≤ Module.finrank ℝ (QuadSpace S ⧸ L_M S m.1)
      omega) (e b)
  let forward : C(QuadComplement S, ArrangementConnectivity.Complement L) := ⟨e, e.continuous⟩
  let backward : C(ArrangementConnectivity.Complement L, QuadComplement S) :=
    ⟨e.symm, e.symm.continuous⟩
  have hcomp : backward.comp forward = ContinuousMap.id (QuadComplement S) := by
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply x
  refine ⟨fun a c => ?_⟩
  have heq := htriv.elim
    (Submission.HomotopyGroup.map forward (rfl : forward b = e b) a)
    (Submission.HomotopyGroup.map forward (rfl : forward b = e b) c)
  have h := congrArg (Submission.HomotopyGroup.map backward (e.symm_apply_apply b)) heq
  simpa only [Submission.HomotopyGroup.map_map_of_comp_eq_id backward forward rfl
    (e.symm_apply_apply b) hcomp] using h

end AkopyanResearch
