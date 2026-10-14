/-
# Axiom audit

Run `lake env lean Axioms.lean` to print the axioms each main theorem depends on.
Nothing here may mention `sorryAx`; the only axioms allowed are Lean's three standard
ones (`propext`, `Classical.choice`, `Quot.sound`).  `Classical.choice` can only appear
in results that talk about `ShortestDistance`, whose definition uses an infinitary
`iInf` over all walks (a `noncomputable` mathematical object); the *implementation* and
its termination/reconstruction facts are fully computational.
-/
import Dijkstra

open Dijkstra

-- The implementation is computable: no `noncomputable`, no `partial`, no `unsafe`.
#eval dijkstraOpt Examples.g2 0 4 -- some 4

/-! ### Requirement A: termination -/
#print axioms dijkstra_terminated
#print axioms dijkstra_step_none
#print axioms dijkstra_fixpoint
#print axioms dijkstra_terminates
#print axioms loop_progress

/-! ### Requirement B: relaxation correctness -/
#print axioms Inv.realized
#print axioms Inv.preserve
#print axioms Inv_init
#print axioms pathBound_spec

/-! ### Requirement C: finalization correctness -/
#print axioms Inv.cut
#print axioms Inv.stable

/-! ### Requirement D: global optimality -/
#print axioms dijkstra_correct
#print axioms dijkstra_source
#print axioms dijkstra_reachable_iff
#print axioms dijkstraOpt_none_iff_unreachable
#print axioms dijkstraOpt_some_iff_shortest
#print axioms dijkstraOpt_is_minimum

/-! ### Requirement E: path reconstruction -/
#print axioms reconstruct_spec
#print axioms dijkstraPath_head
#print axioms dijkstraPath_last
#print axioms dijkstraPath_valid
#print axioms dijkstraPath_weight
#print axioms dijkstraPath_source

/-! ### Requirement F: determinism -/
#print axioms select_spec
#print axioms select_unique_of_spec
#print axioms select_unique
#print axioms dijkstra_deterministic
#print axioms dijkstra_result_unique

/-! ### Specification facts -/
#print axioms ShortestDistance_src
#print axioms reachable_iff_ShortestDistance_ne_top
