/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.EndToEnd
import ProtSat.Contract

/-!
# ProtSat: the two routes as each other oracle (roadmap stage 7, differential gate)

The exhaustive enumeration over the repaired semantics and the SAT route over the old one agree
where the CNF can name what the protocol computes. More than agreement: on these two instances the
correspondence the roadmap states as `encoding_correct` is verified in both directions - a real
attack producing a real model, and a refuted formula producing a real security statement.

```lean
theorem guard_correct : Satisfiable (encode Guard GB) <-> boundedAttackGoals qg
theorem leak_correct  : Satisfiable (encode Leak GB) <-> boundedAttackGoals ql
```

The first is the case where neither side holds; the second is the substantive one - a permitted
execution that leaks, turned into a satisfying assignment of the generated formula by
`Complete.encoding_complete` with no representability hypothesis, because the query is gap-free and
`BoundedExec.withinBounds_of_bounded` did the work. Together they are the two directions of the
correspondence, instantiated on real protocols rather than stated in the abstract.
-/

namespace ProtSat.Differential

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### The guarded protocol: both routes say safe -/

/-- The enumeration over the repaired semantics finds no violation of the selected goal. -/
theorem guard_enum_safe : ProtSat.Reference.Contract.attackFound EndToEnd.qg = false := by decide

/-- So the repaired route independently proves what the CNF route proves. -/
theorem guard_enum_boundedSafe : ProtSat.Reference.Contract.boundedSafe EndToEnd.qg :=
  ProtSat.Reference.Contract.boundedSafe_of_attackFound_false guard_enum_safe

/-- The CNF has no model - the solver answer, checked by the kernel in `EndToEnd`. -/
theorem guard_cnf_unsat : ProtSat.Unsat (encode EndToEnd.Guard EndToEnd.GB) :=
  DPLL.dpll_complete EndToEnd.qg_unsat

/-- **The correspondence, both directions, on a real protocol.** Neither side holds. -/
theorem guard_correct :
    Satisfiable (encode EndToEnd.Guard EndToEnd.GB) <-> boundedAttackGoals EndToEnd.qg :=
  ⟨fun h => absurd h guard_cnf_unsat, fun h => absurd h EndToEnd.qg_safe⟩

/-! ### The leaky protocol: both routes say attack -/

/-- One step: the session publishes the declared key. `Leak` is also the name of the leak
predicate in `ProtSat.Operational`, so the protocol is always qualified. -/
def LC0 : Cfg := initCfg EndToEnd.Leak

def LC1 : Cfg := succSend LC0 0 (Term.key (Key.shrk 0 0))

def Ltr : List Ev := [Ev.act 0 (Term.key (Key.shrk 0 0)) 0]

def LCs : List Cfg := [LC0, LC1]

theorem L_runs : Runs EndToEnd.Leak (initCfg EndToEnd.Leak) Ltr LCs := by
  refine Runs.cons ?_ (Runs.nil EndToEnd.Leak LC1)
  show Rel EndToEnd.Leak LC0 (Ev.act 0 (Term.key (Key.shrk 0 0)) 0) LC1
  refine Rel.rSend (a := 0) (e := Expr.shrk 0 0) ?_ ?_
  · decide
  · decide

theorem L_univ : runsInUniverse LCs (univ EndToEnd.Leak EndToEnd.GB) := by
  intro C hC
  simp only [LCs, LC1, LC0, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hC
  rcases hC with rfl | rfl <;> decide

/-- The leaky run is a bounded execution of the query. -/
theorem L_bounded : BoundedTrace EndToEnd.Leak EndToEnd.GB Ltr LCs :=
  ⟨L_runs, by decide, L_univ⟩

theorem L_leaks : runsLeaks EndToEnd.Leak LCs := by
  refine ⟨LC1, List.mem_cons.mpr (Or.inr (List.Mem.head _)), ?_⟩
  exact (leakBool_iff EndToEnd.Leak LC1).mp (by decide)

/-- **A permitted execution violates the selected goal**, on the old semantics the CNF is
proved against. -/
theorem leak_boundedAttack : boundedAttackGoals EndToEnd.ql :=
  ⟨Goal.secrecy, by decide, Ltr, LCs, L_bounded,
    by rw [violation_secrecy]; exact L_leaks⟩

/-- The query is gap-free, so its bounded executions are representable with no hypothesis. -/
theorem leak_gap : domainGap EndToEnd.Leak EndToEnd.GB = false := by decide

theorem leak_hU : univClosed (shapeOf EndToEnd.Leak EndToEnd.GB) EndToEnd.Leak := by
  unfold univClosed
  decide

theorem leak_hsec : SecretsOK (shapeOf EndToEnd.Leak EndToEnd.GB) EndToEnd.Leak := by
  refine ⟨fun q x h => ?_, ?_⟩
  · have heq : Secret.store q x = Secret.closed (Expr.shrk 0 0) := List.mem_singleton.mp h
    cases heq
  · decide

/-- **Completeness, applied.** The attack produces a satisfying assignment of the generated
formula - no `WithinBounds` hypothesis, because `withinBounds_of_bounded` derived it from the
public bound and the gap check. -/
theorem leak_sat : Satisfiable (encode EndToEnd.Leak EndToEnd.GB) :=
  encoding_complete (P := EndToEnd.Leak) (B := EndToEnd.GB) (tr := Ltr) (Cs := LCs) leak_hU
    leak_hsec L_runs (by decide) L_leaks
    (withinBounds_of_bounded L_bounded leak_gap)

/-- **The correspondence, both directions, on the instance that actually attacks.** -/
theorem leak_correct :
    Satisfiable (encode EndToEnd.Leak EndToEnd.GB) <-> boundedAttackGoals EndToEnd.ql :=
  ⟨fun _ => leak_boundedAttack, fun _ => leak_sat⟩


end ProtSat.Differential