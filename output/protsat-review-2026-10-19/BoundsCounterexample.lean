import ProtSat

namespace TruncationReview
open ProtSat ProtSat.Bounded ProtSat.Encode ProtSat.Analyzer ProtSat.Certificate

def P : Protocol :=
  { roles := [{ acts := [.recv 0 0,
      .check (.fst (.pair (.var 0) (.var 0))) (.var 0),
      .send 0 (.shrk 0 0)] }],
    sessions := [{role := 0, self := 0, peer := 0}],
    agents := [0], nonceDomain := [0], compromised := [],
    secrets := [.closed (.shrk 0 0)], auths := [] }
def B : Bounds := {steps := 3, rounds := 0}
def C0 : Cfg := initCfg P
def C1 : Cfg := succStore C0 0 0 (.agent 0)
def C2 : Cfg := succAdvance C1 0
def C3 : Cfg := succSend C2 0 (.key (.shrk 0 0))
def cert : Certificate :=
  {init := C0,
   steps := [{ev := .act 0 (.agent 0) 0, after := C1},
             {ev := .act 0 (.agent 0) 0, after := C2},
             {ev := .act 0 (.agent 0) 0, after := C3}]}

example : univClosedBool (shapeOf P B) P = true := by decide
example : checkCertificate P cert = true := by decide
example : Term.pair (.agent 0) (.agent 0) ∉ univ P B := by decide
example : Expr.eval (.fst (.pair (.var 0) (.var 0))) (storeOf C1 0) = some (.agent 0) := by decide
example : f2 (shapeOf P B) (.pair (.var 0) (.var 0))
    (uIdx (shapeOf P B) (some (.agent 0)))
    (uIdx (shapeOf P B) (some (.agent 0))) = (shapeOf P B).U.length := by decide
example : Expr.stepEval1 (.fst (.pair (.var 0) (.var 0))) none = none := by decide

theorem inUniverse : runsInUniverse (certCfgs cert) (univ P B) := by
  intro C hC
  simp only [certCfgs, cert, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> decide

theorem boundedAttack : BoundedAttack P B := by
  refine ⟨certTrace cert, certCfgs cert, ⟨?_, by decide, inUniverse⟩, Or.inl ?_⟩
  · exact checkSteps_runs P cert.steps (initCfg P) (by decide)
  · exact (runsLeaksBool_iff P (certCfgs cert)).mp (by decide)

theorem notWithinBounds : ¬ ProtSat.Complete.WithinBounds P B
    (ProtSat.Complete.cfgAt (certCfgs cert)) (ProtSat.Complete.evAt (certTrace cert)) := by
  intro h
  have hx := h.2.2.2.2.2.2.1 1 0 (.pair (.var 0) (.var 0)) (by decide)
  have heq : admissible (shapeOf P B)
      (Expr.eval (.pair (.var 0) (.var 0))
        (storeOf (ProtSat.Complete.cfgAt (certCfgs cert) 1) 0)) = false := by decide
  rw [heq] at hx
  contradiction

end TruncationReview
