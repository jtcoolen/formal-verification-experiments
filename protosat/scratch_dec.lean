import ProtSat
import ProtSat.Analyzer
open ProtSat ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer ProtSat.Bounded ProtSat.DPLL

def P : Protocol :=
  { roles :=
      [ { acts := [Action.send 1 (Expr.encS (Expr.pair (Expr.agent 0) (Expr.shrk 0 1))
                                              (Expr.shrk 0 1))] },
        { acts :=
            [Action.recv 0 0,
             Action.check (Expr.decS (Expr.var 0) (Expr.shrk 0 1))
                          (Expr.pair (Expr.agent 0) (Expr.shrk 0 1)),
             Action.fresh 1 1,
             Action.secret (Expr.var 1)] } ],
    sessions := [{ role := 1, self := 1, peer := 0 }],
    agents := [0, 1],
    nonceDomain := [101001],
    compromised := [],
    secrets := [Secret.store 1 1],
    auths := [] }

def B : Bounds := { steps := 3, rounds := 0 }

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 1000000 in
theorem h : (dpll (encode P B)).isSome = false := by decide
