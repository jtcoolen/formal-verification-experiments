import ProtSat
import ProtSat.Analyzer
open ProtSat ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer ProtSat.Bounded

def toyP : Protocol :=
  { roles :=
      [ { acts := [Action.fresh 0 0, Action.send 1 (Expr.var 0)] },
        { acts := [Action.recv 0 0, Action.secret (Expr.var 0)] } ],
    sessions := [{ role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 }],
    agents := [0, 1],
    nonceDomain := [0, 1],
    compromised := [],
    secrets := [Secret.store 1 0],
    auths := [] }

def B1 : Bounds := { steps := 4, rounds := 1 }

#eval ((shapeOf toyP B1).U.length, shVal (shapeOf toyP B1), nInst (shapeOf toyP B1))
#eval ((encode toyP B1).clauses.length)
#eval match analyze toyP B1 with
  | Verdict.boundsTooSmall => "boundsTooSmall"
  | Verdict.safe => "SAFE"
  | Verdict.attack c => ("ATTACK", c.steps.length)
