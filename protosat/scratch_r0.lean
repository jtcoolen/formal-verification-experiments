import ProtSat
import ProtSat.Analyzer
open ProtSat ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer ProtSat.Bounded

def clearP : Protocol :=
  { roles := [ { acts := [Action.send 0 (Expr.pair (Expr.agent 0) (Expr.shrk 0 0))] } ],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0],
    nonceDomain := [],
    compromised := [],
    secrets := [Secret.closed (Expr.shrk 0 0)],
    auths := [] }

def tinyP : Protocol :=
  { roles := [ { acts := [Action.fresh 0 0, Action.secret (Expr.var 0)] } ],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0],
    nonceDomain := [0],
    compromised := [],
    secrets := [Secret.store 0 0],
    auths := [] }

#eval (univClosedBool (shapeOf clearP { steps := 2, rounds := 0 }) clearP, (shapeOf clearP { steps := 2, rounds := 0 }).U.length, (encode clearP { steps := 2, rounds := 0 }).clauses.length)
#eval match analyze clearP { steps := 2, rounds := 0 } with
  | Verdict.boundsTooSmall => "boundsTooSmall"
  | Verdict.safe => "SAFE"
  | Verdict.attack c => ("ATTACK steps=" ++ toString c.steps.length)
#eval (univClosedBool (shapeOf tinyP { steps := 2, rounds := 0 }) tinyP, (shapeOf tinyP { steps := 2, rounds := 0 }).U.length, (encode tinyP { steps := 2, rounds := 0 }).clauses.length)
#eval match analyze tinyP { steps := 2, rounds := 0 } with
  | Verdict.boundsTooSmall => "boundsTooSmall"
  | Verdict.safe => "SAFE"
  | Verdict.attack c => ("ATTACK steps=" ++ toString c.steps.length)
