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

def CB : Bounds := { steps := 2, rounds := 1 }

#eval (nVarsAll (shapeOf clearP CB))
#eval (DPLL.dpll (encode clearP CB)).map (fun l => l.length)
#eval match analyze clearP CB with
  | Verdict.boundsTooSmall => "boundsTooSmall"
  | Verdict.safe => "SAFE"
  | Verdict.attack c => ("ATTACK steps=" ++ toString c.steps.length)
