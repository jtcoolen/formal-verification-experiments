import ProtSat
import ProtSat.Analyzer
open ProtSat ProtSat.Encode ProtSat.Encoding ProtSat.Analyzer ProtSat.Bounded

def tinyP : Protocol :=
  { roles := [ { acts := [Action.fresh 0 0, Action.secret (Expr.var 0)] } ],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0],
    nonceDomain := [0],
    compromised := [],
    secrets := [Secret.store 0 0],
    auths := [] }

def TB : Bounds := { steps := 2, rounds := 1 }

#eval ((shapeOf tinyP TB).U.length, shVal (shapeOf tinyP TB), nInst (shapeOf tinyP TB))
#eval ((encode tinyP TB).clauses.length)
#eval (DPLL.dpll (encode tinyP TB)).map (fun l => l.length)
