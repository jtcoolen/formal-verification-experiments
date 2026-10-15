/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat

/-!
# ProtSat demonstration

Development snapshot: prints the message algebra and a toy protocol, so that
    lake exe protosatDemo
runs end to end.  The full analyser pipeline (bounded model -> CNF -> DPLL -> trace ->
independent certificate check) replaces this in a later round; see KB/PROTOSAT.md for
the ordered list of remaining modules.
-/

open ProtSat

/-- A tiny symmetric protocol used by the placeholder demo: A sends a fresh nonce to B,
B declares it secret. -/
def toyProtocol : Protocol :=
  { roles :=
      [ { acts := [Action.fresh 0 0, Action.send 1 (Expr.var 0)] },
        { acts := [Action.recv 0 0, Action.secret (Expr.var 0)] } ],
    sessions := [{ role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 }],
    agents := [0, 1],
    nonceDomain := [7, 8],
    compromised := [],
    secrets := [Secret.store 0 0],
    auths := [] }

/-- One line of the demo output. -/
def line (s : String) : IO Unit := IO.println s

def main : IO Unit := do
  line "ProtSat: symbolic protocol analyser (development snapshot)"
  line "=========================================================="
  let t : Term := .encS (.pair (.nonce 7) (.agent 1)) (Key.shrk 0 1)
  line ("example message: " ++ t.show')
  line ("  size " ++ toString t.size ++ ", depth " ++ toString t.depth)
  let P := toyProtocol
  line ("toy protocol: " ++ toString P.sessions.length ++ " sessions, "
    ++ toString P.roles.length ++ " roles")
  line ("  initial attacker knowledge: "
    ++ toString (P.initKn.map fun k => k.show'))
  line ("  closed secrets: " ++ toString (P.closedSecretTerms.map fun k => k.show'))
  line ("  initial configuration has " ++ toString (initCfg P).sess.length
    ++ " session states")
  line ("  session 0 role length: " ++ toString (P.roleLen 0))
  line ("  session 1 role length: " ++ toString (P.roleLen 1))
  line ("  session 0 has an action at pc 0: " ++ toString ((P.actionAt 0 0).isSome))
  line ("  session 0 has an action at pc 5: " ++ toString ((P.actionAt 0 5).isSome))
  line ""
  line "Modules built so far: Syntax, CNF, Attacker, Protocol, Operational, DPLL (core)."
  line "Pending: Theory, Deduce, Bounded, Encode, Certificate, Analyzer, Examples."
