/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat

/-!
# ProtSat: the command-line analyser

    lake exe protosatDemo

prints, for each of the six protocol examples of specification section 9:

* the model's shape (sessions, roles, universe size, deduction instances),
* the size of the generated CNF,
* the analyser's verdict - the real pipeline: bounded model, CNF, DPLL, decoded trace,
  certificate - and, for an attack verdict, the certificate checker's answer,
* for the Needham-Schroeder examples, the independently checked attack traces.

Nothing here is a proof: the proofs are in the library (see the README's theorem
inventory).  This program is the executable evidence that the pipeline runs and that the
bounds are the ones the theorems need.
-/

open ProtSat Term OneHot Bounded Attacker Protocol Encode Encoding Certificate Analyzer Examples
open ProtSat.DPLL (dpll)

/-- Print a verdict in one line, with the certificate checker's answer when there is one. -/
def showVerdict (P : Protocol) (v : Verdict) : String :=
  match v with
  | Verdict.boundsTooSmall => "BOUNDS TOO SMALL (univClosed fails: raise Bounds.rounds)"
  | Verdict.safe => "SAFE within the declared bounds (no model of the CNF)"
  | Verdict.attack c =>
      "ATTACK (" ++ toString c.steps.length ++ " events); certificate accepted: "
        ++ toString (checkCertificate P c)

/-- One example, one block of output. -/
def demo (name : String) (P : Protocol) (B : Bounds) : IO Unit := do
  IO.println ("--- " ++ name)
  IO.println ("    sessions " ++ toString P.sessions.length ++ ", roles " ++ toString P.roles.length
    ++ ", universe " ++ toString ((shapeOf P B).U.length) ++ " messages, "
    ++ toString (nInst (shapeOf P B)) ++ " deduction instances")
  IO.println ("    CNF: " ++ toString (nVarsAll (shapeOf P B)) ++ " variables, "
    ++ toString ((encode P B).clauses.length) ++ " clauses")
  IO.println ("    univClosed: " ++ toString (univClosedBool (shapeOf P B) P))
  IO.println ("    verdict: " ++ showVerdict P (analyze P B))
  IO.println ""

/-- The attack traces that are verified by the independent checker rather than by the solver,
with the checker's answer recomputed here. -/
def demoCert (name : String) (P : Protocol) (tr : List Ev) (expect : Bool) : IO Unit := do
  let c := certOfTrace P tr
  IO.println ("--- " ++ name)
  IO.println ("    " ++ toString tr.length ++ " events; checkCertificate = "
    ++ toString (checkCertificate P c) ++ " (expected " ++ toString expect ++ ")")
  IO.println ("    trace: " ++ toString (certTrace c).length ++ " events replayed by the checker")
  IO.println ""

def main : IO Unit := do
  IO.println "ProtSat: a proof-producing SAT-based protocol analyser, verified in Lean 4"
  IO.println "=========================================================================="
  IO.println ""
  IO.println "EXAMPLES (specification section 9)"
  IO.println ""
  demo "1. challenge-response, secure under explicit assumptions" Challenge.P Challenge.B
  demo "2. replay-vulnerable protocol (static authenticator)" Replay.P Replay.B
  demo "3. secrecy violation by key disclosure (A compromised)" KeyDisclosure.P KeyDisclosure.B
  demo "3b. the same protocol with the key NOT disclosed" KeyDisclosure.PSafe KeyDisclosure.B
  IO.println "4/5. Needham-Schroeder public key and the Lowe attack"
  IO.println ("     sessions " ++ toString NS.P.sessions.length ++ ", universe "
    ++ toString ((shapeOf NS.P NS.B).U.length) ++ " messages at rounds "
    ++ toString NS.B.rounds ++ ", steps " ++ toString NS.B.steps)
  IO.println ("     CNF would have " ++ toString (nVarsAll (shapeOf NS.P NS.B))
    ++ " variables: too large for the reference solver, so the attack is exhibited as a")
  IO.println ("     certificate that the independent checker verifies (see below).")
  IO.println ""
  demoCert "5. Lowe attack on Needham-Schroeder (certificate)" NS.P NS.trace true
  demoCert "6. the same attack on Needham-Schroeder-Lowe (rejected)" NSL.P NSL.trace false
  IO.println "SOLVER SANITY CHECKS (all by the kernel, see ProtSat/DPLL.lean)"
  IO.println ("    demoUnit      isSome = " ++ toString ((dpll DPLL.demoUnit).isSome))
  IO.println ("    demoConflict  isSome = " ++ toString ((dpll DPLL.demoConflict).isSome))
  IO.println ("    demoBranch    isSome = " ++ toString ((dpll DPLL.demoBranch).isSome))
  IO.println ("    demoBranchSat isSome = " ++ toString ((dpll DPLL.demoBranchSat).isSome))
  IO.println ""
  IO.println "Executable attacker (specification section 2): ProtSat/Deduce.lean saturates a"
  IO.println "finite universe and is proved sound, complete on it, and monotone."
