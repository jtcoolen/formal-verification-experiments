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
  | Verdict.encodingUnsat =>
      "ENCODING UNSAT (no model of the generated CNF: no bounded *secret leak*; see ProtSat.Query)"
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

/-- The contract view of the same models: a query names the goals it asks about, and the answer
says what was actually established. See ProtSat/Query.lean. -/
def demoQuery (name : String) (q : Query) : IO Unit := do
  IO.println ("--- " ++ name)
  IO.println ("    selected goals: " ++ toString (q.goals.length)
    ++ "; validation diagnostics: " ++ toString ((validate q).length))
  IO.println ("    answer: " ++ describe (analyzeQuery q))
  IO.println ""

/-- The same question answered by exhaustive enumeration over the repaired semantics: this route can
also decide authentication. See ProtSat/Contract.lean. -/
def demoContract (name : String) (q : Query) : IO Unit := do
  IO.println ("--- " ++ name)
  IO.println ("    selected goals: " ++ toString q.goals.length
    ++ "; validation diagnostics: " ++ toString ((validate q).length))
  let v := ProtSat.Reference.Contract.analyze q
  IO.println ("    answer: " ++ ProtSat.Reference.Contract.describe v)
  match v with
  | ProtSat.Reference.Contract.Verdict.attack x =>
      IO.println ("    witness re-checked without the search: "
        ++ toString (ProtSat.Reference.Contract.checkWitness q x))
  | _ => pure ()
  IO.println ""

/-- A model with a secret declaration that denotes nothing: the validator must say so rather
than answer a question about a secret the model does not contain. -/
def malformedP : Protocol :=
  { roles := [{ acts := [Action.send 0 (Expr.var 0)] }]
    sessions := [{ role := 0, self := 0, peer := 0 }]
    agents := [0]
    nonceDomain := []
    compromised := []
    secrets := [Secret.closed (Expr.var 0)]
    auths := [] }

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
  IO.println "THE QUERY CONTRACT (ProtSat/Query.lean): what each answer means"
  IO.println ""
  demoQuery "challenge-response, asking about secrecy"
    (Query.mk Challenge.P Challenge.B [Goal.secrecy])
  demoQuery "challenge-response, ALSO asking about agreement"
    (Query.mk Challenge.P Challenge.B [Goal.secrecy, Goal.agreement])
  demoQuery "replay protocol, asking about secrecy"
    (Query.mk Replay.P Replay.B [Goal.secrecy])
  demoQuery "the commit-only witness, asking about agreement"
    (Query.mk Regressions.Authentication.P Regressions.Authentication.B [Goal.agreement])
  demoQuery "the transient-pair witness, asking about secrecy"
    (Query.mk Regressions.Bounds.P Regressions.Bounds.B [Goal.secrecy])
  demoQuery "a model whose declared secret denotes nothing"
    (Query.mk malformedP { steps := 2, rounds := 0 } [Goal.secrecy])
  demoQuery "a query that selects no goal"
    (Query.mk Challenge.P Challenge.B [])
  IO.println "THE ENUMERATION CONTRACT (ProtSat/Contract.lean): the repaired semantics decided by"
  IO.println "exhaustive enumeration. This route represents the authentication violation too, so it"
  IO.println "can produce the bounded-safety verdict the CNF route still owes."
  IO.println ""
  demoContract "secure model, both goals selected" ProtSat.Reference.Contract.Gates.secureQ
  demoContract "commit-only authentication model, asking about agreement"
    ProtSat.Reference.Contract.Gates.authQ
  demoContract "transient-pair model, asking about secrecy"
    ProtSat.Reference.Contract.Gates.transientQ
  demoContract "claim then commit in one role, asking about agreement"
    ProtSat.Reference.Contract.Gates.authOrderQ
  demoContract "the same role with the two actions swapped"
    ProtSat.Reference.Contract.Gates.authSwappedQ
  demoContract "a query that selects no goal" ProtSat.Reference.Contract.Gates.emptyQ
  demoContract "a model with a session naming a role that does not exist"
    ProtSat.Reference.Contract.Gates.badQ
  IO.println "SOLVER SANITY CHECKS (all by the kernel, see ProtSat/DPLL.lean)"
  IO.println ("    demoUnit      isSome = " ++ toString ((dpll DPLL.demoUnit).isSome))
  IO.println ("    demoConflict  isSome = " ++ toString ((dpll DPLL.demoConflict).isSome))
  IO.println ("    demoBranch    isSome = " ++ toString ((dpll DPLL.demoBranch).isSome))
  IO.println ("    demoBranchSat isSome = " ++ toString ((dpll DPLL.demoBranchSat).isSome))
  IO.println ""
  IO.println "Executable attacker (specification section 2): ProtSat/Deduce.lean saturates a"
  IO.println "finite universe and is proved sound, complete on it, and monotone."
