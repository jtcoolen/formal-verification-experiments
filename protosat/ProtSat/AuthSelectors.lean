/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.AuthClauses
import ProtSat.BoundedCert

/-!
# Agreement selectors may ignore matched commits

The only session claims tag 0, commits tag 0, then commits the unclaimed tag 1. Reaching the
violating commit requires performing the matched commit first. A selector is therefore an
existential choice of the violation, rather than a definition of whether every commit happened.
The checked assignment below keeps both commits in the execution and selects only tag 1.
-/

namespace ProtSat.AuthSelectors

open ProtSat Bounded Encode AuthClauses

def P : Protocol :=
  { roles := [{ acts := [Action.claim 0 (Expr.agent 0) (Expr.agent 0),
                         Action.commit 0 (Expr.agent 0) (Expr.agent 0),
                         Action.commit 1 (Expr.agent 0) (Expr.agent 0)] }]
    sessions := [{ role := 0, self := 0, peer := 0 }]
    agents := [0]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [] }

def B : Bounds := { steps := 3, rounds := 0 }

def C0 : Cfg := initCfg P
def C1 : Cfg := succAdvance C0 0
def C2 : Cfg := succAdvance C1 0
def C3 : Cfg := succAdvance C2 0

def cert : Certificate :=
  { init := C0
    steps := [{ ev := Ev.act 0 (Term.agent 0) 0, after := C1 },
              { ev := Ev.act 0 (Term.agent 0) 0, after := C2 },
              { ev := Ev.act 0 (Term.agent 0) 0, after := C3 }] }

def matched : AuthOcc :=
  { pos := { isCommit := true, sess := 0, pc := 1, tag := 0,
             peer := Expr.agent 0, val := Expr.agent 0 }
    step := 1
    data := uIdx (shapeOf P B) (some (Term.agent 0))
    peerVal := uIdx (shapeOf P B) (some (Term.agent 0)) }

def unmatched : AuthOcc :=
  { matched with pos := { matched.pos with pc := 2, tag := 1 }, step := 2 }

/-- Keep the characteristic execution assignment and select only the final, unmatched commit. -/
def witness : Assignment := fun v =>
  if v < bsAuth (shapeOf P B) then
    Complete.assignOf (shapeOf P B) P (Complete.cfgAt (certCfgs cert))
      (Complete.evAt (certTrace cert)) v
  else v == authOccVar (shapeOf P B) P unmatched

theorem certificate_checked : BoundedCert.checkBounded P B cert = true := by decide

theorem mixed_commits :
    commitsOf P (certCfgs cert) (certTrace cert) =
      [(0, 0, Term.agent 0), (1, 0, Term.agent 0)] := by decide

theorem only_first_claimed :
    claimsOf P (certCfgs cert) (certTrace cert) = [(0, 0, Term.agent 0)] := by decide

theorem matched_performed_unselected :
    matched ∈ authOccs (shapeOf P B) P true ∧
      (∀ l ∈ authOccLits (shapeOf P B) P matched, l.eval witness = true) ∧
      witness (authOccVar (shapeOf P B) P matched) = false := by decide

theorem unmatched_selected :
    unmatched ∈ authOccs (shapeOf P B) P true ∧
      witness (authOccVar (shapeOf P B) P unmatched) = true := by decide

set_option maxRecDepth 100000 in
/-- Both monitors admit the attack even though an earlier commit was matched. -/
theorem witness_satisfies (m : Matching) : Sat witness (agreementEncode P B m) := by
  cases m <;> exact sat_of_all (by decide)

theorem agreement_only_sat (m : Matching) :
    Satisfiable (encodeGoals P B [Goal.agreement] m) := by
  rw [encodeGoals_agreement]
  exact ⟨witness, witness_satisfies m⟩

end ProtSat.AuthSelectors
