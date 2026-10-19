import ProtSat.Examples

namespace SemanticsReview
open ProtSat ProtSat.Certificate ProtSat.Examples

-- Both fresh actions choose the same concrete nonce. The first nonce is kept
-- inside a pair when the second fresh action runs.
def nestedReuseP : Protocol :=
  { roles := [{ acts := [Action.fresh 0 0,
                        Action.assign 0 (Expr.pair (Expr.var 0) (Expr.agent 0)),
                        Action.fresh 1 1] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := [7]
    compromised := []
    secrets := []
    auths := [] }

def reuseTrace : List Ev :=
  [Ev.act 0 (Term.agent 0) 7,
   Ev.act 0 (Term.agent 0) 0,
   Ev.act 0 (Term.agent 0) 7]

def nestedCert : Certificate := certOfTrace nestedReuseP reuseTrace

-- Kernel-checked: all three steps, including both fresh generations of 7, are valid.
example : checkSteps nestedReuseP (initCfg nestedReuseP) nestedCert.steps = true := by decide

-- The resulting certified run is a run of the independent reference semantics.
example : Runs nestedReuseP (initCfg nestedReuseP)
    (nestedCert.steps.map (fun s => s.ev))
    (initCfg nestedReuseP :: nestedCert.steps.map (fun s => s.after)) :=
  checkSteps_runs _ _ _ (by decide)

-- Immediately before the second fresh generation, 7 still occurs in a stored term,
-- but nonceUsed calls it unused.
def beforeReuse : Cfg := simStep nestedReuseP
    (simStep nestedReuseP (initCfg nestedReuseP) (Ev.act 0 (Term.agent 0) 7)) (Ev.act 0 (Term.agent 0) 0)
example : readVar 0 (storeOf beforeReuse 0) =
    some (Term.pair (Term.nonce 7) (Term.agent 0)) := by decide
example : nonceUsed beforeReuse 7 = false := by decide

-- Even without nesting, overwriting the slot permits reuse of a generated value.
def overwriteReuseP : Protocol :=
  { nestedReuseP with roles := [{ acts :=
      [Action.fresh 0 0, Action.assign 0 (Expr.agent 0), Action.fresh 1 1] }] }
example : checkSteps overwriteReuseP (initCfg overwriteReuseP)
    (certOfTrace overwriteReuseP reuseTrace).steps = true := by decide

-- The advertised Needham-Schroeder authentication break does not occur in its
-- formal trace: there are no authentication events at all.
example : authInsts NS.P (certCfgs (certOfTrace NS.P NS.trace)) NS.trace = [] := by decide
example : authBreakBool NS.P (certCfgs (certOfTrace NS.P NS.trace)) NS.trace = false := by decide

-- A commit can be excused by a later claim from the same actor. There is no
-- matching actor/peer check and no order requirement.
def futureClaimP : Protocol :=
  { roles := [{ acts :=
      [Action.commit 0 (Expr.agent 1) (Expr.agent 0),
       Action.claim 0 (Expr.agent 1) (Expr.agent 0)] }],
    sessions := nestedReuseP.sessions,
    agents := [0, 1],
    nonceDomain := [],
    compromised := [],
    secrets := [],
    auths := [{ tag := 0 }] }
def futureClaimTrace : List Ev :=
  [Ev.act 0 (Term.agent 0) 0, Ev.act 0 (Term.agent 0) 0]
def futureClaimCert : Certificate := certOfTrace futureClaimP futureClaimTrace
example : checkSteps futureClaimP (initCfg futureClaimP) futureClaimCert.steps = true := by decide
example : authBreakBool futureClaimP (certCfgs futureClaimCert) futureClaimTrace = false := by decide

-- A commit using an unset variable advances but produces no auth event.
def unsetCommitP : Protocol :=
  { roles := [{ acts :=
      [Action.commit 0 (Expr.agent 1) (Expr.var 0)] }],
    sessions := nestedReuseP.sessions,
    agents := [0, 1],
    nonceDomain := [],
    compromised := [],
    secrets := [],
    auths := [{ tag := 0 }] }
def unsetCommitTrace : List Ev := [Ev.act 0 (Term.agent 0) 0]
def unsetCommitCert : Certificate := certOfTrace unsetCommitP unsetCommitTrace
example : checkSteps unsetCommitP (initCfg unsetCommitP) unsetCommitCert.steps = true := by decide
example : authInsts unsetCommitP (certCfgs unsetCommitCert) unsetCommitTrace = [] := by decide

end SemanticsReview
