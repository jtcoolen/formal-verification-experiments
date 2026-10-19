/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Query
import ProtSat.Examples

/-!
# ProtSat: permanent regressions for the known verification gaps

These are the review witnesses of 19 October 2026
(`output/protsat-review-2026-10-19/`), promoted into the library so that they are built,
axiom-audited and impossible to lose. Each one is a *theorem of the current code*, not a wish:
they record exactly what the tool may not claim until the corresponding roadmap stage is done.

* `ProtSat.Regressions.Authentication`: a query whose only selected goal is authentication
  agreement has a bounded attack, and the analyser's low-level verdict is the unsatisfiability of
  the CNF. Roadmap stages 1 and 4. The contract refuses this query (`query_refused`).
* `ProtSat.Regressions.Bounds`: a query whose only selected goal is secrecy, with a bounded
  leak attack, and again an unsatisfiable CNF. The attack is real; what fails is
  `ProtSat.Complete.WithinBounds`, because the protocol computes `fst (pair x x)` where the
  intermediate pair is outside the universe. Roadmap stages 3 and 4.
* `ProtSat.Regressions.Semantics`: reference-semantics defects - freshness inferred from
  current stores, a commit excused by a later claim, a malformed annotation that silently
  produces no authentication event, and an NS model that advertises an authentication break with
  no authentication events at all. Roadmap stages 2 and 3.
-/

namespace ProtSat
namespace Regressions

open Term OneHot Bounded Attacker Encode Encoding Complete Certificate Analyzer DPLL Query Examples

-- The kernel reduction of the reference solver on these models needs more recursion than the
-- default, and the UNSAT search is unbounded in heartbeats.
set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-! ### Authentication is not in the formula -/

namespace Authentication

/-- One session of one role that commits to a peer and a value, with nothing else in the model:
no secret is declared, so the only possible violation is an agreement violation. -/
def P : Protocol :=
  { roles := [{ acts := [.commit 0 (.agent 1) (.agent 0)] }],
    sessions := [{ role := 0, self := 0, peer := 1 }],
    agents := [0, 1], nonceDomain := [0], compromised := [], secrets := [],
    auths := [{ tag := 0 }] }

def B : Bounds := { steps := 1, rounds := 0 }

/-- The query: authentication agreement is the only thing asked about. -/
def q : Query := Query.mk P B [Goal.agreement]

/-- The one-step run that performs the commit. -/
def tr : List Ev := [.act 0 (.agent 0) 0]

def c : Certificate := certOfTrace P tr

/-- The step is a legal transition: a commit advances the control state unconditionally. -/
theorem checked : checkCertificate P c = true := by decide

/-- The run violates non-injective agreement: the commit has no matching claim, and there is no
claim anywhere in the trace. -/
theorem authBreak : AuthBreak P (certCfgs c) tr := by
  rw [← certOfTrace_trace P tr]
  exact (authBreakBool_iff P (certCfgs c) (certTrace c)).mp (by decide)

/-- Hence the query has a bounded attack through its selected goal. -/
theorem hasAttack : boundedAttackGoals q :=
  ⟨Goal.agreement, by simp [q], certTrace c, certCfgs c,
    ⟨checkSteps_runs P c.steps (initCfg P) (by decide),
      by decide,
      by
        change ∀ C ∈ certCfgs c, cfgInUniverse C (univ P B) = true
        decide⟩,
    by rw [violation_agreement]; exact authBreak⟩

/-- **The gap.** The low-level analyser answers that the CNF has no model. -/
theorem analyze_encodingUnsat : analyze P B = Verdict.encodingUnsat := by
  have hu : univClosedBool (shapeOf P B) P = true := by decide
  have hn : dpll (encode P B) = none := by decide
  rw [analyze, if_neg (by simp [hu]), hn]

/-- **The gap, in the contract's vocabulary.** The query is well-formed, so the refusal is about
the encoding, not about the model. -/
theorem query_wellFormed : WellFormed q := by
  show validate q = []
  decide

/-- The contract refuses to answer this query instead of reporting unsatisfiability as safety. -/
theorem query_refused : analyzeQuery q = Result.unsupportedGoals [Goal.agreement] := by
  have hval : (validate q).isEmpty = true := by decide
  rw [analyzeQuery, if_pos hval]
  have hg : ¬ q.goals.isEmpty := by decide
  rw [if_neg hg]
  have hu : ! (unsupported q).isEmpty := by decide
  rw [if_pos hu]
  show Result.unsupportedGoals (unsupported q) = _
  simp [unsupported, q, goalEncoded, encodedGoals]

/-- The gate, instantiated: no security verdict for this query. -/
theorem not_security : securityResult (analyzeQuery q) = false :=
  analyzeQuery_not_security_of_unencoded
    ⟨Goal.agreement, by simp [q], by simp [goalEncoded, encodedGoals]⟩

end Authentication

/-! ### A real leak the formula cannot name -/

namespace Bounds

/-- A session receives a message, checks that `fst (pair x x) = x` - true, and always
computable, but the intermediate pair is outside the universe - and then sends a declared secret. -/
def P : Protocol :=
  { roles := [{ acts := [.recv 0 0,
      .check (.fst (.pair (.var 0) (.var 0))) (.var 0),
      .send 0 (.shrk 0 0)] }],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0], nonceDomain := [0], compromised := [],
    secrets := [.closed (.shrk 0 0)], auths := [] }

def B : Bounds := { steps := 3, rounds := 0 }

/-- The query asks only about secrecy, which is the one goal the encoding represents. -/
def q : Query := Query.mk P B [Goal.secrecy]

def C0 : Cfg := initCfg P
def C1 : Cfg := succStore C0 0 0 (.agent 0)
def C2 : Cfg := succAdvance C1 0
def C3 : Cfg := succSend C2 0 (.key (.shrk 0 0))

def cert : Certificate :=
  { init := C0,
    steps := [{ ev := .act 0 (.agent 0) 0, after := C1 },
              { ev := .act 0 (.agent 0) 0, after := C2 },
              { ev := .act 0 (.agent 0) 0, after := C3 }] }

theorem checked : checkCertificate P cert = true := by decide

theorem inUniverse : runsInUniverse (certCfgs cert) (univ P B) := by
  intro C hC
  simp only [certCfgs, cert, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> decide

/-- The attack is a bounded attack through the *selected* goal: the secret is leaked. -/
theorem hasAttack : boundedAttackGoals q :=
  ⟨Goal.secrecy, by simp [q], certTrace cert, certCfgs cert,
    ⟨checkSteps_runs P cert.steps (initCfg P) (by decide),
      by decide,
      inUniverse⟩,
    by rw [violation_secrecy]; exact (runsLeaksBool_iff P (certCfgs cert)).mp (by decide)⟩

/-- The intermediate pair the protocol computes is outside the universe, although its projection
is inside it. -/
theorem pair_outside : Term.pair (.agent 0) (.agent 0) ∉ univ P B := by decide

/-- The evaluation itself is fine: `fst (pair x x) = x` in the session store. -/
theorem eval_ok : Expr.eval (.fst (.pair (.var 0) (.var 0))) (storeOf C1 0) = some (.agent 0) := by
  decide

/-- The encoding's expression table clips the intermediate pair to "no value": the gate for that
subexpression is not admissible, so the run has no name in the formula. -/
theorem gate_clipped :
    f2 (shapeOf P B) (.pair (.var 0) (.var 0))
      (uIdx (shapeOf P B) (some (.agent 0)))
      (uIdx (shapeOf P B) (some (.agent 0))) = (shapeOf P B).U.length := by decide

/-- Hence this legitimate run does **not** satisfy the completeness hypothesis. -/
theorem not_withinBounds :
    ¬ WithinBounds P B (cfgAt (certCfgs cert)) (evAt (certTrace cert)) := by
  intro h
  have hx := h.exprB 1 0 (.pair (.var 0) (.var 0)) (by decide)
  have heq : admissible (shapeOf P B)
      (Expr.eval (.pair (.var 0) (.var 0))
        (storeOf (cfgAt (certCfgs cert) 1) 0)) = false := by decide
  rw [heq] at hx
  contradiction

/-- So the `hwb` hypothesis of `boundedSafe_of_encodingUnsat` cannot be dropped: for this
query the "every bounded execution is representable" condition is false. -/
theorem hwb_fails :
    ¬ (∀ (tr : List Ev) (Cs : List Cfg), BoundedTrace P B tr Cs ->
        WithinBounds P B (cfgAt Cs) (evAt tr)) := by
  intro hall
  exact not_withinBounds (hall (certTrace cert) (certCfgs cert)
    ⟨checkSteps_runs P cert.steps (initCfg P) (by decide),
      by decide, inUniverse⟩)


/-- The query is well-formed and asks only about secrecy, the one goal the encoding represents:
so this is not a refusal, it is a question the analyser will answer. -/
theorem query_wellFormed : WellFormed q := by
  show validate q = []
  decide

theorem query_goals_encoded : ∀ g ∈ q.goals, goalEncoded g := by
  intro g hg
  rw [q] at hg
  simp [List.mem_singleton] at hg
  subst hg
  exact goalEncoded_secrecy

/-- **The gap.** The completeness theorem cannot be applied to this attack, because its
hypothesis fails: there is a bounded attack on the selected goal, and yet `WithinBounds` does
not hold for it. The executable pipeline goes further and reports the CNF as unsatisfiable
(`lake exe protosatDemo` prints it for this query); the kernel-checked content here is the
*reason*, which is what makes the executable answer a soundness problem rather than a solver
limitation: a run the bounds permit may have no name in the formula. -/
theorem attack_but_not_representable :
    boundedAttackGoals q ∧
      ¬ (∀ (tr : List Ev) (Cs : List Cfg), BoundedTrace P B tr Cs ->
          WithinBounds P B (cfgAt Cs) (evAt tr)) :=
  ⟨hasAttack, hwb_fails⟩

end Bounds

/-! ### Reference-semantics defects -/

namespace Semantics

/-- Both fresh actions choose the same concrete nonce; the first is still stored inside a pair
when the second runs. -/
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

/-- Freshness is inferred from current store contents, so reusing a generated nonce is legal even
though the value is still held, nested, in the session store. -/
theorem nested_reuse_accepted :
    checkSteps nestedReuseP (initCfg nestedReuseP) nestedCert.steps = true := by decide

theorem nested_reuse_runs :
    Runs nestedReuseP (initCfg nestedReuseP)
      (nestedCert.steps.map (fun s => s.ev))
      (initCfg nestedReuseP :: nestedCert.steps.map (fun s => s.after)) :=
  checkSteps_runs _ _ _ (by decide)

theorem nonce_still_stored :
    readVar 0 (storeOf (simStep nestedReuseP
        (simStep nestedReuseP (initCfg nestedReuseP) (Ev.act 0 (Term.agent 0) 7))
        (Ev.act 0 (Term.agent 0) 0)) 0) =
      some (Term.pair (Term.nonce 7) (Term.agent 0)) := by decide

theorem nonce_considered_unused :
    nonceUsed (simStep nestedReuseP
      (simStep nestedReuseP (initCfg nestedReuseP) (Ev.act 0 (Term.agent 0) 7))
      (Ev.act 0 (Term.agent 0) 0)) 7 = false := by decide

/-- Without nesting, overwriting the slot is enough to permit reuse. -/
def overwriteReuseP : Protocol :=
  { nestedReuseP with roles := [{ acts :=
      [Action.fresh 0 0, Action.assign 0 (Expr.agent 0), Action.fresh 1 1] }] }

theorem overwrite_reuse_accepted :
    checkSteps overwriteReuseP (initCfg overwriteReuseP)
      (certOfTrace overwriteReuseP reuseTrace).steps = true := by decide

/-- The Needham-Schroeder model declares no authentication events, so no authentication property
of it can be evaluated: the advertised agreement break is not expressible in its trace. -/
theorem NS_has_no_auth_events :
    authInsts NS.P (certCfgs (certOfTrace NS.P NS.trace)) NS.trace = [] := by decide

theorem NS_auth_not_broken :
    authBreakBool NS.P (certCfgs (certOfTrace NS.P NS.trace)) NS.trace = false := by decide

/-- A commit excused by a *later* claim from the same actor: agreement has no ordering
requirement, and no actor/peer matching. -/
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

theorem later_claim_excuses_commit :
    authBreakBool futureClaimP (certCfgs (certOfTrace futureClaimP futureClaimTrace))
      futureClaimTrace = false := by decide

/-- A commit whose peer expression does not evaluate advances the session and produces no
authentication event at all: the annotation is silently erased. -/
def unsetCommitP : Protocol :=
  { roles := [{ acts := [Action.commit 0 (Expr.agent 1) (Expr.var 0)] }],
    sessions := nestedReuseP.sessions,
    agents := [0, 1],
    nonceDomain := [],
    compromised := [],
    secrets := [],
    auths := [{ tag := 0 }] }

def unsetCommitTrace : List Ev := [Ev.act 0 (Term.agent 0) 0]

theorem unset_commit_produces_nothing :
    authInsts unsetCommitP (certCfgs (certOfTrace unsetCommitP unsetCommitTrace))
      unsetCommitTrace = [] := by decide

/-- The validator catches the vacuity class: a query about agreement over a model with no
authentication events is rejected as ill-formed rather than answered. -/
def NSAuthQuery : Query := Query.mk NS.P NS.B [Goal.agreement]

theorem ns_auth_query_rejected :
    analyzeQuery NSAuthQuery = Result.unsupportedGoals [Goal.agreement] := by
  have hval : (validate NSAuthQuery).isEmpty = true := by decide
  rw [analyzeQuery, if_pos hval]
  have hg : ¬ NSAuthQuery.goals.isEmpty := by decide
  rw [if_neg hg]
  have hu : ! (unsupported NSAuthQuery).isEmpty := by decide
  rw [if_pos hu]
  show Result.unsupportedGoals (unsupported NSAuthQuery) = _
  simp [unsupported, NSAuthQuery, goalEncoded, encodedGoals]

end Semantics

end Regressions
end ProtSat