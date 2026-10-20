/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Query
import ProtSat.BoundedExec
import ProtSat.Examples

/-!
# ProtSat: SAFE read as security (roadmap stage 4, gate)

The headline claim of this development is that a verdict means

  no execution permitted by the stated model, assumptions and bounds violates a selected goal.

For the CNF route that implication used to need a bundle of execution-wide assumptions
(`WithinBounds`, twelve unnamed conditions). Two changes remove the bundle for the gap-free class:

* `ProtSat/BoundedExec.lean` derives ten of the twelve from the public bound, and `RunOK.actB`
  now bounds the two event fields only where an action reads them - which the public bound also
  implies (`actB_of_bounded`);
* `ProtSat/Represent.lean` makes the eleventh and twelfth decidable from the protocol and the
  bounds: `domainGap` computes whether the protocol can build a value the universe cannot name,
  and `exprB_of_domainGap_false` turns "no gap" into `RunOK.exprB` for every run at once.

`Query.boundedSafe_of_encodingUnsat_of_gapFree` is the result: for a query with no domain gap,
the analyser answering `encodingUnsat` *is* the statement `boundedSafeGoals q`, with no hypothesis
about any execution.

This module instantiates it on `Examples.KeyDisclosure`: a session publishes whatever it receives,
and the declared secret is the shared key that is withheld in the safe variant and disclosed in the
attack variant. The example is non-vacuous by construction - the same role with the disclosure has
a kernel-checked attack certificate (`Examples.KeyDisclosure.checked`, `attack`) - so the safety
below is caused by the compromise assumption, not by a role that never reaches its leak.

What is *not* proved here is the solver answer itself as a kernel fact, and the measured cost is
the reason. Re-deriving `dpll (encode P B) = none` by `decide`:

| instance | variables | clauses | kernel cost of the re-derivation |
|---|---|---|---|
| `Examples.KeyDisclosure` (steps 2) | 1263 | 2995 | exceeds the default recursion budget |
| a 3-action gated protocol (steps 3) | 828 | 1204 | > 200k heartbeats in 14 s at raised
  `maxRecDepth`; not finished in 2 min |
| the same gated protocol (steps 2) | 494 | 662 | not finished in 5 min at raised budgets |
| `Regressions.Authentication` (steps 1) | 648 | - | decides in the normal build |

So the answer is computed by the analyser at runtime (the demo prints it) and enters the theorem
below as the named hypothesis `hvs`. Everything *else* the security statement needs is decided in
this file. A verdict that has to be re-run rather than checked is exactly what roadmap stage 6
exists to close: an independently checked UNSAT certificate would replace minutes of kernel
solver-replay with a linear proof check.
-/

namespace ProtSat.EndToEnd

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  Examples

/-- The disclosure-free query, asking the one goal the encoding represents. -/
def qsafe : Query := Query.mk KeyDisclosure.PSafe KeyDisclosure.B [Goal.secrecy]

/-- The query is well-formed: session indices exist, the declared secret denotes, the compromise
set is inside the agent domain. -/
theorem wf_safe : WellFormed qsafe := by
  show validate qsafe = []
  decide

/-- **No gap.** Every value this protocol computes is named by the universe at these bounds. -/
theorem gapFree_safe : domainGap KeyDisclosure.PSafe KeyDisclosure.B = false := by decide

theorem hU_safe : univClosed (shapeOf KeyDisclosure.PSafe KeyDisclosure.B)
    KeyDisclosure.PSafe := by
  unfold univClosed
  decide

theorem hsec_safe : SecretsOK (shapeOf KeyDisclosure.PSafe KeyDisclosure.B)
    KeyDisclosure.PSafe := by
  refine ⟨fun q x h => ?_, ?_⟩
  · have heq : Secret.store q x = Secret.closed (Expr.nonce 5) := List.mem_singleton.mp h
    cases heq
  · decide

theorem hgoals : ∀ g ∈ qsafe.goals, goalEncoded g := by decide

theorem hne : qsafe.goals ≠ [] := by decide

/-- **SAFE means security, for a gap-free query.** The only hypothesis is the analyser's own answer
about the generated formula. There is no `WithinBounds`, no representability assumption, and
nothing at all about the executions of the protocol: the public bound and the query supply those.
This is the implication the review said was missing, established for the class of queries whose
value domain has no gap - a class the tool now decides. -/
theorem boundedSafe_of_gapFree (hvs : analyzeQuery qsafe = Result.encodingUnsat) :
    boundedSafeGoals qsafe :=
  boundedSafe_of_encodingUnsat_of_gapFree hgoals hne hU_safe hsec_safe gapFree_safe hvs

/-- The same statement in the public vocabulary: no execution the model permits, within the
declared universe and event bound, leaks a declared secret. -/
theorem noLeak (hvs : analyzeQuery qsafe = Result.encodingUnsat) :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg),
        BoundedTrace KeyDisclosure.PSafe KeyDisclosure.B tr Cs ∧
          runsLeaks KeyDisclosure.PSafe Cs := by
  intro h
  obtain ⟨tr, Cs, hbt, hleak⟩ := h
  exact boundedSafe_of_gapFree hvs
    ⟨Goal.secrecy, by decide, tr, Cs, hbt, by rw [violation_secrecy]; exact hleak⟩

/-- **Non-vacuity, kernel-checked.** The same role and bounds with the key disclosed have an
accepted certificate - the independent checker verifies every step and the leak
(`Examples.KeyDisclosure.checked`, `attack`). So `noLeak` is a fact about the compromise
assumption, not about a protocol that cannot reach its leak. -/
theorem disclosure_certificate :
    checkCertificate KeyDisclosure.P (certOfTrace KeyDisclosure.P KeyDisclosure.tr) = true :=
  KeyDisclosure.checked
/-! ### A closed verdict: no hypotheses at all -/

/-- The two protocols below differ in one action: which expression the session publishes. The
first never publishes the declared key, the second publishes nothing else. Both are gap-free, so
by the theorems above the analyser answer *is* the security statement - and at this size the
kernel can check the solver answer directly (about 20 s of `decide` over 246 variables and 291
clauses), so the verdict below carries no hypothesis at all. -/
def Guard : Protocol :=
  { roles := [{ acts := [Action.send 0 (Expr.agent 0)] }],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0], nonceDomain := [], compromised := [],
    secrets := [Secret.closed (Expr.shrk 0 0)], auths := [] }

/-- The same shape publishing the secret itself: the pipeline must call this one unsafe. -/
def Leak : Protocol :=
  { roles := [{ acts := [Action.send 0 (Expr.shrk 0 0)] }],
    sessions := [{ role := 0, self := 0, peer := 0 }],
    agents := [0], nonceDomain := [], compromised := [],
    secrets := [Secret.closed (Expr.shrk 0 0)], auths := [] }

def GB : Bounds := { steps := 1, rounds := 0 }

/-- The guarded query. -/
def qg : Query := Query.mk Guard GB [Goal.secrecy]

/-- The leaky query. -/
def ql : Query := Query.mk Leak GB [Goal.secrecy]

theorem qg_wf : WellFormed qg := by
  show validate qg = []
  decide

theorem qg_gap : domainGap Guard GB = false := by decide

theorem qg_hU : univClosed (shapeOf Guard GB) Guard := by
  unfold univClosed
  decide

theorem qg_hsec : SecretsOK (shapeOf Guard GB) Guard := by
  refine ⟨fun q x h => ?_, ?_⟩
  · have heq : Secret.store q x = Secret.closed (Expr.shrk 0 0) := List.mem_singleton.mp h
    cases heq
  · decide

theorem qg_goals : ∀ g ∈ qg.goals, goalEncoded g := by decide

theorem qg_ne : qg.goals ≠ [] := by decide

set_option maxRecDepth 4000 in
/-- The solver answer, checked by the kernel at this size. -/
theorem qg_unsat : DPLL.dpll (encode Guard GB) = none := by decide

/-- Hence the analyser answer, and hence the verdict - with no hypotheses. -/
theorem qg_verdict : analyzeQuery qg = Result.encodingUnsat := by
  have hu : univClosedBool (shapeOf Guard GB) Guard = true := by decide
  have hana : analyze Guard GB = Verdict.encodingUnsat := by
    rw [analyze, if_neg (by simp [hu]), qg_unsat]
  show analyzeQuery qg = Result.encodingUnsat
  rw [analyzeQuery]
  rw [if_pos (by simpa [WellFormed] using qg_wf)]
  rw [if_neg (by simp [qg])]
  rw [if_neg (by simp [qg, unsupported, goalEncoded, encodedGoals])]
  rw [show analyze qg.protocol qg.bounds = Verdict.encodingUnsat from hana]
  rfl

/-- **The closed security statement.** No `WithinBounds`, no representability hypothesis, no
solver-answer hypothesis: for every execution this model permits, within these sessions, these
compromises, this universe and this event bound, no selected goal is violated. That is the
sentence the objective asked SAFE to mean, proved end to end on the CNF route. -/
theorem qg_safe : boundedSafeGoals qg :=
  boundedSafe_of_encodingUnsat_of_gapFree qg_goals qg_ne qg_hU qg_hsec qg_gap qg_verdict

/-- In the public vocabulary: no permitted execution leaks a declared secret. -/
theorem qg_noLeak :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg),
        BoundedTrace Guard GB tr Cs ∧ runsLeaks Guard Cs := by
  intro h
  obtain ⟨tr, Cs, hbt, hleak⟩ := h
  exact qg_safe ⟨Goal.secrecy, by decide, tr, Cs, hbt,
    by rw [violation_secrecy]; exact hleak⟩

end ProtSat.EndToEnd