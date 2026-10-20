/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Correspondence
import ProtSat.Regressions
import ProtSat.CheckedSafe

/-!
# ProtSat/AuthGap.lean - why this module exists

The founding defect of this development is a naming defect that became a soundness defect:
`ProtSat.Analyzer.analyze` answers whether the generated CNF has a model, and the CNF's violation
clause (`ProtSat.Encode.violationLits`) demands one thing only - that a declared secret reaches the
attacker. So `Verdict.encodingUnsat`, and every verdict built on it, is silent about executions that
break authentication agreement without leaking a secret.

`ProtSat/Query.lean` *labels* that gap: `goalEncoded`, `encodedGoals`, `unsupported` and the gate
theorems refuse to hand a security verdict to a query whose selected goals the encoding cannot
represent. `ProtSat/Regressions.lean` exhibits the data: a one-session, one-step protocol whose only
possible violation is an agreement violation, which the analyser nevertheless reports as
`Verdict.encodingUnsat`.

This module turns the label into a theorem. For the protocol `Authentication.P` and the bounds
`Authentication.B` of `Regressions`:

* the secrecy reading is *proved safe* by the CNF route - `safe_for_secrecy`, derived from the
  unsatisfiability of `encode Authentication.P Authentication.B` through the gap-free bridge
  `Correspondence.boundedSafe_of_unsat_gapFree`, with all its side conditions discharged in this
  file (`univSub` is no longer one of them - `Complete.univSub_shapeOf` proves it);
* the agreement reading of the same model is *attacked* - `attacked_for_agreement`, from the
  kernel-checked `AuthBreak` witness in `Regressions`;
* both at once is `auth_gap_is_real`: same protocol, same bounds, safety for one goal and a genuine
  bounded attack for the other.

* section 6 answers the obvious objection to that pairing. `Authentication.P` declares no secret,
  so its secrecy safety is vacuous. `P2` declares one - a long-term private key - a bounded honest
  run of it holds that key (`secret_held`), its violation clause is not empty
  (`violationLits_nonempty`, `no_empty_clause2`), and the CNF is unsatisfiable anyway
  (`safe_for_secrecy2`) while the same bounds admit an unmatched commit (`attacked_for_agreement2`).

Every line below is a proposition about the definitions the tool actually uses, not a comment about
them. And nothing here overclaims: the safety proved is a *secrecy* statement, and
`why_the_formula_is_unsat` says out loud how thin its evidence is. The reason it cannot be promoted
to a statement about agreement is `goal_hypothesis_is_needed`, which shows that the goal-selection
hypothesis of `CheckedSafe.boundedSafeGoals_of_secrecy` is not decoration.
-/

namespace ProtSat.AuthGap

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  Regressions

/-! ### The two readings of one protocol -/

/-- The protocol of `Regressions.Authentication`: one session of one role that commits to a peer and
a value. No secret is declared, so no execution of it can violate the secrecy goal, and its only
`auths` tag is used by that commit, so the model is well-formed for either question. -/
abbrev P : Protocol := Authentication.P

/-- The bounds: a single event, no constructor-closure rounds. -/
abbrev B : Bounds := Authentication.B

/-- The secrecy reading: the same protocol and bounds, asking the one goal the encoding
represents. -/
def qs : Query := Query.mk P B [Goal.secrecy]

/-- The agreement reading: the query of `Regressions.Authentication`, refused by the contract. -/
abbrev qa : Query := Authentication.q

/-- The secrecy query is well-formed: nothing about the model makes the question unanswerable, so
what the CNF route says about it is not a refusal. -/
theorem qs_wellFormed : WellFormed qs := by
  show validate qs = []
  decide

/-- Every selected goal of `qs` is represented by the encoding, and something is selected: the two
conditions the bridge needs in order to be allowed to speak about this query at all. -/
theorem qs_goals : ∀ g ∈ qs.goals, goalEncoded g := by decide

theorem qs_ne : qs.goals ≠ [] := by decide

/-- The model declares no secret. Recorded because it is the whole reason the secrecy reading is
easy, and `why_the_formula_is_unsat` below makes that precise. -/
theorem no_secrets_declared : P.secrets = [] := rfl

/-! ### The side conditions of the bridge -/

/-- **The formula fact.** The analyser's `encodingUnsat` answer for this protocol *is* the statement
that the generated CNF has no model: `Regressions.Authentication.analyze_encodingUnsat` says the
solver returned `none`, and `DPLL.dpll_complete` turns that into `ProtSat.Unsat`. Nothing here
re-runs the solver: the fact is inherited from the regression, which is itself a kernel check over
the same formula. -/
theorem unsat : ProtSat.Unsat (Encode.encode P B) :=
  DPLL.dpll_complete (analyze_encodingUnsat_facts Authentication.analyze_encodingUnsat).2

/-- **The bounds name the protocol's closed expressions.** Derived from the same verdict equation,
through the two facts `analyze_encodingUnsat_facts` extracts from it and the Boolean test
`univClosedBool_iff`. This is also why the analyser did not answer `boundsTooSmall`. -/
theorem hU : univClosed (shapeOf P B) P :=
  (univClosedBool_iff (shapeOf P B) P).mp
    (analyze_encodingUnsat_facts Authentication.analyze_encodingUnsat).1

/-- **The declared store secrets are named by the bounds.** This protocol declares no store secret
at all, so no session variable needs a slot and the hypothesis is vacuous here. It is still a real
side condition in general - `Encode.shapeOf` sizes the store stride from the variables the roles
touch, not from the secret declarations - and it is the only half of the old `SecretsOK` that is not
a theorem of the construction: the other half, that every closed declared secret is a universe
message, is `Complete.secretsClosed_subset_univ`, so it is no longer asked for. -/
theorem hsec : SecretsOKStore (shapeOf P B) P := by
  intro q x h
  exact absurd h (by simp [Authentication.P])

/-- **No representability gap.** The protocol cannot build a value the CNF's value domain does not
name, so every bounded execution of it has a name in the formula. This is the decidable form of what
used to be a twelve-item hypothesis about the runs, and it is what lets the bridge be applied with
no assumption about executions at all. -/
theorem gapFree : domainGap P B = false := by decide

/-! ### 1. The CNF route proves safety - for secrecy -/

/-- **`safe_for_secrecy`.** The CNF route, run on the secrecy reading of this protocol and these
bounds, yields a bounded-security theorem: no execution the model permits, within these sessions,
these domains, this universe and this one-event bound, violates the selected goal.

The route is `Correspondence.boundedSafe_of_unsat_gapFree`: the unsatisfiability of `encode P B`
plus the side conditions discharged above. No `WithinBounds`, and no hypothesis about any
particular execution. Read it together with `why_the_formula_is_unsat`: the derivation is genuine,
and the evidence behind it is thin. -/
theorem safe_for_secrecy :
    boundedSafeGoals (Query.mk Authentication.P Authentication.B [Goal.secrecy]) :=
  Correspondence.boundedSafe_of_unsat_gapFree gapFree hU hsec unsat

/-- The same statement in the name of the query, for the theorems below that reuse it. -/
theorem safe_for_secrecy_qs : boundedSafeGoals qs := safe_for_secrecy

/-- What `safe_for_secrecy` says in the public vocabulary: no execution the model permits within
these bounds leaks a declared secret. The statement is true, and it says nothing about the commit
that has no matching claim. -/
theorem no_leak :
    ¬ ∃ (tr : List Ev) (Cs : List Cfg), BoundedTrace P B tr Cs ∧ runsLeaks P Cs := by
  intro h
  obtain ⟨tr, Cs, hbt, hleak⟩ := h
  exact safe_for_secrecy
    ⟨Goal.secrecy, by decide, tr, Cs, hbt, by rw [violation_secrecy]; exact hleak⟩

/-! ### 1b. How thin the evidence for that safety is -/

/-- **The violation clause is the empty disjunction.** `violationLits` builds one literal per way a
declared secret can become known; with no declared secret it builds none. Decided here rather than
asserted. -/
theorem why_the_formula_is_unsat : violationLits (shapeOf P B) P = [] := by decide

set_option maxRecDepth 20000 in
/-- Hence the generated CNF literally contains the empty clause, and is unsatisfiable before any
solver looks at it: the UNSAT answer is a fact about a violation clause that cannot be stated, not a
fact about the protocol's executions. -/
theorem empty_clause_in_encode : ([] : List Lit) ∈ (Encode.encode P B).clauses := by decide

/-- And the secrecy goal has no instances at all for this model, which is the semantic face of the
same fact: `safe_for_secrecy` is true, and it is true for a reason the CNF route cannot distinguish
from a protocol that really protects its secrets. -/
theorem secrecy_goal_is_unviolable : ∀ (Cs : List Cfg), ¬ runsLeaks P Cs := by
  intro Cs ⟨_C, _hC, h⟩
  cases h with
  | inl h =>
      obtain ⟨s, hs, _⟩ := h
      exact absurd hs (by simp [Authentication.P, Protocol.closedSecretTerms])
  | inr h =>
      obtain ⟨_q, _x, _v, hs, _h1, _h2⟩ := h
      exact absurd hs (by simp [Authentication.P])

/-! ### 2. The same protocol and bounds have a real authentication attack -/

/-- **`attacked_for_agreement`.** The agreement reading of the very same model is not safe: the
bounded run `Regressions.Authentication.tr` performs a commit with no matching claim anywhere, which
is `AuthBreak`, hence a `boundedAttackGoals` witness for the selected goal. This is not a labelling
choice - the witness is kernel-checked in `Regressions`. -/
theorem attacked_for_agreement : ¬ boundedSafeGoals Authentication.q :=
  fun h => h Authentication.hasAttack

/-- The attack is a bounded attack of the public predicate as well: agreement failure is one of the
two ways `Bounded.BoundedAttack` is violated, so the tool's own notion of "this model has an attack"
is inhabited at these very bounds. -/
theorem boundedAttack_exists : BoundedAttack P B := by
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := Authentication.hasAttack
  have hgeq : g = Goal.agreement := by simpa [qa, Authentication.q] using hg
  subst hgeq
  exact ⟨tr, Cs, hbt, Or.inr ((violation_agreement P Cs tr).mp hv)⟩

/-! ### 3. The headline -/

/-- **The gap, as one theorem.** Same protocol, same bounds: the CNF route proves the secrecy query
safe, and the agreement query has a genuine bounded attack. Anyone told "the formula is
unsatisfiable, therefore the protocol is safe" is being told something false as stated, and this is
the counterexample. -/
theorem auth_gap_is_real :
    boundedSafeGoals (Query.mk Authentication.P Authentication.B [Goal.secrecy]) ∧
      ¬ boundedSafeGoals Authentication.q :=
  ⟨safe_for_secrecy, attacked_for_agreement⟩

/-- The same fact in the query names, so it can be read next to the answers in section 5. -/
theorem auth_gap_is_real_qs : boundedSafeGoals qs ∧ ¬ boundedSafeGoals qa :=
  ⟨safe_for_secrecy_qs, attacked_for_agreement⟩

/-! ### 4. The goal hypothesis is doing real work -/

/-- **`goal_hypothesis_is_needed`.** `CheckedSafe.boundedSafeGoals_of_secrecy` carries
`hq : ∀ g ∈ q.goals, goalEncoded g`, and that hypothesis is not decoration: the statement obtained
by dropping it is false. Instantiated at `Authentication.q`, it would say that safety for the
secrecy reading of a query implies safety for the query itself - and here the secrecy reading is
safe (`safe_for_secrecy`) while the query is attacked (`attacked_for_agreement`). -/
theorem goal_hypothesis_is_needed :
    ¬ (∀ q : Query, boundedSafeGoals (Query.mk q.protocol q.bounds [Goal.secrecy]) →
        boundedSafeGoals q) := by
  intro hall
  exact attacked_for_agreement (hall qa safe_for_secrecy)

/-- The witness form of the same fact: a query that is safe for its secrecy reading and attacked for
itself, exhibited rather than negated. -/
theorem goal_hypothesis_is_needed_witness :
    ∃ q : Query, boundedSafeGoals (Query.mk q.protocol q.bounds [Goal.secrecy]) ∧
      ¬ boundedSafeGoals q :=
  ⟨qa, safe_for_secrecy, attacked_for_agreement⟩

/-! ### 5. What the tool actually answers -/

/-- The goal-selection gate passes for `qs`: nothing it selects is unsupported, because secrecy is
the one goal the encoding represents. -/
theorem qs_unsupported : unsupported qs = [] := by
  simp [qs, unsupported, goalEncoded, encodedGoals]

/-- The CNF route's answer for the secrecy reading: `encodingUnsat`. Note what this theorem is *not*
- it is not `Result.boundedSafe`, which `Query.lean` records that nothing constructs from a solver
answer. -/
theorem cnf_answer_is_encodingUnsat :
    analyzeQuery (Query.mk Authentication.P Authentication.B [Goal.secrecy]) =
      Result.encodingUnsat := by
  -- `qs` validates (`qs_wellFormed`), selects a goal (`qs_ne`) and selects nothing the encoding
  -- cannot represent (`qs_unsupported`), so `analyzeQuery` reduces to the lifted analyser verdict.
  show liftVerdict (analyze Authentication.P Authentication.B) = Result.encodingUnsat
  exact congrArg liftVerdict Authentication.analyze_encodingUnsat

/-- The contrast: the agreement reading is refused rather than answered. The tool does not call this
query safe - it says the goal is not represented. The gap this module proves is therefore a gap in
the *encoding*, which the contract is honest about, and not a gap in the contract. -/
theorem agreement_answer_is_refused :
    analyzeQuery Authentication.q = Result.unsupportedGoals [Goal.agreement] :=
  Authentication.query_refused

/-- And the unsatisfiability answer is not a security verdict, by the contract's own test: the
`encodingUnsat` answer asserts a fact about a formula. -/
theorem cnf_answer_is_not_security :
    securityResult (analyzeQuery (Query.mk Authentication.P Authentication.B [Goal.secrecy])) =
      false := by
  rw [cnf_answer_is_encodingUnsat]
  simp [securityResult]

/-- The two answers side by side, with the semantic fact behind them: one is a formula fact the
contract declines to call security, the other a refusal, and the protocol has a bounded attack. -/
theorem the_tool_never_says_agreement_is_broken :
    analyzeQuery (Query.mk Authentication.P Authentication.B [Goal.secrecy]) =
      Result.encodingUnsat ∧
      analyzeQuery Authentication.q = Result.unsupportedGoals [Goal.agreement] ∧
      ¬ boundedSafeGoals Authentication.q :=
  ⟨cnf_answer_is_encodingUnsat, agreement_answer_is_refused, attacked_for_agreement⟩

/-! ### 6. A second model, this one with something to keep -/

/-- **A protocol that has a secret.** The first example is honest about being vacuous; this one is
not. A principal `0` holds a long-term private key `sk(0)`, declared secret and not compromised.
Session 0 plays the committing role: it finishes a run and commits on `sk(0)`. Session 1 plays the
holding role: it loads `sk(0)` into its own register and never transmits it. The model can reach the
secret, the encoding can name the leak, and the CNF is still unsatisfiable - so the safety below is
not the safety of a protocol with nothing to protect.

The model has one principal, so the commit is addressed to that principal: what `AuthBreak` needs is
not two principals but an unmatched commit, and that is what session 0 produces. -/
def P2 : Protocol :=
  { roles := [{ acts := [Action.commit 0 (Expr.agent 0) (Expr.privk 0)] },
              { acts := [Action.assign 0 (Expr.privk 0)] }],
    sessions := [{ role := 0, self := 0, peer := 0 }, { role := 1, self := 0, peer := 0 }],
    agents := [0], nonceDomain := [], compromised := [],
    secrets := [Secret.closed (Expr.privk 0)], auths := [{ tag := 0 }] }

/-- One event: enough for either role to take its single step, and small enough that the kernel can
replay the solver's answer to it (`dpll_none2`). -/
def B2 : Bounds := { steps := 1, rounds := 0 }

/-- The declared secret message: the value of `Expr.privk 0`. -/
def sec : Term := Term.key (Key.priv 0)

/-- **(1) A secret is declared, and it is not compromised.** The declaration is non-empty, the
compromise set is empty, the secret really is one of the closed secret messages the encoding
reads, and - the point of the last line - the attacker is not handed it at the start. -/
theorem p2_has_secret : P2.secrets ≠ [] := by decide

theorem p2_not_compromised : P2.compromised = [] := rfl

theorem p2_secret_is_declared : sec ∈ P2.closedSecretTerms := by decide

theorem p2_secret_not_initial : sec ∉ initKn P2 := by decide

/-- The initial configuration, the configuration after the holding role's single step, and the
certificate of that step. The transition is exhibited, not asserted: `hold_steps` is the step
checker's own answer. -/
def K0 : Cfg := initCfg P2

/-- Session 1's store after it loads the secret. -/
def K1 : Cfg := succStore K0 1 0 sec

/-- The one-step certificate of the holding run. -/
def certHold : Certificate :=
  { init := K0, steps := [{ ev := .act 1 (.agent 0) 0, after := K1 }] }

/-- The holding step is a legal transition of the reference semantics, checked by the step
checker. -/
theorem hold_steps : checkSteps P2 K0 certHold.steps = true := by decide

/-- Hence it is a run of the operational semantics. -/
theorem hold_runs : Runs P2 (initCfg P2) (certTrace certHold) (certCfgs certHold) :=
  checkSteps_runs P2 certHold.steps K0 hold_steps

/-- And a *bounded* run: one event, every configuration inside the universe. -/
theorem hold_bounded : BoundedTrace P2 B2 (certTrace certHold) (certCfgs certHold) := by
  refine ⟨hold_runs, by decide, ?_⟩
  change ∀ C ∈ certCfgs certHold, cfgInUniverse C (univ P2 B2) = true
  decide

/-- **(2) The executability witness.** In this bounded execution the declared secret's value is
present - it sits in session 1's register - so the leak the violation literals ask about is a live
possibility of the model rather than a nullity. Contrast `no_secrets_declared`: here there *is*
something to keep. -/
theorem secret_held : ∃ C ∈ certCfgs certHold, readVar 0 (storeOf C 1) = some sec :=
  ⟨K1, List.Mem.tail _ (List.Mem.head _), by decide⟩

/-- The held value is not the attacker's: this honest run stores the key without publishing it. -/
theorem secret_not_in_knowledge : sec ∉ K1.kn := by decide

/-- Session 0's configuration after its commit, and the certificate of that step. -/
def L1 : Cfg := succAdvance K0 0

/-- The one-step certificate of the committing run. -/
def certCommit : Certificate :=
  { init := K0, steps := [{ ev := .act 0 (.agent 0) 0, after := L1 }] }

/-- The commit step is a legal transition, and a bounded run. -/
theorem commit_steps : checkSteps P2 K0 certCommit.steps = true := by decide

theorem commit_bounded : BoundedTrace P2 B2 (certTrace certCommit) (certCfgs certCommit) := by
  refine ⟨checkSteps_runs P2 certCommit.steps K0 commit_steps, by decide, ?_⟩
  change ∀ C ∈ certCfgs certCommit, cfgInUniverse C (univ P2 B2) = true
  decide

/-- The commit has no matching claim anywhere in the run, so non-injective agreement fails. -/
theorem authbreak2 : AuthBreak P2 (certCfgs certCommit) (certTrace certCommit) :=
  (authBreakBool_iff P2 (certCfgs certCommit) (certTrace certCommit)).mp (by decide)

/-- Hence the agreement reading of this model has a bounded attack, through its selected goal. -/
theorem p2_agreement_attacked : boundedAttackGoals (Query.mk P2 B2 [Goal.agreement]) :=
  ⟨Goal.agreement, by decide, certTrace certCommit, certCfgs certCommit, commit_bounded,
   by rw [violation_agreement]; exact authbreak2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- **(3) The solver answer, replayed by the kernel.** `dpll` finds no model of `encode P2 B2`.
This is not free: the formula has 410 variables and 465 clauses, and the replay costs about a minute
of kernel time - the cost `EndToEnd.lean` documents. It is also the *interesting*
case: unlike `Authentication.P`, the violation clause here is not empty, so the answer is not handed
to the solver for nothing. -/
theorem dpll_none2 : DPLL.dpll (Encode.encode P2 B2) = none := by decide

/-- **(3) The formula fact.** -/
theorem unsat2 : ProtSat.Unsat (Encode.encode P2 B2) := DPLL.dpll_complete dpll_none2

/-- **(7) The violation group is not empty.** One literal per way the declared secret can become
known at a step; the key is a universe message here, so the literal exists. -/
theorem violationLits_nonempty : violationLits (shapeOf P2 B2) P2 ≠ [] := by decide

set_option maxRecDepth 20000 in
/-- And the generated CNF contains no empty clause: contrast `empty_clause_in_encode`, where the
first model's UNSAT was explained by a violation clause that could not be stated at all. Here the
solver had to work. -/
theorem no_empty_clause2 : ([] : List Lit) ∉ (Encode.encode P2 B2).clauses := by decide

/-- The side conditions of the bridge, all closed for the second model too: the bounds name the
protocol's closed expressions, every store secret has a slot, and the value domain has no gap.
Subterm-closure of the universe is no longer a side condition to discharge:
`Complete.univSub_shapeOf` proves it for `P2` and `B2` like for anything else. Neither is the
condition that the declared secret `sec` is a universe message:
`Complete.secretsClosed_subset_univ` proves that of every protocol and every bounds, which is why
`hsec2` below is only the store-slot half and no longer has to put `sec` in the universe by
`decide`. -/
theorem hU2 : univClosed (shapeOf P2 B2) P2 := by
  unfold univClosed
  decide

theorem hsec2 : SecretsOKStore (shapeOf P2 B2) P2 :=
  fun q x h => absurd h (by simp [P2])

theorem gapFree2 : domainGap P2 B2 = false := by decide

/-- The analyser's verdict for the second model. -/
theorem analyze2 : analyze P2 B2 = Verdict.encodingUnsat := by
  have hu : univClosedBool (shapeOf P2 B2) P2 = true := by decide
  rw [analyze]
  simp [hu, dpll_none2]

theorem q2_wf : WellFormed (Query.mk P2 B2 [Goal.secrecy]) := by
  show validate (Query.mk P2 B2 [Goal.secrecy]) = []
  decide

theorem q2_goals : ∀ g ∈ (Query.mk P2 B2 [Goal.secrecy]).goals, goalEncoded g := by decide

theorem q2_ne : (Query.mk P2 B2 [Goal.secrecy]).goals ≠ [] := by decide

/-- The contract's answer to the secrecy query: `encodingUnsat`, reached through the analyser rather
than assumed. -/
theorem cnf_answer_is_encodingUnsat2 :
    analyzeQuery (Query.mk P2 B2 [Goal.secrecy]) = Result.encodingUnsat := by
  show liftVerdict (analyze P2 B2) = Result.encodingUnsat
  exact congrArg liftVerdict analyze2

/-- The agreement query is well-formed and refused, exactly as for the first model. -/
theorem q2a_wf : WellFormed (Query.mk P2 B2 [Goal.agreement]) := by
  show validate (Query.mk P2 B2 [Goal.agreement]) = []
  decide

theorem agreement_answer_is_refused2 :
    analyzeQuery (Query.mk P2 B2 [Goal.agreement]) =
      Result.unsupportedGoals [Goal.agreement] := by
  show Result.unsupportedGoals (unsupported (Query.mk P2 B2 [Goal.agreement])) = _
  simp [unsupported, goalEncoded, encodedGoals]

/-- **(3) continued: the CNF route proves safety, non-vacuously.** The same bridge as
`safe_for_secrecy`, fed with the verdict equation: the tool answers `encodingUnsat` for this query,
the goal it selected is one the encoding represents, the value domain has no gap, and therefore no
permitted execution of `P2` within `B2` leaks the declared key. Unlike the first model, there *was*
a key to leak. -/
theorem safe_for_secrecy2 : boundedSafeGoals (Query.mk P2 B2 [Goal.secrecy]) :=
  boundedSafe_of_encodingUnsat_of_gapFree q2_goals q2_ne hU2 hsec2 gapFree2
    cnf_answer_is_encodingUnsat2

/-- **(4) continued.** And yet the same model, at the same bounds, has a bounded attack on
agreement. -/
theorem attacked_for_agreement2 : ¬ boundedSafeGoals (Query.mk P2 B2 [Goal.agreement]) :=
  fun h => h p2_agreement_attacked

/-- **(6) The headline, non-vacuously.** Same protocol, same bounds, a declared secret the model
really reaches and the encoding really asks about: the CNF route proves the secrecy query safe, and
the agreement query is attacked. The gap is not an artefact of a model with nothing to protect. -/
theorem auth_gap_is_real_nonvacuous :
    boundedSafeGoals (Query.mk P2 B2 [Goal.secrecy]) ∧
      ¬ boundedSafeGoals (Query.mk P2 B2 [Goal.agreement]) :=
  ⟨safe_for_secrecy2, attacked_for_agreement2⟩

/-- The two models side by side: in the first the violation clause is the empty disjunction; in the
second it is not, and the CNF is unsatisfiable anyway. -/
theorem the_gap_survives_the_nonvacuity_check :
    violationLits (shapeOf P B) P = [] ∧ violationLits (shapeOf P2 B2) P2 ≠ [] ∧
      ProtSat.Unsat (Encode.encode P2 B2) ∧
        ¬ boundedSafeGoals (Query.mk P2 B2 [Goal.agreement]) :=
  ⟨why_the_formula_is_unsat, violationLits_nonempty, unsat2, attacked_for_agreement2⟩

end ProtSat.AuthGap

/-!
## What this proves and what it does not

**Proved.**

* `safe_for_secrecy` - the CNF route, through the gap-free bridge and four side conditions each
  decided in this file (or derived from the analyser's own verdict), establishes
  `boundedSafeGoals (Query.mk Authentication.P Authentication.B [Goal.secrecy])`.
* `attacked_for_agreement` - the same protocol and bounds admit a bounded execution that violates
  non-injective agreement, inherited from the kernel-checked `AuthBreak` witness in `Regressions`.
* `auth_gap_is_real` - the two hold simultaneously. That is the review's headline, as a proposition
  of the current code.
* `goal_hypothesis_is_needed` - the goal-selection hypothesis of
  `CheckedSafe.boundedSafeGoals_of_secrecy` cannot be dropped: the universal statement without it is
  false, with `Authentication.q` as the counterexample.
* `cnf_answer_is_encodingUnsat` and `agreement_answer_is_refused` - what the executable pipeline
  answers for the two readings, and `cnf_answer_is_not_security` - that the first of those answers
  is not labelled a security verdict by the contract.
* `why_the_formula_is_unsat` and `empty_clause_in_encode` - *why* the answer came out UNSAT for this
  model: the violation clause is the empty disjunction, so the formula is unsatisfiable before the
  solver runs.
* `safe_for_secrecy2`, `secret_held`, `violationLits_nonempty` and `no_empty_clause2` - the same
  story on a model that does declare a secret, reaches it in a bounded honest run, and has a
  non-empty violation clause with no empty clause anywhere in the formula. The second safety result
  is not vacuous, and `auth_gap_is_real_nonvacuous` pairs it with an unmatched commit at the same
  bounds.

**Not proved, and not claimed.**

* It is *not* proved that the protocol is secure. `safe_for_secrecy` is a statement about the
  secrecy goal: no permitted execution leaks a declared secret - and this protocol declares none
  (`no_secrets_declared`, `secrecy_goal_is_unviolable`), which is exactly why that half is easy, why
  the CNF is trivially unsatisfiable, and why none of it is evidence about agreement.
* It is *not* proved that the CNF route can ever decide agreement. Turning the safety statement
  above into a security statement about agreement requires agreement violation clauses in the
  encoding - a literal per way a commit fails to be matched by a claim - and
  `Encode.violationLits` contains no such clause. Until roadmap stage 4 adds them,
  `goalEncoded Goal.agreement = false` and `analyzeQuery` keeps refusing this query, which is the
  contract behaving correctly, not a fix to the encoding.
* Nothing here weakens the existing bridges. `Query.boundedSafe_of_encodingUnsat_of_gapFree` and
  `Correspondence.boundedSafe_of_unsat_gapFree` are used exactly as stated, with their hypotheses
  discharged rather than bypassed. The point of this file is that they *cannot* be applied to the
  agreement query, not that they were applied wrongly to the secrecy one.
* The bounds are one event and zero closure rounds in both models. The gap is not an artefact of
  that smallness - the agreement attack is present at these bounds and the CNF is unsatisfiable at
  these bounds - but no claim here extends to larger bounds or to unbounded security.
* The second model has one principal, so its commit is addressed to that principal. `AuthBreak` asks
  for an unmatched commit, not for a second party, and `authbreak2` exhibits exactly that - but
  `P2` is a logical witness, not a realistic protocol. A two-principal version (the same shape over
  `agents := [0, 1]`, secret `K(0,1)`) was tried: its generated CNF has 850 variables and the kernel
  replay of the solver did not finish in ten minutes, so the one-principal model is the price of
  keeping `dpll_none2` a checked fact rather than a hypothesis.
* The unsatisfiability of `encode P2 B2` is evidence the kernel replays: `dpll_none2` costs about a
  minute of check time at 410 variables. It is not an independently checked refutation. Roadmap
  stage 6 is what replaces the replay with a certificate, and
  `Correspondence.boundedSafe_of_refutation` is the socket it would plug into.
-/
