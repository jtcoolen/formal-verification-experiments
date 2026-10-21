/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Correspondence
import ProtSat.Contract
import ProtSat.Explore
import ProtSat.Examples

/-!
# ProtSat/CredentialGap.lean — the credential-provisioning gap, as a theorem

## What this file does

`ProtSat/Reference.lean` repairs a hole in the old semantics: a session may only name the credentials
it was actually given. The repair is `requiredKeys` / `provisioned` / `availableKeys` / `canUse` /
`actionUsable` (`Reference.lean:144-191`), applied by `Reference.stepOf` at `Reference.lean:241`;
its witnesses are `Reference.Gates.unprovisioned_decryption_blocked` (`:873`),
`Reference.Gates.provisioned_decryption_works` (`:880`),
`Reference.Gates.unprovisioned_key_not_publishable` (`:887`) and
`Reference.ReviewGates.unrelated_shared_key_blocked` (`:965`). Every one of those is a statement
about the *repaired* semantics. None is decided against the old one, and the audit's point is that the
old one has no notion to decide it with:

* `Expr.eval (Expr.privk a) s = some (Term.key (Key.priv a))` for *every* store `s`
  (`Protocol.lean:96`), so naming a principal's private key is the same act as naming one's own
  (`eval_privk_any_store`);
* `Expr.eval (Expr.decA (Expr.encA e a) a) s = Expr.eval e s` (`eval_decA_encA`): "decrypt for `a`"
  checks only that the ciphertext is addressed to `a`, never that the session holds the key
  (`Protocol.lean:113-116`);
* `Rel.rSend` and `Rel.rAssign` (`Operational.lean:328-332`, `:341-345`) have exactly two premises —
  the action is at that program counter, and evaluation succeeds. Neither is a credential
  (`old_send_no_credential`, `old_assign_no_credential`);
* the CNF encoding mirrors those rules and inherits the silence: the only guard in front of every
  action clause is `actGuard sh i q c = [neg (evAct ..), neg (vpc ..)]` (`Clauses.lean:305-306`) —
  two control-state literals, nothing about keys (`actGuard_shapes`) — and `sendPublishClause` puts
  whatever the expression evaluates to into the attacker's knowledge
  (`send_publish_clause_in_encode`).

Section 1 turns that into theorems. Sections 2-6 are the decided witness: the one-session protocol
`leakP` whose role is `send 0 (Expr.privk 1)`, played by a session whose `self` is `0`, with
`Secret.closed (Expr.privk 1)` declared. One event is enough.

* the old route accepts it: the independent certificate checker approves the run (`certificate_checked`)
  and it is a bounded execution that leaks (`old_attack`, i.e. `boundedAttackGoals q`);
* the CNF route *reports an attack on it*: the generated formula has a model (`cnf_sat`, obtained from
  the proved completeness bridge `Correspondence.encoding_complete_gapFree` rather than from a solver
  replay), so the analyser takes its `attack` branch (`cnf_reports_attack`) — and the violation clause
  is not the empty disjunction (`violationLits_nonempty`, `no_empty_clause`), so this is not the
  vacuous answer `AuthGap.why_the_formula_is_unsat` complains about;
* the repaired route forbids it: `Reference.stepOf` returns `none` on that very event
  (`step_blocked`, `run_blocked`, `no_reference_run`), and the deciding contract enumerates every
  execution `leakP` permits at these bounds and finds no violation (`reference_safe`,
  `reference_answer_is_safe`).

Section 7 is the headline, `credential_gap_is_real`. Section 8 is the non-vacuity the repair needs: the
*same* protocol and the *same* declaration, played by the principal the key belongs to (`provP`),
mirroring `Reference.Gates.provisioned_key_publishable` and
`Reference.Gates.provisioned_decryption_works`), runs, leaks, and is attacked by the repaired contract
(`provisioned_run`, `provisioned_leaks`, `provisioned_attacked`). The gate discriminates on the
credential, not on the constructor. Section 9 states the general negative fact: no theorem lifts an
old-route attack verdict — not even an accepted certificate — to a repaired-route attack, because `q`
is a counterexample. Section 10 puts the audit's own model, `Reference.Gates.leakKeyP`, through the
same machinery and explains why it yields a *silent* answer rather than a false attack.

## What this file does NOT do

* It does **not** fix the encoding. The fix is a clause family over variables the encoding already has:
  gate `actGuard sh i q c` on "every key the action's expressions name is available to session `q` at
  step `i`", which the audit rates mechanical. It is not mechanical in one place:
  `Complete.sat_violation` and `Sound.decCfgsFrom_runsLeaks` both read the step clauses, so both
  directions of the correspondence have to be re-proved against the new guard. Nothing here changes
  `Clauses.lean`, `Complete.lean`, `Sound.lean` or `Encode.lean`.
* It does **not** claim the old semantics is wrong about itself. `boundedAttackGoals q` is proved, and
  `Certificate.checkCertificate_sound` is genuine: the certificate really is a run of `ProtSat.Rel`.
  The defect is that `ProtSat.Rel` lets a role acquire the power to decrypt for, and to publish the key
  of, a principal it was never provisioned as.
* **This gap produces a FALSE ATTACK, not a FALSE SAFE, and the reader must not conflate it with
  `ProtSat/SnapshotGap.lean`.** SnapshotGap shows the CNF route proving SAFE while the repaired
  contract finds an attack — a wrong answer in the dangerous direction. Here the CNF route reports an
  attack that the repaired semantics does not admit: a wrong answer in the annoying direction. A false
  attack costs an engineer an afternoon and is caught the first time someone tries to reproduce it; a
  false safe is what ships. The value of this file is not "the tool is unsafe" but "the two semantics
  disagree about which runs exist, in both directions, and the older one is what the SAT correspondence
  is proved against". The same hole read the other way *is* the dangerous direction: with nothing
  declared (`Reference.Gates.leakKeyP`, section 10) the old route grants the capability and its secrecy
  question never asks about it — a silent yes from an empty clause, which is `SnapshotGap`'s subject.
* It does **not** re-run the SAT solver inside the kernel. `Encode.encode leakP B` has 659 clauses; the
  kernel replay of `DPLL.dpll (Encode.encode leakP B) ≠ none` was measured at **58.7 s of `decide` and
  89 s of type checking** on this machine (with `maxHeartbeats` raised to let it finish), which is past
  what a build should carry. So `cnf_sat` comes from the proved completeness bridge instead and
  `dpll_not_none` is a classical consequence of it at no cost; the VM answers SAT in about 0.3 s.
  **Timing of the kernel work this file does carry:** 53 `by decide` invocations, 2.8 s in total; the
  slowest is 755 ms (`attack_found_false3`, the three-event enumeration), then 430 ms
  (`send_publish_clause_in_encode`), 380 ms (`no_empty_clause`), 216 ms (`attack_found_false2`) and
  139 ms (`attack_found_false`); the module elaborates in 3.6 s wall. Nothing here is anywhere near the
  minute a solver replay would cost.
* It does **not** cover the `decA` form of the hole as a decided CNF attack (only as the evaluator fact
  `eval_decA_encA` and the reference gates), does not extend to unbounded security, to more than three
  events or two closure rounds, or to the agreement goals. And it does not re-derive the old route's own
  theorems: they are correct about `ProtSat.Rel`, and this file is a statement that `ProtSat.Rel` is not
  the semantics anybody should want.
-/

namespace ProtSat.CredentialGap

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query Represent Examples

/-! ### 1. The defect, as facts about the two semantics and the encoding -/

/-- **The old evaluator hands any private key to any store.** `Expr.eval` is a constant lookup:
`Expr.privk a` evaluates to the key of `a` in *every* session store, whatever role that store belongs
to. There is no side condition to gate on, because there is nothing to gate. -/
theorem eval_privk_any_store (a : Agent) (s : List (Var × Term)) :
    Expr.eval (Expr.privk a) s = some (Term.key (Key.priv a)) := rfl

/-- **The old evaluator decrypts for anyone named.** `decA m a` succeeds whenever `m` evaluates to a
ciphertext addressed to `a`; the session's keyring is never consulted, so the destructor round-trips
for every role that can see the ciphertext. -/
theorem eval_decA_encA (e : Expr) (a : Agent) (s : List (Var × Term)) :
    Expr.eval (Expr.decA (Expr.encA e a) a) s = Expr.eval e s := by
  cases h : Expr.eval e s <;> simp [h, Expr.eval]

/-- **`rSend` has no credential premise.** The introduction rule of `Operational.lean:328-332` with
the evaluation hypothesis discharged by `eval_privk_any_store`: a session may send another principal's
private key, and the only two things the rule asks are that the action is at that program counter and
that evaluation succeeds. The message and nonce fields the event carries are not even used. -/
theorem old_send_no_credential {P : Protocol} {C : ProtSat.Cfg} {q : Nat} {a b : Agent}
    {m : Term} {d : NonceName}
    (hact : P.actionAt q (pcOf C q) = some (Action.send a (Expr.privk b))) :
    Rel P C (Ev.act q m d) (succSend C q (Term.key (Key.priv b))) :=
  Rel.rSend hact (eval_privk_any_store b _)

/-- **`rAssign` has no credential premise either** (`Operational.lean:341-345`): the same key can be
moved into a session register by a role that was never given it — which then makes a *store*
declaration report the key as held. -/
theorem old_assign_no_credential {P : Protocol} {C : ProtSat.Cfg} {q : Nat} {x : Var} {b : Agent}
    {m : Term} {d : NonceName}
    (hact : P.actionAt q (pcOf C q) = some (Action.assign x (Expr.privk b))) :
    Rel P C (Ev.act q m d) (succStore C q x (Term.key (Key.priv b))) :=
  Rel.rAssign hact (eval_privk_any_store b _)

/-- **The repaired gate, once for every protocol and action.** If `actionUsable` says the session may
not read the action's expressions, the event has no successor. The mechanism is not specific to the
witness below, and this is the premise the old semantics never asks. -/
theorem gate_blocks {P : Protocol} {C : Reference.Cfg} {q : Nat} {act : Action}
    (h : Reference.actionUsable P C q act = false)
    (hact : P.actionAt q (Reference.pcOf C q) = some act) :
    Reference.stepOf P C (Reference.Ev.act q) = none := by
  rw [Reference.stepOf, hact]
  simp [h]

/-- **The encoding's act-guard is control state and nothing else.** Every action clause is an
implication with these two literals in front (`Clauses.lean:305-306): "session `q` acts at step `i`"
and "its program counter is `c`". No literal names a key, a session, or a credential, so the formula
has no place to say "and `q` holds the key". -/
theorem actGuard_shapes {sh : Shape} {i q c : Nat} {l : Lit} (h : l ∈ actGuard sh i q c) :
    (∃ i q, l = neg (evAct sh i q)) ∨ (∃ i q c, l = neg (vpc sh i q c)) := by
  unfold actGuard at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact Or.inl ⟨i, q, rfl⟩
  · exact Or.inr ⟨i, q, c, rfl⟩

/-- The publish clause of a send as built by `Clauses.lean:432-433`: the guard, "the expression's value
is `u`", "the attacker knows `u` at the next step". Nothing else. -/
theorem sendPublishClause_shape (sh : Shape) (i q c E u : Nat) :
    sendPublishClause sh i q c E u =
      actGuard sh i q c ++ [neg (vxe sh i q E u), pos (vkn sh (i + 1) u)] := rfl

/-! ### 2. The models -/

/-- **The credential-leak role.** One action: publish the private key of principal 1. The session that
plays it is instantiated as principal 0, so under the repaired semantics the key is not its credential
to lose. This is `Reference.Gates.leakKeyP`'s role (`Reference.lean:885`) with a declaration attached. -/
def credRole : Role := { acts := [Action.send 0 (Expr.privk 1)] }

/-- **`leakP`: the model the two routes disagree about.** One session playing agent 0 against peer 1,
and the declaration `Secret.closed (Expr.privk 1)` — the declaration is what turns the capability gap
into a *question* the old route will answer. Nothing is compromised, so the attacker does not hold the
key at the start: the only way it learns the key is the role publishing it. -/
def leakP : Protocol :=
  { roles := [credRole]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := [Secret.closed (Expr.privk 1)]
    auths := [] }

/-- **`provP`: the same model played by the owner of the key.** Only the session's `self` changes,
from 0 to 1. This is the non-vacuity control of section 8;
`Reference.Gates.provisioned_key_publishable` (`Reference.lean:895`) is this shape. -/
def provP : Protocol := { leakP with sessions := [{ role := 0, self := 1, peer := 0 }] }

/-- One event — the send — and no constructor-closure rounds: the seed universe already names the key. -/
def B : Bounds := { steps := 1, rounds := 0 }

/-- Two events, used to show the disagreement is not an artefact of a bound so small that nothing can
happen. -/
def B2 : Bounds := { steps := 2, rounds := 0 }

/-- Three events: the enumeration below still finishes in well under a second, so the repaired verdict is
checked at three bounds rather than one. -/
def B3 : Bounds := { steps := 3, rounds := 0 }

/-- The secrecy query on `leakP`. -/
def q : Query := Query.mk leakP B [Goal.secrecy]

/-- The same query at the larger event bound. -/
def q2 : Query := Query.mk leakP B2 [Goal.secrecy]

/-- The same query at three events. -/
def q3 : Query := Query.mk leakP B3 [Goal.secrecy]

/-- The secrecy query on the provisioned model. -/
def qp : Query := Query.mk provP B [Goal.secrecy]

/-- The key at issue. -/
def sk1 : Term := Term.key (Key.priv 1)

/-- **The validator does not reject this model.** This is the first thing to check, and it is what makes
the rest of the file a defect report rather than a curiosity: `Query.validate` looks at session indices,
agent domains, secret well-formedness, the compromise set and unused authentication tags, and has no
credential check. `leakP` passes with no diagnostics at all, so the driver is *permitted to answer* —
and section 4 shows what it answers. -/
theorem validator_accepts_the_model : validate q = [] := by decide

/-- Hence the query is well-formed: the disagreement below is not a refusal. -/
theorem q_wellFormed : WellFormed q := validator_accepts_the_model

/-- The same at the larger bound. -/
theorem q2_wellFormed : WellFormed q2 := by show validate q2 = []; decide

/-- The provisioned query is well-formed too: the two models differ only in who plays the role. -/
theorem qp_wellFormed : WellFormed qp := by show validate qp = []; decide

/-- The query selects the one goal the encoding represents, so the CNF route is allowed to speak. -/
theorem q_goals : ∀ g ∈ q.goals, goalEncoded g := by decide

/-- And it selects something. -/
theorem q_ne : q.goals ≠ [] := by decide

/-- **Nothing refuses this query.** The model validates, a goal is selected, and the selected goal is one
the encoding represents - so `Query.analyzeQuery` does not answer `invalidModel`, `noGoals` or
`unsupportedGoals` for `q`. It goes to the solver, and section 4 shows which branch the solver lands in.
This is the difference between a gap that is *labelled* and one that is *answered wrongly*. -/
theorem driver_not_permitted_to_refuse :
    (validate q).isEmpty = true ∧ q.goals.isEmpty = false ∧ (unsupported q).isEmpty = true := by
  refine ⟨by simp [validator_accepts_the_model], by decide, ?_⟩
  simp [unsupported, goalEncoded, encodedGoals, q]

/-- The declaration really declares the key: `closedSecretTerms` evaluates `Expr.privk 1` in the empty
store and gets it — the same value the role publishes. -/
theorem declared_is_published : sk1 ∈ leakP.closedSecretTerms := by decide

/-- The attacker does not start with it: the leak is the role's doing, not a compromise assumption. -/
theorem not_initially_known : sk1 ∉ Protocol.initKn leakP := by decide

/-- The universe names it, so the bounds can state the question at all. -/
theorem key_in_universe : sk1 ∈ univ leakP B := by decide

/-! ### 3. The old route: a permitted run that leaks -/

/-- The one event of the honest run in the old event type: session 0 acts. The message and nonce fields
are dummies, unused by `rSend` (`old_send_no_credential`). -/
def oldTrace : List Ev := [Ev.act 0 (Term.agent 0) 0]

/-- The certificate of that run: built by the simulator, checked by the independent checker. -/
def cert : Certificate := certOfTrace leakP oldTrace

set_option maxRecDepth 40000 in
/-- **The step checker accepts the credential leak.** One step, `rSend`, and `relDecide` has no
credential test to fail. -/
theorem steps_checked : checkSteps leakP (initCfg leakP) cert.steps = true := by decide

/-- **The certificate checker accepts it as an attack**: the run is a transition sequence and a visited
configuration knows a declared secret. This is the evidence format the CNF route's `attack` verdict
carries, so it is the tool's own checker that is being shown the wrong run. -/
theorem certificate_checked : checkCertificate leakP cert = true := by decide

/-- The attacker's knowledge at the end of the run contains the key. -/
theorem key_learned : sk1 ∈ (cfgAt (certCfgs cert) 1).kn := by decide

/-- The old leak predicate fires on the run. -/
theorem old_leaks_bool : runsLeaksBool leakP (certCfgs cert) = true := by decide

/-- The run is a genuine execution of the operational semantics. -/
theorem old_runs : Runs leakP (initCfg leakP) (certTrace cert) (certCfgs cert) :=
  checkSteps_runs leakP cert.steps (initCfg leakP) steps_checked

/-- And a bounded one: one event, every configuration inside the universe. -/
theorem old_bounded : BoundedTrace leakP B (certTrace cert) (certCfgs cert) :=
  ⟨old_runs, by decide, by
    intro C hC
    have hall : (certCfgs cert).all (fun C => cfgInUniverse C (univ leakP B)) = true := by decide
    exact List.all_eq_true.mp hall C hC⟩

/-- **The old route reports an attack on the query.** `boundedAttackGoals` is the proposition the CNF
correspondence is stated against, and it holds for `q` with the kernel-checked witness above. -/
theorem old_attack : boundedAttackGoals q :=
  ⟨Goal.secrecy, by decide, certTrace cert, certCfgs cert, old_bounded,
    by rw [violation_secrecy]; exact (runsLeaksBool_iff leakP (certCfgs cert)).mp old_leaks_bool⟩

/-- The same attack at the larger bound: raising `Bounds.steps` does not make it go away, because the
run is still one event long. -/
theorem old_attack2 : boundedAttackGoals q2 :=
  ⟨Goal.secrecy, by decide, certTrace cert, certCfgs cert,
    ⟨old_runs, by decide, by
      intro C hC
      have hall : (certCfgs cert).all (fun C => cfgInUniverse C (univ leakP B2)) = true := by decide
      exact List.all_eq_true.mp hall C hC⟩,
    by rw [violation_secrecy]; exact (runsLeaksBool_iff leakP (certCfgs cert)).mp old_leaks_bool⟩

/-- The old route's attack at three events, for the matching pair. -/
theorem old_attack3 : boundedAttackGoals q3 :=
  ⟨Goal.secrecy, by decide, certTrace cert, certCfgs cert,
    ⟨old_runs, by decide, by
      intro C hC
      have hall : (certCfgs cert).all (fun C => cfgInUniverse C (univ leakP B3)) = true := by decide
      exact List.all_eq_true.mp hall C hC⟩,
    by rw [violation_secrecy]; exact (runsLeaksBool_iff leakP (certCfgs cert)).mp old_leaks_bool⟩

/-- And in the goal-free form the older theorems use. -/
theorem old_attack_BoundedAttack : BoundedAttack leakP B :=
  ⟨certTrace cert, certCfgs cert, old_bounded, Or.inl
    ((runsLeaksBool_iff leakP (certCfgs cert)).mp old_leaks_bool)⟩

/-! ### 4. The CNF route: the formula has a model, so the analyser takes its attack branch -/

/-- The bounds name the protocol's closed expressions, so the analyser does not answer
`boundsTooSmall`. -/
theorem hU : univClosed (shapeOf leakP B) leakP := by unfold univClosed; decide

/-- No store secret is declared, so the store half of the shape condition is vacuous. -/
theorem hsec : SecretsOKStore (shapeOf leakP B) leakP := by
  intro q' x h
  exact absurd h (by simp [leakP])

/-- No representability gap: every value the protocol can compute is named by the universe, so the
bridge needs no hypothesis about the executions. -/
theorem gapFree : domainGap leakP B = false := by decide

set_option maxRecDepth 40000 in
/-- **The violation clause is not the empty disjunction.** Contrast `AuthGap.why_the_formula_is_unsat`
and `SnapshotGap.violationLits_nil_P0`: here the encoding really does ask whether this key reaches the
attacker, so its SAT answer is evidence about a real question — the wrong question, but a question. -/
theorem violationLits_nonempty : violationLits (shapeOf leakP B) leakP ≠ [] := by decide

set_option maxRecDepth 40000 in
/-- And the generated CNF contains no empty clause: the answer was not handed to the solver for free. -/
theorem no_empty_clause : ([] : List Lit) ∉ (Encode.encode leakP B).clauses := by decide

/-- The expression index of the published key. -/
def Ekey : Nat := eIdx leakP (Expr.privk 1)

/-- The universe slot of the published key. -/
def ukey : Nat := uIdx (shapeOf leakP B) (some sk1)

set_option maxRecDepth 40000 in
/-- **The publish clause for this send is in the generated formula**: if session 0 acts at step 0 with
program counter 0 and the expression's value is the key, then the attacker knows the key at step 1. The
only literals in front of it are `actGuard`'s two control-state literals (`actGuard_shapes`) — there is
no fourth place to put a credential test. This is the encoding half of the audit's third bullet. -/
theorem send_publish_clause_in_encode :
    actGuard (shapeOf leakP B) 0 0 0 ++ [neg (vxe (shapeOf leakP B) 0 0 Ekey ukey),
      pos (vkn (shapeOf leakP B) 1 ukey)] ∈ (Encode.encode leakP B).clauses := by decide

/-- **The CNF has a model.** Derived, not searched: `Correspondence.encoding_complete_gapFree` turns the
decided bounded attack of section 3 into a satisfying assignment, using the three side conditions above.
That is the honest way to state it — the encoding is complete for secrecy, so an old-route attack *must*
be a model of the formula, and the solver is only the finder. -/
theorem cnf_sat : ProtSat.Satisfiable (Encode.encode leakP B) :=
  Correspondence.encoding_complete_gapFree gapFree hU hsec old_attack

/-- Hence the solver cannot answer UNSAT. No replay: this is the contrapositive of `DPLL.dpll_complete`
applied to `cnf_sat`, so the kernel never evaluates `dpll` (the module header records what the replay
costs). -/
theorem dpll_not_none : DPLL.dpll (Encode.encode leakP B) ≠ none :=
  fun h => DPLL.dpll_complete h cnf_sat

/-- **The CNF route reports an ATTACK on `q`.** The analyser's own function, on the model the repaired
semantics forbids, lands in the `Verdict.attack` branch: the bounds precheck passes and the solver does
not return `none`. The evidence format of that branch is a certificate, and the certificate checker
accepts the one-event credential leak of section 3 (`certificate_checked`) - so the verdict the CNF route
would emit here is one its own checker signs off on, independently of the solver. -/
theorem cnf_reports_attack : ∃ c, Analyzer.analyze leakP B = Verdict.attack c := by
  have hu : univClosedBool (shapeOf leakP B) leakP = true := (univClosedBool_iff _ _).mpr hU
  rw [Analyzer.analyze, if_neg (by simp [hu])]
  cases h : DPLL.dpll (Encode.encode leakP B) with
  | none => exact absurd h dpll_not_none
  | some asg => exact ⟨certOf leakP B (DPLL.asgVal asg), rfl⟩

/-- Everything the CNF route asserts about this model, in one place: the branch it takes, the evidence
its checker accepts, and the semantic statement the correspondence is proved against. -/
theorem the_tool_says_attack :
    (∃ c, Analyzer.analyze leakP B = Verdict.attack c) ∧ checkCertificate leakP cert = true ∧
      boundedAttackGoals q :=
  ⟨cnf_reports_attack, certificate_checked, old_attack⟩

/-! ### 5. The repaired semantics forbids the very same event -/

/-- Session 0 of `leakP` is provisioned with its own private key and the two long-term keys of its
conversation — and with nothing else. -/
theorem provisioned_leakP :
    Reference.provisioned leakP 0 = [Key.priv 0, Key.shrk 0 1, Key.shrk 1 0] := by decide

/-- The key at issue is not among them. -/
theorem key_not_provisioned : Key.priv 1 ∉ Reference.provisioned leakP 0 := by decide

/-- The store is empty at the start, so nothing has been received into it: the available set is exactly
the provisioned set. -/
theorem available_eq_provisioned :
    Reference.availableKeys leakP (Reference.initCfg leakP) 0 =
      Reference.provisioned leakP 0 := by decide

/-- The expression demands the key and nothing else. -/
theorem requiredKeys_leak : Reference.requiredKeys (Expr.privk 1) = [Key.priv 1] := by decide

/-- So the session may not read the expression. -/
theorem can_use_false :
    Reference.canUse leakP (Reference.initCfg leakP) 0 (Expr.privk 1) = false := by decide

/-- And the action is not usable. -/
theorem action_usable_false :
    Reference.actionUsable leakP (Reference.initCfg leakP) 0 (Action.send 0 (Expr.privk 1)) = false := by
  decide

/-- **The repaired step function has no successor for that event** — the same one event the old
semantics accepts by `rSend`. -/
theorem step_blocked :
    Reference.stepOf leakP (Reference.initCfg leakP) (Reference.Ev.act 0) = none := by decide

/-- The same fact through the general mechanism of section 1: it is the credential gate that blocks,
not an absent action or a malformed model. -/
theorem step_blocked_by_the_gate :
    Reference.stepOf leakP (Reference.initCfg leakP) (Reference.Ev.act 0) = none :=
  gate_blocks action_usable_false (by decide)

/-- **There is no run of the repaired semantics in which session 0 publishes the key.** -/
theorem run_blocked :
    Reference.run leakP (Reference.initCfg leakP) [Reference.Ev.act 0] = none := by decide

/-- Hence no configuration list witnesses it: the repaired `Runs` relation is empty for that trace.
This is the half of the audit's claim that was never decided before — not "the repaired semantics
dislikes this run", but "the run the old route accepts does not exist there at all". -/
theorem no_reference_run :
    ¬ ∃ Cs : List Reference.Cfg, Reference.Runs leakP (Reference.initCfg leakP)
      [Reference.Ev.act 0] Cs := by
  intro ⟨Cs, h⟩
  rw [Reference.Runs] at h
  rw [run_blocked] at h
  exact absurd h (by simp)

/-! ### 6. The repaired route says SAFE -/

/-- **The enumeration finds nothing.** `Reference.Contract.attackFound` walks every execution `leakP`
permits within these bounds — every idle step, every deduction the universe offers, every delivery, and
the one blocked action — and no visited configuration knows a declared secret. Exhaustive, not sampled:
`Contract.attackFound_decides` is the two-sided statement. -/
theorem attack_found_false : Reference.Contract.attackFound q = false := by decide

/-- **`Reference.Contract.boundedSafe q`**: no permitted execution of the query's model violates a
selected goal. -/
theorem reference_safe : Reference.Contract.boundedSafe q :=
  Reference.Contract.boundedSafe_of_attackFound_false attack_found_false

/-- Equivalently: the repaired route has no attack to report. -/
theorem reference_not_attack : ¬ Reference.Contract.boundedAttack q := reference_safe

/-- The deciding contract's own answer: a `boundedSafe` verdict with its evidence attached — the verdict
the CNF driver is not allowed to produce at all (`Query.analyzeQuery_ne_boundedSafe`). -/
theorem reference_answer_is_safe :
    ∃ e, Reference.Contract.analyze q = Reference.Contract.Verdict.boundedSafe e := by
  rw [Reference.Contract.analyze, if_pos (by simp [validator_accepts_the_model]),
    if_neg (by decide)]
  exact Reference.Contract.answer_boundedSafe attack_found_false

/-- At the larger bound too: two events, every deduction and delivery the universe offers, and still no
violation. The disagreement is not an artefact of a bound so small that the model cannot move. -/
theorem attack_found_false2 : Reference.Contract.attackFound q2 = false := by decide

/-- Hence safety at `B2` as well. -/
theorem reference_safe2 : Reference.Contract.boundedSafe q2 :=
  Reference.Contract.boundedSafe_of_attackFound_false attack_found_false2

/-- Three events: the enumeration still finds nothing, so the repaired verdict is checked at three
bounds rather than one (the cost is in the module header's timing note). -/
theorem attack_found_false3 : Reference.Contract.attackFound q3 = false := by decide

/-- Hence safety at `B3` too. -/
theorem reference_safe3 : Reference.Contract.boundedSafe q3 :=
  Reference.Contract.boundedSafe_of_attackFound_false attack_found_false3

/-! ### 7. The disagreement -/

/-- **`credential_gap_is_real`.** Same protocol, same bounds, same selected goal: the old route — the
one the SAT correspondence is proved against, and the one the CNF driver answers about — has a
kernel-checked bounded attack, and the repaired reference semantics has no such run and is proved safe
by exhaustion. The credential-provisioning repair is therefore not a refactoring of the same judgements:
it changes which executions exist, and the two answers are opposite. Read with
`SnapshotGap.snapshot_gap_is_real`, which is the same shape of disagreement pointing the other way. -/
theorem credential_gap_is_real :
    boundedAttackGoals q ∧ Reference.Contract.boundedSafe q := ⟨old_attack, reference_safe⟩

/-- The disagreement as a disagreement about safety: the old route's safety statement is *false* for
this query, and the repaired route's is *true*. -/
theorem attacked_here_safe_there : ¬ boundedSafeGoals q ∧ Reference.Contract.boundedSafe q :=
  ⟨fun h => h old_attack, reference_safe⟩

/-- The disagreement at the level of the two drivers' answers: the CNF route takes its attack branch,
the deciding contract produces a safety verdict with evidence. -/
theorem two_drivers_opposite_answers :
    (∃ c, Analyzer.analyze leakP B = Verdict.attack c) ∧
      (∃ e, Reference.Contract.analyze q = Reference.Contract.Verdict.boundedSafe e) :=
  ⟨cnf_reports_attack, reference_answer_is_safe⟩

/-- Where the role stands at the start: session 0's program counter is 0 and the action there is the
publication of the key. Both routes read this the same way; they disagree about what it entitles. -/
theorem action_at_zero :
    leakP.actionAt 0 (pcOf (initCfg leakP) 0) = some (Action.send 0 (Expr.privk 1)) := by decide

/-- One event, two verdicts, stated about the step functions rather than the queries: the old transition
relation has the step, the repaired step function returns `none`. -/
theorem one_event_two_verdicts :
    (∃ C' : ProtSat.Cfg, Rel leakP (initCfg leakP) (Ev.act 0 (Term.agent 0) 0) C') ∧
      Reference.stepOf leakP (Reference.initCfg leakP) (Reference.Ev.act 0) = none :=
  ⟨⟨succSend (initCfg leakP) 0 sk1,
     Rel.rSend action_at_zero (eval_privk_any_store 1 _)⟩, step_blocked⟩

/-- **The disagreement survives larger bounds.** At two and at three events the old route still has the
attack and the repaired route still proves safety. -/
theorem credential_gap_is_real2 :
    boundedAttackGoals q2 ∧ Reference.Contract.boundedSafe q2 := ⟨old_attack2, reference_safe2⟩

/-- The same at three events. -/
theorem credential_gap_is_real3 :
    boundedAttackGoals q3 ∧ Reference.Contract.boundedSafe q3 := ⟨old_attack3, reference_safe3⟩

/-! ### 8. Non-vacuity: the repair is not "block everything" -/

/-- **The provisioned run exists.** `provP` is `leakP` with the session playing the owner of the key;
the repaired semantics runs the very same event. This is
`Reference.Gates.provisioned_key_publishable` (`Reference.lean:895`) for this model: the difference is
the credential, not the expression. -/
theorem provisioned_run :
    Reference.run provP (Reference.initCfg provP) [Reference.Ev.act 0] ≠ none := by decide

/-- Hence a genuine repaired-semantics execution, not merely a non-`none` function value. -/
theorem provisioned_runs :
    ∃ Cs : List Reference.Cfg, Reference.Runs provP (Reference.initCfg provP)
      [Reference.Ev.act 0] Cs := by
  cases h : Reference.run provP (Reference.initCfg provP) [Reference.Ev.act 0] with
  | none => exact absurd h provisioned_run
  | some Cs => exact ⟨Cs, h⟩

/-- **And it leaks.** The published key is a declared secret of the same model, so the repaired
semantics' own monitor reports the violation. The gate is not a ban on the constructor: when the session
may name the key, publishing it is an attack. -/
theorem provisioned_leaks :
    Reference.traceLeaksBool provP (Reference.Gates.visit provP [Reference.Ev.act 0]) = true := by
  decide

/-- The repaired contract therefore *finds* the attack on the provisioned model: exhaustive enumeration,
positive answer, no hand-carried witness. -/
theorem provisioned_attack_found : Reference.Contract.attackFound qp = true := by decide

/-- Hence `boundedAttack` for the provisioned query. -/
theorem provisioned_attacked : Reference.Contract.boundedAttack qp :=
  Reference.Contract.boundedAttack_of_attackFound provisioned_attack_found

/-- The old route agrees there. With the credential present the two semantics say the same thing, which
is what makes the disagreement of section 7 about the credential and nothing else. -/
theorem provisioned_old_attack : boundedAttackGoals qp :=
  ⟨Goal.secrecy, by decide, certTrace (certOfTrace provP oldTrace),
    certCfgs (certOfTrace provP oldTrace),
    ⟨checkSteps_runs provP (certOfTrace provP oldTrace).steps (initCfg provP) (by decide), by decide,
      by
        intro C hC
        have hall : (certCfgs (certOfTrace provP oldTrace)).all
            (fun C => cfgInUniverse C (univ provP B)) = true := by decide
        exact List.all_eq_true.mp hall C hC⟩,
    by
      rw [violation_secrecy]
      exact (runsLeaksBool_iff provP (certCfgs (certOfTrace provP oldTrace))).mp (by decide)⟩

/-- The repair's own positive control, restated as a proposition rather than a Boolean: the unprovisioned
decryption is blocked (`Reference.Gates.unprovisioned_decryption_blocked`, `Reference.lean:873`) while
the provisioned one *is* an execution (`Reference.Gates.provisioned_decryption_works`, `:880`). The
`decA` case needs the ciphertext delivered first, which is why it is a three-event trace. -/
theorem provisioned_decryption_works_as_prop :
    ∃ Cs : List Reference.Cfg, Reference.Runs Reference.Gates.decAOwnP
      (Reference.initCfg Reference.Gates.decAOwnP) Reference.Gates.decATrace Cs := by
  cases h : Reference.run Reference.Gates.decAOwnP (Reference.initCfg Reference.Gates.decAOwnP)
      Reference.Gates.decATrace with
  | none => exact absurd h (by simpa using Reference.Gates.provisioned_decryption_works)
  | some Cs => exact ⟨Cs, h⟩

/-- A session's own key *is* available to it, so the gate is not a blanket refusal to name keys. -/
theorem own_key_available :
    Key.priv 0 ∈ Reference.availableKeys leakP (Reference.initCfg leakP) 0 := by decide

/-! ### 9. There is no lift from old-route attacks to repaired-route attacks -/

/-- **No theorem lifts an old-route attack verdict to a repaired-route attack verdict.** The universal
statement is false and `q` is the counterexample: it has a kernel-checked `boundedAttackGoals` proof and
a proved `Reference.Contract.boundedSafe`. Compare
`SnapshotGap.reference_semantics_hypothesis_is_needed`, which makes the dual point for *safety* verdicts,
and `AuthGap.goal_hypothesis_is_needed`, which makes it for goal selection. -/
theorem credential_authority_hypothesis_is_needed :
    ¬ ( ∀ (qq : Query), boundedAttackGoals qq → Reference.Contract.boundedAttack qq) := by
  intro hall
  exact reference_not_attack (hall q old_attack)

/-- The witness form: exhibited rather than negated. -/
theorem credential_authority_hypothesis_is_needed_witness :
    ∃ qq : Query, boundedAttackGoals qq ∧ Reference.Contract.boundedSafe qq :=
  ⟨q, old_attack, reference_safe⟩

/-- **The certificate checker is not a decision procedure for the repaired semantics either.** "The
independent checker accepted the certificate, therefore the protocol has an attack" is a theorem of the
old semantics (`Certificate.checkCertificate_sound`), and its conclusion does not transfer: this
certificate is accepted and names no repaired-semantics execution at all. The strongest transfer
principle one might hope for, refuted. -/
theorem certificate_accepted_not_reference_attack :
    ¬ ( ∀ (P : Protocol) (Bd : Bounds) (c : Certificate),
          checkCertificate P c = true →
            Reference.Contract.boundedAttack (Query.mk P Bd [Goal.secrecy])) := by
  intro hall
  exact reference_not_attack (hall leakP B cert certificate_checked)

/-- Dually for the CNF verdict: an `attack` answer of the CNF route does not entail a repaired-route
attack, so the verdict cannot be re-labelled without re-proving the encoding against the repaired step
function. -/
theorem cnf_attack_verdict_not_reference_attack :
    ¬ ( ∀ (P : Protocol) (Bd : Bounds),
          (∃ c, Analyzer.analyze P Bd = Verdict.attack c) →
            Reference.Contract.boundedAttack (Query.mk P Bd [Goal.secrecy])) := by
  intro hall
  exact reference_not_attack (hall leakP B cnf_reports_attack)

/-! ### 10. The audit's own model -/

/-- The model the repair was written against (`Reference.Gates.leakKeyP`, `Reference.lean:884-885):
the same publication of a key the session was not given. -/
abbrev leakKeyP : Protocol := Reference.Gates.leakKeyP

/-- The old semantics permits it: one event, accepted as a run. -/
theorem leakKeyP_old_run :
    Runs leakKeyP (initCfg leakKeyP) (certTrace (certOfTrace leakKeyP oldTrace))
      (certCfgs (certOfTrace leakKeyP oldTrace)) :=
  checkSteps_runs leakKeyP (certOfTrace leakKeyP oldTrace).steps (initCfg leakKeyP) (by decide)

/-- The attacker really learns the key in that run of the old semantics. -/
theorem leakKeyP_key_learned :
    sk1 ∈ (cfgAt (certCfgs (certOfTrace leakKeyP oldTrace)) 1).kn := by decide

/-- The repaired semantics blocks it — `Reference.Gates.unprovisioned_key_not_publishable`
(`Reference.lean:887`). -/
theorem leakKeyP_blocked :
    Reference.run leakKeyP (Reference.initCfg leakKeyP) [Reference.Ev.act 0] = none := by decide

/-- **Why the audit's model gives a silent answer rather than a false attack:** it declares no secret at
all (`secrets := []`, `Reference.lean:812`), so neither route has a secrecy question to answer, the
CNF's violation clause is the empty disjunction
(`SnapshotGap.violationLits_nil_of_secrets_nil`) and its CNF is unsatisfiable at every bound
(`SnapshotGap.unsat_of_secrets_nil`). `leakP` is that model plus the one declaration that makes the
question askable — and the answer it then gets is the false attack of section 4. Capability gap and false
attack are the same hole seen from two sides: with nothing declared the old route says nothing, and with
the key declared it says the wrong thing. -/
theorem leakKeyP_declares_nothing : leakKeyP.secrets = [] := rfl

/-- And `leakP` differs from it by exactly that declaration: the one `Secret` that makes the old route
answer, instead of saying nothing. -/
theorem leakP_has_the_declaration : leakP.secrets = [Secret.closed (Expr.privk 1)] := rfl

end ProtSat.CredentialGap
