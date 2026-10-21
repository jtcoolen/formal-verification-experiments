/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Correspondence
import ProtSat.CheckedSafe
import ProtSat.AnalyzerEvidence
import ProtSat.Certificate
import ProtSat.Contract
import ProtSat.Prune

/-!
# ProtSat/SnapshotGap.lean - the `Action.secret` snapshot gap, as a theorem

## What this file does

`ProtSat.Action.secret` is a real constructor of the protocol language (`Protocol.lean:181`,
"Declare the value of e secret"). The repaired reference semantics implements it: `Reference.actStep`
evaluates the expression and stores the *value* into the persistent obligation list `Cfg.oblig`
(`Reference.lean:73`, `:94`, `:214`), and the leak predicate reads that list (`declaredSecrets`,
`:479-480`). `Reference.Gates.snapshot_obligation_kept` (`:929`) and `Reference.Gates.snapshot_leaks`
(`:934`) are the kernel-checked witnesses that a value declared secret and then overwritten is still
caught by the repaired semantics.

The CNF encoding does not implement it. `Encode.actionClauses` has no case for `Action.secret`: the
match ends in a catch-all `| _ => []` (`Clauses.lean:469`), so the action contributes no clauses at
all beyond advancing the program counter. The secrecy violation clause is
`closedLeakLits ++ storeLeakLits` (`Clauses.lean:679-680`) and the second family reads the *current*
value of a register named by `Secret.store` (`:650-654`, `:669-672`). Section 1 turns those source
facts into theorems: `actionClauses_secret` is `rfl`, `violationLits_shapes` says every literal of
the violation clause names either "the attacker knows `u` at step `i`" or "session `q`'s register `x`
holds `u` and the attacker knows `u` at step `i`" - there is nowhere in it to put an obligation - and
`unsat_of_secrets_nil` says that a model whose only secrecy declaration is an `Action.secret`
generates a CNF with an empty clause, so the solver's UNSAT for it is a fact about a question the
encoding cannot state.

Sections 2-7 reproduce, for this gap, the pattern `ProtSat/AuthGap.lean` established for the
agreement gap, on two models that share one role.

* `P0` - the snapshot role with no `Secret` declaration at all. The CNF route is *proved* safe for it
  (section 5, through `Correspondence.boundedSafe_of_unsat_gapFree`, the unsatisfiability supplied
  free of charge by `unsat_of_secrets_nil`), the repaired contract finds a bounded attack on the same
  query (section 6), and the two together are `snapshot_gap_is_real`. The price of that cheapness is
  vacuity: `violationLits_nil_P0` says the secrecy violation clause of `P0` is the empty disjunction,
  so the CNF cannot even state the question. That is *worse* than the agreement gap, where at least a
  secrecy question existed to be answered, and the file says so out loud.
* `P` - the same role plus the declaration the CNF *can* read, `secrets := [Secret.store 0 0]`. Now
  the violation clause is not empty (`violationLits_nonempty`), the generated CNF has no empty clause
  (`no_empty_clause`), and the encoding really does ask whether the register that held the declared
  value ever holds a known message. It asks the right question about the right register and reads it
  at the wrong time: the register was overwritten before the value was published, so the answer is
  still "no leak" while the repaired semantics says the value leaked. Section 4 exhibits the honest
  execution in both semantics; section 8 records why the kernel cannot afford to replay the solver on
  this model and states its safety theorem with the formula fact as a single hypothesis, exactly as
  `EndToEnd.lean` does when a replay is out of budget.

Section 7 is the headline and section 8 states the general necessity fact: no theorem lifts a
CNF-route safety verdict to the repaired contract's safety, because these queries are counterexamples
to the lift. Section 9 puts the audit's own model, `Reference.Gates.snapshotP`, through the same
machinery, at every bound.

## What this file does NOT do

* It does **not** fix the gap. The fix is an obligation-variable block in the encoding (a `vobl`
  family, one variable per "the value declared secret at event `j` is `u`"), a third family of secrecy
  violation literals reading it, and `Complete.sat_violation` re-proved for the new violation clause.
  None of that is here, and nothing here changes `Clauses.lean`, `Complete.lean` or `Encode.lean`. The
  audit's note that the decoding cone does not read `sat_violation` is right about one direction and
  wrong about the other, and the file records which is which: `Complete.sat_violation`
  (Complete.lean:4413) is the only consumer of `violationLits` on the run-to-assignment side, but the
  assignment-to-run side reads the clause too - `Sound.decCfgsFrom_runsLeaks` goes through
  `Complete.violation_leak` - so a new violation family has to be re-decoded there as well. The fix is
  cheap because those two lemmas are local, not because nothing else reads the clause.
* It does **not** claim the protocol is secure, nor that the CNF route is unsound with respect to the
  semantics it was proved against. `boundedSafeGoals` is true of these queries and its proofs are
  genuine; what this file establishes is that the proposition is about the wrong leak predicate.
* It does **not** re-run the solver inside the kernel at a cost the build can afford. Section 8 records
  the measurement: the replay of `DPLL.dpll (Encode.encode P B) = none` on the non-vacuous model did
  not finish in 43 minutes, so that one safety theorem carries the formula fact as a hypothesis. Every
  `by decide` that *is* in this file costs at most 0.4 s and the module elaborates in about 4 s.
* It does **not** extend to unbounded security, to larger bounds, or to the agreement goals.
-/

namespace ProtSat.SnapshotGap

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  CheckedSafe Correspondence

/-! ### 1. The defect, as facts about the encoding -/

/-- **`Action.secret` generates no clauses.** For every shape, protocol, step, session and program
counter, the action-specific clause family of a `secret` action is the empty list: the match in
`Encode.actionClauses` (`Clauses.lean:446-469`) has no case for it and falls into the catch-all. The
action still advances the program counter, and that is all the encoding sees of it. -/
theorem actionClauses_secret (sh : Shape) (P : Protocol) (i q c : Nat) (e : Expr) :
    Encode.actionClauses sh P i q c (Action.secret e) = [] := rfl

/-- Every literal of the closed-secret family is a knowledge literal: "the attacker knows `u` at step
`i`". Nothing about how `u` came to be declared secret appears in it. -/
theorem mem_closedLeakLits {sh : Shape} {P : Protocol} {i : Nat} {l : Lit}
    (h : l ∈ closedLeakLits sh P i) : ∃ u, l = pos (vkn sh i u) := by
  unfold closedLeakLits at h
  obtain ⟨u, hu, heq⟩ := List.mem_filterMap.mp h
  cases hval : valAt sh u with
  | none => simp [hval] at heq
  | some t =>
      simp only [hval] at heq
      split at heq
      · exact ⟨u, (Option.some.inj heq).symm⟩
      · exact absurd heq (by simp)

/-- Every literal of the store-leak family is a store-leak conjunction: "session `q`'s register `x`
holds `u` *now* and the attacker knows `u` *now*". The reading is of the current store, which is
precisely what a snapshot obligation is not. -/
theorem mem_storeLeakLits {sh : Shape} {P : Protocol} {i : Nat} {l : Lit}
    (h : l ∈ storeLeakLits sh P i) : ∃ q x u, l = pos (vau sh i q x u) := by
  unfold storeLeakLits litsSess litsVar at h
  obtain ⟨q, hq, h'⟩ := List.mem_flatMap.mp h
  obtain ⟨x, hx, h2⟩ := List.mem_flatMap.mp h'
  unfold storeLeakLitsAt at h2
  split at h2
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h2
    exact ⟨q, x, u, rfl⟩
  · exact absurd h2 (by simp)

/-- **The violation clause has no place for an obligation.** Every literal the secrecy violation
clause can contain names either a knowledge variable or a store-leak auxiliary variable, and both are
read at the step the literal is indexed by. Neither can say "a `secret` action happened earlier and
the value it named is now known". This is the gap, stated once for every protocol and every shape. -/
theorem violationLits_shapes {sh : Shape} {P : Protocol} {l : Lit}
    (h : l ∈ violationLits sh P) :
    (∃ i u, l = pos (vkn sh i u)) ∨ (∃ i q x u, l = pos (vau sh i q x u)) := by
  unfold violationLits at h
  obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
  rw [List.mem_append] at h
  rcases h with h | h
  · left
    obtain ⟨u, hu⟩ := mem_closedLeakLits h
    exact ⟨i, u, hu⟩
  · right
    obtain ⟨q, x, u, hu⟩ := mem_storeLeakLits h
    exact ⟨i, q, x, u, hu⟩

/-- With no `Secret` declared there are no closed secret terms. -/
theorem closedSecretTerms_nil {P : Protocol} (h : P.secrets = []) : P.closedSecretTerms = [] := by
  simp [Protocol.closedSecretTerms, h]

/-- So the closed-secret half of the violation clause is empty. -/
theorem closedLeakLits_nil {sh : Shape} {P : Protocol} (h : P.closedSecretTerms = []) (i : Nat) :
    closedLeakLits sh P i = [] := by
  unfold closedLeakLits
  refine List.eq_nil_iff_forall_not_mem.mpr (fun l hl => ?_)
  obtain ⟨u, hu, heq⟩ := List.mem_filterMap.mp hl
  cases hval : valAt sh u with
  | none => simp [hval] at heq
  | some t =>
      simp only [hval, h] at heq
      simp at heq

/-- And the store-leak half: `storeSecret` asks whether `Secret.store q x` is in `P.secrets`, and an
`Action.secret` is not a `Secret`. -/
theorem storeLeakLits_nil {sh : Shape} {P : Protocol} (h : P.secrets = []) (i : Nat) :
    storeLeakLits sh P i = [] := by
  unfold storeLeakLits litsSess litsVar storeLeakLitsAt storeSecret
  simp [h]

/-- **The whole violation clause is empty.** For a model whose only secrecy declaration is the
`Action.secret` in its role, `Encode.violationLits` builds no literal at all. -/
theorem violationLits_nil_of_secrets_nil {sh : Shape} {P : Protocol} (h : P.secrets = []) :
    violationLits sh P = [] := by
  unfold violationLits litsStep1
  refine List.eq_nil_iff_forall_not_mem.mpr (fun l hl => ?_)
  obtain ⟨i, hi, h2⟩ := List.mem_flatMap.mp hl
  rw [List.mem_append] at h2
  rcases h2 with h2 | h2
  · rw [closedLeakLits_nil (closedSecretTerms_nil h) i] at h2
    exact absurd h2 (by simp)
  · rw [storeLeakLits_nil h i] at h2
    exact absurd h2 (by simp)

/-- Hence the generated CNF literally contains the empty clause: it is unsatisfiable before a solver
looks at it. -/
theorem empty_clause_of_secrets_nil {P : Protocol} {B : Bounds} (h : P.secrets = []) :
    ([] : List Lit) ∈ (Encode.encode P B).clauses := by
  show ([] : List Lit) ∈ (encodeGroups (shapeOf P B) P).flatMap (fun g => g.clauses)
  refine List.mem_flatMap.mpr ⟨violationClauses (shapeOf P B) P, by simp [encodeGroups], ?_⟩
  rw [violationClauses, cnfOf, violationLits_nil_of_secrets_nil h]
  exact List.Mem.head _

/-- **A model that declares its secret only by `Action.secret` is CNF-unsatisfiable, hence "safe".**
Whatever the protocol and whatever the bounds: if `P.secrets = []` then the encoding has no model, so
the bridge is entitled to answer `boundedSafeGoals` for the secrecy query - and that answer carries
no information about any secret the role declared by an action. -/
theorem unsat_of_secrets_nil {P : Protocol} {B : Bounds} (h : P.secrets = []) :
    ProtSat.Unsat (Encode.encode P B) := by
  rintro ⟨a, ha⟩
  have hcl := ha [] (empty_clause_of_secrets_nil h)
  exact absurd hcl (by simp [Clause.eval])

/-! ### 2. The models -/

/-- **The snapshot role.** One session, four actions:

* `pc 0` loads the long-term private key `sk(0)` into register 0 - the session *has* the value;
* `pc 1` declares it secret with `Action.secret` - the repaired semantics snapshots the value into
  `Cfg.oblig`; the CNF sees nothing at all (`actionClauses_secret`);
* `pc 2` overwrites register 0 with `K(0,0)`, a different key the attacker does not hold either - the
  register the encoding reads no longer names the declared value;
* `pc 3` publishes `sk(0)`.

This is the shape of `Reference.Gates.snapshotP` (`Reference.lean:902-914`) with the pair-and-project
step replaced by a direct publication, so that the same four events are expressible in the old
operational semantics too and the two routes can be compared on one execution. -/
def snapshotRole : Role :=
  { acts := [Action.assign 0 (Expr.privk 0), Action.secret (Expr.privk 0),
             Action.assign 0 (Expr.shrk 0 0), Action.send 0 (Expr.privk 0)] }

/-- The declared value: the private key of the only principal. -/
def v : Term := Term.key (Key.priv 0)

/-- The scrub value: a different key, which the attacker does not hold either. -/
def w : Term := Term.key (Key.shrk 0 0)

/-- **The vacuous model.** The snapshot role, and nothing in `secrets`. The CNF has no vocabulary in
which this model states a secrecy question. -/
def P0 : Protocol :=
  { roles := [snapshotRole]
    sessions := [{ role := 0, self := 0, peer := 0 }]
    agents := [0]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [] }

/-- **The non-vacuous model.** The same role, and the declaration the CNF *can* read: register 0 of
session 0 is a declared secret. The value that register holds is the one the role declares by
`Action.secret` and then overwrites. -/
def P : Protocol := { P0 with secrets := [Secret.store 0 0] }

/-- Four events: enough for the one session to take its four steps and no more. -/
def B : Bounds := { steps := 4, rounds := 0 }

/-- The secrecy query on the vacuous model. -/
def q0 : Query := Query.mk P0 B [Goal.secrecy]

/-- The secrecy query on the non-vacuous model. -/
def q : Query := Query.mk P B [Goal.secrecy]

theorem P0_secrets : P0.secrets = [] := rfl
theorem P_secrets : P.secrets = [Secret.store 0 0] := rfl
theorem P0_no_closed : P0.closedSecretTerms = [] := closedSecretTerms_nil P0_secrets
theorem P_no_closed : P.closedSecretTerms = [] := by
  simp [Protocol.closedSecretTerms, P]

theorem q0_wellFormed : WellFormed q0 := by
  show validate q0 = []
  decide

theorem q_wellFormed : WellFormed q := by
  show validate q = []
  decide

theorem q0_goals :  ∀ g ∈ q0.goals, goalEncoded g := by decide
theorem q_goals :  ∀ g ∈ q.goals, goalEncoded g := by decide
theorem q0_ne : q0.goals ≠ [] := by decide
theorem q_ne : q.goals ≠ [] := by decide

/-! ### 3. The honest execution, in both semantics -/

/-- The four session events of the honest execution. -/
def tr : List Reference.Ev :=
  [Reference.Ev.act 0, Reference.Ev.act 0, Reference.Ev.act 0, Reference.Ev.act 0]

/-- The configurations the honest execution visits, vacuous model. -/
def Cs0 : List Reference.Cfg := Reference.Gates.visit P0 tr

/-- The configurations the honest execution visits, non-vacuous model. -/
def Cs : List Reference.Cfg := Reference.Gates.visit P tr

/-- **The execution is legal.** The honest run really reaches the `secret` action and really
publishes the declared value: the reference step function returns a successor for all four events. -/
theorem run_reaches_the_secret : Reference.run P (Reference.initCfg P) tr ≠ none := by decide

/-- The same for the vacuous model - the two models share the role. -/
theorem run_reaches_the_secret0 : Reference.run P0 (Reference.initCfg P0) tr ≠ none := by decide

/-- The register really held the declared value: after the first action, session 0's register 0 is
`sk(0)`, so the `secret` action at the next program counter declares what the session holds. -/
theorem register_held_it :
    readVar 0 (Reference.storeOf (Reference.Gates.nthCfg P tr 1) 0) = some v := by decide

/-- The `secret` action snapshots the value into the obligation list, and the obligation survives:
four events later, with the register long overwritten, `Cfg.oblig` still names `sk(0)`. This is
`Reference.Gates.snapshot_obligation_kept` for this model. -/
theorem obligation_kept : (Reference.Gates.nthCfg P tr 4).oblig = [v] := by decide

/-- The register no longer names it: the third action overwrote it with `K(0,0)`, and that is all a
check that reads the current store can see. This is `Reference.Gates.snapshot_register_forgotten`. -/
theorem register_forgotten :
    readVar 0 (Reference.storeOf (Reference.Gates.nthCfg P tr 4) 0) = some w := by decide

/-- The overwrite value is not known either, so the store declaration cannot report the leak by
accident. -/
theorem scrub_not_known : w ∉ (Reference.Gates.nthCfg P tr 4).kn := by decide

/-- The declared value *is* known at the end of the honest run: the fourth action published it. -/
theorem value_published : v ∈ (Reference.Gates.nthCfg P tr 4).kn := by decide

/-- **The repaired semantics leaks**, non-vacuous model: decided by the same monitor
`Reference.Gates.snapshot_leaks` uses. -/
theorem leaks_decided : Reference.traceLeaksBool P Cs = true := by decide

/-- The same fact on the vacuous model. -/
theorem leaks_decided0 : Reference.traceLeaksBool P0 Cs0 = true := by decide

theorem leaks : Reference.traceLeaks P Cs :=
  (Reference.traceLeaksBool_iff P Cs).mp leaks_decided

theorem leaks0 : Reference.traceLeaks P0 Cs0 :=
  (Reference.traceLeaksBool_iff P0 Cs0).mp leaks_decided0

/-- The honest execution is a *bounded* execution of the repaired semantics at these very bounds:
four events, every configuration inside the universe and the nonce domain. -/
theorem honest_bounded : Reference.Explore.BoundedRun P B tr Cs :=
  ⟨by show Reference.run P (Reference.initCfg P) tr = some Cs; decide, by decide, by
      intro C hC
      have hall : (Cs.all fun C => Reference.Explore.inBoundsBool P B C) = true := by decide
      exact (Reference.Explore.inBoundsBool_iff (P := P) (B := B) (C := C)).mp
        (List.all_eq_true.mp hall C hC)⟩

/-- The same for the vacuous model. -/
theorem honest_bounded0 : Reference.Explore.BoundedRun P0 B tr Cs0 :=
  ⟨by show Reference.run P0 (Reference.initCfg P0) tr = some Cs0; decide, by decide, by
      intro C hC
      have hall : (Cs0.all fun C => Reference.Explore.inBoundsBool P0 B C) = true := by decide
      exact (Reference.Explore.inBoundsBool_iff (P := P0) (B := B) (C := C)).mp
        (List.all_eq_true.mp hall C hC)⟩

/-! ### 4. Non-vacuity on the CNF side -/

set_option maxRecDepth 20000 in
/-- **The violation clause of the non-vacuous model is not the empty disjunction.** Contrast
`AuthGap.why_the_formula_is_unsat`, where the agreement model's secrecy clause was empty and its UNSAT
meant nothing: here the encoding really does ask whether the register that held the declared secret
ever holds a known message, at every one of the five time points. -/
theorem violationLits_nonempty : violationLits (shapeOf P B) P ≠ [] := by decide

/-- Every violation literal of this model is a positive literal of the store-leak auxiliary block:
with no closed secret declared, `closedLeakLits` contributes nothing and the clause is exactly the
register question. -/
theorem violationLits_in_store_block :
    (violationLits (shapeOf P B) P).all (fun l => ! l.neg && bsAu (shapeOf P B) ≤ l.var) = true := by
  decide

set_option maxRecDepth 20000 in
/-- And the generated CNF contains no empty clause: the solver was not handed the answer for free,
which is the test `AuthGap` uses to tell a real UNSAT from a vacuous one. -/
theorem no_empty_clause : ([] : List Lit) ∉ (Encode.encode P B).clauses := by decide

/-- **The vacuous model's clause is empty**, by the general theorem: the CNF cannot even state the
secrecy question for it, which is the loud case. -/
theorem violationLits_nil_P0 : violationLits (shapeOf P0 B) P0 = [] :=
  violationLits_nil_of_secrets_nil P0_secrets

theorem empty_clause_P0 : ([] : List Lit) ∈ (Encode.encode P0 B).clauses :=
  empty_clause_of_secrets_nil P0_secrets

/-- The four events really are a run of the *old* operational semantics too - the one the CNF
correspondence is proved against. The same protocol record is expressible in both semantics, and the
certificate checker verifies every transition. -/
def cert : Certificate :=
  { init := ProtSat.initCfg P,
    steps := [{ ev := ProtSat.Ev.act 0 (Term.agent 0) 0,
                after := ProtSat.succStore (ProtSat.initCfg P) 0 0 v },
              { ev := ProtSat.Ev.act 0 (Term.agent 0) 0,
                after := ProtSat.succAdvance (ProtSat.succStore (ProtSat.initCfg P) 0 0 v) 0 },
              { ev := ProtSat.Ev.act 0 (Term.agent 0) 0,
                after := ProtSat.succStore
                  (ProtSat.succAdvance (ProtSat.succStore (ProtSat.initCfg P) 0 0 v) 0) 0 0 w },
              { ev := ProtSat.Ev.act 0 (Term.agent 0) 0,
                after := ProtSat.succSend
                  (ProtSat.succStore (ProtSat.succAdvance
                    (ProtSat.succStore (ProtSat.initCfg P) 0 0 v) 0) 0 0 w) 0 v }] }

/-- The old-semantics step checker accepts the same four events. -/
theorem old_steps : checkSteps P (ProtSat.initCfg P) cert.steps = true := by decide

/-- Hence it is a run of the operational semantics. -/
theorem old_runs : Runs P (ProtSat.initCfg P) (certTrace cert) (certCfgs cert) :=
  checkSteps_runs P cert.steps (ProtSat.initCfg P) old_steps

/-- And a bounded one: four events, every configuration inside the universe. -/
theorem old_bounded : BoundedTrace P B (certTrace cert) (certCfgs cert) :=
  ⟨old_runs, by decide, by
    intro C hC
    have hall : (certCfgs cert).all (fun C => cfgInUniverse C (univ P B)) = true := by decide
    exact List.all_eq_true.mp hall C hC⟩

/-- **The old leak predicate does not fire.** The attacker knows `sk(0)` at the end of the run, but
the register the declaration names holds `K(0,0)` and there is no closed secret, so `runsLeaks` - the
predicate `Violation P Goal.secrecy` unfolds to, and the predicate the CNF's violation clause is
proved against - is false for this execution. -/
theorem old_no_leak : runsLeaksBool P (certCfgs cert) = false := by decide

/-- **The leak is the obligation's, not the register's.** At the final configuration the obligation
names `sk(0)`, the attacker knows `sk(0)`, the register the declaration names holds `K(0,0)`, and
that is what the CNF-readable part of the secret set contains. So the two routes are not merely
differently worded: they read different parts of the same configuration. -/
theorem the_leak_is_the_obligation :
    (Reference.Gates.nthCfg P tr 4).oblig = [v] ∧ v ∈ (Reference.Gates.nthCfg P tr 4).kn ∧
      Reference.storeSecretTerms P (Reference.Gates.nthCfg P tr 4) = [w] ∧
      readVar 0 (Reference.storeOf (Reference.Gates.nthCfg P tr 4) 0) ≠ some v := by decide

theorem old_no_leak' : ¬ runsLeaks P (certCfgs cert) := fun h =>
  absurd ((runsLeaksBool_iff P (certCfgs cert)).mpr h) (by simp [old_no_leak])

/-- The two semantics, same protocol, same four events, opposite answers about the same execution:
the repaired one leaks, the one the CNF reads does not. -/
theorem two_semantics_one_run :
    BoundedTrace P B (certTrace cert) (certCfgs cert) ∧ ¬ runsLeaks P (certCfgs cert) ∧
      Reference.Explore.BoundedRun P B tr Cs ∧ Reference.traceLeaks P Cs :=
  ⟨old_bounded, old_no_leak', honest_bounded, leaks⟩

/-! ### 5. The CNF route says SAFE -/

/-- The bounds name the protocol's closed expressions. -/
theorem hU : univClosed (shapeOf P B) P := by
  unfold univClosed
  decide

theorem hU0 : univClosed (shapeOf P0 B) P0 := by
  unfold univClosed
  decide

/-- The declared store secret has a slot in the shape's store stride. -/
theorem hsec : SecretsOKStore (shapeOf P B) P := by
  intro q' x h
  have h2 : Secret.store q' x = Secret.store 0 0 := by simpa [P] using h
  cases h2
  decide

theorem hsec0 : SecretsOKStore (shapeOf P0 B) P0 := by
  intro q' x h
  exact absurd h (by simp [P0])

/-- No representability gap: every value the protocol can compute is named by the universe, so the
bridge needs no hypothesis about the executions. -/
theorem gapFree : domainGap P B = false := by decide
theorem gapFree0 : domainGap P0 B = false := by decide

/-- **The formula fact for the vacuous model**, with no solver anywhere: the violation clause is the
empty disjunction, so the CNF has no model. -/
theorem cnf_unsat0 : ProtSat.Unsat (Encode.encode P0 B) := unsat_of_secrets_nil P0_secrets

/-- **`safe_for_secrecy0`.** The CNF route, run on the vacuous model and these bounds, yields a
bounded security theorem: no execution the model permits within these sessions, this universe and
this four-event bound violates the selected goal. Read it together with `violationLits_nil_P0`: the
derivation is genuine and the evidence behind it is an empty clause. -/
theorem safe_for_secrecy0 : boundedSafeGoals q0 :=
  Correspondence.boundedSafe_of_unsat_gapFree gapFree0 hU0 hsec0 cnf_unsat0

/-- The analyser's own answer for that query. -/
theorem cnf_answer0 : analyze P0 B = Verdict.encodingUnsat := by
  have hnone : DPLL.dpll (Encode.encode P0 B) = none :=
    (dpll_none_iff_unsat _).mpr cnf_unsat0
  have hu : univClosedBool (shapeOf P0 B) P0 = true := (univClosedBool_iff _ _).mpr hU0
  rw [Analyzer.analyze]
  simp [hu, hnone]

theorem q0_goals_ne : q0.goals.isEmpty = false := by decide

theorem q0_unsupported : (unsupported q0).isEmpty = true := by
  simp [q0, unsupported, goalEncoded, encodedGoals]

/-- The contract's answer for the vacuous query. -/
theorem cnf_answer_query0 : analyzeQuery q0 = Result.encodingUnsat := by
  rw [analyzeQuery, if_pos (by decide), if_neg (by decide), if_neg (by simp [q0_unsupported])]
  show liftVerdict (analyze P0 B) = Result.encodingUnsat
  rw [cnf_answer0]
  rfl

/-- And the contract does not call that answer a security verdict. -/
theorem cnf_answer_is_not_security0 : securityResult (analyzeQuery q0) = false := by
  rw [cnf_answer_query0]
  simp [securityResult]

/-! ### 6. The repaired contract says ATTACK -/

/-- **`attacked_for_secrecy0`.** The vacuous model, read by the repaired contract, has a bounded attack
on the very same query: the honest execution is a permitted execution of the query's model within the
query's bounds, and it leaks through the obligation. -/
theorem attacked_for_secrecy0 : Reference.Contract.boundedAttack q0 :=
  ⟨Goal.secrecy, by decide, tr, Cs0, honest_bounded0, leaks0⟩

/-- **`attacked_for_secrecy`.** The same for the non-vacuous model - the register declaration does not
save it. -/
theorem attacked_for_secrecy : Reference.Contract.boundedAttack q :=
  ⟨Goal.secrecy, by decide, tr, Cs, honest_bounded, leaks⟩

/-- The non-vacuous attack from the executable side: the pruned explorer enumerates the repaired
semantics, finds a violating execution, and `Prune.attackFoundP_imp` plus
`Contract.boundedAttack_of_attackFound` turn the answer into the proposition. No witness is
hand-carried here. -/
theorem attacked_for_secrecy_decided : Reference.Contract.boundedAttack q :=
  Reference.Contract.boundedAttack_of_attackFound (Prune.attackFoundP_imp (by decide))

/-- The vacuous attack, likewise decided by the pruned explorer. -/
theorem attacked_for_secrecy0_decided : Reference.Contract.boundedAttack q0 :=
  Reference.Contract.boundedAttack_of_attackFound (Prune.attackFoundP_imp (by decide))

theorem not_contract_safe0 : ¬ Reference.Contract.boundedSafe q0 :=
  fun h => h attacked_for_secrecy0

theorem not_contract_safe : ¬ Reference.Contract.boundedSafe q :=
  fun h => h attacked_for_secrecy

/-! ### 7. The headline -/

/-- **`snapshot_gap_is_real`.** Same protocol, same bounds, same selected goal: the CNF route proves
the query safe and the repaired contract finds a bounded attack on it. A `boundedSafeGoals` answer
for a `[Goal.secrecy]` query on a model that declares its secret by `Action.secret` and then
overwrites the register means "no register-named secret leaked", while the repaired contract says the
value leaked. This is the same class of defect `AuthGap.auth_gap_is_real` establishes for agreement -
SAFE while an attack is permitted - in a place nobody had looked. -/
theorem snapshot_gap_is_real :
    boundedSafeGoals q0 ∧ Reference.Contract.boundedAttack q0 :=
  ⟨safe_for_secrecy0, attacked_for_secrecy0⟩

/-- Safe for one semantics, attacked for the other, stated as a disagreement about safety. -/
theorem safe_here_unsafe_there :
    boundedSafeGoals q0 ∧ ¬ Reference.Contract.boundedSafe q0 :=
  ⟨safe_for_secrecy0, not_contract_safe0⟩

/-- What the tool prints, what the bridge proves, and what the contract proves, about one query. -/
theorem the_tool_says_safe :
    analyzeQuery q0 = Result.encodingUnsat ∧ boundedSafeGoals q0 ∧
      Reference.Contract.boundedAttack q0 :=
  ⟨cnf_answer_query0, safe_for_secrecy0, attacked_for_secrecy0⟩

/-- **The semantics hypothesis is doing real work.** There is no theorem lifting a CNF-route safety
verdict to the repaired contract's safety: the universal statement is false, and this query is the
counterexample. Compare `AuthGap.goal_hypothesis_is_needed`, which makes the analogous point for the
*goal-selection* hypothesis of `CheckedSafe.boundedSafeGoals_of_secrecy`. -/
theorem reference_semantics_hypothesis_is_needed :
    ¬ ( ∀ q : Query, boundedSafeGoals q → Reference.Contract.boundedSafe q) := by
  intro hall
  exact not_contract_safe0 (hall q0 safe_for_secrecy0)

/-- The witness form: a query that is safe for the CNF route and attacked for the contract, exhibited
rather than negated. -/
theorem reference_semantics_hypothesis_is_needed_witness :
    ∃ q : Query, boundedSafeGoals q ∧ Reference.Contract.boundedAttack q :=
  ⟨q0, safe_for_secrecy0, attacked_for_secrecy0⟩

/-! ### 8. The non-vacuous model, and what the kernel cannot afford -/

/-- **The formula fact for the non-vacuous model, as a hypothesis.** `Encode.encode P B` has no model
- the analyser says so at run time, and `DPLL.dpll` returns `none` when it is run - but this file does
not replay the search inside the kernel, because the replay does not finish in the budget a build can
carry. `cnf_unsat_cost` records the measurement. Everything the safety statement needs *besides* the
formula fact is decided in this file: `gapFree`, `hU`, `hsec`, `violationLits_nonempty`,
`no_empty_clause`. -/
theorem safe_for_secrecy_of_unsat (h : ProtSat.Unsat (Encode.encode P B)) : boundedSafeGoals q :=
  Correspondence.boundedSafe_of_unsat_gapFree gapFree hU hsec h

/-- The gap on the non-vacuous model, conditional on the same formula fact: the CNF route's safety
theorem and the contract's attack on one query whose violation clause is *not* empty. -/
theorem snapshot_gap_is_real_nonvacuous_of_unsat (h : ProtSat.Unsat (Encode.encode P B)) :
    boundedSafeGoals q ∧ Reference.Contract.boundedAttack q :=
  ⟨safe_for_secrecy_of_unsat h, attacked_for_secrecy⟩

/-! **The measurement.** At these bounds `Encode.encode P B` has 961 variables and 1261 clauses. The kernel replay of
`DPLL.dpll (Encode.encode P B) = none` was started twice and abandoned: 43 minutes on this model, and
20 minutes on the variant whose `secret` action reads the register (1242 variables, 1705 clauses). For
scale, `AuthGap.dpll_none2` costs about a minute at 410 variables and `EndToEnd.qg` about 20 seconds
at 246. The snapshot gap is inherently more expensive to witness than the agreement gap: the leak
needs four events - load, declare, overwrite, publish - and every event multiplies the encoding, while
`AuthGap`'s non-vacuous witness fitted in one. The consequence for the roadmap is that the fix (an
obligation variable block) must ship with an evidence format, because a four-event instance is already
past the point where replaying the solver is affordable. -/

/-! ### 9. The audit's own model -/

/-- The model the repair was written against (`Reference.Gates.snapshotP`): generate a nonce, declare it
secret, hide it in a pair, overwrite the register, publish the pair, and the attacker projects the
nonce out of it. -/
abbrev snapshotP : Protocol := Reference.Gates.snapshotP

/-- Its `secrets` list is empty: the only secrecy declaration in the model is the `Action.secret` in
the role. -/
theorem snapshotP_no_secrets : snapshotP.secrets = [] := rfl

/-- So the CNF cannot state the secrecy question for it at any bound: the violation clause is the
empty disjunction. -/
theorem snapshot_violationLits_empty (Bnd : Bounds) :
    violationLits (shapeOf snapshotP Bnd) snapshotP = [] :=
  violationLits_nil_of_secrets_nil snapshotP_no_secrets

/-- And the CNF is unsatisfiable for it at any bound, so the CNF route would answer "safe" to any
secrecy question about it, whatever the role does with its obligations. -/
theorem snapshot_unsat (Bnd : Bounds) : ProtSat.Unsat (Encode.encode snapshotP Bnd) :=
  unsat_of_secrets_nil snapshotP_no_secrets

/-- The repair's own witness leaks: `Reference.Gates.snapshot_leaks`, re-stated as a proposition
rather than a Boolean. Read this together with section 9's other theorems and *not* as a
`Contract.boundedAttack` for `snapshotP`: that model publishes a pair, so its honest execution is
inside `Explore.inBounds` only once `Bounds.rounds` is raised to 1, and the CNF at that bound is far
past anything the kernel could replay. The point made here is the sharper one - the CNF has no
secrecy question to answer for `snapshotP` at *any* bound, while the repaired semantics finds the leak
at the bound the gate itself uses. -/
theorem snapshot_leaks' :
    Reference.traceLeaks snapshotP
      (Reference.Gates.visit snapshotP Reference.Gates.snapshotTrace) :=
  (Reference.traceLeaksBool_iff snapshotP _).mp Reference.Gates.snapshot_leaks

end ProtSat.SnapshotGap
