/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.SnapshotGap
import ProtSat.EndToEnd
import ProtSat.Benchmarks
import ProtSat.AgreementPredicates

/-!
# ProtSat/SecrecyGuard.lean - a gate on the CNF route's secrecy verdict

## What this file does

`ProtSat/SnapshotGap.lean` proves, with kernel evidence, that the CNF route can answer SAFE to a
secrecy query whose model declares its secret by `ProtSat.Action.secret`: the constructor generates
no clauses (`actionClauses_secret`), the secrecy violation clause is built entirely from
`P.secrets` (`violationLits_shapes`), and a model with `P.secrets = []` gets the empty clause into
`Encode.encode P B` at every bound (`unsat_of_secrets_nil`). The driver therefore emits
`boundedSafeGoals q0` for a query the repaired contract proves attacked.

The real repair is an obligation-variable block plus a third violation family, and it is blocked on a
design decision about `Operational.Leak`. This file does the cheap thing that is possible today: it
states, and proves, a **guard** that makes the driver unable to emit that verdict.

* `secrecyObligationVisible (q : Query) : Bool` is decidable and purely syntactic: it reads the
  query's `Protocol`, never the encoding. It is true exactly when the CNF route's secrecy violation
  clause has a literal for every secret the model declares - every `Action.secret e` performed by an
  instantiated session must name a value that `P.secrets` also names, either as a `Secret.closed`
  with the same value or, when the action declares a register (`e = Expr.var x`), as the declaration
  `Secret.store q x`. A query that selects no secrecy goal passes trivially.
* `uncoveredSecretActions P` is the same test as a list of `(session, pc, expression)` triples, so a
  refusal can name what it refused instead of swallowing it.
* Sections 2 and 3 are the meaning theorems. `not_visible_of_secrets_nil`: any model that performs
  `Action.secret` and declares no `Secret` fails the guard. `mem_closedLeakLits_of_declared` and
  `storeLeakLitsAt_nil_of_undeclared`: the two families really are generated from the declarations, so
  acceptance is justified and refusal is not arbitrary. `vacuous_of_secrets_nil`: the connection the
  task asks for - for such a model the empty clause is in the CNF, `violationLits` is the empty
  disjunction, `Unsat` follows with no solver, and the guard is false; so the UNSAT the safety bridge
  consumes is a fact about an empty disjunction, not evidence. `guard_false_unsat_at_every_bound`
  sharpens that: the answer does not even depend on the bounds.
* Section 4 is the decided witness: `guard_false_q0` (proved structurally, not merely evaluated),
  `guard_fires_where_the_tool_was_wrong` - guard false on `SnapshotGap.q0` *while*
  `boundedSafeGoals q0` and `Reference.Contract.boundedAttack q0` both hold - and the same pair for
  the non-vacuous `SnapshotGap.q`, whose violation clause is *not* empty and which the guard still
  refuses.
* Section 5 decides the guard against the secrecy-selecting queries the repository names - the three
  `EndToEnd` queries, `AuthGap.qs`/`qa`, `Regressions.Authentication.q`, `Regressions.Bounds.q`, the
  `Reference.Contract.Gates` queries, `AgreementPredicates.injQ`, all eight `Benchmarks` queries, and
  both `SnapshotGap` queries - plus two models that use `Action.secret` *and* declare the value,
  which the guard accepts, and one that declares a store secret but names a compound value, which it
  refuses. `GoalCompose.mixQ` is not in the list because that module imports the driver this
  file guards, and deciding it here would cycle. Its model `mixP` declares `Secret.closed` and
  performs no `Action.secret`, so the guard passes it - by inspection of that definition, not by a
  decided theorem in this file.

## What this file does NOT do

* It does **not** make the CNF route prove declared-value secrecy. A model that passes the guard still
  gets a verdict about the secrets `P.secrets` names, read at the indexed step. The guard only refuses
  when the model declares something the clause cannot name at all: it is a gate on what the driver may
  conclude, not a repair of what the encoding can express.
* It does **not** reject every vacuous SAFE. A model that declares no secret at all and asks a secrecy
  question (`AuthGap.qs`, i.e. `Regressions.Authentication.P`) passes the guard: nothing is declared,
  so nothing is unnamed. That vacuity is `AuthGap.why_the_formula_is_unsat`'s subject, it is a
  different defect, and refusing it would break the existing `qs_driver_safe` gate - which would be
  the guard neutering the tool rather than guarding it.
* It does **not** catch the *timing* half of the snapshot gap. A model that declares
  `Secret.store q x`, performs `Action.secret (Expr.var x)` and then overwrites `x` before publishing
  the value passes the guard, because the clause does name that register - but it names it *at the step
  the literal is indexed by*, not *from the step of the declaration*, so the obligation can still be
  missed. Only the obligation-variable block fixes that.
* It does **not** change the encoding, the semantics or the query vocabulary. Nothing here touches
  `Clauses.lean`, `Encode.lean`, `Complete.lean`, `Operational.lean`, `Reference.lean` or
  `Query.lean`. In particular it cannot add a `Diagnostic` constructor, which is why the driver's
  refusal is `Result.unsupportedGoals [Goal.secrecy]` and not `Result.invalidModel`; see
  `ProtSat/GoalAnalyze.lean` section 4.
* It does **not** make `SnapshotGap`'s theorems false. `boundedSafeGoals q0` remains provable, and
  correct relative to the leak predicate it was proved against. What the guard stops is the *driver* -
  the thing that prints an answer - from promoting solver evidence to that verdict for a model whose
  secrets it cannot see.
* It is a **stopgap and it is meant to be deleted**. The day the obligation-variable block lands - a
  `vobl` family, a third secrecy violation family reading it, `Complete.sat_violation` and
  `Complete.violation_leak` re-proved, and `Operational.Leak` or `boundedSafeGoals` grown to carry the
  obligation - the clause names action-declared secrets directly, every model here passes, and both
  this file and the branch of `driverGate` that reads it should be removed. `SnapshotGap.q0` is the
  regression test to re-run at that moment: it should stop being a refusal and become a real answer.

Nothing here runs a solver. Every `by decide` is a list walk over a protocol record or a small Boolean
evaluation.
-/

namespace ProtSat.SecrecyGuard

open ProtSat Term Protocol Bounded Encode Encoding Complete Analyzer Query BoundedExec Represent
  CheckedSafe Correspondence

/-! ### 1. The test -/

/-- **The `secret` occurrences of the instantiated sessions**: one triple `(session, program
counter, expression)` for every `Action.secret` the model performs. Sessions the model does not
instantiate are not walked: `Protocol.actionAt` is `none` for them everywhere, so they declare
nothing. The enumeration is the one `Query.authEvents` uses for `claim` and `commit`. -/
def secretActionOccurrences (P : Protocol) : List (Nat × Nat × Expr) :=
  (List.range P.sessions.length).flatMap fun qq =>
    (List.range (P.roleLen qq)).flatMap fun pc =>
      match P.actionAt qq pc with
      | some (Action.secret e) => [(qq, pc, e)]
      | _ => []

/-- Does the CNF's secrecy vocabulary have a literal for the value this `Action.secret e` declares?

The violation clause is `closedLeakLits ++ storeLeakLits` and both families are generated from
`P.secrets` alone: the first emits "the attacker knows `t` at step `i`" for `t` ranging over
`P.closedSecretTerms`, the second emits the store-leak auxiliary for session `qq`'s register `x` only
when `qq` is instantiated and `Secret.store qq x ∈ P.secrets` (`Encode.storeSecret`). So the value an action names is in the clause's vocabulary in
exactly two situations:

* `e` is closed and its value is a declared closed secret - the closed family then reads that value at
  every step, which is what an obligation needs;
* `e` is the register `x` of the session performing the action and `Secret.store q x` is declared -
  the clause then reads that register at every step (at a step, not *from* the step of the
  declaration: see "What this file does NOT do").

Anything else - a store-dependent compound expression, or a register nobody declared - has no literal
anywhere in the clause. -/
def secretActionNamed (P : Protocol) (qq : Nat) (e : Expr) : Bool :=
  match Expr.eval e [] with
  | some t => t ∈ P.closedSecretTerms
  | none => match e with
            | Expr.var x => Secret.store qq x ∈ P.secrets
            | _ => false

/-- The occurrences the clause cannot name: the guard's diagnostic payload, so a refusal can print
which action its author has to declare rather than refusing silently. -/
def uncoveredSecretActions (P : Protocol) : List (Nat × Nat × Expr) :=
  (secretActionOccurrences P).filter fun o => ! secretActionNamed P o.1 o.2.2

/-- **The protocol half of the guard**: every secret the model declares by an action is a secret the
CNF's violation clause can name. -/
def actionSecretsNamed (P : Protocol) : Bool := (uncoveredSecretActions P).isEmpty

/-- **The guard.** A query that does not select `Goal.secrecy` passes: the defect lives in the secrecy
violation clause, and an agreement-only query never reads it. A query that does select it passes
exactly when the model's action-declared secrets are all named by `P.secrets`. -/
def secrecyObligationVisible (q : Query) : Bool :=
  ! q.goals.elem Goal.secrecy || actionSecretsNamed q.protocol

/-- The guard is a statement about the model, not about the bounds: the same protocol with the same
goal list passes or fails identically at any bound. -/
theorem secrecyObligationVisible_bounds_irrelevant {P : Protocol} {B B' : Bounds} {gs : List Goal} :
    secrecyObligationVisible (Query.mk P B gs) = secrecyObligationVisible (Query.mk P B' gs) := rfl

/-- A query that selects no secrecy goal passes, whatever its model does. -/
theorem visible_of_no_secrecy_goal {P : Protocol} {B : Bounds} {gs : List Goal}
    (h : Goal.secrecy ∉ gs) : secrecyObligationVisible (Query.mk P B gs) = true := by
  unfold secrecyObligationVisible
  rw [show gs.elem Goal.secrecy = false from by simpa using h]
  simp

/-! ### 2. When the guard fires -/

private theorem lt_length_of_rget_some {alpha : Type} {l : List alpha} {i : Nat} {a : alpha}
    (h : rget l i = some a) : i < l.length := by
  cases l with
  | nil => cases i <;> simp [rget] at h
  | cons x xs =>
      cases i with
      | zero => simp
      | succ i =>
          simp [rget] at h
          exact Nat.succ_lt_succ (lt_length_of_rget_some h)

/-- `valAt` is `rget` on the universe, so a slot that names a value is in range. -/
theorem lt_length_of_valAt_some {sh : Shape} {u : Nat} {t : Term} (h : valAt sh u = some t) :
    u < sh.U.length := lt_length_of_rget_some h

/-- An `Action.secret` at an instantiated session and a real program counter is an occurrence. -/
theorem mem_secretActionOccurrences {P : Protocol} {qq pc : Nat} {e : Expr}
    (hqq : qq < P.sessions.length) (hpc : pc < P.roleLen qq)
    (h : P.actionAt qq pc = some (Action.secret e)) : (qq, pc, e) ∈ secretActionOccurrences P := by
  unfold secretActionOccurrences
  rw [List.mem_flatMap]
  refine ⟨qq, List.mem_range.mpr hqq, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨pc, List.mem_range.mpr hpc, ?_⟩
  rw [h]
  simp

/-- With no declaration at all, nothing an action declares is named: both halves of
`secretActionNamed` ask about `P.secrets`, and `P.closedSecretTerms` is a `filterMap` over it. -/
theorem secretActionNamed_false_of_secrets_nil {P : Protocol} (h : P.secrets = [])
    (qq : Nat) (e : Expr) : secretActionNamed P qq e = false := by
  have hc : P.closedSecretTerms = [] := SnapshotGap.closedSecretTerms_nil h
  unfold secretActionNamed
  rw [hc, h]
  cases hval : Expr.eval e [] with
  | some _t => simp
  | none => cases e with
            | var _x => simp
            | _ => simp

/-- So every occurrence of such a model is uncovered. -/
theorem mem_uncovered_of_secrets_nil {P : Protocol} (h : P.secrets = [])
    {o : Nat × Nat × Expr} (ho : o ∈ secretActionOccurrences P) : o ∈ uncoveredSecretActions P := by
  unfold uncoveredSecretActions
  rw [List.mem_filter]
  exact ⟨ho, by simpa using secretActionNamed_false_of_secrets_nil h o.1 o.2.2⟩

/-- One uncovered occurrence is enough to fail the protocol half of the guard. -/
theorem actionSecretsNamed_false_of_mem {P : Protocol} {o : Nat × Nat × Expr}
    (ho : o ∈ uncoveredSecretActions P) : actionSecretsNamed P = false := by
  unfold actionSecretsNamed
  cases h2 : uncoveredSecretActions P with
  | nil => rw [h2] at ho; exact absurd ho (by simp)
  | cons _ _ => simp

/-- **The guard fires on the whole class.** A model that performs `Action.secret` anywhere in an
instantiated role and declares no `Secret` at all fails the guard. This is `SnapshotGap.P0`, it is
`Reference.Gates.snapshotP`, and it is every Needham-Schroeder model in `ProtSat/Benchmarks.lean`. -/
theorem not_actionSecretsNamed_of_secrets_nil {P : Protocol} (h : P.secrets = [])
    (hu : (secretActionOccurrences P).isEmpty = false) : actionSecretsNamed P = false := by
  cases occ : secretActionOccurrences P with
  | nil => exact absurd hu (by rw [occ]; decide)
  | cons o rest =>
      have ho : o ∈ secretActionOccurrences P := by rw [occ]; exact List.Mem.head rest
      exact actionSecretsNamed_false_of_mem (mem_uncovered_of_secrets_nil h ho)

/-- **`not_visible_of_secrets_nil`.** The same for the query-level guard: the class of models
`SnapshotGap` exhibits is refused, at every bound, by a theorem rather than by evaluation. -/
theorem not_visible_of_secrets_nil {P : Protocol} {B : Bounds} {gs : List Goal}
    (h : P.secrets = []) (hu : (secretActionOccurrences P).isEmpty = false)
    (hgoal : Goal.secrecy ∈ gs) : secrecyObligationVisible (Query.mk P B gs) = false := by
  have hmem : (Query.mk P B gs).goals.elem Goal.secrecy = true := by simpa using hgoal
  have hthis := not_actionSecretsNamed_of_secrets_nil h hu
  unfold secrecyObligationVisible
  rw [hmem]
  simpa using hthis

/-- The guard fires on any goal list that selects secrecy alongside something else: refusing the
query is not an artefact of the driver's secrecy-only safety bridge. -/
theorem not_visible_of_secrets_nil' {P : Protocol} {B : Bounds} {gs : List Goal}
    (h : P.secrets = []) (hu : (secretActionOccurrences P).isEmpty = false) :
    secrecyObligationVisible (Query.mk P B (Goal.secrecy :: gs)) = false :=
  not_visible_of_secrets_nil h hu (List.Mem.head _)

/-! ### 3. What the clause can name, and what it cannot -/

/-- **Acceptance is justified, closed half.** If the action's value is a declared closed secret and
the universe names it at slot `u`, then the clause contains "the attacker knows it at step `i`" - at
every step, which is what an obligation needs. The guard does not refuse a model the encoding can
speak about. -/
theorem mem_closedLeakLits_of_declared {sh : Shape} {P : Protocol} {i u : Nat} {t : Term}
    (hval : valAt sh u = some t) (hmem : t ∈ P.closedSecretTerms) :
    pos (vkn sh i u) ∈ closedLeakLits sh P i := by
  unfold closedLeakLits
  refine List.mem_filterMap.mpr ⟨u, List.mem_range.mpr (lt_length_of_valAt_some hval), ?_⟩
  simp [hval, hmem]

/-- **Refusal is justified, store half.** If nobody declared session `q`'s register `x`, the store
family contributes nothing for that pair at all, at any step. -/
theorem storeLeakLitsAt_nil_of_undeclared {sh : Shape} {P : Protocol} {i q x : Nat}
    (h : Secret.store q x ∉ P.secrets) : storeLeakLitsAt sh P i q x = [] := by
  unfold storeLeakLitsAt storeSecret
  simp [h]

/-- And the store family does name a declared register: the positive counterpart, so the guard's
acceptance of the `Secret.store` case is not a concession either. -/
theorem mem_storeLeakLits_of_declared {sh : Shape} {P : Protocol} {i q x u : Nat}
    (hn : q < sh.nS1) (hx : x < shV sh) (h : Secret.store q x ∈ P.secrets)
    (hu : u < sh.U.length) : pos (vau sh i q x u) ∈ storeLeakLits sh P i := by
  unfold storeLeakLits litsSess litsVar
  refine List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (by show q < sh.nS1 + 1; omega),
    List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩⟩
  unfold storeLeakLitsAt storeSecret
  split
  · exact List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩
  · rename_i hdec; exact absurd hdec (by simp [hn, h])

/-- An uncovered occurrence is exactly one the vocabulary does not name. -/
theorem not_secretActionNamed_of_mem_uncovered {P : Protocol} {o : Nat × Nat × Expr}
    (ho : o ∈ uncoveredSecretActions P) : secretActionNamed P o.1 o.2.2 = false := by
  rw [uncoveredSecretActions, List.mem_filter] at ho
  have h2 : ! secretActionNamed P o.1 o.2.2 = true := by simpa using ho.2
  have hall : ∀ b : Bool, !b = true → b = false := by
    intro b
    cases b <;> intro hb <;> simp_all
  exact hall _ h2

/-- **The meaning of an uncovered occurrence, closed case.** If `(qq, pc, e)` is uncovered and `e`
evaluates to `t`, then `t` is not a declared closed secret: the value the action declares is outside
the only source the closed family reads, so no step of that family has a literal for it. -/
theorem not_closed_of_uncovered {P : Protocol} {qq pc : Nat} {e : Expr} {t : Term}
    (ho : (qq, pc, e) ∈ uncoveredSecretActions P) (he : Expr.eval e [] = some t) :
    t ∉ P.closedSecretTerms := by
  have hnamed : secretActionNamed P qq e = decide (t ∈ P.closedSecretTerms) := by
    unfold secretActionNamed
    rw [he]
  have hnot := not_secretActionNamed_of_mem_uncovered (o := (qq, pc, e)) ho
  rw [hnamed] at hnot
  simpa using hnot

/-- And if the uncovered occurrence reads a register, that register is undeclared - so the store
family contributes nothing for that pair, at any step. -/
theorem not_store_of_uncovered {P : Protocol} {qq pc x : Nat}
    (ho : (qq, pc, Expr.var x) ∈ uncoveredSecretActions P) : Secret.store qq x ∉ P.secrets := by
  have hnamed : secretActionNamed P qq (Expr.var x) = decide (Secret.store qq x ∈ P.secrets) := by
    unfold secretActionNamed
    rw [show Expr.eval (Expr.var x) [] = none from rfl]
  have hnot := not_secretActionNamed_of_mem_uncovered (o := (qq, pc, Expr.var x)) ho
  rw [hnamed] at hnot
  simpa using hnot

/-- **The vacuity link.** For a model that declares its secret by an action and nothing else: the
empty clause is literally in the generated CNF, the secrecy violation clause is the empty
disjunction, the CNF is unsatisfiable with no solver anywhere, and the guard is false. Read this as
the reason the driver must not promote a refutation of that formula to a security verdict: the
`Unsat` it would consume is a fact about an empty disjunction. -/
theorem vacuous_of_secrets_nil {P : Protocol} {B : Bounds} (h : P.secrets = [])
    (hu : (secretActionOccurrences P).isEmpty = false) :
    ProtSat.Unsat (Encode.encode P B) ∧ ([] : List Lit) ∈ (Encode.encode P B).clauses ∧
      violationLits (shapeOf P B) P = [] ∧
      secrecyObligationVisible (Query.mk P B [Goal.secrecy]) = false :=
  ⟨SnapshotGap.unsat_of_secrets_nil h, SnapshotGap.empty_clause_of_secrets_nil h,
    SnapshotGap.violationLits_nil_of_secrets_nil h,
    not_visible_of_secrets_nil h hu (by simp)⟩

/-- **The verdict does not depend on the bounds.** For this class of model, raising `Bounds.steps`
cannot make the UNSAT meaningful: it is a theorem for every bound, by the same empty clause. This is
the sharpest cheap form of "the UNSAT is vacuous rather than evidence" - the safety bridge's
hypothesis is free, so it carries no information about the protocol at all. -/
theorem guard_false_unsat_at_every_bound {P : Protocol} (h : P.secrets = [])
    (hu : (secretActionOccurrences P).isEmpty = false) :
    ∀ B : Bounds, ProtSat.Unsat (Encode.encode P B) ∧
      secrecyObligationVisible (Query.mk P B [Goal.secrecy]) = false :=
  fun B => ⟨SnapshotGap.unsat_of_secrets_nil h, not_visible_of_secrets_nil h hu (by simp)⟩

/-! ### 4. The decided witnesses -/

/-- `SnapshotGap.P0` really does perform a `secret` action in its instantiated role. -/
theorem P0_uses_action_secret : (secretActionOccurrences SnapshotGap.P0).isEmpty = false := by
  decide

/-- **The guard fires on the vacuous model** - structurally, as an instance of
`not_visible_of_secrets_nil`, not merely as an evaluation. -/
theorem guard_false_q0 : secrecyObligationVisible SnapshotGap.q0 = false := by
  show secrecyObligationVisible (Query.mk SnapshotGap.P0 SnapshotGap.B [Goal.secrecy]) = false
  exact not_visible_of_secrets_nil SnapshotGap.P0_secrets P0_uses_action_secret (by simp)

/-- The same refusal, evaluated: the guard is a decidable test and the kernel checks it. -/
theorem guard_false_q0_decided : secrecyObligationVisible SnapshotGap.q0 = false := by decide

/-- **The guard fires on the audit's own model** (`Reference.Gates.snapshotP`), at the bound the
repair's gate uses. -/
theorem guard_false_snapshotP :
    secrecyObligationVisible
      (Query.mk Reference.Gates.snapshotP { steps := 6, rounds := 0 } [Goal.secrecy]) = false :=
  not_visible_of_secrets_nil SnapshotGap.snapshotP_no_secrets (by decide) (by simp)

/-- `SnapshotGap.P` also uses the action, and its single declaration does not name the value. -/
theorem P_uses_action_secret : (secretActionOccurrences SnapshotGap.P).isEmpty = false := by decide

/-- **The guard fires on the non-vacuous model too.** `SnapshotGap.P` declares
`Secret.store 0 0`, so its violation clause is *not* empty and its CNF has no empty clause
(`SnapshotGap.violationLits_nonempty`, `SnapshotGap.no_empty_clause`) - and the guard still refuses
it, because the obligation is about `sk(0)` and no declaration names `sk(0)`. The guard is therefore
not a detector for "the clause happens to be empty". -/
theorem guard_false_q : secrecyObligationVisible SnapshotGap.q = false := by decide

/-- **The guard fires exactly where the tool was wrong.** `SnapshotGap.snapshot_gap_is_real` proved
`boundedSafeGoals q0` and `Reference.Contract.boundedAttack q0` for one query. This is the same
query, with the guard's verdict added: the guard is false precisely where the CNF route's SAFE was
wrong - not before it, not after it, on it. -/
theorem guard_fires_where_the_tool_was_wrong :
    secrecyObligationVisible SnapshotGap.q0 = false ∧ boundedSafeGoals SnapshotGap.q0 ∧
      Reference.Contract.boundedAttack SnapshotGap.q0 :=
  ⟨guard_false_q0, SnapshotGap.safe_for_secrecy0, SnapshotGap.attacked_for_secrecy0⟩

/-- And on the non-vacuous model, where the safety side needs the formula fact as a hypothesis: the
guard refuses a query whose clause is nonempty and whose attack is decided. -/
theorem guard_fires_on_the_nonvacuous_model :
    secrecyObligationVisible SnapshotGap.q = false ∧
      violationLits (shapeOf SnapshotGap.P SnapshotGap.B) SnapshotGap.P ≠ [] ∧
      Reference.Contract.boundedAttack SnapshotGap.q :=
  ⟨guard_false_q, SnapshotGap.violationLits_nonempty, SnapshotGap.attacked_for_secrecy⟩

/-- The vacuity of `q0`, instantiated: the empty clause is in the CNF the driver would have asked the
solver about. -/
theorem q0_vacuous :
    ProtSat.Unsat (Encode.encode SnapshotGap.P0 SnapshotGap.B) ∧
      ([] : List Lit) ∈ (Encode.encode SnapshotGap.P0 SnapshotGap.B).clauses ∧
      violationLits (shapeOf SnapshotGap.P0 SnapshotGap.B) SnapshotGap.P0 = [] ∧
      secrecyObligationVisible SnapshotGap.q0 = false := by
  obtain ⟨a, b, c, d⟩ := vacuous_of_secrets_nil SnapshotGap.P0_secrets P0_uses_action_secret
  exact ⟨a, b, c, d⟩

/-! ### 5. Models the guard accepts, and models it refuses -/

/-- **A model that declares by action *and* declares the value.** The action names `K(0,1)` and
`Secret.closed (Expr.shrk 0 1)` names the same value, so the closed family reads it at every step and
the guard passes. This is the case that keeps the guard from being "no `Action.secret`, ever". -/
def coveredClosedP : Protocol :=
  { roles := [{ acts := [Action.secret (Expr.shrk 0 1), Action.send 0 (Expr.shrk 0 1)] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := [Secret.closed (Expr.shrk 0 1)]
    auths := [] }

/-- The closed case passes, decided. -/
theorem coveredClosed_visible :
    secrecyObligationVisible
      (Query.mk coveredClosedP { steps := 2, rounds := 0 } [Goal.secrecy]) = true := by decide

/-- **The register case.** `Explore.Gates.secureP` - generate a nonce, declare it secret, publish it
under a key the attacker lacks - with the one declaration the guard needs added: session 0's register 0
is a declared store secret, so the clause reads that register at every step. -/
def coveredStoreP : Protocol :=
  { roles := [{ acts := [Action.fresh 0 0, Action.secret (Expr.var 0),
                         Action.send 0 (Expr.encS (Expr.var 0) (Expr.shrk 0 1))] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := [7]
    compromised := []
    secrets := [Secret.store 0 0]
    auths := [] }

/-- The store case passes, decided - and the pass is justified by
`mem_storeLeakLits_of_declared`, not granted. -/
theorem coveredStore_visible :
    secrecyObligationVisible
      (Query.mk coveredStoreP { steps := 3, rounds := 0 } [Goal.secrecy]) = true := by decide

/-- **A declaration is not a free pass.** The action declares `fst (var 0)`: a store-dependent
compound that no `Secret` names, even though the model declares a store secret. The guard refuses it,
so the test is about the value the action names, not about `P.secrets` being nonempty. -/
def uncoveredCompoundP : Protocol :=
  { roles := [{ acts := [Action.recv 0 0, Action.secret (Expr.fst (Expr.var 0)),
                         Action.send 0 (Expr.fst (Expr.var 0))] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := [Secret.store 0 0]
    auths := [] }

/-- Refused, decided. -/
theorem uncoveredCompound_not_visible :
    secrecyObligationVisible
      (Query.mk uncoveredCompoundP { steps := 3, rounds := 0 } [Goal.secrecy]) = false := by decide

/- The rest of this section is the audit of the guard against the models the project already uses.
Each line is a `decide`; the list is what the task asks for: a guard that rejects everything would be
worse than no guard, and a guard that rejects nothing proves nothing. -/

/-- **`EndToEnd.qsafe` passes.** `Examples.KeyDisclosure.P` declares `Secret.closed (Expr.nonce 5)`
and its roles never use `Action.secret`. -/
theorem qsafe_visible : secrecyObligationVisible EndToEnd.qsafe = true := by decide

/-- **`EndToEnd.qg` passes** - the model behind the driver's existing safety gate
`qg_driver_safe`. `EndToEnd.Guard` declares `Secret.closed (Expr.shrk 0 0)` and performs no
`Action.secret`. -/
theorem qg_visible : secrecyObligationVisible EndToEnd.qg = true := by decide

/-- `EndToEnd.ql`, the leaky twin, likewise passes: the guard is not a filter that keeps only the
models it likes. -/
theorem ql_visible : secrecyObligationVisible EndToEnd.ql = true := by decide

/-- **`AuthGap.qs` passes** - the model behind `qs_driver_safe`. `Regressions.Authentication.P`
declares no secret and performs no `Action.secret`: its secrecy question is vacuous for a *different*
reason (nothing is declared), which this guard deliberately does not refuse. -/
theorem qs_visible : secrecyObligationVisible AuthGap.qs = true := by decide

/-- `AuthGap.qa` selects agreement only, so the guard does not apply to it and the existing
`authGap_driver_attack` gate is untouched. -/
theorem qa_visible : secrecyObligationVisible AuthGap.qa = true := by decide

/-- The same fact for the raw regression query. -/
theorem authentication_q_visible : secrecyObligationVisible Regressions.Authentication.q = true := by
  decide

/-- **`Regressions.Bounds.q` passes**: the transient-pair model, whose secrecy question is real (it
declares `Secret.closed (Expr.shrk 0 0)` and publishes it) and whose defect is representability,
not invisibility. The guard refuses nothing the clause can state. -/
theorem bounds_q_visible : secrecyObligationVisible Regressions.Bounds.q = true := by decide

/-- **`Reference.Contract.Gates.transientQ` passes**: the transient-pair model declares
`Secret.closed (Expr.shrk 0 0)` and uses no `Action.secret`. -/
theorem transientQ_visible : secrecyObligationVisible Reference.Contract.Gates.transientQ = true := by
  decide

/-- `Reference.Contract.Gates.authQ` and `AgreementPredicates.injQ` select no secrecy goal, so the
guard passes them: the agreement refusals the driver already implements are unchanged. -/
theorem authQ_visible : secrecyObligationVisible Reference.Contract.Gates.authQ = true := by decide

theorem injQ_visible : secrecyObligationVisible AgreementPredicates.injQ = true := by decide

/-- `Reference.Contract.ReviewGates.storeDeclaredQ` passes: `storeP` generates a nonce and declares
the register, with no `Action.secret` anywhere. -/
theorem storeDeclaredQ_visible :
    secrecyObligationVisible Reference.Contract.ReviewGates.storeDeclaredQ = true := by decide

/-- **The finding, stated rather than hidden: the guard refuses every secrecy-selecting query in
`ProtSat/Benchmarks.lean`.** Each of those models declares its secret by `Action.secret (Expr.var
1001)` in B's role and leaves `secrets := []`, so the CNF's violation clause has no literal for the
nonce B declares - which is exactly the vacuity `SnapshotGap` proves, and `SnapshotGap`'s own
conclusion about `Reference.Gates.snapshotP`. The refusal is therefore correct, not coarse. What it
costs: none of these queries is answered by the CNF driver anywhere in the repository - `Benchmarks`
and `Reference.Contract.Gates` route them through the deciding contract's explorer, which reads the
obligations and is untouched by this guard - so no existing gate changes its answer. -/
theorem NS2q_not_visible : secrecyObligationVisible Benchmarks.NS2q = false := by decide

theorem NSL2q_not_visible : secrecyObligationVisible Benchmarks.NSL2q = false := by decide

theorem NS2cq_not_visible : secrecyObligationVisible Benchmarks.NS2cq = false := by decide

theorem NSL2cq_not_visible : secrecyObligationVisible Benchmarks.NSL2cq = false := by decide

theorem NSL2cNoCheckQ_not_visible : secrecyObligationVisible Benchmarks.NSL2cNoCheckQ = false := by
  decide

theorem NSL2cqE_not_visible : secrecyObligationVisible Benchmarks.NSL2cqE = false := by decide

theorem NS2cqE_not_visible : secrecyObligationVisible Benchmarks.NS2cqE = false := by decide

theorem NSL2earlyQ_not_visible : secrecyObligationVisible Benchmarks.NSL2earlyQ = false := by decide

/-- **The same finding for the explorer's flagship model.** `Reference.Contract.Gates.secureQ` is
`Explore.Gates.secureP` - generate, declare by action, publish - with `secrets := []`. The deciding
contract proves it safe by exhaustion and keeps that verdict; the CNF route, which is what
`driverGate` fronts, cannot state its secrecy question at all (`SnapshotGap.snapshot_unsat` makes
the same point for `snapshotP`). `coveredStoreP` above is this model with the declaration added: that
is the guard's advice to its author. -/
theorem secureQ_not_visible : secrecyObligationVisible Reference.Contract.Gates.secureQ = false := by
  decide

/-- The explorer's own model, at its own bound, refused by the guard for the CNF route. -/
theorem secureP_not_visible :
    secrecyObligationVisible
      (Query.mk Reference.Explore.Gates.secureP Reference.Explore.Gates.secureB [Goal.secrecy]) = false :=
    by decide

/-- A malformed model is still refused - but for its own reason: the guard does not fire on it, so
`driverGate`'s `invalidModel` branch keeps its meaning. -/
theorem badQ_visible : secrecyObligationVisible Reference.Contract.Gates.badQ = true := by decide

/-- The guard is not constant: one query it passes and one it refuses, both exhibited. -/
theorem guard_is_not_constantly_true : ∃ q : Query, secrecyObligationVisible q = false :=
  ⟨SnapshotGap.q0, guard_false_q0_decided⟩

theorem guard_is_not_constantly_false : ∃ q : Query, secrecyObligationVisible q = true :=
  ⟨EndToEnd.qg, qg_visible⟩

end ProtSat.SecrecyGuard
