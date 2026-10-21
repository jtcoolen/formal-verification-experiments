/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.AgreesBase
import ProtSat.AnalyzerEvidence
import ProtSat.AgreementPredicates
import ProtSat.SecrecyGuard

/-!
# ProtSat: a goal-indexed analyser with checked evidence

`analyzeGoalsOfUsing q fuel cand code` runs the query validation and bounds checks, then searches
for a checked refutation or an accepted model of `formulaOfGoals q`. Optional candidate assignments
and serialized refutations are checked against that exact formula. The exported contract is:

* `attack_sound`: an attack answer witnesses `boundedAttackGoals q` and its certificate passes the
  independent checker;
* `boundedSafeGoals_of_boundedSafe`: an evidence-bearing safety answer proves `boundedSafeGoals q`;
* `unsat_of_encodingUnsat`: an unsatisfiability answer refutes `formulaOfGoals q`.

## The agreement monitor

`Query.Violation P Goal.agreement` is the unordered `AuthBreak` predicate, so this driver uses
`Matching.tripleOnly`. `GoalEncode.encodeGoalsOf` defaults to the different `orderAware` monitor;
using that default here would pair the formula with the wrong semantic conclusion. The decoded-run
and certificate bridges below use the semantic clause groups alone, without requiring a secrecy
violation in an agreement-only query.

## The answers

* `attack c`: a candidate model or DPLL model produces a selected-goal attack and an independently
  checkable certificate.
* `boundedSafe e`: a checked refutation, secrecy-only goals, and the decidable universe,
  store-secret and representability conditions construct safety evidence for this query.
* `encodingUnsat`: a checked refutation exists, but the driver's safety bridge does not apply.
  This driver remains conservative for agreement queries: it does not consume the separate
  agreement-completeness results.
* `unsupportedGoals`: injective agreement receives the front end's highest-priority refusal. The legacy
  `Query.Violation` for that goal is `True`, so interpreting it as an ordinary violation would call
  every such query attacked. `refuses_agreementInj` records the unconditional refusal.
* `unknown resourceExhausted`: the refutation producer reached no refutation at the supplied fuel
  and no model was returned. The fuel bounds the refutation producer only; DPLL still runs its
  total search and can be expensive.
* `unknown solverFailure`: the agreement annotations fail the decidable nameability condition of
  the decoded-run theorem. The existing answer type has no dedicated reason for this condition.
* `unsupportedGoals [Goal.secrecy]`: the **secrecy guard**. The query selects secrecy on a model that
  declares a secret by `Action.secret` without `P.secrets` naming that value, so the violation clause of
  the formula this driver would build has no literal for it (`ProtSat/SecrecyGuard.lean`). The refusal
  happens before any formula is built: the driver declines to answer rather than answer a question the
  encoding cannot state. See section 6.
* `invalidModel`, `noGoals`, `boundsTooSmall`: the corresponding front-end checks failed.

The mixed secrecy/agreement formula retains `GoalEncode`'s conjunction of violation demands.
It can find an execution violating both goals, but it can miss executions violating only one.
The driver never promotes a refutation of that stronger formula to a safety verdict.

## Update: the mixed-goal gap is closed one level up, in `ProtSat/GoalCompose.lean`

The three sentences above still describe THIS driver, which builds one formula per goal list and is
therefore conservative about it. The composition defect they describe is fixed in
`ProtSat/GoalCompose.lean`: `formulaOfGoal q g` asks each selected goal separately, and the verdicts
are composed at the level of results rather than of clauses - `boundedAttackGoals_of_exists_sat` for
the attack, `boundedSafeGoals_of_forall_unsat` for safety, the latter driven by
`Serialize.checkCode` and `modelOK` evidence rather than by a solver answer. That is where an
agreement SAFETY verdict now lives (`GoalCompose.agree_boundedSafe`), and
`GoalCompose.mixQ` is the decided-on-proof model where the conjunction is refutable while the query
is attacked. Nothing here changes: `never_boundedSafe_of_agreement` remains true of this driver, and
this driver remains the whole-list-formula route.

## The secrecy guard

`ProtSat/SnapshotGap.lean` proves that for a model whose only secrecy declaration is an
`Action.secret`, `Encode.encode P B` contains the empty clause: `ProtSat.Unsat` is then a theorem with
no solver in it, and the safety bridge would happily consume it. `secrecyObligationVisible` is the
front-end test that says when that would be a verdict in name only; `driverGate` refuses such a query
with `unsupportedGoals [Goal.secrecy]` before building anything. The guard is a stopgap: it is retired
the day the obligation-variable block lands, and `SecrecyGuard.lean`'s header says so.

What it costs: the refusal is at the front end, so a refused query gets no attack search either. That
is deliberate - an `attack` answer from this route would be a leak of a *declared* secret, and the
model asked about a secret that is not declared - but it is a cost, and `no_attack_of_not_visible`
records exactly which answers are withheld. What it does not cost: every query the driver currently
answers is unaffected (`SecrecyGuard.qg_visible`, `SecrecyGuard.qs_visible`), and the four regression
gates below still decide to the same answers.

## Regression gates

`authGap_driver_attack` checks the existing candidate model through the agreement driver.
`qg_driver_safe` checks the guarded protocol's serialized certificate through the safety driver.
`qs_driver_safe` checks the producer's zero-fuel example. `injQ_driver_refused` checks the
injective-goal refusal. `q0_driver_refused` checks the secrecy guard on the query `SnapshotGap`
exhibited. All computations used by these proofs are checked by the kernel.
-/

namespace ProtSat.GoalAnalyze

open ProtSat Term Protocol OneHot Bounded Attacker Encode Encoding Complete Query DPLL Sound
  Represent BoundedExec Certificate Analyzer AuthClauses GoalEncode Refute Serialize Resolution
open ProtSat.Encoding
open ProtSat.SecrecyGuard
open Protocol

/-! ### 1. The decidable side conditions the driver reads -/

/-- **The decidable form of 'AuthClauses.authNameable'.** 'authNameable' is a 'Prop' quantified over
the finite list 'authPositions P', so it is a Boolean test; the driver needs the test and
'AgreesBase.decodedRun_of_sat_agreement' needs the proposition. -/
def authNameableBool (sh : Shape) (P : Protocol) : Bool :=
  (authPositions P).all fun p => (authOccIdx sh p).isSome

/-- The test agrees with the proposition it decides. -/
theorem authNameableBool_iff (sh : Shape) (P : Protocol) :
    authNameableBool sh P = true <-> authNameable sh P := by
  simp [authNameableBool, authNameable, List.all_eq_true]

/-- **The decidable form of 'Complete.SecretsOKStore'.** Every declared 'Secret.store q x' must name a
variable the shape has a store slot for; otherwise the violation clause cannot state the leak. -/
def secretsOKStoreBool (sh : Shape) (P : Protocol) : Bool :=
  P.secrets.all fun sc => match sc with
    | Secret.store _q x => decide (x < shV sh)
    | Secret.closed _e => true

/-- The test agrees with the proposition it decides. -/
theorem secretsOKStoreBool_iff (sh : Shape) (P : Protocol) :
    secretsOKStoreBool sh P = true <-> SecretsOKStore sh P := by
  classical
  constructor
  · intro h q x hx
    rw [secretsOKStoreBool, List.all_eq_true] at h
    have h2 := h (Secret.store q x) hx
    simpa using h2
  · intro h
    unfold secretsOKStoreBool
    rw [List.all_eq_true]
    intro sc hsc
    cases sc with
    | closed _e => simp
    | store q x => simpa using h q x hsc

/-- **A candidate model, checked.** The SAT-side analogue of 'Serialize.checkCode': the caller hands
over an assignment and the driver walks the clause list. Nothing here trusts the producer - the solver,
an external tool, or a hand-written list like 'AuthClauses.attackAsg'. -/
def modelOK (a : Assignment) (f : CNF) : Bool := f.clauses.all fun c => Clause.eval a c

/-- A candidate that passes the walk is a model. -/
theorem sat_of_modelOK {a : Assignment} {f : CNF} (h : modelOK a f = true) : Sat a f :=
  sat_of_all h

/-- And every model passes the walk, so the test loses nothing. -/
theorem modelOK_of_sat {a : Assignment} {f : CNF} (h : Sat a f) : modelOK a f = true := by
  rw [modelOK, List.all_eq_true]
  exact fun c hc => h c hc

/-- **The goal list asks for secrecy and nothing else.** Decidable, and the exact condition under which
this driver promotes a refutation to a security statement. Agreement safety remains outside this
driver's safety bridge. -/
def secrecyOnly (gs : List Goal) : Bool :=
  ! gs.isEmpty && gs.all (fun g => g == Goal.secrecy)

/-- What 'secrecyOnly' means: something is selected and every selected goal is 'Goal.secrecy'. -/
theorem secrecyOnly_iff {gs : List Goal} :
    secrecyOnly gs = true <-> ((∀ g ∈ gs, g = Goal.secrecy) ∧ gs ≠ []) := by
  unfold secrecyOnly
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg => of_decide_eq_true (h2 g hg), ?_⟩
    cases gs with
    | nil => simp at h1
    | cons _ _ => simp
  · rintro ⟨h1, h2⟩
    refine ⟨by cases gs <;> simp_all, fun g hg => decide_eq_true (h1 g hg)⟩

/-- A 'secrecyOnly' goal list contains only goals 'Query.goalEncoded' represents. -/
theorem goalEncoded_of_secrecyOnly {gs : List Goal} (h : secrecyOnly gs = true) (g : Goal)
    (hg : g ∈ gs) : goalEncoded g = true := by
  rw [secrecyOnly_iff] at h
  rw [h.1 g hg]
  exact goalEncoded_secrecy

/-- Membership in a list, in the Boolean form the driver's tests use. -/
theorem mem_iff_elem {α : Type} [DecidableEq α] (a : α) (l : List α) :
    (l.elem a = true) = (a ∈ l) := by
  apply propext
  simp

/-- The goals the driver refuses: 'Goal.agreementInj', whose 'Query.Violation' is 'True'. -/
def refusedGoals (q : Query) : List Goal := q.goals.filter fun g => g == Goal.agreementInj

/-- If the query selected 'Goal.agreementInj', the refusal list is not empty: the driver names what it
refused rather than swallowing it. -/
theorem refusedGoals_ne {q : Query} (h : Goal.agreementInj ∈ q.goals) :
    ! (refusedGoals q).isEmpty := by
  have hm : Goal.agreementInj ∈ refusedGoals q := by
    rw [refusedGoals, List.mem_filter]
    exact ⟨h, by simp⟩
  cases h2 : refusedGoals q with
  | nil => rw [h2] at hm; simp at hm
  | cons _ _ => simp

/-! ### 2. The goal-indexed formula of a query -/

/-- **The formula the driver asks about.** The ten semantic groups plus the violation group the query's
goals select, at the monitor 'Query.Violation' supports for 'Goal.agreement': 'Matching.tripleOnly'.
'GoalEncode's header explains why the repository default 'orderAware' is the wrong pairing for a
conclusion in 'Query's vocabulary; the driver follows the correction. -/
def formulaOfGoals (q : Query) : CNF :=
  encodeGoalsOfM q.protocol q.bounds q.goals Matching.tripleOnly

/-- **The regression gate at the level of a query.** A secrecy-only query gets, definitionally, the
formula the whole development is stated about. This is what makes the driver's secrecy answers the same
computation 'analyzeQuery' performs, not merely an equivalent one. -/
theorem formulaOfGoals_eq_encode_of {q : Query} (hsec : Goal.secrecy ∈ q.goals)
    (hsub : ∀ g ∈ q.goals, g = Goal.secrecy) :
    formulaOfGoals q = encode q.protocol q.bounds := by
  have h1 : q.goals.elem Goal.secrecy = true := by rw [mem_iff_elem]; exact hsec
  have hne : Goal.agreement ∉ q.goals := by
    intro he
    exact absurd (hsub Goal.agreement he) (by simp)
  have h2 : q.goals.elem Goal.agreement = false := by
    simpa using hne
  have hvg : violationGroups (shapeOf q.protocol q.bounds) q.protocol q.goals
      Matching.tripleOnly = [violationClauses (shapeOf q.protocol q.bounds) q.protocol] := by
    simp [violationGroups, hsec, hne]
  show encodeGoals q.protocol q.bounds q.goals Matching.tripleOnly = encode q.protocol q.bounds
  unfold encodeGoals encode
  rw [hvg, ← encodeGroups_eq]

/-- An agreement-selecting, secrecy-free goal list gets the agreement encoding of the singleton list:
the monitor and the secrecy branch are both pinned by membership, so neither order nor duplication in
the query's list can change the formula. -/
theorem encodeGoalsOfM_eq_agreement_of {P : Protocol} {B : Bounds} {gs : List Goal}
    (hsec : Goal.secrecy ∉ gs) (hag : Goal.agreement ∈ gs) :
    encodeGoalsOfM P B gs Matching.tripleOnly =
      encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly := by
  have h1 : gs.elem Goal.secrecy = false := by simpa using hsec
  have h2 : gs.elem Goal.agreement = true := by rw [mem_iff_elem]; exact hag
  have h3 : ([Goal.agreement] : List Goal).elem Goal.secrecy = false := by decide
  have h4 : ([Goal.agreement] : List Goal).elem Goal.agreement = true := by decide
  show encodeGoals P B gs Matching.tripleOnly = encodeGoals P B [Goal.agreement] Matching.tripleOnly
  unfold encodeGoals
  rw [violationGroups, violationGroups, h1, h2, h3, h4]

/-- **The transport, at the monitor the driver uses.** A model of a secrecy-selecting goal-indexed
formula is a model of 'encode P B': 'GoalEncode.sat_encode_of_sat' with the monitor made explicit, so
all of 'Complete.lean' and 'Sound.lean' applies to the driver's formula. -/
theorem sat_encode_of_satM {P : Protocol} {B : Bounds} {gs : List Goal} {a : Assignment}
    (hsec : Goal.secrecy ∈ gs) (h : Sat a (encodeGoalsOfM P B gs Matching.tripleOnly)) :
    Sat a (encode P B) := by
  rw [encode_eq_base_append]
  refine sat_append.mpr ⟨GoalEncode.sat_baseEncode_of_sat h,
    GoalEncode.sat_violationClauses_of_sat hsec h⟩

/-- **SOUND, secrecy half, at the driver's monitor.** A model of the goal-indexed formula of a query
that selects secrecy is a bounded attack on that query. The attack it produces is a leak, so it says
nothing about agreement. -/
theorem boundedAttackGoals_of_sat_goalsM {P : Protocol} {B : Bounds} {gs : List Goal}
    {a : Assignment} (hsec : Goal.secrecy ∈ gs) (hU : univClosed (shapeOf P B) P)
    (h : Sat a (formulaOfGoals (Query.mk P B gs))) :
    boundedAttackGoals (Query.mk P B gs) := by
  have hs : Sat a (encode P B) := sat_encode_of_satM hsec h
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ := encoding_correct_sound hU ⟨a, hs⟩
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨Goal.secrecy, hsec, tr, Cs, hbt, hv⟩

/-- The agreement clauses, at the driver's monitor, produce an unclaimed commit triple out of a model:
'GoalEncode.boundedAttackGoals_of_sat_agreement's engine with the decoded run named, so the certificate
theorem can cite it without reaching through an existential. -/
theorem authBreak_of_sat_agreement {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (h : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly)) :
    AuthBreak P (decCfgsFrom P B a B.steps) (decEvsFrom P B a B.steps) := by
  obtain ⟨htrace, hcomm, hclaim⟩ := AgreesBase.decodedRun_of_sat_agreement hU hN h
  obtain ⟨o, ho, hao⟩ := exists_commit_candidate (by simp) h
  have hall : ∀ l ∈ authOccLits (shapeOf P B) P o, l.eval a = true :=
    authOccLits_true (by simp) h ho hao
  obtain ⟨c, hc, hot⟩ := hcomm o ho hall
  refine ⟨c, hc, ?_⟩
  intro hclaimed
  obtain ⟨k, hk, htk, kall⟩ := hclaim c hclaimed
  have hexc : claimExcuses Matching.tripleOnly (shapeOf P B) P o k = true :=
    claimExcuses_tripleOnly ho hk hot htk
  obtain ⟨l, hl, hf⟩ := authNoExcuse (by simp) h ho hk hexc hao
  exact absurd (kall l hl) (by cases h' : l.eval a <;> simp_all)

/-- **SOUND, agreement half, at the driver's monitor, with the bridge discharged.** A model of the
goal-indexed formula of a query that selects agreement and not secrecy is a bounded attack on that
query, provided the bounds keep the protocol inside the universe and every authentication position of
the model is nameable. THE CONCLUSION IS THE UNORDERED READING: 'Query.Violation P Goal.agreement' is
'ProtSat.AuthBreak', so the attack is a committed '(tag, peer, value)' triple that no session ever
claimed - no ordering, no identity of principals. 'AgreementPredicates' proves the ordered monitor is
incomparable with it and inexpressible in this vocabulary. -/
theorem boundedAttackGoals_of_sat_agreementM {P : Protocol} {B : Bounds} {gs : List Goal}
    {a : Assignment} (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (hsec : Goal.secrecy ∉ gs) (hag : Goal.agreement ∈ gs)
    (h : Sat a (formulaOfGoals (Query.mk P B gs))) :
    boundedAttackGoals (Query.mk P B gs) := by
  have h2 : encodeGoalsOfM P B gs Matching.tripleOnly
      = encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly :=
    encodeGoalsOfM_eq_agreement_of hsec hag
  have h' : Sat a (encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly) := by
    rw [← h2]; exact h
  obtain ⟨g, hg, tr, Cs, hbt, hv⟩ :=
    AgreesBase.boundedAttackGoals_of_sat_agreement_discharged hU hN h'
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨Goal.agreement, hag, tr, Cs, hbt, hv⟩

/-- **The limitation, in a statement.** The attack the agreement route produces is an 'AuthBreak' of the
decoded run: a commit triple no session claimed. Nothing here proves, or can prove, the ordered
property. -/
theorem unordered_attack_conclusion {P : Protocol} {B : Bounds} {gs : List Goal} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (hN : authNameable (shapeOf P B) P)
    (hsec : Goal.secrecy ∉ gs) (hag : Goal.agreement ∈ gs)
    (h : Sat a (formulaOfGoals (Query.mk P B gs))) :
    ∃ (tr : List Ev) (Cs : List Cfg),
      BoundedTrace P B tr Cs ∧ AuthBreak P Cs tr :=
  ⟨decEvsFrom P B a B.steps, decCfgsFrom P B a B.steps,
    AgreesBase.boundedTrace_of_sat_goals hU h,
    authBreak_of_sat_agreement hU hN
      (by
        have h2 : encodeGoalsOfM P B gs Matching.tripleOnly
            = encodeGoalsOfM P B [Goal.agreement] Matching.tripleOnly :=
          encodeGoalsOfM_eq_agreement_of hsec hag
        rw [← h2]; exact h)⟩

/-! ### 3. The certificate checker over the semantic groups -/

/-- 'Analyzer.stepsOf_ok' with the secrecy violation clause dropped: every decoded step is a transition
the step checker accepts, given only a model of the semantic groups. The proof is the one in
'ProtSat/Analyzer.lean' with 'agrees_decRun' and 'rel_agrees' replaced by the '_b' lemmas of
'ProtSat/AgreesBase.lean' - which is exactly what that re-statement was for. -/
theorem stepsOf_ok_b {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B)) :
    ∀ (k : Nat), k ≤ B.steps ->
      checkSteps P (decRun P B a (B.steps - k)) (stepsOf P B a k) = true := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hi : B.steps - (k + 1) < B.steps := by omega
      have hag := agrees_decRun_b h hU (B.steps - (k + 1)) (by omega)
      have hstep := rel_agrees_b hU h hi hag
      have hdec : decStep P B a (decRun P B a (B.steps - (k + 1))) (B.steps - (k + 1))
          = decRun P B a (B.steps - k) := by
        rw [show B.steps - k = (B.steps - (k + 1)) + 1 by omega]
        rfl
      show checkSteps P (decRun P B a (B.steps - (k + 1)))
          ({ ev := decEv (shapeOf P B) P a (B.steps - (k + 1)),
             after := decRun P B a (B.steps - k) } :: stepsOf P B a k) = true
      rw [checkSteps, Bool.and_eq_true]
      refine ⟨relDecide_complete (hdec ▸ hstep.1), ih (by omega)⟩

/-- The step part of the certificate checker, over the semantic groups alone. -/
theorem checkSteps_certOf_b {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (h : Sat a (AuthClauses.baseEncode P B)) :
    checkSteps P (initCfg P) (certOf P B a).steps = true := by
  have h0 : decRun P B a (B.steps - B.steps) = initCfg P := by
    rw [Nat.sub_self]; exact decRun_zero P B a
  rw [← h0]
  exact stepsOf_ok_b hU h B.steps (Nat.le_refl _)

/-- **An agreement attack certificate is accepted by the independent checker.** The decoded run of a
model of the agreement clauses is a legal execution (section 3's step lemma) and it contains a commit
triple no session claimed, which is the checker's own second disjunct. So 'Result.attack' - whose
payload is a 'Certificate' - means the same thing for an agreement verdict as for a secrecy one, with no
reference to the secrecy clause, the solver or the encoder. -/
theorem certOf_checked_of_authBreak {P : Protocol} {B : Bounds} {a : Assignment}
    (hU : univClosed (shapeOf P B) P) (hbase : Sat a (AuthClauses.baseEncode P B))
    (hbrk : AuthBreak P (decCfgsFrom P B a B.steps) (decEvsFrom P B a B.steps)) :
    checkCertificate P (certOf P B a) = true := by
  have hbreak : authBreakBool P (certCfgs (certOf P B a)) (certTrace (certOf P B a)) = true :=
    (authBreakBool_iff P (certCfgs (certOf P B a)) (certTrace (certOf P B a))).mpr
      (by rw [certOf_cfgs, certOf_trace]; exact hbrk)
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨beq_iff_eq.mpr rfl, checkSteps_certOf_b hU hbase⟩, Or.inr hbreak⟩

/-- The leak half of the same statement, for a secrecy-selecting query: 'Analyzer.certOf_checked' read
through the transport of section 2. -/
theorem certOf_checked_of_secrecy {P : Protocol} {B : Bounds} {gs : List Goal} {a : Assignment}
    (hsec : Goal.secrecy ∈ gs) (hU : univClosed (shapeOf P B) P)
    (h : Sat a (encodeGoalsOfM P B gs Matching.tripleOnly)) :
    checkCertificate P (certOf P B a) = true :=
  certOf_checked hU (sat_encode_of_satM hsec h)

/-! ### 4. The driver -/

/-- **The six Boolean tests the front end runs, in the order it runs them.** The sixth is
`ProtSat.SecrecyGuard.secrecyObligationVisible`: the secrecy violation clause of the formula the driver
is about to build has no literal for a secret the model declares by `Action.secret` unless `P.secrets`
also names that value. SnapshotGap proves what happens when it does not - `unsat_of_secrets_nil` hands
the solver an empty clause, so UNSAT is free and a refutation of it is no evidence at all. The guard is
what stops this driver from turning that free UNSAT into a security verdict. -/
def driverGateTests (q : Query) : Bool × Bool × Bool × Bool × Bool × Bool :=
  (q.goals.elem Goal.agreementInj, (validate q).isEmpty, q.goals.isEmpty,
    univClosedBool (shapeOf q.protocol q.bounds) q.protocol,
    q.goals.elem Goal.agreement && ! (authNameableBool (shapeOf q.protocol q.bounds) q.protocol),
    secrecyObligationVisible q)

/-- The driver's front end: 'some r' means the answer is 'r', with no formula built and no solver run.
'Goal.agreementInj' has the highest-priority refusal, with no hypothesis, because its
'Query.Violation' is 'True': any driver that let it reach the semantics would report ATTACK for every
query that names it. -/
def driverGate (q : Query) : Option Result :=
  match driverGateTests q with
  | (true, _, _, _, _, _) => some (Result.unsupportedGoals (refusedGoals q))
  | (false, false, _, _, _, _) => some (Result.invalidModel (validate q))
  | (false, true, true, _, _, _) => some Result.noGoals
  | (false, true, false, false, _, _) => some Result.boundsTooSmall
  | (false, true, false, true, true, _) => some (Result.unknown UnknownReason.solverFailure)
  | (false, true, false, true, false, false) => some (Result.unsupportedGoals [Goal.secrecy])
  | (false, true, false, true, false, true) => none

/- **Why the sixth branch is 'unsupportedGoals' and not 'invalidModel'.** The answer type is fixed in
'Query.lean', which this task may not edit, and 'Diagnostic' has no constructor that names this defect:
the model is not malformed - 'validate' says so - it is *unanswerable by this route*. Inventing a
diagnostic by reusing 'closedSecretNotClosed' or 'closedSecretUndefined' would misreport the reason, so
the driver reports the goal it cannot answer instead: 'unsupportedGoals [Goal.secrecy]' means "the
secrecy question this query asks is not expressible in the CNF of this model". The refused list is
honest about which goal, and 'SecrecyGuard.uncoveredSecretActions' is the list of which action, for
whichever front end wants to print it. The natural home of the sharper answer is a new constructor
'Diagnostic.secretActionNotDeclared (q pc : Nat) (e : Expr)' in 'Query.lean'; that is a one-line change
to a file this task does not own, and it is reported as such. -/

/-- The front end refuses an 'agreementInj' query, and the refusal names the goals. -/
theorem driverGate_agreementInj {q : Query} (h : q.goals.elem Goal.agreementInj = true) :
    driverGate q = some (Result.unsupportedGoals (refusedGoals q)) := by
  unfold driverGate driverGateTests
  rw [h]

/-- The front end reports a malformed model. -/
theorem driverGate_invalid {q : Query} (h1 : q.goals.elem Goal.agreementInj = false)
    (h2 : (validate q).isEmpty = false) :
    driverGate q = some (Result.invalidModel (validate q)) := by
  unfold driverGate driverGateTests
  rw [h1, h2]

/-- The front end reports that nothing was selected. -/
theorem driverGate_noGoals {q : Query} (h1 : q.goals.elem Goal.agreementInj = false)
    (h2 : (validate q).isEmpty = true) (h3 : q.goals.isEmpty = true) :
    driverGate q = some Result.noGoals := by
  unfold driverGate driverGateTests
  rw [h1, h2, h3]

/-- The front end reports bounds too small. -/
theorem driverGate_bounds {q : Query} (h1 : q.goals.elem Goal.agreementInj = false)
    (h2 : (validate q).isEmpty = true) (h3 : q.goals.isEmpty = false)
    (h4 : univClosedBool (shapeOf q.protocol q.bounds) q.protocol = false) :
    driverGate q = some Result.boundsTooSmall := by
  unfold driverGate driverGateTests
  rw [h1, h2, h3, h4]

/-- The front end declines an agreement query whose model is not nameable. -/
theorem driverGate_notNameable {q : Query} (h1 : q.goals.elem Goal.agreementInj = false)
    (h2 : (validate q).isEmpty = true) (h3 : q.goals.isEmpty = false)
    (h4 : univClosedBool (shapeOf q.protocol q.bounds) q.protocol = true)
    (h5 : (q.goals.elem Goal.agreement && ! (authNameableBool (shapeOf q.protocol q.bounds) q.protocol))
      = true) :
    driverGate q = some (Result.unknown UnknownReason.solverFailure) := by
  unfold driverGate driverGateTests
  rw [h1, h2, h3, h4, h5]

/-- The front end lets the query through - and only when the secrecy guard is satisfied. -/
theorem driverGate_passes {q : Query} (h1 : q.goals.elem Goal.agreementInj = false)
    (h2 : (validate q).isEmpty = true) (h3 : q.goals.isEmpty = false)
    (h4 : univClosedBool (shapeOf q.protocol q.bounds) q.protocol = true)
    (h5 : (q.goals.elem Goal.agreement && ! (authNameableBool (shapeOf q.protocol q.bounds) q.protocol))
      = false) (h6 : secrecyObligationVisible q = true) :
    driverGate q = none := by
  unfold driverGate driverGateTests
  rw [h1, h2, h3, h4, h5, h6]

/-- **The guard's refusal, as a theorem.** A query that selects secrecy on a model whose action-declared
secrets the violation clause cannot name is refused at the front end, with no formula built and no
solver run. -/
theorem driverGate_refused_of_not_visible {q : Query} (h1 : q.goals.elem Goal.agreementInj = false)
    (h2 : (validate q).isEmpty = true) (h3 : q.goals.isEmpty = false)
    (h4 : univClosedBool (shapeOf q.protocol q.bounds) q.protocol = true)
    (h5 : (q.goals.elem Goal.agreement && ! (authNameableBool (shapeOf q.protocol q.bounds) q.protocol))
      = false) (h6 : secrecyObligationVisible q = false) :
    driverGate q = some (Result.unsupportedGoals [Goal.secrecy]) := by
  unfold driverGate driverGateTests
  rw [h1, h2, h3, h4, h5, h6]

/-- Everything the front end guarantees when it lets the driver proceed. Unchanged by the guard: the
guard adds a refusal, not a hypothesis the search needs, so every theorem downstream of this one is
literally the theorem it was. -/
theorem of_driverGate_none {q : Query} (h : driverGate q = none) :
    WellFormed q ∧ q.goals ≠ [] ∧ Goal.agreementInj ∉ q.goals
      ∧ univClosedBool (shapeOf q.protocol q.bounds) q.protocol = true
      ∧ (Goal.agreement ∈ q.goals ->
          authNameableBool (shapeOf q.protocol q.bounds) q.protocol = true) := by
  cases h1 : q.goals.elem Goal.agreementInj <;>
    cases h2 : (validate q).isEmpty <;>
      cases h3 : q.goals.isEmpty <;>
        cases h4 : univClosedBool (shapeOf q.protocol q.bounds) q.protocol <;>
          cases h5 : (q.goals.elem Goal.agreement &&
            ! (authNameableBool (shapeOf q.protocol q.bounds) q.protocol)) <;>
            simp_all [driverGate, driverGateTests, WellFormed, Bool.and_eq_true]

/-- **The guard is a front-end refusal, not a hypothesis the search could discharge.** A query whose
secrecy obligations the CNF cannot name never reaches `driverSearch`: no branch of `driverGate` returns
`none` when the sixth test is false. -/
theorem not_visible_imp_driverGate_some {q : Query} (h : secrecyObligationVisible q = false) :
    driverGate q ≠ none := by
  intro hn
  cases h1 : q.goals.elem Goal.agreementInj <;>
    cases h2 : (validate q).isEmpty <;>
      cases h3 : q.goals.isEmpty <;>
        cases h4 : univClosedBool (shapeOf q.protocol q.bounds) q.protocol <;>
          cases h5 : q.goals.elem Goal.agreement <;>
            cases h6 : authNameableBool (shapeOf q.protocol q.bounds) q.protocol <;>
              simp_all [driverGate, driverGateTests]

/-- So a query the front end lets through has visible secrecy obligations. -/
theorem visible_of_driverGate_none {q : Query} (h : driverGate q = none) :
    secrecyObligationVisible q = true := by
  cases h2 : secrecyObligationVisible q with
  | false => exact absurd h (not_visible_imp_driverGate_some h2)
  | true => rfl

/-- The front end never produces an attack answer. -/
theorem driverGate_not_attack {q : Query} {r : Result} (h : driverGate q = some r)
    (x : Certificate) : r ≠ Result.attack x := by
  unfold driverGate at h
  split at h <;> cases h <;> simp

/-- The front end never produces a safety answer either. -/
theorem driverGate_not_boundedSafe {q : Query} {r : Result} (h : driverGate q = some r)
    (e : SafeEvidence) : r ≠ Result.boundedSafe e := by
  unfold driverGate at h
  split at h <;> cases h <;> simp

/-- The model the driver accepts: a verified hint when the hint checks out, otherwise DPLL's answer. The
hint is checked, never trusted; if it fails the driver falls back to its own search. -/
def driverModelStep (q : Query) (cand : Option (List (BVar × Bool))) :
    Option (List (BVar × Bool)) :=
  match cand with
  | some asg => match modelOK (asgVal asg) (formulaOfGoals q) with
                | true => some asg
                | false => DPLL.dpll (formulaOfGoals q)
  | none => DPLL.dpll (formulaOfGoals q)

/-- With no hint the model step is the solver's own answer. -/
theorem driverModelStep_none (q : Query) :
    driverModelStep q none = DPLL.dpll (formulaOfGoals q) := rfl

/-- A model the driver accepts is a model of the query's formula. -/
theorem driverModelStep_some {q : Query} {cand : Option (List (BVar × Bool))}
    {asg : List (BVar × Bool)} (h : driverModelStep q cand = some asg) :
    Sat (asgVal asg) (formulaOfGoals q) := by
  cases hc : cand with
  | none => exact dpll_sound (by simpa [driverModelStep, hc] using h)
  | some a =>
      cases hm : modelOK (asgVal a) (formulaOfGoals q) with
      | true =>
          have heq : a = asg := by simpa [driverModelStep, hc, hm] using h
          subst asg
          exact sat_of_modelOK hm
      | false => exact dpll_sound (by simpa [driverModelStep, hc, hm] using h)

/-- The proved-sound producer applied to the query's own formula: saturate with 'fuel' rounds, take the
refutation it reaches, serialize it with the decode fuel 'Serialize.proofOfCode_proofCode'' needs. -/
def driverProduced (q : Query) (fuel : Nat) : Option (Nat × List Int) :=
  (refutationOf (formulaOfGoals q) fuel).map fun p => (p.length + 1, proofCode p)

/-- What the producer emits, the checker accepts: 'refute_sound' through the serialization round trip.
The driver still checks it; this lemma is why the check cannot fail, not a licence to skip it. -/
theorem checkCode_driverProduced {q : Query} {fuel : Nat} {p : List Line}
    (h : refutationOf (formulaOfGoals q) fuel = some p) :
    checkCode (formulaOfGoals q) (p.length + 1) (proofCode p) = true := by
  rw [checkCode_iff_checkProof]
  exact refute_sound h

/-- The refutation the driver accepts: a checked hint when the hint checks out, otherwise the producer's
output. -/
def driverRefutationStep (q : Query) (fuel : Nat) (code : Option (Nat × List Int)) :
    Option (Nat × List Int) :=
  match code with
  | some kc => match checkCode (formulaOfGoals q) kc.1 kc.2 with
               | true => some kc
               | false => driverProduced q fuel
  | none => driverProduced q fuel

/-- With no hint the refutation step is the producer. -/
theorem driverRefutationStep_none (q : Query) (fuel : Nat) :
    driverRefutationStep q fuel none = driverProduced q fuel := rfl

/-- A refutation the driver accepts is a checked refutation of the query's formula. This is the only
place the driver trusts a Boolean: everything downstream of it is 'Serialize.checkCode_sound'. -/
theorem driverRefutationStep_some {q : Query} {fuel : Nat}
    {code : Option (Nat × List Int)} {kc : Nat × List Int}
    (h : driverRefutationStep q fuel code = some kc) :
    checkCode (formulaOfGoals q) kc.1 kc.2 = true := by
  have hproduced : ∀ {kc : Nat × List Int}, driverProduced q fuel = some kc ->
      checkCode (formulaOfGoals q) kc.1 kc.2 = true := by
    intro kc hp
    unfold driverProduced at hp
    cases hr : refutationOf (formulaOfGoals q) fuel with
    | none => simp [hr] at hp
    | some p =>
        have heq : (p.length + 1, proofCode p) = kc := by simpa [hr] using hp
        subst kc
        exact checkCode_driverProduced hr
  cases hc : code with
  | none => exact hproduced (by simpa [driverRefutationStep, hc] using h)
  | some kc' =>
      cases hm : checkCode (formulaOfGoals q) kc'.1 kc'.2 with
      | true =>
          have heq : kc' = kc := by simpa [driverRefutationStep, hc, hm] using h
          subst kc
          exact hm
      | false => exact hproduced (by simpa [driverRefutationStep, hc, hm] using h)

/-- The five decidable tests the safe verdict needs, as one Boolean. -/
def safetyTests (q : Query) (k : Nat) (c : List Int) : Bool :=
  secrecyOnly q.goals && univClosedBool (shapeOf q.protocol q.bounds) q.protocol
    && secretsOKStoreBool (shapeOf q.protocol q.bounds) q.protocol
    && ! domainGap q.protocol q.bounds && checkCode (formulaOfGoals q) k c

/-- **The safety bridge, goal-indexed.** A checked refutation of the query's own formula refutes the
secrecy formula too - for a secrecy-only list the two formulas are the same term - and
'CheckedSafe.boundedSafeGoals_of_unsat' does the rest. -/
theorem boundedSafeGoals_of_checkedCode_goals {q : Query} {k : Nat} {c : List Int}
    (hso : secrecyOnly q.goals = true)
    (hU : univClosedBool (shapeOf q.protocol q.bounds) q.protocol = true)
    (hsec : secretsOKStoreBool (shapeOf q.protocol q.bounds) q.protocol = true)
    (hgap : domainGap q.protocol q.bounds = false)
    (hchk : checkCode (formulaOfGoals q) k c = true) : boundedSafeGoals q := by
  have hne : q.goals ≠ [] := (secrecyOnly_iff.mp hso).2
  have hgoal : ∀ g ∈ q.goals, goalEncoded g := by
    intro g hg; exact goalEncoded_of_secrecyOnly hso g hg
  have hU' : univClosed (shapeOf q.protocol q.bounds) q.protocol :=
    (univClosedBool_iff _ _).mp hU
  have hsec' : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol :=
    (secretsOKStoreBool_iff _ _).mp hsec
  have hsecmem : Goal.secrecy ∈ q.goals := by
    cases hq : q.goals with
    | nil => exact absurd hq hne
    | cons x xs =>
        have hx : x ∈ x :: xs := List.Mem.head xs
        have heq : x = Goal.secrecy := (secrecyOnly_iff.mp hso).1 x (by rw [hq]; exact hx)
        subst heq
        simp
  have hfe : formulaOfGoals q = encode q.protocol q.bounds :=
    formulaOfGoals_eq_encode_of hsecmem (fun g hg => (secrecyOnly_iff.mp hso).1 g hg)
  exact CheckedSafe.boundedSafeGoals_of_unsat hgoal hne hU' hsec' hgap
    (by rw [← hfe]; exact checkCode_sound hchk)

/-- The five tests, unpacked. -/
theorem safetyTests_imp {q : Query} {k : Nat} {c : List Int} (h : safetyTests q k c = true) :
    boundedSafeGoals q := by
  simp only [safetyTests, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact boundedSafeGoals_of_checkedCode_goals h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2

/-- **The safety evidence a checked refutation licenses**, or 'none' when it licenses nothing. Every
hypothesis the bridge needs is a decidable test the driver runs itself: the goal list must be
secrecy-only (the driver's supported safety bridge), the bounds must name the protocol's closed expressions, every store
secret must have a slot, the value domain must have no representability gap, and the code must refute
THIS formula. -/
def driverSafetyEvidence (q : Query) (k : Nat) (c : List Int) : Option SafeEvidence :=
  if h : safetyTests q k c = true then some ⟨q, safetyTests_imp h⟩ else none

/-- The evidence, when it exists, is about the query it was asked for, and it is true. -/
theorem boundedSafeGoals_of_driverSafetyEvidence {q : Query} {k : Nat} {c : List Int}
    {e : SafeEvidence} (h : driverSafetyEvidence q k c = some e) : boundedSafeGoals q := by
  by_cases hs : safetyTests q k c = true
  · have : driverSafetyEvidence q k c = some ⟨q, safetyTests_imp hs⟩ := dite_eq_left hs
    rw [this] at h
    cases h
    exact safetyTests_imp hs
  · rw [driverSafetyEvidence, dite_eq_right hs] at h
    cases h

/-- The driver conservatively withholds agreement safety evidence: this bridge only handles
secrecy-only queries. -/
theorem driverSafetyEvidence_none_of_agreement {q : Query} {k : Nat} {c : List Int}
    (hag : Goal.agreement ∈ q.goals) : driverSafetyEvidence q k c = none := by
  have hs : safetyTests q k c = false := by
    cases hso : secrecyOnly q.goals with
    | false => rw [safetyTests, hso]; simp
    | true =>
        exfalso
        rw [secrecyOnly_iff] at hso
        exact absurd (hso.1 Goal.agreement hag) (by simp)
  rw [driverSafetyEvidence, dite_eq_right (by simp [hs])]

/-- The safe-side verdict: evidence if the bridge accepts it, otherwise the formula fact and nothing
more. -/
def driverSafeVerdict (q : Query) (k : Nat) (c : List Int) : Result :=
  match driverSafetyEvidence q k c with
  | some e => Result.boundedSafe e
  | none => Result.encodingUnsat

/-- The safe-side verdict is never an attack answer. -/
theorem driverSafeVerdict_not_attack (q : Query) (k : Nat) (c : List Int) (x : Certificate) :
    driverSafeVerdict q k c ≠ Result.attack x := by
  unfold driverSafeVerdict
  cases h : driverSafetyEvidence q k c with
  | some _ => intro hc; cases hc
  | none => intro hc; cases hc

/-- The safe-side verdict, when it says 'boundedSafe', says something true. -/
theorem boundedSafe_of_driverSafeVerdict {q : Query} {k : Nat} {c : List Int} {e : SafeEvidence}
    (h : driverSafeVerdict q k c = Result.boundedSafe e) : boundedSafeGoals q :=
  boundedSafeGoals_of_driverSafetyEvidence (by
    unfold driverSafeVerdict at h
    cases h2 : driverSafetyEvidence q k c with
    | some e' => rw [h2] at h; cases h; rfl
    | none => rw [h2] at h; cases h)

/-- And when it says 'encodingUnsat' after a checked refutation, that is exactly a formula fact. -/
theorem unsat_of_driverSafeVerdict {q : Query} {k : Nat} {c : List Int}
    (hchk : checkCode (formulaOfGoals q) k c = true)
    (_h : driverSafeVerdict q k c = Result.encodingUnsat) : ProtSat.Unsat (formulaOfGoals q) :=
  checkCode_sound hchk

/-- **The search.** Cheapest evidence first: try to refute (a checked hint, then the proved-sound
producer within its fuel); if nothing refutes, try to satisfy (a verified hint, then DPLL).
'unknown resourceExhausted' is the answer when neither happened: the driver declines to report safety on
the strength of a search it cannot certify, and declines to report an attack it did not find. -/
def driverSearch (q : Query) (fuel : Nat) (cand : Option (List (BVar × Bool)))
    (code : Option (Nat × List Int)) : Result :=
  match driverRefutationStep q fuel code with
  | some kc => driverSafeVerdict q kc.1 kc.2
  | none => match driverModelStep q cand with
            | some asg => Result.attack (certOf q.protocol q.bounds (asgVal asg))
            | none => Result.unknown UnknownReason.resourceExhausted

/-- **The goal-indexed analyser.** 'q' in, 'Result' out: the front end, then the search. -/
def analyzeGoalsOfUsing (q : Query) (fuel : Nat) (cand : Option (List (BVar × Bool)))
    (code : Option (Nat × List Int)) : Result :=
  match driverGate q with
  | some r => r
  | none => driverSearch q fuel cand code

/-- **The driver the task asks for.** The violation group is chosen by 'q.goals'; the answer is a
statement about the goals the query selected. 'fuel' is the refutation producer's budget, which is
roadmap stage 6's "no fuel policy" gap: at 'fuel = 0' the producer accepts only a refutation already
present in the seed. -/
def analyzeGoalsOf (q : Query) (fuel : Nat) : Result :=
  analyzeGoalsOfUsing q fuel none none

/-- The driver with a candidate model: the SAT side is a *checked* assignment rather than a DPLL run.
Same verdicts, same theorems, and the only affordable way to decide an agreement attack. -/
def analyzeGoalsOfModel (q : Query) (asg : List (BVar × Bool)) : Result :=
  analyzeGoalsOfUsing q 0 (some asg) none

/-- The driver with a serialized refutation: the UNSAT side is a *checked* code rather than a producer
run. 'AnalyzerEvidence.qgCode' is such a code for the secrecy formula. -/
def analyzeGoalsOfCode (q : Query) (k : Nat) (c : List Int) : Result :=
  analyzeGoalsOfUsing q 0 none (some (k, c))

/-! ### 5. The driver's security contract -/

/-- A nonempty supported goal list contains secrecy or agreement. -/
theorem secrecy_or_agreement_of_driverGate_none {q : Query} (h : driverGate q = none) :
    Goal.secrecy ∈ q.goals ∨ Goal.agreement ∈ q.goals := by
  obtain ⟨_, hne, hni, _, _⟩ := of_driverGate_none h
  cases hgs : q.goals with
  | nil => exact False.elim (hne hgs)
  | cons g gs =>
      have hg : g ∈ q.goals := by rw [hgs]; exact List.Mem.head _
      cases g with
      | secrecy => exact Or.inl (List.Mem.head _)
      | agreement => exact Or.inr (List.Mem.head _)
      | agreementInj => exact False.elim (hni hg)

/-- A model accepted after the front end witnesses a selected security violation. -/
theorem boundedAttackGoals_of_driverModel {q : Query} {a : Assignment}
    (hg : driverGate q = none) (hs : Sat a (formulaOfGoals q)) : boundedAttackGoals q := by
  have hfront := of_driverGate_none hg
  have hU := (univClosedBool_iff _ _).mp hfront.2.2.2.1
  by_cases hsec : Goal.secrecy ∈ q.goals
  · exact boundedAttackGoals_of_sat_goalsM hsec hU hs
  · have hag := (secrecy_or_agreement_of_driverGate_none hg).resolve_left hsec
    have hN := (authNameableBool_iff _ _).mp (hfront.2.2.2.2 hag)
    exact boundedAttackGoals_of_sat_agreementM hU hN hsec hag hs

/-- A secrecy model gives an independently accepted certificate. -/
theorem attack_certificate_of_secrecy {q : Query} {a : Assignment}
    (hsec : Goal.secrecy ∈ q.goals)
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hs : Sat a (formulaOfGoals q)) :
    checkCertificate q.protocol (certOf q.protocol q.bounds a) = true :=
  certOf_checked_of_secrecy hsec hU hs

/-- An agreement model gives an independently accepted certificate. -/
theorem attack_certificate_of_agreement {q : Query} {a : Assignment}
    (hsec : Goal.secrecy ∉ q.goals) (hag : Goal.agreement ∈ q.goals)
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hN : authNameable (shapeOf q.protocol q.bounds) q.protocol)
    (hs : Sat a (formulaOfGoals q)) :
    checkCertificate q.protocol (certOf q.protocol q.bounds a) = true := by
  have heq := encodeGoalsOfM_eq_agreement_of (P := q.protocol) (B := q.bounds) hsec hag
  have hs' : Sat a (encodeGoalsOfM q.protocol q.bounds [Goal.agreement] Matching.tripleOnly) := by
    rw [← heq]
    exact hs
  exact certOf_checked_of_authBreak hU (GoalEncode.sat_baseEncode_of_sat hs')
    (authBreak_of_sat_agreement hU hN hs')

/-- The certificate produced from an accepted model passes the independent checker. -/
theorem checkedCertificate_of_driverModel {q : Query} {a : Assignment}
    (hg : driverGate q = none) (hs : Sat a (formulaOfGoals q)) :
    checkCertificate q.protocol (certOf q.protocol q.bounds a) = true := by
  have hfront := of_driverGate_none hg
  have hU := (univClosedBool_iff _ _).mp hfront.2.2.2.1
  by_cases hsec : Goal.secrecy ∈ q.goals
  · exact attack_certificate_of_secrecy hsec hU hs
  · have hag := (secrecy_or_agreement_of_driverGate_none hg).resolve_left hsec
    have hN := (authNameableBool_iff _ _).mp (hfront.2.2.2.2 hag)
    exact attack_certificate_of_agreement hsec hag hU hN hs

/-- An attack answer both violates a selected goal and carries an independently checked certificate. -/
theorem attack_sound {q : Query} {fuel : Nat} {cand : Option (List (BVar × Bool))}
    {code : Option (Nat × List Int)} {c : Certificate}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.attack c) :
    boundedAttackGoals q ∧ checkCertificate q.protocol c = true := by
  unfold analyzeGoalsOfUsing at h
  cases hg : driverGate q with
  | some r =>
      rw [hg] at h
      exact False.elim (driverGate_not_attack hg c h)
  | none =>
      rw [hg] at h
      unfold driverSearch at h
      cases hr : driverRefutationStep q fuel code with
      | some kc =>
          rw [hr] at h
          exact False.elim (driverSafeVerdict_not_attack q kc.1 kc.2 c h)
      | none =>
          rw [hr] at h
          cases hm : driverModelStep q cand with
          | none => simp [hm] at h
          | some asg =>
              rw [hm] at h
              cases h
              have hs := driverModelStep_some hm
              exact ⟨boundedAttackGoals_of_driverModel hg hs, checkedCertificate_of_driverModel hg hs⟩

/-- The attack answer is about a goal the query actually selected. -/
theorem boundedAttackGoals_of_attack {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {c : Certificate}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.attack c) : boundedAttackGoals q :=
  (attack_sound h).1

/-- The accepted attack certificate can be checked without the solver or encoder. -/
theorem checkedCertificate_of_attack {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {c : Certificate}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.attack c) :
    checkCertificate q.protocol c = true := (attack_sound h).2

/-- A bounded-safety answer proves safety for this query's selected goals. -/
theorem boundedSafeGoals_of_boundedSafe {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {e : SafeEvidence}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.boundedSafe e) : boundedSafeGoals q := by
  unfold analyzeGoalsOfUsing at h
  cases hg : driverGate q with
  | some r =>
      rw [hg] at h
      exact False.elim (driverGate_not_boundedSafe hg e h)
  | none =>
      rw [hg] at h
      unfold driverSearch at h
      cases hr : driverRefutationStep q fuel code with
      | some kc =>
          rw [hr] at h
          exact boundedSafe_of_driverSafeVerdict h
      | none =>
          rw [hr] at h
          cases hm : driverModelStep q cand <;> simp [hm] at h

/-- Agreement queries cannot receive a safety verdict from the driver's secrecy-only bridge. -/
theorem never_boundedSafe_of_agreement {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)}
    (hag : Goal.agreement ∈ q.goals) (e : SafeEvidence) :
    analyzeGoalsOfUsing q fuel cand code ≠ Result.boundedSafe e := by
  unfold analyzeGoalsOfUsing
  cases hg : driverGate q with
  | some r => exact driverGate_not_boundedSafe hg e
  | none =>
      simp only
      unfold driverSearch
      cases hr : driverRefutationStep q fuel code with
      | some kc => simp [driverSafeVerdict, driverSafetyEvidence_none_of_agreement hag]
      | none => cases hm : driverModelStep q cand <;> simp

/-- Injective agreement is refused before either search runs. -/
theorem refuses_agreementInj {q : Query} (fuel : Nat) (cand : Option (List (BVar × Bool)))
    (code : Option (Nat × List Int)) (hinj : Goal.agreementInj ∈ q.goals) :
    analyzeGoalsOfUsing q fuel cand code = Result.unsupportedGoals (refusedGoals q) := by
  have hmem : q.goals.elem Goal.agreementInj = true := by simpa using hinj
  simp [analyzeGoalsOfUsing, driverGate_agreementInj hmem]

theorem not_attack_of_agreementInj {q : Query} (fuel : Nat)
    (cand : Option (List (BVar × Bool))) (code : Option (Nat × List Int))
    (hinj : Goal.agreementInj ∈ q.goals) (c : Certificate) :
    analyzeGoalsOfUsing q fuel cand code ≠ Result.attack c := by
  rw [refuses_agreementInj fuel cand code hinj]
  intro h
  cases h

theorem not_boundedSafe_of_agreementInj {q : Query} (fuel : Nat)
    (cand : Option (List (BVar × Bool))) (code : Option (Nat × List Int))
    (hinj : Goal.agreementInj ∈ q.goals) (e : SafeEvidence) :
    analyzeGoalsOfUsing q fuel cand code ≠ Result.boundedSafe e := by
  rw [refuses_agreementInj fuel cand code hinj]
  intro h
  cases h

/-- An encoding-unsatisfiability answer is a fact about this driver's selected formula. -/
theorem unsat_of_encodingUnsat {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.encodingUnsat) :
    ProtSat.Unsat (formulaOfGoals q) := by
  unfold analyzeGoalsOfUsing at h
  cases hg : driverGate q with
  | some r =>
      rw [hg] at h
      unfold driverGate at hg
      split at hg <;> cases hg <;> cases h
  | none =>
      rw [hg] at h
      unfold driverSearch at h
      cases hr : driverRefutationStep q fuel code with
      | some kc => exact checkCode_sound (driverRefutationStep_some hr)
      | none =>
          rw [hr] at h
          cases hm : driverModelStep q cand <;> simp [hm] at h

/-! ### 6. The secrecy guard at the front end -/

/-- **The safety route is not applicable to a query the guard refuses.** This is the theorem that makes
the guard meaningful rather than decorative: not "the driver prints a different word", but "the driver
cannot reach the bridge at all". No refutation, no checked code, no fuel and no candidate hint turns a
refused query into a `boundedSafe` answer, because the front end returns before `driverSearch` runs. -/
theorem no_boundedSafe_of_not_visible {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {e : SafeEvidence}
    (h : secrecyObligationVisible q = false) :
    analyzeGoalsOfUsing q fuel cand code ≠ Result.boundedSafe e := by
  intro hcon
  unfold analyzeGoalsOfUsing at hcon
  cases hg : driverGate q with
  | none => exact absurd hg (not_visible_imp_driverGate_some h)
  | some r => rw [hg] at hcon; exact driverGate_not_boundedSafe hg e hcon

/-- The refusal withholds the attack answer too: the driver declines the query rather than answer part
of it. Recorded as a theorem so the conservatism is visible, not hidden in a match arm. -/
theorem no_attack_of_not_visible {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {c : Certificate}
    (h : secrecyObligationVisible q = false) :
    analyzeGoalsOfUsing q fuel cand code ≠ Result.attack c := by
  intro hcon
  unfold analyzeGoalsOfUsing at hcon
  cases hg : driverGate q with
  | none => exact absurd hg (not_visible_imp_driverGate_some h)
  | some r => rw [hg] at hcon; exact driverGate_not_attack hg c hcon

/-- **The driver's contract, strengthened by the guard.** Every safety verdict this driver emits is
true of the query (`boundedSafeGoals_of_boundedSafe`) *and* about a model whose declared secrets the
CNF can name. Nothing previously sound became unsound; one more condition is now enforced. -/
theorem boundedSafe_imp_visible {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {e : SafeEvidence}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.boundedSafe e) :
    secrecyObligationVisible q = true := by
  cases h2 : secrecyObligationVisible q with
  | true => rfl
  | false => exact absurd h (no_boundedSafe_of_not_visible h2)

/-- The same for an attack answer: whatever the driver reports as an attack, it reported about a model
it could ask about. -/
theorem attack_imp_visible {q : Query} {fuel : Nat}
    {cand : Option (List (BVar × Bool))} {code : Option (Nat × List Int)} {c : Certificate}
    (h : analyzeGoalsOfUsing q fuel cand code = Result.attack c) :
    secrecyObligationVisible q = true := by
  cases h2 : secrecyObligationVisible q with
  | true => rfl
  | false => exact absurd h (no_attack_of_not_visible h2)

/-- The guard never fires on an agreement-only query, so the agreement half of the driver is untouched
by construction - which is why `authGap_driver_attack` and `injQ_driver_refused` still decide. -/
theorem visible_of_no_secrecy {q : Query} (h : Goal.secrecy ∉ q.goals) :
    secrecyObligationVisible q = true := visible_of_no_secrecy_goal h

set_option maxRecDepth 20000 in
/-- **The guard fires on the query `SnapshotGap` exhibited.** `SnapshotGap.the_tool_says_safe` recorded
that the contract's own `analyzeQuery` answers `encodingUnsat` for `SnapshotGap.q0` while the repaired
contract proves a bounded attack on it. This driver now refuses the same query outright, before
building a formula or running a solver: the wrong verdict is not merely unproved anywhere here, it is
not an answer the tool can produce. -/
theorem q0_driver_refused :
    analyzeGoalsOf SnapshotGap.q0 0 = Result.unsupportedGoals [Goal.secrecy] := by
  rw [analyzeGoalsOf, analyzeGoalsOfUsing,
    driverGate_refused_of_not_visible (by decide) (by decide) (by decide)
      ((univClosedBool_iff (shapeOf SnapshotGap.P0 SnapshotGap.B) SnapshotGap.P0).mpr SnapshotGap.hU0)
      (by decide) ProtSat.SecrecyGuard.guard_false_q0]

/-- The refusal is not a security claim: `securityResult` says so. -/
theorem q0_not_security : securityResult (analyzeGoalsOf SnapshotGap.q0 0) = false := by
  rw [q0_driver_refused]
  rfl

/-- No safety evidence and no attack certificate is reachable for the refused query, whatever the fuel
and whatever hints are supplied: the refusal is at the front end, ahead of both searches. -/
theorem q0_no_verdict (e : SafeEvidence) (c : Certificate)
    (fuel : Nat) (cand : Option (List (BVar × Bool))) (code : Option (Nat × List Int)) :
    analyzeGoalsOfUsing SnapshotGap.q0 fuel cand code ≠ Result.boundedSafe e ∧
      analyzeGoalsOfUsing SnapshotGap.q0 fuel cand code ≠ Result.attack c :=
  ⟨no_boundedSafe_of_not_visible ProtSat.SecrecyGuard.guard_false_q0,
    no_attack_of_not_visible ProtSat.SecrecyGuard.guard_false_q0⟩

/-- **The headline, at the driver.** The guard is false, the driver refuses, and the repaired contract
still proves the leak on the same query: the guard fires exactly where the tool was wrong, and nowhere
else that the tool was right. -/
theorem guard_blocks_the_wrong_verdict :
    analyzeGoalsOf SnapshotGap.q0 0 = Result.unsupportedGoals [Goal.secrecy] ∧
      secrecyObligationVisible SnapshotGap.q0 = false ∧
      Reference.Contract.boundedAttack SnapshotGap.q0 :=
  ⟨q0_driver_refused, ProtSat.SecrecyGuard.guard_false_q0, SnapshotGap.attacked_for_secrecy0⟩

/-! ### 7. Executable regression gates -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- A checked candidate reaches the agreement attack branch on AuthGap. -/
theorem authGap_driver_attack :
    (match analyzeGoalsOfModel AuthGap.qa AuthClauses.attackAsg with
     | Result.attack _ => true
     | _ => false) = true := by decide

set_option maxRecDepth 20000 in
/-- The guarded protocol's existing checked code reaches the evidence-bearing safety branch. -/
theorem qg_driver_safe :
    (match analyzeGoalsOfCode EndToEnd.qg AnalyzerEvidence.qgCheckFuel AnalyzerEvidence.qgCode with
     | Result.boundedSafe _ => true
     | _ => false) = true := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The saturation producer's zero-fuel example also reaches the safety branch. -/
theorem qs_driver_safe :
    (match analyzeGoalsOf AuthGap.qs 0 with
     | Result.boundedSafe _ => true
     | _ => false) = true := by decide

/-- The concrete injective query is refused before the solver can run. -/
theorem injQ_driver_refused :
    analyzeGoalsOf AgreementPredicates.injQ 0 =
      Result.unsupportedGoals [Goal.agreementInj] := by
  rw [analyzeGoalsOf, refuses_agreementInj 0 none none (by decide)]
  rfl

end ProtSat.GoalAnalyze
