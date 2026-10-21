/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Analyzer
import ProtSat.BoundedExec

/-!
# ProtSat: the verification contract (roadmap stage 1)

## Why this module exists

`ProtSat.Analyzer.analyze` answers a question about a *Boolean formula*: it reports
`Verdict.encodingUnsat` when `ProtSat.DPLL.dpll (encode P B)` returns `none`, and the proved
solver theorem (`ProtSat.DPLL.dpll_complete`) says only that the generated CNF has no model.
The question a user asks is about a *protocol*: no execution the model permits violates a security
property I selected. Those two coincide exactly when the encoding is complete for every selected
property - and today it is complete for secrecy and not for authentication agreement, because
`ProtSat.Encode.violationLits` contains only leak literals.

The review witnesses are kernel-checked: `ProtSat.Regressions.Authentication` has
`analyze P B = Verdict.encodingUnsat` and `BoundedAttack P B` holding at the same time.

So this module states the contract instead of gesturing at it:

* `Query` is the one object a verdict is about: the protocol, the bounds, and the **selected
  goals**. Domains and compromise assumptions are model data inside `Protocol`, so a query cannot
  quietly disagree with the protocol it names.
* `Goal` names a security property; `encodedGoals` records which of them the CNF can represent
  a violation of. That is the gap, in the API rather than in a comment.
* `Violation`, `boundedAttackFor`, `boundedAttackGoals`, `boundedSafeGoals` give the
  goal-indexed semantics of "the query has an attack" and "the query is safe", stated over the
  reference semantics only, so this is the target the encoding is measured against.
* `validate` is a decidable model checker and `WellFormed` is the proposition it decides.
* `Result` is the answer type with the categories the contract needs, and `analyzeQuery` is the
  reference analyser. The theorems in the acceptance-gate section are the point: a query whose
  selected goals the encoding does not represent gets **no security verdict**, an empty goal set
  gets `noGoals`, a malformed model gets `invalidModel`, the total reference analyser never
  answers `unknown`, and nothing answers `boundedSafe` at all until the encoding catches up.

## What each answer means

| `analyzeQuery q`      | what is proved                                                     |
|-------------------------|--------------------------------------------------------------------|
| `attack c`            | `checkCertificate q.protocol c = true`, hence a real `Attack`  |
| `encodingUnsat`       | `ProtSat.Unsat (encode ...)` - a fact about the CNF             |
| `boundedSafe e`       | never produced; when it is, `e : SafeEvidence` carries the proof |
| `unsupportedGoals us` | the selected goals `us` are not represented by the encoding      |
| `noGoals`             | the query selected nothing                                         |
| `invalidModel ds`     | the model fails validation; `ds` says where                      |
| `boundsTooSmall`      | the bounds cannot name the protocol's own closed messages          |
| `unknown _`           | reserved for a resource-bounded driver; the reference one is total |

The bridge from `encodingUnsat` to a security statement is `boundedSafe_of_encodingUnsat`;
read its hypotheses as the list of things stages 3 and 4 of the roadmap still have to discharge.
-/

namespace ProtSat

open Term Protocol Bounded Encode Encoding Complete Certificate Analyzer DPLL

/-! ### The selected goals -/

/-- A security property a query can select.

* `secrecy`: no declared secret (`ProtSat.Secret`, in either form) ever reaches the attacker;
* `agreement`: non-injective agreement - every `commit` is matched by a `claim` of the same
  tag, peer and value somewhere in the run (`ProtSat.AuthBreak` is its failure);
* `agreementInj`: injective agreement - distinct commits need distinct earlier matching claims
  (`ProtSat.Reference.agreesInj`, with its own proved monitor `ProtSat.Reference.agreesInjBool`).
  It is a separate goal rather than a flag on `agreement` because the two can disagree on the same
  model: one claim excused by nothing is a non-injective failure too, while two commits sharing one
  claim passes the first and fails the second (`ProtSat.Reference.Gates.replayP`). -/
inductive Goal where
  | secrecy : Goal
  | agreement : Goal
  | agreementInj : Goal
  deriving Repr, DecidableEq

/-- The goals whose violation the generated CNF demands. `Encode.violationLits` builds one
literal per way a declared secret can become known at some step, and nothing else, so secrecy is the
only goal the encoding can ask about. Adding the authentication violation clauses is roadmap stage
4; when that happens this list grows and the gate theorems below begin to admit agreement queries
instead of refusing them. -/
def encodedGoals : List Goal := [Goal.secrecy]

/-- Is a selected goal represented by the encoding? -/
def goalEncoded (g : Goal) : Bool := g ∈ encodedGoals

theorem goalEncoded_secrecy : goalEncoded Goal.secrecy = true := by
  simp [goalEncoded, encodedGoals]

theorem not_goalEncoded_agreement : goalEncoded Goal.agreement = false := by
  simp [goalEncoded, encodedGoals]

theorem not_goalEncoded_agreementInj : goalEncoded Goal.agreementInj = false := by
  simp [goalEncoded, encodedGoals]

theorem goalEncoded_iff (g : Goal) : goalEncoded g = true <-> g = Goal.secrecy := by
  cases g
  · simp [goalEncoded_secrecy]
  · simp [not_goalEncoded_agreement]
  · simp [not_goalEncoded_agreementInj]

/-! ### The query -/

/-- **A verification query**: the single object every verdict and every evidence artifact refers to.
The protocol carries the role and session instantiation, the principal, nonce and key domains, the
initial attacker knowledge and the compromise assumptions (`Protocol.initKn`,
`Protocol.compromised`); `Bounds` carries the execution bound and the message-depth bound;
`goals` carries which security properties the answer is about. -/
structure Query where
  /-- The protocol model: roles, sessions, domains, compromise set, declarations. -/
  protocol : Protocol
  /-- The bounds of the bounded-model-checking question. -/
  bounds : Bounds
  /-- The security properties the answer is about. -/
  goals : List Goal
  deriving Repr

/-! ### Goal-indexed attacks -/

/-- The executions that violate goal `g`. Stated over the reference semantics only: no SAT object
appears here, which is what makes this the target the encoding is measured against. -/
def Violation (P : Protocol) : Goal -> List Cfg -> List Ev -> Prop
  | Goal.secrecy, Cs, tr => runsLeaks P Cs
  | Goal.agreement, Cs, tr => AuthBreak P Cs tr
  | Goal.agreementInj, _Cs, _tr => True

theorem violation_secrecy (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    Violation P Goal.secrecy Cs tr <-> runsLeaks P Cs := Iff.rfl

theorem violation_agreement (P : Protocol) (Cs : List Cfg) (tr : List Ev) :
    Violation P Goal.agreement Cs tr <-> AuthBreak P Cs tr := Iff.rfl

/-- The old semantics has no injective monitor, so every run counts as violating that goal. This is
deliberate and it is the safe direction: a contract cannot report safety for a property it has no
semantics for. The CNF route refuses such a query anyway (`goalEncoded`), and the deciding contract
`ProtSat.Reference.Contract` gives the goal its real semantics. -/
theorem violation_agreementInj (P : Protocol) :
    ∀ (Cs : List Cfg) (tr : List Ev), Violation P Goal.agreementInj Cs tr := fun _ _ => trivial

/-- An attack on query `q` through goal `g`: a bounded execution of the query's protocol within
the query's bounds that violates `g`. -/
def boundedAttackFor (q : Query) (g : Goal) : Prop :=
  ∃ (tr : List Ev) (Cs : List Cfg),
    BoundedTrace q.protocol q.bounds tr Cs ∧ Violation q.protocol g Cs tr

/-- The query has an attack: some **selected** goal is violated by some permitted execution. -/
def boundedAttackGoals (q : Query) : Prop := ∃ g ∈ q.goals, boundedAttackFor q g

/-- **The intended meaning of SAFE**: no execution permitted by the query's model and bounds
violates any goal the query selected. -/
def boundedSafeGoals (q : Query) : Prop := ¬ boundedAttackGoals q

/-- With both goals selected, the goal-indexed predicate is exactly the public
`ProtSat.Bounded.BoundedAttack`: the tie between the new contract and the definition the encoding
theorems were stated against. -/
theorem boundedAttackGoals_iff_BoundedAttack (P : Protocol) (B : Bounds) :
    boundedAttackGoals (Query.mk P B [Goal.secrecy, Goal.agreement]) <-> BoundedAttack P B := by
  unfold boundedAttackGoals boundedAttackFor BoundedAttack
  constructor
  · rintro ⟨g, hg, tr, Cs, hbt, hv⟩
    cases g
    · exact ⟨tr, Cs, hbt, Or.inl (by rwa [violation_secrecy] at hv)⟩
    · exact ⟨tr, Cs, hbt, Or.inr (by rwa [violation_agreement] at hv)⟩
    · exact absurd hg (by simp)
  · rintro ⟨tr, Cs, hbt, h | h⟩
    · exact ⟨Goal.secrecy, by simp, tr, Cs, hbt, h⟩
    · exact ⟨Goal.agreement, by simp [List.mem_cons], tr, Cs, hbt, h⟩

/-- Selecting no goal makes `boundedAttackGoals` false for a purely logical reason: there is
nothing to violate. This is why `analyzeQuery` answers `noGoals` instead of a safety verdict. -/
theorem not_boundedAttackGoals_of_nil (P : Protocol) (B : Bounds) :
    ¬ boundedAttackGoals (Query.mk P B []) := by
  intro ⟨g, hg, _⟩
  exact absurd hg (by simp)

/-! ### Model validation -/

/-- Why a model was rejected. Each constructor names a declaration that makes the question
unanswerable as posed; the point is that these are *reported*, not silently repaired. In particular
`closedSecretNotClosed` and `closedSecretUndefined` exist because `Protocol.closedSecretTerms`
is a `filterMap`: a secret whose expression is open, or which denotes nothing, currently
disappears from the set of secrets, and a run would then be called safe because the declaration
never existed. -/
inductive Diagnostic where
  | roleOutOfRange (sess role : Nat)
  | selfNotInDomain (sess : Nat) (a : Agent)
  | peerNotInDomain (sess : Nat) (a : Agent)
  | closedSecretNotClosed (e : Expr)
  | closedSecretUndefined (e : Expr)
  | storeSecretSessionOutOfRange (q : Nat)
  | storeSecretUnusedVar (q x : Nat)
  | compromisedNotInDomain (a : Agent)
  | authTagUnused (tag : Tag)
  deriving Repr, DecidableEq

/-- The authentication events the instantiated sessions really perform: a `claim` is recorded as
`false`, a `commit` as `true`, each with its tag. -/
def authEvents (P : Protocol) : List (Bool × Tag) :=
  (List.range P.sessions.length).flatMap fun qq =>
    (List.range (P.roleLen qq)).flatMap fun pc =>
      match P.actionAt qq pc with
      | some (Action.claim tag _ _) => [(false, tag)]
      | some (Action.commit tag _ _) => [(true, tag)]
      | _ => []

/-- Sessions must name a role that exists and principals that are in the domain: a session whose
role index is out of range has `actionAt = none` everywhere, so it is a dead participant that
still consumes the session bound. -/
def validateSessions (P : Protocol) : List Diagnostic :=
  (List.range P.sessions.length).flatMap fun i =>
    match rget P.sessions i with
    | none => []
    | some s =>
        (if s.role < P.roles.length then [] else [Diagnostic.roleOutOfRange i s.role])
          ++ (if s.self ∈ P.agents then [] else [Diagnostic.selfNotInDomain i s.self])
          ++ (if s.peer ∈ P.agents then [] else [Diagnostic.peerNotInDomain i s.peer])

/-- A `Secret.closed e` must be closed and must denote, or else `closedSecretTerms` drops it. A
`Secret.store q x` must name an instantiated session and a variable that session actually uses;
otherwise no configuration can ever make it leak and the declaration is decoration. -/
def validateSecrets (P : Protocol) : List Diagnostic :=
  P.secrets.flatMap fun sc =>
    match sc with
    | Secret.closed e =>
        (if Expr.isClosed e then [] else [Diagnostic.closedSecretNotClosed e])
          ++ (if (Expr.eval e []).isSome then [] else [Diagnostic.closedSecretUndefined e])
    | Secret.store qq xx =>
        (if qq < P.sessions.length then [] else [Diagnostic.storeSecretSessionOutOfRange qq])
          ++ (if xx ∈ P.sessionVars qq then [] else [Diagnostic.storeSecretUnusedVar qq xx])

/-- A compromised principal must be in the agent domain: `Protocol.compromisedKeys` forms
`Key.shrk a b` for `b` ranging over `P.agents`, so a name outside the domain is a key that is
announced as revealed but never provisioned. -/
def validateCompromised (P : Protocol) : List Diagnostic :=
  P.compromised.filterMap fun a =>
    if a ∈ P.agents then none else some (Diagnostic.compromisedNotInDomain a)

/-- An `auths` entry whose tag no instantiated session claims or commits can never be violated and
can never be satisfied: it is a property the model does not express. This is the vacuity check the
review asked for - the Needham-Schroeder examples of `ProtSat.Examples` declare no authentication
events at all, so an authentication claim about them must not be answerable. -/
def validateAuths (P : Protocol) : List Diagnostic :=
  P.auths.filterMap fun ap =>
    if authEvents P |>.any (fun e => e.2 == ap.tag) then none
    else some (Diagnostic.authTagUnused ap.tag)

/-- The decidable validator. The authentication check runs only when the query actually selected
agreement: a secrecy question is not ill-formed because it ignores an unused tag. -/
def validate (q : Query) : List Diagnostic :=
  validateSessions q.protocol ++ validateSecrets q.protocol
    ++ validateCompromised q.protocol
    ++ if Goal.agreement ∈ q.goals || Goal.agreementInj ∈ q.goals then
         validateAuths q.protocol
       else []

/-- **Well-formedness of a query**: the proposition the validator decides. Every condition is a
finite membership test over the query's own protocol, so defining the proposition as "the validator
produces no diagnostic" keeps the two from drifting apart; the content of the notion is the list of
`Diagnostic` constructors. -/
def WellFormed (q : Query) : Prop := validate q = []

theorem wellFormed_iff_isEmpty {q : Query} : WellFormed q <-> (validate q).isEmpty = true := by
  rw [WellFormed]
  constructor
  · intro h; simp [h]
  · intro h; simpa using h

/-! ### The answer -/

/-- Why the analyser could not answer. The total mathematical analyser never produces one of these
(`analyzeQuery_ne_unknown`); they exist so that a resource-bounded production driver can share the
same result type and the same theorems about it. -/
inductive UnknownReason where
  | resourceExhausted : UnknownReason
  | solverFailure : UnknownReason
  deriving Repr, DecidableEq

/-- Evidence for a bounded-safety verdict: the query it is evidence *for*, and the proof that no
bounded execution of that query violates any of its selected goals. A verdict is therefore
inseparable from the question it answers: an evidence record cannot be replayed against a different
protocol, bounds, or goal set, because its `safe` field is a proposition about `query`. Nothing
constructs one yet - see `analyzeQuery_ne_boundedSafe`. -/
structure SafeEvidence where
  query : Query
  safe : boundedSafeGoals query

/-- The analyser's answer; see the module header for what each case means. -/
inductive Result where
  | invalidModel : List Diagnostic -> Result
  | noGoals : Result
  | unsupportedGoals : List Goal -> Result
  | boundsTooSmall : Result
  | encodingUnsat : Result
  | attack : Certificate -> Result
  | unknown : UnknownReason -> Result
  | boundedSafe : SafeEvidence -> Result

/-- Which answers assert something about the protocol's security. `encodingUnsat` is deliberately
not one of them: it asserts something about a formula. -/
def securityResult : Result -> Bool
  | Result.attack _ => true
  | Result.boundedSafe _ => true
  | _ => false

/-- The selected goals the encoding cannot represent. -/
def unsupported (q : Query) : List Goal := q.goals.filter fun g => ! goalEncoded g

/-- The low-level verdict, seen as an answer of the contract. The two "no model" cases are kept
apart on purpose: `Verdict.encodingUnsat` is the formula fact, and only `Result.boundedSafe`
is a security claim. -/
def liftVerdict : Verdict -> Result
  | Verdict.boundsTooSmall => Result.boundsTooSmall
  | Verdict.encodingUnsat => Result.encodingUnsat
  | Verdict.attack c => Result.attack c

@[simp] theorem liftVerdict_boundsTooSmall :
    liftVerdict Verdict.boundsTooSmall = Result.boundsTooSmall := rfl

@[simp] theorem liftVerdict_encodingUnsat :
    liftVerdict Verdict.encodingUnsat = Result.encodingUnsat := rfl

@[simp] theorem liftVerdict_attack (c : Certificate) :
    liftVerdict (Verdict.attack c) = Result.attack c := rfl

/-- **The reference analyser**, stated over a query: validation first, then the goal-selection gate,
then the low-level analyser (bounds precheck and solver). -/
def analyzeQuery (q : Query) : Result :=
  if (validate q).isEmpty then
    if q.goals.isEmpty then Result.noGoals
    else if ! (unsupported q).isEmpty then Result.unsupportedGoals (unsupported q)
    else liftVerdict (analyze q.protocol q.bounds)
  else Result.invalidModel (validate q)

/-! ### The acceptance gate -/

/-- The three cases of `liftVerdict`, told apart. These are the lemmas the gate theorems below use
instead of case-splitting inside an equation about the analyser. -/
theorem liftVerdict_ne_boundedSafe (e : SafeEvidence) (v : Verdict) :
    liftVerdict v ≠ Result.boundedSafe e := by
  cases v
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

theorem liftVerdict_ne_unknown (u : UnknownReason) (v : Verdict) :
    liftVerdict v ≠ Result.unknown u := by
  cases v
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

theorem liftVerdict_eq_encodingUnsat_iff (v : Verdict) :
    liftVerdict v = Result.encodingUnsat <-> v = Verdict.encodingUnsat := by
  cases v <;> simp [liftVerdict]

theorem liftVerdict_eq_attack_iff (v : Verdict) (c : Certificate) :
    liftVerdict v = Result.attack c <-> v = Verdict.attack c := by
  cases v <;> simp [liftVerdict]

/-- A malformed model gets `invalidModel`, and nothing else. -/
theorem analyzeQuery_invalidModel_of_diagnostics {q : Query}
    (h : ¬ (validate q).isEmpty) : analyzeQuery q = Result.invalidModel (validate q) := by
  rw [analyzeQuery, if_neg h]

/-- A malformed model gets no security verdict. -/
theorem not_securityResult_of_diagnostics {q : Query}
    (h : ¬ (validate q).isEmpty) : securityResult (analyzeQuery q) = false := by
  rw [analyzeQuery_invalidModel_of_diagnostics h]
  simp [securityResult]

/-- A query that selects nothing gets `noGoals` rather than a vacuous safety verdict. -/
theorem analyzeQuery_noGoals_of_empty {q : Query}
    (hval : (validate q).isEmpty) (h : q.goals.isEmpty) : analyzeQuery q = Result.noGoals := by
  rw [analyzeQuery, if_pos hval, if_pos h]

/-- A query that selects nothing gets no security verdict. -/
theorem not_securityResult_of_noGoals {q : Query}
    (hval : (validate q).isEmpty) (h : q.goals.isEmpty) :
    securityResult (analyzeQuery q) = false := by
  rw [analyzeQuery_noGoals_of_empty hval h]
  simp [securityResult]

/-- Some selected goal is not represented by the encoding: the filter is nonempty. -/
theorem unsupported_ne_nil {q : Query} (h : ∃ g ∈ q.goals, ! goalEncoded g) :
    ! (unsupported q).isEmpty := by
  obtain ⟨g, hg, hne⟩ := h
  have hmem : g ∈ unsupported q := List.mem_filter.mpr ⟨hg, hne⟩
  cases h' : unsupported q with
  | nil => rw [h'] at hmem; simp at hmem
  | cons _ _ => rfl

/-- A query selecting a goal the encoding does not represent gets `unsupportedGoals`. -/
theorem analyzeQuery_unsupported_of_unencoded {q : Query}
    (hval : (validate q).isEmpty) (hg : ¬ q.goals.isEmpty)
    (h : ∃ g ∈ q.goals, ! goalEncoded g) :
    analyzeQuery q = Result.unsupportedGoals (unsupported q) := by
  rw [analyzeQuery, if_pos hval, if_neg hg, if_pos (unsupported_ne_nil h)]

/-- **Gate, first form.** Selecting a goal the encoding cannot represent means the analyser does not
answer with a security verdict. This is the property the review asked for: the commit-only
authentication witness cannot receive a SAFE result. -/
theorem analyzeQuery_not_security_of_unencoded {q : Query}
    (h : ∃ g ∈ q.goals, ! goalEncoded g) : securityResult (analyzeQuery q) = false := by
  by_cases hval : (validate q).isEmpty
  · by_cases hg : q.goals.isEmpty
    · rw [analyzeQuery_noGoals_of_empty hval hg]
      simp [securityResult]
    · rw [analyzeQuery_unsupported_of_unencoded hval hg h]
      simp [securityResult]
  · rw [analyzeQuery_invalidModel_of_diagnostics hval]
    simp [securityResult]

/-- **Gate, second form.** An agreement query never even gets the unsatisfiability answer: the tool
refuses rather than answering a different question. -/
theorem analyzeQuery_ne_encodingUnsat_of_agreement {q : Query}
    (h : Goal.agreement ∈ q.goals) : analyzeQuery q ≠ Result.encodingUnsat := by
  have hsel : ! goalEncoded Goal.agreement := by simp [goalEncoded, encodedGoals]
  by_cases hval : (validate q).isEmpty
  · have hg : ¬ q.goals.isEmpty := by
      intro hh
      cases hq : q.goals with
      | nil => rw [hq] at h; simp at h
      | cons _ _ => rw [hq] at hh; simp at hh
    rw [analyzeQuery_unsupported_of_unencoded hval hg ⟨Goal.agreement, h, hsel⟩]
    intro hc; cases hc
  · rw [analyzeQuery_invalidModel_of_diagnostics hval]
    intro hc; cases hc

/-- **Gate, third form.** Nothing the analyser computes is a `boundedSafe` verdict: the security
label is not issued at all until the encoding covers the selected goals. -/
theorem analyzeQuery_ne_boundedSafe {q : Query} (e : SafeEvidence) :
    analyzeQuery q ≠ Result.boundedSafe e := by
  by_cases hval : (validate q).isEmpty
  · by_cases hg : q.goals.isEmpty
    · rw [analyzeQuery, if_pos hval, if_pos hg]
      intro hc; cases hc
    · by_cases hu : ! (unsupported q).isEmpty
      · rw [analyzeQuery, if_pos hval, if_neg hg, if_pos hu]
        intro hc; cases hc
      · rw [analyzeQuery, if_pos hval, if_neg hg, if_neg hu]
        exact liftVerdict_ne_boundedSafe e (analyze q.protocol q.bounds)
  · rw [analyzeQuery, if_neg hval]
    intro hc; cases hc

/-- **Gate, fourth form.** The reference analyser is total and never reports a resource failure. -/
theorem analyzeQuery_ne_unknown {q : Query} (u : UnknownReason) :
    analyzeQuery q ≠ Result.unknown u := by
  by_cases hval : (validate q).isEmpty
  · by_cases hg : q.goals.isEmpty
    · rw [analyzeQuery, if_pos hval, if_pos hg]
      intro hc; cases hc
    · by_cases hu : ! (unsupported q).isEmpty
      · rw [analyzeQuery, if_pos hval, if_neg hg, if_pos hu]
        intro hc; cases hc
      · rw [analyzeQuery, if_pos hval, if_neg hg, if_neg hu]
        exact liftVerdict_ne_unknown u (analyze q.protocol q.bounds)
  · rw [analyzeQuery, if_neg hval]
    intro hc; cases hc

/-! ### What the answers mean -/

/-- The two facts an `encodingUnsat` answer of the low-level analyser is made of: the bounds cover
the protocol, and the solver found no model. -/
theorem analyze_encodingUnsat_facts {P : Protocol} {B : Bounds}
    (h : analyze P B = Verdict.encodingUnsat) :
    univClosedBool (shapeOf P B) P = true ∧ dpll (Encode.encode P B) = none := by
  by_cases hu : univClosedBool (shapeOf P B) P
  · have hnone : dpll (Encode.encode P B) = none := by
      cases hd : dpll (Encode.encode P B) with
      | none => rfl
      | some asg =>
          rw [analyze, if_neg (by simp [hu]), hd] at h
          cases h
    exact ⟨hu, hnone⟩
  · rw [analyze, if_pos (by simp [hu])] at h
    cases h

/-- If the query analyser reached the solver and got an unsatisfiability answer, so did the
low-level analyser. -/
theorem analyze_of_analyzeQuery_encodingUnsat {q : Query}
    (h : analyzeQuery q = Result.encodingUnsat) :
    analyze q.protocol q.bounds = Verdict.encodingUnsat := by
  by_cases hv : (validate q).isEmpty
  · by_cases hg : q.goals.isEmpty
    · rw [analyzeQuery, if_pos hv, if_pos hg] at h
      cases h
    · by_cases hu : ! (unsupported q).isEmpty
      · rw [analyzeQuery, if_pos hv, if_neg hg, if_pos hu] at h
        cases h
      · rw [analyzeQuery, if_pos hv, if_neg hg, if_neg hu] at h
        exact (liftVerdict_eq_encodingUnsat_iff _).mp h
  · rw [analyzeQuery, if_neg hv] at h
    cases h

/-- An `encodingUnsat` answer is exactly the solver's proof that the CNF has no model. This is the
whole content of the answer, and it is what the rename from `safe` records. -/
theorem analyzeQuery_encodingUnsat_unsat {q : Query}
    (h : analyzeQuery q = Result.encodingUnsat) :
    ProtSat.Unsat (Encode.encode q.protocol q.bounds) :=
  DPLL.dpll_complete (analyze_encodingUnsat_facts (analyze_of_analyzeQuery_encodingUnsat h)).2

/-- The bounds really do cover the protocol when an `encodingUnsat` answer comes out. -/
theorem univClosed_of_analyzeQuery_encodingUnsat {q : Query}
    (h : analyzeQuery q = Result.encodingUnsat) :
    univClosed (shapeOf q.protocol q.bounds) q.protocol :=
  (univClosedBool_iff (shapeOf q.protocol q.bounds) q.protocol).mp
    (analyze_encodingUnsat_facts (analyze_of_analyzeQuery_encodingUnsat h)).1

/-- If the query analyser reached the solver and produced a certificate, so did the low-level
analyser, with the same certificate. -/
theorem analyze_of_analyzeQuery_attack {q : Query} {c : Certificate}
    (h : analyzeQuery q = Result.attack c) :
    analyze q.protocol q.bounds = Verdict.attack c := by
  by_cases hv : (validate q).isEmpty
  · by_cases hg : q.goals.isEmpty
    · rw [analyzeQuery, if_pos hv, if_pos hg] at h
      cases h
    · by_cases hu : ! (unsupported q).isEmpty
      · rw [analyzeQuery, if_pos hv, if_neg hg, if_pos hu] at h
        cases h
      · rw [analyzeQuery, if_pos hv, if_neg hg, if_neg hu] at h
        exact (liftVerdict_eq_attack_iff _ _).mp h
  · rw [analyzeQuery, if_neg hv] at h
    cases h

/-- An `attack` answer is a certificate the independent checker accepts, and hence a genuine attack
trace of the reference semantics within the step bound. Inherited from
`ProtSat.Analyzer.analyze_attack_bounded`; note that the certificate checker does not yet verify
the message-universe bound, which is roadmap stage 5. -/
theorem analyzeQuery_attack_sound {q : Query} {c : Certificate}
    (h : analyzeQuery q = Result.attack c) :
    checkCertificate q.protocol c = true ∧ Attack q.protocol (certTrace c) ∧
      (certTrace c).length ≤ q.bounds.steps := by
  have hana := analyze_of_analyzeQuery_attack h
  refine ⟨(analyze_attack_sound hana).1, (analyze_attack_bounded hana).1,
    (analyze_attack_bounded hana).2⟩

/-- **The conditional bridge, stated honestly.** If every selected goal is represented by the
encoding, the bounds cover the protocol and its secrets, and every bounded execution is
representable by the encoding, then an `encodingUnsat` answer means the query is safe.

The last hypothesis is the gap roadmap stages 3 and 4 have to close: `WithinBounds` is a
per-execution side condition the compiler adds, not something the public bounded predicate promises.
`ProtSat.Regressions.Bounds` exhibits a bounded execution that fails it. -/
theorem boundedSafe_of_encodingUnsat {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hwb : ∀ (tr : List Ev) (Cs : List Cfg), BoundedTrace q.protocol q.bounds tr Cs ->
        WithinBounds q.protocol q.bounds (cfgAt Cs) (evAt tr))
    (h : analyzeQuery q = Result.encodingUnsat) : boundedSafeGoals q := by
  intro ⟨g, hg, tr, Cs, hbt, hv⟩
  have henc : goalEncoded g = true := hq g hg
  rw [goalEncoded_iff] at henc
  subst henc
  rw [violation_secrecy] at hv
  exact analyze_safe_sound hU hsecStore (analyze_of_analyzeQuery_encodingUnsat h)
    ⟨tr, Cs, hbt.1, hbt.2.1, hv, hwb tr Cs hbt⟩

/-- **The bridge with the residual hypothesis.** `WithinBounds` has twelve conditions; eleven of
them are now theorems about the public bound (`ProtSat/BoundedExec.lean`), and exactly one remains:
expression representability (`Residual.exprB`), the dummy-field half of `actB` having become
`actB_of_bounded`. Stating the bridge in terms of `BoundedExec.Residual` is therefore a strict
weakening of `boundedSafe_of_encodingUnsat`: whatever is known about a query's bounded executions
now has to be assumed about one named property with a documented repair site, instead of about the
whole bundle. -/
theorem boundedSafe_of_encodingUnsat_of_residual {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hres : ∀ (tr : List Ev) (Cs : List Cfg), BoundedTrace q.protocol q.bounds tr Cs →
        BoundedExec.Residual q.protocol q.bounds tr Cs)
    (h : analyzeQuery q = Result.encodingUnsat) : boundedSafeGoals q :=
  boundedSafe_of_encodingUnsat hq hne hU hsecStore
    (fun tr Cs hbt => BoundedExec.withinBounds_of_residual hbt (hres tr Cs hbt)) h

/-- The residual is not vacuously satisfiable in the old semantics: `BoundedExec.exprB_not_derivable`
exhibits a bounded execution of a concrete query with no `Residual`, so this hypothesis - like the
one it replaces - is a real condition, not a formality. -/
theorem residual_is_a_real_condition :
    ¬ (∀ (tr : List Ev) (Cs : List Cfg),
        BoundedTrace BoundedExec.P0 BoundedExec.B0 tr Cs →
          BoundedExec.Residual BoundedExec.P0 BoundedExec.B0 tr Cs) := fun hall =>
  BoundedExec.exprB_not_derivable
    (fun tr Cs hbt i q e he => (hall tr Cs hbt).exprB i q e he)

/-- **The bridge with no execution hypothesis.** For a query whose value domain reports no gap -
  decidable from the protocol and the bounds alone - every bounded execution is representable, so
  an unsatisfiable encoding is a bounded-security theorem about the *protocol*, not about a
  bundle of assumptions on its runs. This is roadmap stage 4 gate met for the gap-free class;
  `Represent.domainGap` is the check that says whether a query is in it. -/
theorem boundedSafe_of_encodingUnsat_of_gapFree {q : Query}
    (hq : ∀ g ∈ q.goals, goalEncoded g) (hne : q.goals ≠ [])
    (hU : univClosed (shapeOf q.protocol q.bounds) q.protocol)
    (hsecStore : SecretsOKStore (shapeOf q.protocol q.bounds) q.protocol)
    (hgap : Represent.domainGap q.protocol q.bounds = false)
    (h : analyzeQuery q = Result.encodingUnsat) : boundedSafeGoals q :=
  boundedSafe_of_encodingUnsat hq hne hU hsecStore
    (fun tr Cs hbt => BoundedExec.withinBounds_of_bounded hbt hgap) h

/-! ### Display -/

/-- One-line rendering of an answer, for the command-line driver. -/
def describe : Result -> String
  | Result.invalidModel ds =>
      "INVALID MODEL (" ++ toString ds.length ++ " diagnostics)"
  | Result.noGoals => "NO GOALS SELECTED (nothing was asked)"
  | Result.unsupportedGoals us =>
      "UNSUPPORTED GOALS (" ++ toString us.length ++
        " selected): the encoding cannot represent their violation"
  | Result.boundsTooSmall => "BOUNDS TOO SMALL (univClosed fails: raise Bounds.rounds)"
  | Result.encodingUnsat =>
      "ENCODING UNSAT (the generated CNF has no satisfying assignment)"
  | Result.attack c => "ATTACK (" ++ toString c.steps.length ++ " events); certificate accepted"
  | Result.unknown UnknownReason.resourceExhausted => "UNKNOWN (resource exhausted)"
  | Result.unknown UnknownReason.solverFailure => "UNKNOWN (solver failure)"
  | Result.boundedSafe _ => "BOUNDED SAFE (evidence carried)"

end ProtSat
