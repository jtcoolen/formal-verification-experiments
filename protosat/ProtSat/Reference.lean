/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Bounded
import ProtSat.Certificate

/-!
# ProtSat: the repaired reference semantics (roadmap stage 2)

## Why a second semantics module

`ProtSat.Operational` is the semantics the SAT correspondence (8A, 8B) is proved against, and
those proofs are eight thousand lines long; changing it would invalidate them. The review found
defects in it that must be fixed before the correspondence can mean anything, so this module
states the *repaired* reference semantics, independently of SAT, and the defects become theorems
here rather than comments there.

* **Freshness is an allocation history, not a reading of the current stores.**
  `ProtSat.nonceUsed` looks at what sessions store *now*, so a nonce that was generated and then
  overwritten, or generated and then nested inside a pair, counts as unused and can be generated
  again (`Regressions.Semantics.nested_reuse_accepted`). Here `Cfg.alloc` is a monotone history
  of every nonce a generation event has allocated: `not_generate_allocated` says a value already
  in the history can never be generated again, and `alloc_mono` says the history never shrinks.
* **Events carry what they actually need.** `ProtSat.Ev.act q m d` supplies a message and a nonce
  to *every* session action, and the encoding's `RunOK.actB` then demands `d ∈ sh.D` even for a
  send or a check, so a protocol with an empty nonce domain cannot be represented at all. Here an
  event is `idle`, `ded t`, `recv q m`, `generate q n` or `act q`: a receive carries the
  delivered message, a generation carries the fresh identity, and a deterministic action carries
  nothing. What a send publishes and which authentication event happened are derived from the
  action that was executed (`instAt`). `Gates.empty_domain_run` exhibits a receive-check-send
  run in a model whose nonce domain is empty.
* **A malformed annotation blocks instead of vanishing.** `ProtSat.authOfStep` evaluates the peer
  and value of a claim or commit and, when evaluation fails, returns the empty list: the session
  advances and the annotation is silently erased
  (`Regressions.Semantics.unset_commit_produces_nothing`). Here a claim or commit is enabled only
  when its peer evaluates to an agent and its value evaluates at all (`Gates.claim_blocked`).
* **Agreement is ordered and role-aware.** `ProtSat.AuthBreak` asks only that the committed
  (tag, peer, value) triple appear *somewhere* among the claims, so a later claim excuses an
  earlier commit and a claim by the wrong principal excuses a commit
  (`Regressions.Semantics.later_claim_excuses_commit`). Here a commit must be matched by a
  strictly earlier claim *from the peer it believes it talked to* (`claimMatches`), and injective
  agreement is a separate monitor (`agreesInj`) with an example that separates the two.

## What is not here yet

Secret obligations with snapshot persistence, role parameterisation by self/peer, and the
credential-provisioning discipline for decryption (roadmap stage 2b), and any connection to the
encoding: the correspondence between this semantics and the CNF is what stages 3-4 build. Nothing
here imports `ProtSat.CNF`, `Encode`, `Encoding`, `Complete` or `DPLL`.
-/

namespace ProtSat.Reference

open ProtSat Term Protocol Attacker

/-! ### Configurations -/

/-- A configuration: the local state of every session, the attacker's knowledge, the **allocation
history** of every nonce this run has generated, and the **secret obligations** the run has
undertaken.

The history is part of the state because freshness cannot be recovered from the stores: a nonce
stops being visible the moment it is overwritten or wrapped into a pair, but it does not stop being
used. The obligations are part of the state for the same reason one step further on: a value
declared secret at some event stays secret after the register that held it is overwritten, and a
check that reads the current store forgets the promise (`ProtSat.Secret.store` does exactly
that). -/
structure Cfg where
  sess : List SessState
  kn : List Term
  alloc : List NonceName
  oblig : List Term
  deriving Repr, DecidableEq

/-- The local state of session `q`. -/
def sessAt (C : Cfg) (q : Nat) : Option SessState := rget C.sess q

/-- The program counter of session `q` (0 if there is no such session). -/
def pcOf (C : Cfg) (q : Nat) : Nat := (sessAt C q).map (fun s => s.pc) |>.getD 0

/-- The store of session `q`. -/
def storeOf (C : Cfg) (q : Nat) : List (Var × Term) :=
  (sessAt C q).map (fun s => s.store) |>.getD []

/-- The initial configuration: every session at program counter 0 with an empty store, the
attacker holding exactly the public information and the compromised keys, and nothing allocated.
-/
def initCfg (P : Protocol) : Cfg :=
  { sess := P.sessions.map fun _ => { pc := 0, store := [] },
    kn := P.initKn, alloc := [], oblig := [] }

/-- Record a secret obligation: the *value* snapshot at the declaring event, not the register. -/
def declareObl (C : Cfg) (v : Term) : Cfg := { C with oblig := C.oblig ++ [v] }

@[simp] theorem declareObl_alloc (C : Cfg) (v : Term) : (declareObl C v).alloc = C.alloc := rfl
@[simp] theorem declareObl_kn (C : Cfg) (v : Term) : (declareObl C v).kn = C.kn := rfl
@[simp] theorem declareObl_oblig (C : Cfg) (v : Term) :
    (declareObl C v).oblig = C.oblig ++ [v] := rfl

/-! ### Events -/

/-- One event of the labelled transition system. Compare `ProtSat.Ev`, whose `act` carries a
message and a nonce whether or not the action needs them. -/
inductive Ev where
  | idle : Ev
  | ded : Term -> Ev
  | recv : Nat -> Term -> Ev
  | generate : Nat -> NonceName -> Ev
  | act : Nat -> Ev
  deriving Repr, DecidableEq

/-! ### Configuration updates -/

/-- Apply `f` to session `q`'s local state. -/
def mapSess (f : SessState -> SessState) (C : Cfg) (q : Nat) : Cfg :=
  { C with sess := rput f C.sess q }

/-- Publish a message to the attacker. -/
def publish (C : Cfg) (t : Term) : Cfg := { C with kn := C.kn ++ [t] }

/-- Record that a nonce value has been allocated. -/
def allocate (C : Cfg) (n : NonceName) : Cfg := { C with alloc := C.alloc ++ [n] }

@[simp] theorem publish_alloc (C : Cfg) (t : Term) : (publish C t).alloc = C.alloc := rfl
@[simp] theorem allocate_alloc (C : Cfg) (n : NonceName) : (allocate C n).alloc = C.alloc ++ [n] := rfl
@[simp] theorem mapSess_alloc (f : SessState -> SessState) (C : Cfg) (q : Nat) :
    (mapSess f C q).alloc = C.alloc := rfl
@[simp] theorem publish_kn (C : Cfg) (t : Term) : (publish C t).kn = C.kn ++ [t] := rfl
@[simp] theorem allocate_kn (C : Cfg) (n : NonceName) : (allocate C n).kn = C.kn := rfl
@[simp] theorem mapSess_kn (f : SessState -> SessState) (C : Cfg) (q : Nat) :
    (mapSess f C q).kn = C.kn := rfl

/-! ### Credential provisioning -/

/-- *Credential provisioning.*

`Expr.decA m a` decrypts with the private key of `a`, and `Expr.privk a` names that key: in
`Expr.eval` either is available to *any* role that writes it, so a role acquires the power to
decrypt for a principal merely by naming it, and can publish that principal's private key. The
repaired semantics makes the authority explicit: a session is provisioned with its own private key
and the long-term shared keys of its conversation, plus whatever key it has actually received, and
an expression that needs any other private key is not enabled. -/
def requiredPrivKeys (e : Expr) : List Agent :=
  (e.subexpressions.filterMap fun
    | Expr.privk a => some a
    | Expr.decA _ a => some a
    | _ => none).eraseDups

/-- The keys a session holds by right of its role: its own private key and the long-term keys of
its conversation. -/
def provisioned (P : Protocol) (q : Nat) : List Key :=
  match rget P.sessions q with
  | none => []
  | some s => Key.priv s.self :: [Key.shrk s.self s.peer, Key.shrk s.peer s.self]

/-- Every key appearing anywhere in a message. -/
def keysIn : Term -> List Key :=
  fun t => (Bounded.subtermsL t).filterMap fun
    | Term.key k => some k
    | _ => none

/-- The keys a session may use: its credentials plus every key it has received or stored. -/
def availableKeys (P : Protocol) (C : Cfg) (q : Nat) : List Key :=
  provisioned P q ++ (storeVals (storeOf C q)).flatMap keysIn

/-- May this session evaluate this expression? -/
def canUse (P : Protocol) (C : Cfg) (q : Nat) (e : Expr) : Bool :=
  (requiredPrivKeys e).all fun a => Key.priv a ∈ availableKeys P C q

/-- Is every expression the action reads within the session's authority? This is the gate that
`stepOf` applies before executing a deterministic action. -/
def actionUsable (P : Protocol) (C : Cfg) (q : Nat) (act : Action) : Bool :=
  (act.exprs).all fun e => canUse P C q e

/-! ### When an authentication annotation is meaningful -/

/-- The (peer, value) a claim or commit records, evaluated in the acting session's store. The peer
must be an *agent*: a claim whose peer expression does not evaluate to a principal says nothing, so
the action is not enabled rather than recorded with a placeholder. -/
def authData (P : Protocol) (C : Cfg) (q : Nat) (peer v : Expr) : Option (Agent × Term) :=
  match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
  | some (Term.agent a), some d => some (a, d)
  | _, _ => none

/-! ### The step function -/

/-- The successor a deterministic session action prescribes. Split out from `stepOf` so that
reasoning about it can case-split on the action itself. -/
def actStep (P : Protocol) (C : Cfg) (q : Nat) : Action -> Option Cfg
  | Action.send _ e => (Expr.eval e (storeOf C q)).map fun t => publish (mapSess bump C q) t
  | Action.assign x e => (Expr.eval e (storeOf C q)).map fun t => mapSess (bumpStore x t) C q
  | Action.check e1 e2 =>
      match Expr.eval e1 (storeOf C q), Expr.eval e2 (storeOf C q) with
      | some v1, some v2 => if v1 == v2 then some (mapSess bump C q) else none
      | _, _ => none
  | Action.secret e => (Expr.eval e (storeOf C q)).map fun v => declareObl (mapSess bump C q) v
  | Action.claim _ peer v =>
      if (authData P C q peer v).isSome then some (mapSess bump C q) else none
  | Action.commit _ peer v =>
      if (authData P C q peer v).isSome then some (mapSess bump C q) else none
  | Action.fresh _ _ => none
  | Action.recv _ _ => none

/-- The successor the semantics prescribes for one event, or `none` when the event is not enabled.
-/
def stepOf (P : Protocol) (C : Cfg) : Ev -> Option Cfg
  | Ev.idle => some C
  | Ev.ded t => if oneStepBool C.kn t then some (publish C t) else none
  | Ev.recv q m =>
      match P.actionAt q (pcOf C q) with
      | some (Action.recv _ x) => if m ∈ C.kn then some (mapSess (bumpStore x m) C q) else none
      | _ => none
  | Ev.generate q n =>
      match P.actionAt q (pcOf C q) with
      | some (Action.fresh x _) =>
          if n ∈ P.nonceDomain then
            if n ∈ C.alloc then none
            else some (allocate (mapSess (bumpStore x (Term.nonce n)) C q) n)
          else none
      | _ => none
  | Ev.act q =>
      match P.actionAt q (pcOf C q) with
      | some act => if actionUsable P C q act then actStep P C q act else none
      | none => none

/-- **The transition relation** of the repaired semantics: `C'` is what the step function
prescribes. Stating it as a function rather than an inductive is what makes the gate examples
checkable by the kernel, and it costs nothing: the relation is deterministic in the event. -/
def Rel (P : Protocol) (C : Cfg) (e : Ev) (C' : Cfg) : Prop := stepOf P C e = some C'

/-- Walk a trace, collecting the configurations it visits (the initial one first). -/
def run : (P : Protocol) -> Cfg -> List Ev -> Option (List Cfg)
  | _, C, [] => some [C]
  | P, C, e :: rest =>
      match stepOf P C e with
      | none => none
      | some C' => (run P C' rest).map fun Cs => C :: Cs

/-- `Runs P C0 tr Cs`: `tr` is a valid execution from `C0` visiting exactly `Cs`. -/
def Runs (P : Protocol) (C0 : Cfg) (tr : List Ev) (Cs : List Cfg) : Prop := run P C0 tr = some Cs

theorem runs_nil (P : Protocol) (C : Cfg) : Runs P C [] [C] := rfl

theorem runs_cons {P : Protocol} {C C' : Cfg} {e : Ev} {tr : List Ev} {rest : List Cfg}
    (hstep : Rel P C e C') (hrun : Runs P C' tr rest) : Runs P C (e :: tr) (C :: rest) := by
  unfold Runs at hrun ⊢
  unfold Rel at hstep
  simp [run, hstep, hrun]

/-- A run visits one more configuration than it has events. -/
theorem run_length : ∀ (P : Protocol) (tr : List Ev) (C : Cfg) (Cs : List Cfg),
    run P C tr = some Cs -> Cs.length = tr.length + 1 := by
  intro P tr
  induction tr with
  | nil =>
      intro C Cs h
      have := Option.some.inj h
      subst this
      rfl
  | cons e rest ih =>
      intro C Cs h
      cases hstep : stepOf P C e with
      | none => simp [run, hstep] at h
      | some C' =>
          cases hr : run P C' rest with
          | none => simp [run, hstep, hr] at h
          | some rest' =>
              simp [run, hstep, hr] at h
              subst h
              rw [List.length_cons, ih C' rest' hr]
              rfl

/-! ### Invariants of a step -/

/-- A deterministic action never touches the allocation history. -/
theorem alloc_eq_of_actStep {P : Protocol} {C C' : Cfg} {q : Nat} {act : Action}
    (h : actStep P C q act = some C') : C'.alloc = C.alloc := by
  cases act with
  | fresh _ _ => simp [actStep] at h
  | send a e =>
      cases he : Expr.eval e (storeOf C q) with
      | none => simp [actStep, he] at h
      | some t => simp [actStep, he] at h; subst h; simp
  | recv _ _ => simp [actStep] at h
  | assign x e =>
      cases he : Expr.eval e (storeOf C q) with
      | none => simp [actStep, he] at h
      | some t => simp [actStep, he] at h; subst h; simp
  | check e1 e2 =>
      cases he1 : Expr.eval e1 (storeOf C q) with
      | none => simp [actStep, he1] at h
      | some v1 =>
          cases he2 : Expr.eval e2 (storeOf C q) with
          | none => simp [actStep, he1, he2] at h
          | some v2 =>
              by_cases hv : v1 == v2
              · simp [actStep, he1, he2, hv] at h; subst h; rfl
              · simp [actStep, he1, he2, hv] at h
  | secret e =>
      cases he : Expr.eval e (storeOf C q) with
      | none => simp [actStep, he] at h
      | some t => simp [actStep, he] at h; subst h; rfl
  | claim tag peer v =>
      by_cases hd : (authData P C q peer v).isSome
      · simp [actStep, hd] at h; subst h; rfl
      · simp [actStep, hd] at h
  | commit tag peer v =>
      by_cases hd : (authData P C q peer v).isSome
      · simp [actStep, hd] at h; subst h; rfl
      · simp [actStep, hd] at h

/-- A deterministic action never removes knowledge. -/
theorem kn_mono_of_actStep {P : Protocol} {C C' : Cfg} {q : Nat} {act : Action}
    (h : actStep P C q act = some C') : ∀ t ∈ C.kn, t ∈ C'.kn := by
  cases act with
  | fresh _ _ => simp [actStep] at h
  | send a e =>
      cases he : Expr.eval e (storeOf C q) with
      | none => simp [actStep, he] at h
      | some t =>
          simp [actStep, he] at h
          subst h
          intro k hk
          rw [publish_kn]
          exact List.mem_append.mpr (Or.inl hk)
  | recv _ _ => simp [actStep] at h
  | assign x e =>
      cases he : Expr.eval e (storeOf C q) with
      | none => simp [actStep, he] at h
      | some t => simp [actStep, he] at h; subst h; exact fun k hk => hk
  | check e1 e2 =>
      cases he1 : Expr.eval e1 (storeOf C q) with
      | none => simp [actStep, he1] at h
      | some v1 =>
          cases he2 : Expr.eval e2 (storeOf C q) with
          | none => simp [actStep, he1, he2] at h
          | some v2 =>
              by_cases hv : v1 == v2
              · simp [actStep, he1, he2, hv] at h; subst h; exact fun k hk => hk
              · simp [actStep, he1, he2, hv] at h
  | secret e =>
      cases he : Expr.eval e (storeOf C q) with
      | none => simp [actStep, he] at h
      | some t => simp [actStep, he] at h; subst h; exact fun k hk => hk
  | claim tag peer v =>
      by_cases hd : (authData P C q peer v).isSome
      · simp [actStep, hd] at h; subst h; exact fun k hk => hk
      · simp [actStep, hd] at h
  | commit tag peer v =>
      by_cases hd : (authData P C q peer v).isSome
      · simp [actStep, hd] at h; subst h; exact fun k hk => hk
      · simp [actStep, hd] at h

/-- **Allocation-history monotonicity.** Whatever the event, a step keeps every nonce already
allocated. This is the property `ProtSat.nonceUsed` lacks: it recomputes "used" from the current
stores, so an overwrite erases the evidence that a nonce was ever generated. -/
theorem alloc_mono {P : Protocol} {C C' : Cfg} {e : Ev} (h : Rel P C e C') :
    ∀ n ∈ C.alloc, n ∈ C'.alloc := by
  unfold Rel at h
  cases e
  · simp [stepOf] at h; subst h; exact fun n hn => hn
  · rename_i t
    by_cases hb : oneStepBool C.kn t
    · simp [stepOf, hb] at h; subst h; exact fun n hn => hn
    · simp [stepOf, hb] at h
  · rename_i q m
    rw [stepOf] at h
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | recv _ x =>
            by_cases hm : m ∈ C.kn
            · simp [hact, hm] at h; subst h; exact fun n hn => hn
            · simp [hact, hm] at h
        | _ => simp [hact] at h
  · rename_i q n
    rw [stepOf] at h
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | fresh _ _ =>
            simp [hact] at h
            rcases h with ⟨_, _, heq⟩
            subst heq
            intro k hk
            rw [allocate_alloc]
            exact List.mem_append.mpr (Or.inl hk)
        | _ => simp [hact] at h
  · rename_i q
    rw [stepOf] at h
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at h
    | some act =>
        rw [hact] at h
        by_cases hu : actionUsable P C q act
        · simp [hact, hu] at h
          intro n hn
          have heq := alloc_eq_of_actStep h
          rw [heq]
          exact hn
        · simp [hact, hu] at h

/-- The attacker's knowledge is monotone along a step. -/
theorem kn_mono {P : Protocol} {C C' : Cfg} {e : Ev} (h : Rel P C e C') :
    ∀ t ∈ C.kn, t ∈ C'.kn := by
  unfold Rel at h
  cases e
  · simp [stepOf] at h; subst h; exact fun t ht => ht
  · rename_i t
    by_cases hb : oneStepBool C.kn t
    · simp [stepOf, hb] at h
      subst h
      intro k hk
      rw [publish_kn]
      exact List.mem_append.mpr (Or.inl hk)
    · simp [stepOf, hb] at h
  · rename_i q m
    rw [stepOf] at h
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | recv _ x =>
            by_cases hm : m ∈ C.kn
            · simp [hact, hm] at h; subst h; exact fun k hk => hk
            · simp [hact, hm] at h
        | _ => simp [hact] at h
  · rename_i q n
    rw [stepOf] at h
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at h
    | some act =>
        cases act with
        | fresh _ _ => simp [hact] at h; rcases h with ⟨_, _, heq⟩; subst heq; exact fun k hk => hk
        | _ => simp [hact] at h
  · rename_i q
    rw [stepOf] at h
    cases hact : P.actionAt q (pcOf C q) with
    | none => simp [hact] at h
    | some act =>
        rw [hact] at h
        by_cases hu : actionUsable P C q act
        · simp [hact, hu] at h
          exact kn_mono_of_actStep h
        · simp [hact, hu] at h

/-! ### What a run must not reveal -/

/-- The secrets a configuration must keep: the protocol's static closed secrets, and every value
snapshotted by a `secret` action so far. The second part is what `ProtSat.Secret.store` cannot
express: it re-reads the register at every configuration, so overwriting the register retires the
promise. -/
def declaredSecrets (P : Protocol) (C : Cfg) : List Term := P.closedSecretTerms ++ C.oblig

/-- A configuration leaks when the attacker knows one of the declared secrets. -/
def leaks (P : Protocol) (C : Cfg) : Prop := ∃ s ∈ declaredSecrets P C, s ∈ C.kn

/-- The executable form. -/
def leaksBool (P : Protocol) (C : Cfg) : Bool :=
  (declaredSecrets P C).any fun s => decide (s ∈ C.kn)

theorem leaksBool_iff (P : Protocol) (C : Cfg) : leaksBool P C = true <-> leaks P C := by
  classical
  rw [leaksBool, leaks, List.any_eq_true]
  constructor
  · rintro ⟨s, hs, hmem⟩
    exact ⟨s, hs, of_decide_eq_true hmem⟩
  · rintro ⟨s, hs, hmem⟩
    exact ⟨s, hs, decide_eq_true hmem⟩

/-- A trace leaks when one of the configurations it visits does. -/
def traceLeaks (P : Protocol) (Cs : List Cfg) : Prop := ∃ C ∈ Cs, leaks P C

def traceLeaksBool (P : Protocol) (Cs : List Cfg) : Bool := Cs.any (leaksBool P)

theorem traceLeaksBool_iff (P : Protocol) (Cs : List Cfg) :
    traceLeaksBool P Cs = true <-> traceLeaks P Cs := by
  classical
  rw [traceLeaksBool, List.any_eq_true, traceLeaks]
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, (leaksBool_iff P C).mp h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, (leaksBool_iff P C).mpr h⟩

/-! ### Authentication events -/

/-- One authentication event of a trace: who performed it (session, role and the principal it
plays), whom it believes it was talking to, on which tag and data, and at which position of the
trace. The position is what makes the ordering requirement expressible. -/
structure Inst where
  isCommit : Bool
  sess : Nat
  role : Nat
  self : Agent
  peer : Agent
  tag : Tag
  data : Term
  idx : Nat
  deriving Repr, DecidableEq

/-- The authentication event of one step, if that step is a claim or a commit whose annotations
evaluate. On a valid run there is never anything to drop, because a claim or commit is enabled only
when its annotations evaluate. -/
def instAt (P : Protocol) (Cs : List Cfg) (tr : List Ev) (i : Nat) : Option Inst :=
  match rget tr i, rget Cs i with
  | some (Ev.act q), some C =>
      match P.actionAt q (pcOf C q), rget P.sessions q with
      | some (Action.claim tag peer v), some se =>
          (authData P C q peer v).map fun (a, d) =>
            { isCommit := false, sess := q, role := se.role, self := se.self, peer := a,
              tag := tag, data := d, idx := i }
      | some (Action.commit tag peer v), some se =>
          (authData P C q peer v).map fun (a, d) =>
            { isCommit := true, sess := q, role := se.role, self := se.self, peer := a,
              tag := tag, data := d, idx := i }
      | _, _ => none
  | _, _ => none

/-- All authentication events of a trace, in trace order. -/
def insts (P : Protocol) (Cs : List Cfg) (tr : List Ev) : List Inst :=
  (List.range tr.length).filterMap (instAt P Cs tr)

/-- A commit is matched by an earlier claim *to it*: the claim's principal is the commit's peer,
the claim's peer is the commit's principal, and the tag and agreed data agree. The strict inequality
is what stops a later claim from excusing an earlier commit. Stated as a `Bool` so that the same
predicate serves the declarative and the executable monitor. -/
def claimMatches (c r : Inst) : Bool :=
  ! r.isCommit && r.tag == c.tag && r.data == c.data &&
    r.self == c.peer && r.peer == c.self && r.idx < c.idx

/-- **Non-injective agreement**: every commit has a matching earlier claim. -/
def agrees (ls : List Inst) : Prop :=
  ∀ c ∈ ls, c.isCommit → ∃ r ∈ ls, claimMatches c r = true

/-- The identity of a claim or commit for injective-matching purposes. -/
def key (a : Inst) : Bool × Nat × Nat × Agent × Agent × Term :=
  (a.isCommit, a.tag, a.role, a.self, a.peer, a.data)

/-- **Injective agreement**: at each commit, the claims that could match it outnumber the commits
that already consumed them, so distinct commits need distinct earlier claims. -/
def agreesInj (ls : List Inst) : Prop :=
  ∀ c ∈ ls, c.isCommit →
    (ls.filter (claimMatches c)).length >
      (ls.filter fun r => r.isCommit && key r == key c && r.idx < c.idx).length

/-- Injective agreement implies non-injective agreement: if a commit had no matching claim at all,
the counting condition would demand `0 > n`. -/
theorem agreesInj.agrees {ls : List Inst} (hall : agreesInj ls) : agrees ls := by
  classical
  intro c hc hcom
  by_contra hnone
  push Not at hnone
  have hfilter : ls.filter (claimMatches c) = [] :=
    List.filter_eq_nil_iff.mpr fun r hr hm => hnone r hr hm
  have hgt := hall c hc hcom
  rw [hfilter, List.length_nil] at hgt
  omega

/-- The failure notions for a trace. -/
def authBreak (P : Protocol) (Cs : List Cfg) (tr : List Ev) : Prop :=
  ¬ agrees (insts P Cs tr)

def authBreakInj (P : Protocol) (Cs : List Cfg) (tr : List Ev) : Prop :=
  ¬ agreesInj (insts P Cs tr)

/-! ### Decidable monitors -/

/-- The executable agreement monitor: `false` exactly when some commit has no matching earlier
claim. -/
def agreesBool (ls : List Inst) : Bool :=
  ls.all fun c => ! c.isCommit || ls.any (claimMatches c)

theorem agreesBool_iff (ls : List Inst) : agreesBool ls = true <-> agrees ls := by
  classical
  rw [agreesBool, agrees, List.all_eq_true]
  constructor
  · intro hall c hc hcom
    rcases Bool.or_eq_true_iff.mp (hall c hc) with h | h
    · exact absurd hcom (by simpa using h)
    · obtain ⟨r, hr, hm⟩ := List.any_eq_true.mp h
      exact ⟨r, hr, hm⟩
  · intro hall c hc
    refine Bool.or_eq_true_iff.mpr ?_
    by_cases hcom : c.isCommit
    · right
      obtain ⟨r, hr, hm⟩ := hall c hc hcom
      exact List.any_eq_true.mpr ⟨r, hr, hm⟩
    · left
      simpa using hcom

/-- The executable injective monitor. -/
def agreesInjBool (ls : List Inst) : Bool :=
  ls.all fun c => ! c.isCommit ||
    (ls.filter (claimMatches c)).length >
      (ls.filter fun r => r.isCommit && key r == key c && r.idx < c.idx).length

theorem agreesInjBool_iff (ls : List Inst) : agreesInjBool ls = true <-> agreesInj ls := by
  classical
  rw [agreesInjBool, agreesInj, List.all_eq_true]
  constructor
  · intro hall c hc hcom
    rcases Bool.or_eq_true_iff.mp (hall c hc) with h | h
    · exact absurd hcom (by simpa using h)
    · exact of_decide_eq_true h
  · intro hall c hc
    refine Bool.or_eq_true_iff.mpr ?_
    by_cases hcom : c.isCommit
    · right
      exact decide_eq_true (hall c hc hcom)
    · left
      simpa using hcom

/-! ### The stage-2 acceptance gate

Each example here is the repaired counterpart of a witness in `ProtSat.Regressions`: the same
model, the same trace, and the opposite verdict. All of them are kernel-checked by `decide`. -/

namespace Gates

open ProtSat.Reference

/-- The nested-reuse model of `Regressions.Semantics.nestedReuseP`: generate a nonce, store a
pair containing it, generate again. The old semantics accepted a second generation of the same
value because the value was no longer visible in the store. -/
def reuseP : Protocol :=
  { roles := [{ acts := [Action.fresh 0 0,
                        Action.assign 0 (Expr.pair (Expr.var 0) (Expr.agent 0)),
                        Action.fresh 1 1] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := [7]
    compromised := []
    secrets := []
    auths := [] }

/-- **Rejected.** The third event regenerates the only nonce of the domain, which the history
already contains - even though the value is now hidden inside a pair. -/
theorem nested_reuse_rejected :
    run reuseP (initCfg reuseP)
      [Ev.generate 0 7, Ev.act 0, Ev.generate 0 7] = none := by decide

/-- The first two events are a genuine run: the rejection is about the reuse, not about the model.
-/
theorem reuse_prefix_runs :
    run reuseP (initCfg reuseP) [Ev.generate 0 7, Ev.act 0] ≠ none := by decide

/-- Without nesting, overwriting the slot is enough to make the old semantics accept a reuse. -/
def overwriteReuseP : Protocol :=
  { reuseP with roles := [{ acts :=
      [Action.fresh 0 0, Action.assign 0 (Expr.agent 0), Action.fresh 1 1] }] }

/-- **Rejected**, for the same reason: the history remembers the allocation. -/
theorem overwrite_reuse_rejected :
    run overwriteReuseP (initCfg overwriteReuseP)
      [Ev.generate 0 7, Ev.act 0, Ev.generate 0 7] = none := by decide

/-- A send and a check need no nonce at all: with an **empty nonce domain** the deterministic
actions still run. This is the case the old event type could not even express, because every
`Ev.act` carried a nonce that had to belong to the domain. -/
def emptyDomainP : Protocol :=
  { roles := [{ acts := [Action.recv 0 0,
                        Action.check (Expr.var 0) (Expr.agent 0),
                        Action.send 0 (Expr.var 0)] }]
    sessions := [{ role := 0, self := 0, peer := 0 }]
    agents := [0]
    nonceDomain := []
    compromised := []
    secrets := [Secret.closed (Expr.shrk 0 0)]
    auths := [] }

theorem empty_domain_run :
    run emptyDomainP (initCfg emptyDomainP)
      [Ev.recv 0 (Term.agent 0), Ev.act 0, Ev.act 0] ≠ none := by decide

/-- The same trace with a generation event inserted is blocked, because there is no nonce to
generate: the domain bound is respected, not silently widened. -/
theorem empty_domain_no_generate :
    run { emptyDomainP with roles := [{ acts := [Action.fresh 0 0] }] }
      (initCfg { emptyDomainP with roles := [{ acts := [Action.fresh 0 0] }] })
      [Ev.generate 0 3] = none := by decide

/-- The configurations a trace visits, or empty when it is not a trace. -/
def visit (P : Protocol) (tr : List Ev) : List Cfg := (run P (initCfg P) tr).getD []

/-- The configuration reached after `i` events, or the initial one if the trace is not a run. -/
def nthCfg (P : Protocol) (tr : List Ev) (i : Nat) : Cfg :=
  ((visit P tr).drop i).head?.getD (initCfg P)

/-- Two sessions, one claiming and one committing on the same tag and data. -/
def pairP : Protocol :=
  { roles := [{ acts := [Action.claim 0 (Expr.agent 1) (Expr.nonce 5)] },
              { acts := [Action.commit 0 (Expr.agent 0) (Expr.nonce 5)] }]
    sessions := [{ role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [{ tag := 0 }] }

/-- **Executability witness.** The honest run really reaches both authentication events, so the
agreement statement below is not vacuous. -/
theorem pair_honest_run :
    run pairP (initCfg pairP) [Ev.act 0, Ev.act 1] ≠ none := by decide

theorem pair_agrees : agreesBool (insts pairP (visit pairP [Ev.act 0, Ev.act 1])
    [Ev.act 0, Ev.act 1]) = true := by decide

/-- The honest run does **not** break agreement. -/
theorem pair_no_break : ¬ authBreak pairP (visit pairP [Ev.act 0, Ev.act 1])
    [Ev.act 0, Ev.act 1] :=
  fun h => h (agreesBool_iff _ |>.mp pair_agrees)

/-- **The later claim no longer excuses the commit.** Same model, commit first: the old monitor
said "no break" because the triple was claimed *somewhere*. -/
theorem later_claim_does_not_excuse :
    authBreak pairP (visit pairP [Ev.act 1, Ev.act 0]) [Ev.act 1, Ev.act 0] := by
  intro hall
  have h1 : agreesBool (insts pairP (visit pairP [Ev.act 1, Ev.act 0])
      [Ev.act 1, Ev.act 0]) = false := by decide
  have h2 := (agreesBool_iff _).mpr hall
  simp_all

/-- A claim by the wrong principal does not excuse a commit: matching is between the two ends of
the intended conversation, not a lookup in a global set of triples. -/
def wrongPeerP : Protocol :=
  { roles := [{ acts := [Action.claim 0 (Expr.agent 2) (Expr.nonce 5)] },
              { acts := [Action.commit 0 (Expr.agent 2) (Expr.nonce 5)] }]
    sessions := [{ role := 0, self := 0, peer := 2 }, { role := 1, self := 1, peer := 2 }]
    agents := [0, 1, 2]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [{ tag := 0 }] }

theorem wrong_peer_breaks :
    authBreak wrongPeerP (visit wrongPeerP [Ev.act 0, Ev.act 1]) [Ev.act 0, Ev.act 1] := by
  intro hall
  have h1 : agreesBool (insts wrongPeerP (visit wrongPeerP [Ev.act 0, Ev.act 1])
      [Ev.act 0, Ev.act 1]) = false := by decide
  have h2 := (agreesBool_iff _).mpr hall
  simp_all

/-- A commit whose peer expression does not evaluate is **not enabled**: the annotation cannot be
erased, the session stops. Compare `Regressions.Semantics.unset_commit_produces_nothing`, where
the old semantics advanced and produced no event at all. -/
def unsetCommitP : Protocol :=
  { roles := [{ acts := [Action.commit 0 (Expr.agent 1) (Expr.var 0)] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [{ tag := 0 }] }

theorem unset_commit_blocked :
    stepOf unsetCommitP (initCfg unsetCommitP) (Ev.act 0) = none := by decide

/-- A commit naming a peer that is not a principal is blocked too: the peer must evaluate to an
agent, not merely to something. -/
def noncePeerP : Protocol :=
  { roles := [{ acts := [Action.commit 0 (Expr.nonce 1) (Expr.agent 0)] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [{ tag := 0 }] }

theorem nonce_peer_blocked :
    stepOf noncePeerP (initCfg noncePeerP) (Ev.act 0) = none := by decide

/-- **Non-injective and injective agreement differ.** One claim, two commits on the same tag and
data: every commit has *a* matching earlier claim, but the second one reuses the only claim
available. This is the replay that injective agreement is supposed to rule out. -/
def replayP : Protocol :=
  { roles := [{ acts := [Action.claim 0 (Expr.agent 1) (Expr.nonce 5)] },
              { acts := [Action.commit 0 (Expr.agent 0) (Expr.nonce 5),
                         Action.commit 0 (Expr.agent 0) (Expr.nonce 5)] }]
    sessions := [{ role := 0, self := 0, peer := 1 }, { role := 1, self := 1, peer := 0 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [{ tag := 0 }] }

def replayTrace : List Ev := [Ev.act 0, Ev.act 1, Ev.act 1]

theorem replay_runs : run replayP (initCfg replayP) replayTrace ≠ none := by decide

theorem replay_agrees_noninjectively :
    agreesBool (insts replayP (visit replayP replayTrace) replayTrace) = true := by decide

theorem replay_breaks_injectively :
    agreesInjBool (insts replayP (visit replayP replayTrace) replayTrace) = false := by decide

/-- The injective monitor really is stronger: on the honest single-commit run both agree. -/
theorem pair_agrees_injectively :
    agreesInjBool (insts pairP (visit pairP [Ev.act 0, Ev.act 1])
      [Ev.act 0, Ev.act 1]) = true := by decide

/-- *Credential provisioning.*

A role that names another principal's private key is not thereby entitled to it. The session plays
agent 0 and tries to decrypt a ciphertext addressed to agent 1. -/
def decARole : Role :=
  { acts := [Action.recv 0 0, Action.assign 1 (Expr.decA (Expr.var 0) 1)] }

def decABase : Protocol :=
  { roles := [decARole]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := []
    compromised := []
    secrets := []
    auths := [] }

/-- The ciphertext addressed to agent 1. -/
def ctTo1 : Term := Term.encA (Term.agent 1) 1

/-- The trace: the attacker builds the ciphertext (asymmetric encryption is one of its steps),
delivers it, and the session tries to decrypt it for agent 1. -/
def decATrace : List Ev := [Ev.ded ctTo1, Ev.recv 0 ctTo1, Ev.act 0]

/-- **Rejected.** The session plays 0, so it holds no private key for 1: naming 1 in a `decA`
gives it nothing. -/
theorem unprovisioned_decryption_blocked :
    run decABase (initCfg decABase) decATrace = none := by decide

/-- The same role played by the principal the ciphertext is addressed to: now the key is
provisioned and the step is enabled. The difference is the credential, not the expression. -/
def decAOwnP : Protocol := { decABase with sessions := [{ role := 0, self := 1, peer := 0 }] }

theorem provisioned_decryption_works :
    run decAOwnP (initCfg decAOwnP) decATrace ≠ none := by decide

/-- Nor may a role publish a private key it was not given. -/
def leakKeyP : Protocol :=
  { decABase with roles := [{ acts := [Action.send 0 (Expr.privk 1)] }] }

theorem unprovisioned_key_not_publishable :
    run leakKeyP (initCfg leakKeyP) [Ev.act 0] = none := by decide

/-- But its own key is its own to lose: the discipline is about provisioning, not a ban on the
constructor. -/
def leakOwnKeyP : Protocol :=
  { leakKeyP with sessions := [{ role := 0, self := 1, peer := 0 }] }

theorem provisioned_key_publishable :
    run leakOwnKeyP (initCfg leakOwnKeyP) [Ev.act 0] ≠ none := by decide

/-- *Secret obligations survive an overwrite.*

The session generates a nonce, declares it secret, hides it inside a pair, overwrites the register,
and finally publishes the pair; the attacker projects the nonce out of it. -/
def snapshotP : Protocol :=
  { roles := [{ acts :=
        [Action.fresh 0 0,
         Action.secret (Expr.var 0),
         Action.assign 1 (Expr.pair (Expr.var 0) (Expr.agent 0)),
         Action.assign 0 (Expr.agent 0),
         Action.send 1 (Expr.var 1)] }]
    sessions := [{ role := 0, self := 0, peer := 1 }]
    agents := [0, 1]
    nonceDomain := [7]
    compromised := []
    secrets := []
    auths := [] }

def snapshotTrace : List Ev :=
  [Ev.generate 0 7, Ev.act 0, Ev.act 0, Ev.act 0, Ev.act 0, Ev.ded (Term.nonce 7)]

/-- The run is legal. -/
theorem snapshot_runs : run snapshotP (initCfg snapshotP) snapshotTrace ≠ none := by decide

/-- The register no longer holds the declared value: a check that reads the store at the end of the
run sees `agent 0`, not the nonce. -/
theorem snapshot_register_forgotten :
    readVar 0 (storeOf ((nthCfg snapshotP snapshotTrace 6)) 0) =
      some (Term.agent 0) := by decide

/-- And the obligation still names the nonce. -/
theorem snapshot_obligation_kept :
    (nthCfg snapshotP snapshotTrace 6).oblig = [Term.nonce 7] := by decide

/-- **The leak is detected.** The final configuration leaks through the obligation, even though
the register was overwritten three steps earlier. -/
theorem snapshot_leaks :
    traceLeaksBool snapshotP (visit snapshotP snapshotTrace) = true := by decide

end Gates

end ProtSat.Reference