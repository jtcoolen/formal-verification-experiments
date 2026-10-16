/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Protocol

/-!
# ProtSat: small-step operational semantics (specification sections 3 and 4)

## Independence

This module is the *reference* semantics of protocol execution.  It is stated
directly in terms of the message algebra (ProtSat.Term), the attacker relation
(ProtSat.Attacker) and the protocol language (ProtSat.Protocol).  It does not import
ProtSat.CNF, ProtSat.Encode or ProtSat.DPLL: the specification requires that "the
operational semantics must not depend on the SAT encoding", and the module graph
enforces that.  Everything proved here is therefore available to the independent
certificate checker of section 7, which likewise does not import the encoding.

## The transition system

A configuration (Cfg) holds the local state of every session and the attacker's
knowledge.  An event (Ev) is one of

  idle          - nothing happens, so a run of length at most L is a run of length
                  exactly L padded with idles;
  ded t         - the attacker performs one deduction step, learning t.  Making
                  attacker steps explicit is what lets the bound on execution steps
                  also bound the attacker's derivation depth, which is exactly the
                  property the SAT encoding's completeness theorem needs;
  act q m d     - session q performs its current action.  m is the message the
                  attacker delivers if q receives; d is the nonce value q picks if q
                  generates a fresh nonce.  Both are always supplied and used only
                  when relevant, which keeps the encoding uniform.

Rel P C e C' is inductive, with one introduction rule per action kind (rIdle, rDed,
rFresh, rSend, rRecv, rAssign, rCheck, rSecret, rClaim, rCommit).  Because it is
inductive, a certificate can *present* a transition and be checked by constructing
the corresponding Rel proof term - which is precisely what ProtSat.Certificate does,
and it is why no decision procedure is trusted there.

The attacker controls the network: a send publishes the message (the attacker's
knowledge grows), and a receive takes any message the attacker can deduce, so
replays and injections are instances of the recv rule.

## Freshness

A fresh nonce value must be new: it may not already occur in any session store nor
in the attacker's knowledge.  This is enforced locally in rFresh, which is equivalent
to the usual global "all sessions pick distinct values" condition because stores and
knowledge only grow.
-/

namespace ProtSat

open Term
open ProtSat.Attacker

/-! ### Indexing lists without bound proofs -/

/-- The r-th element of a list, as an Option (no bound proof required). -/
def rget {α : Type} : List α -> Nat -> Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => rget xs n

/-- Replace the r-th element of a list by f applied to its current value; a no-op if
r is out of range. -/
def rput {α : Type} (f : α -> α) : List α -> Nat -> List α
  | [], _ => []
  | x :: xs, 0 => f x :: xs
  | x :: xs, n + 1 => x :: rput f xs n

@[simp] theorem rget_rput_same {α : Type} (f : α -> α) (l : List α) (q : Nat) :
    rget (rput f l q) q = (rget l q).map f := by
  induction l generalizing q with
  | nil => cases q <;> rfl
  | cons x xs ih =>
      cases q with
      | zero => rfl
      | succ q => simp only [rget, rput]; exact ih q

theorem rget_rput_other {α : Type} {f : α -> α} {l : List α} {q s : Nat} (h : s ≠ q) :
    rget (rput f l q) s = rget l s := by
  induction l generalizing q s with
  | nil => cases q <;> cases s <;> simp [rget, rput]
  | cons x xs ih =>
      cases q with
      | zero =>
          cases s with
          | zero => exact absurd h (by simp)
          | succ s => rfl
      | succ q =>
          cases s with
          | zero => simp [rget, rput]
          | succ s =>
              simp only [rget, rput]
              exact ih (fun e => h (e ▸ rfl))

/-! ### Configurations -/

/-- A configuration: the local state of every session plus the attacker's knowledge.

The set of configurations is finite once the bounds of ProtSat.Bounded are fixed:
program counters range over role lengths, stores over the term universe, and the
knowledge over finite subsets of the universe.  This is the "represent protocol
configurations as finite states" requirement of section 4. -/
structure Cfg where
  /-- One local state per session, in the order given by Protocol.sessions. -/
  sess : List SessState
  /-- The messages the attacker has seen or derived.  Membership is what matters; the
  list representation keeps the semantics and the certificate checker simple. -/
  kn : List Term
  deriving Repr, DecidableEq

/-- The local state of session q. -/
def sessAt (C : Cfg) (q : Nat) : Option SessState := rget C.sess q

/-- The program counter of session q (0 if there is no such session). -/
def pcOf (C : Cfg) (q : Nat) : Nat := (sessAt C q).map (fun s => s.pc) |>.getD 0

/-- The store of session q. -/
def storeOf (C : Cfg) (q : Nat) : List (Var × Term) :=
  (sessAt C q).map (fun s => s.store) |>.getD []

/-- Write a variable into a session store, replacing any previous value. -/
def writeVar (x : Var) (t : Term) (s : List (Var × Term)) : List (Var × Term) :=
  (x, t) :: s.filter fun p => p.1 != x

/-- Read a variable from a session store. -/
def readVar (x : Var) (s : List (Var × Term)) : Option Term := Expr.lookup x s

/-- The messages currently stored by a session. -/
def storeVals (s : List (Var × Term)) : List Term := s.map fun p => p.2

/-- Is the nonce value d already used in C (in some session store, or known to the
attacker)?  Used by the freshness rule. -/
def nonceUsed (C : Cfg) (d : NonceName) : Bool :=
  (C.sess.any fun s => (storeVals s.store).contains (Term.nonce d))
  || (C.kn.contains (Term.nonce d))

/-! ### Successor configurations

Each successor is a named function, so that the transition rules, the certificate
checker and the SAT encoding all speak about the same object. -/

/-- Advance a session's program counter. -/
def bump (s : SessState) : SessState := { s with pc := s.pc + 1 }

/-- Advance a session and set x := t in its store. -/
def bumpStore (x : Var) (t : Term) (s : SessState) : SessState :=
  { s with pc := s.pc + 1, store := writeVar x t s.store }

/-- Advance session q's program counter. -/
def succAdvance (C : Cfg) (q : Nat) : Cfg :=
  { C with sess := rput bump C.sess q }

/-- Advance session q and set x := t in its store. -/
def succStore (C : Cfg) (q : Nat) (x : Var) (t : Term) : Cfg :=
  { C with sess := rput (bumpStore x t) C.sess q }

/-- Advance session q and publish t to the attacker. -/
def succSend (C : Cfg) (q : Nat) (t : Term) : Cfg :=
  { sess := rput bump C.sess q, kn := C.kn ++ [t] }

/-- Add t to the attacker's knowledge. -/
def succDed (C : Cfg) (t : Term) : Cfg :=
  { C with kn := C.kn ++ [t] }

/-- A step by session q leaves every *other* session's local state alone.  These
frame lemmas are the semantic content of the frame clauses of the SAT encoding. -/
theorem sessAt_succAdvance_other (C : Cfg) (q r : Nat) (h : r ≠ q) :
    sessAt (succAdvance C q) r = sessAt C r := by
  cases C with
  | mk sess kn => simp only [succAdvance, sessAt]; exact rget_rput_other h

theorem sessAt_succStore_other (C : Cfg) (q r : Nat) (x : Var) (t : Term) (h : r ≠ q) :
    sessAt (succStore C q x t) r = sessAt C r := by
  cases C with
  | mk sess kn => simp only [succStore, sessAt]; exact rget_rput_other h

theorem sessAt_succSend_other (C : Cfg) (q r : Nat) (t : Term) (h : r ≠ q) :
    sessAt (succSend C q t) r = sessAt C r := by
  cases C with
  | mk sess kn => simp only [succSend, sessAt]; exact rget_rput_other h

/-- The acting session's local state is updated by bump. -/
theorem sessAt_succAdvance_same (C : Cfg) (q : Nat) :
    sessAt (succAdvance C q) q = (sessAt C q).map bump := by
  cases C with
  | mk sess kn => simp only [succAdvance, sessAt]; exact rget_rput_same bump sess q

theorem sessAt_succStore_same (C : Cfg) (q : Nat) (x : Var) (t : Term) :
    sessAt (succStore C q x t) q = (sessAt C q).map (bumpStore x t) := by
  cases C with
  | mk sess kn => simp only [succStore, sessAt]; exact rget_rput_same (bumpStore x t) sess q

/-- The acting session's program counter advances by one. -/
theorem pcOf_succAdvance (C : Cfg) (q : Nat) (st : SessState) (h : sessAt C q = some st) :
    pcOf (succAdvance C q) q = st.pc + 1 := by
  simp only [pcOf, h]
  rw [sessAt_succAdvance_same, h]
  simp [bump]

/-- The acting session's variable x holds t after a succStore step. -/
theorem readVar_succStore (C : Cfg) (q x : Nat) (t : Term) (st : SessState)
    (h : sessAt C q = some st) :
    readVar x (storeOf (succStore C q x t) q) = some t := by
  simp only [storeOf]
  rw [sessAt_succStore_same, h]
  simp [bumpStore, readVar, writeVar, Expr.lookup]

/-- Reading a variable other than the one written is unaffected by a store update. -/
theorem readVar_writeVar_other {a b : Nat} {t : Term} (h : a ≠ b) :
    ∀ (s : List (Nat × Term)), readVar b (writeVar a t s) = readVar b s := by
  intro s
  induction s with
  | nil => simp [writeVar, readVar, Expr.lookup, h]
  | cons p rest ih =>
      simp only [writeVar, readVar, List.filter_cons, Expr.lookup]
      by_cases hp : p.1 = a <;>
      by_cases hab : p.1 = b <;>
      simp_all [writeVar, readVar, Expr.lookup]

/-- A store update leaves the other slots of the acting session alone. -/
theorem readVar_succStore_other (C : Cfg) (q x y : Nat) (t : Term) (h : x ≠ y) :
    readVar y (storeOf (succStore C q x t) q) = readVar y (storeOf C q) := by
  have h1 : sessAt (succStore C q x t) q = (sessAt C q).map (bumpStore x t) :=
    sessAt_succStore_same C q x t
  unfold storeOf
  rw [h1]
  cases h2 : sessAt C q with
  | none => simp [h2]
  | some st => simp [h2, bumpStore, readVar_writeVar_other h]

/-- A send advances the acting session's program counter and leaves its store alone. -/
theorem sessAt_succSend_same (C : Cfg) (q : Nat) (t : Term) :
    sessAt (succSend C q t) q = (sessAt C q).map bump := by
  cases C with
  | mk sess kn => simp only [succSend, sessAt]; exact rget_rput_same bump sess q

theorem pcOf_succSend (C : Cfg) (q : Nat) (t : Term) (st : SessState)
    (h : sessAt C q = some st) : pcOf (succSend C q t) q = st.pc + 1 := by
  simp only [pcOf]
  rw [sessAt_succSend_same, h]
  simp [bump]

theorem pcOf_succStore (C : Cfg) (q x : Nat) (t : Term) (st : SessState)
    (h : sessAt C q = some st) : pcOf (succStore C q x t) q = st.pc + 1 := by
  simp only [pcOf]
  rw [sessAt_succStore_same, h]
  simp [bumpStore]

theorem pcOf_succDed (C : Cfg) (q : Nat) (t : Term) : pcOf (succDed C t) q = pcOf C q := rfl

theorem readVar_succDed (C : Cfg) (q x : Nat) (t : Term) :
    readVar x (storeOf (succDed C t) q) = readVar x (storeOf C q) := rfl

theorem readVar_succSend (C : Cfg) (q x : Nat) (t : Term) :
    readVar x (storeOf (succSend C q t) q) = readVar x (storeOf C q) := by
  have h1 : sessAt (succSend C q t) q = (sessAt C q).map bump := sessAt_succSend_same C q t
  unfold storeOf
  rw [h1]
  cases h2 : sessAt C q with
  | none => simp [h2]
  | some st => simp [h2, bump]

/-- An advance step changes no store. -/
theorem storeOf_succAdvance (C : Cfg) (q r : Nat) :
    storeOf (succAdvance C q) r = storeOf C r := by
  unfold storeOf
  by_cases h : r = q
  · subst h
    rw [sessAt_succAdvance_same]
    cases h2 : sessAt C r with
    | none => simp [h2]
    | some st => simp [h2, bump]
  · rw [sessAt_succAdvance_other C q r h]

/-- A deduction step changes no session's local state. -/
theorem sessAt_succDed (C : Cfg) (t : Term) (q : Nat) : sessAt (succDed C t) q = sessAt C q := rfl

/-- Only a send or a deduction grows the attacker's knowledge. -/
theorem kn_succAdvance (C : Cfg) (q : Nat) : (succAdvance C q).kn = C.kn := rfl
theorem kn_succStore (C : Cfg) (q : Nat) (x : Var) (t : Term) : (succStore C q x t).kn = C.kn := rfl
theorem kn_succDed (C : Cfg) (t : Term) : (succDed C t).kn = C.kn ++ [t] := rfl
theorem kn_succSend (C : Cfg) (q : Nat) (t : Term) : (succSend C q t).kn = C.kn ++ [t] := rfl

/-- The initial configuration of a protocol: every session at program counter 0 with
an empty store, and the attacker holding exactly the public information and the
compromised keys. -/
def initCfg (P : Protocol) : Cfg :=
  { sess := P.sessions.map fun _ => { pc := 0, store := [] }, kn := P.initKn }

/-! ### Events -/

/-- The events of the labelled transition system. -/
inductive Ev where
  /-- Nothing happens. -/
  | idle
  /-- The attacker performs one deduction step, learning t. -/
  | ded (t : Term)
  /-- Session q acts: m is the message delivered to it (used by recv), d the nonce
  value it picks (used by fresh). -/
  | act (q : Nat) (m : Term) (d : NonceName)
  deriving Repr, DecidableEq

/-! ### The transition relation -/

/-- Rel P C e C': the small-step transition relation of the operational semantics,
one introduction rule per event kind.  This is the mathematical object that the
soundness and completeness theorems of sections 8A and 8B are about. -/
inductive Rel : Protocol -> Cfg -> Ev -> Cfg -> Prop
  /-- The network may always be idle. -/
  | rIdle : ∀ (P : Protocol) (C : Cfg), Rel P C Ev.idle C
  /-- Attacker deduction: one rule instance adds its conclusion to the knowledge. -/
  | rDed : ∀ {P : Protocol} {C : Cfg} {t : Term},
      OneStep C.kn t -> Rel P C (Ev.ded t) (succDed C t)
  /-- Fresh nonce generation, with the freshness side condition. -/
  | rFresh : ∀ {P : Protocol} {C : Cfg} {q : Nat} {x : Var} {N : NonceName}
      {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.fresh x N) ->
      d ∈ P.nonceDomain ->
      nonceUsed C d = false ->
      Rel P C (Ev.act q m d) (succStore C q x (Term.nonce d))
  /-- Sending publishes: the attacker learns the message. -/
  | rSend : ∀ {P : Protocol} {C : Cfg} {q : Nat} {a : Agent} {e : Expr} {t : Term}
      {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.send a e) ->
      Expr.eval e (storeOf C q) = some t ->
      Rel P C (Ev.act q m d) (succSend C q t)
  /-- Receiving takes any message the attacker knows: replay and injection are
  instances of this rule. -/
  | rRecv : ∀ {P : Protocol} {C : Cfg} {q : Nat} {a : Agent} {x : Var} {m : Term}
      {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.recv a x) ->
      m ∈ C.kn ->
      Rel P C (Ev.act q m d) (succStore C q x m)
  /-- Local computation: x := value of e. -/
  | rAssign : ∀ {P : Protocol} {C : Cfg} {q : Nat} {x : Var} {e : Expr} {t : Term}
      {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.assign x e) ->
      Expr.eval e (storeOf C q) = some t ->
      Rel P C (Ev.act q m d) (succStore C q x t)
  /-- Equality test: enabled only when both sides evaluate to the same message. -/
  | rCheck : ∀ {P : Protocol} {C : Cfg} {q : Nat} {e1 e2 : Expr} {v : Term}
      {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.check e1 e2) ->
      Expr.eval e1 (storeOf C q) = some v ->
      Expr.eval e2 (storeOf C q) = some v ->
      Rel P C (Ev.act q m d) (succAdvance C q)
  /-- Declaring a secret advances the control state; the property itself is checked
  globally by Leak. -/
  | rSecret : ∀ {P : Protocol} {C : Cfg} {q : Nat} {e : Expr} {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.secret e) ->
      Rel P C (Ev.act q m d) (succAdvance C q)
  /-- Authentication events: they advance the control state and are recorded by the
  trace-level agreement predicate. -/
  | rClaim : ∀ {P : Protocol} {C : Cfg} {q : Nat} {tag : Tag} {peer v : Expr}
      {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.claim tag peer v) ->
      Rel P C (Ev.act q m d) (succAdvance C q)
  | rCommit : ∀ {P : Protocol} {C : Cfg} {q : Nat} {tag : Tag} {peer v : Expr}
      {m : Term} {d : NonceName},
      P.actionAt q (pcOf C q) = some (Action.commit tag peer v) ->
      Rel P C (Ev.act q m d) (succAdvance C q)

/-! ### Traces -/

/-- Runs P C0 tr Cs: tr is a trace of P starting in C0 that visits the configurations
Cs (so Cs has one more element than tr, and consecutive elements are related).

Carrying the visited configurations in the predicate is what makes the certificate
checker possible: a certificate *is* such a list, and checking it means constructing
this proof. -/
inductive Runs : Protocol -> Cfg -> List Ev -> List Cfg -> Prop
  /-- The empty trace visits just the starting configuration. -/
  | nil : ∀ (P : Protocol) (C : Cfg), Runs P C [] [C]
  /-- One more step: e takes C to C' and the rest of the trace continues from C'. -/
  | cons : ∀ {P : Protocol} {C C' : Cfg} {e : Ev} {tr : List Ev} {rest : List Cfg},
      Rel P C e C' -> Runs P C' tr rest -> Runs P C (e :: tr) (C :: rest)

/-- Trace P C0 tr: tr is a valid execution of P from C0 (for some visit list). -/
def Trace (P : Protocol) (C0 : Cfg) (tr : List Ev) : Prop := ∃ Cs, Runs P C0 tr Cs

/-- A trace visits exactly one more configuration than it has events. -/
theorem runs_length : ∀ {P : Protocol} {C : Cfg} {tr : List Ev} {Cs : List Cfg},
    Runs P C tr Cs -> Cs.length = tr.length + 1 := by
  intro P C tr Cs h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- The configurations a trace visits *after* its initial one.  For a valid trace of
n events this is a list of n configurations, one per step, which is what the
encoding's per-step decoding produces. -/
def visited (P : Protocol) (C0 : Cfg) (tr : List Ev) (Cs : List Cfg) : List Cfg :=
  Cs.drop 1

/-! ### Security properties -/

/-- Leak P C: the attacker knows one of the declared secrets in configuration C.
Both forms of Secret are covered: closed expressions and session-store variables. -/
def Leak (P : Protocol) (C : Cfg) : Prop :=
  (∃ s ∈ P.closedSecretTerms, s ∈ C.kn)
  ∨ (∃ q x v, (Secret.store q x) ∈ P.secrets
        ∧ (sessAt C q).map (fun st => readVar x st.store) = some (some v)
        ∧ v ∈ C.kn)

/-- A visited list of configurations leaks if any of them does. -/
def runsLeaks (P : Protocol) (Cs : List Cfg) : Prop := ∃ C ∈ Cs, Leak P C

/-- One authentication event of a trace: whether it was a commit (as opposed to a
claim), and on which (tag, peer, value) triple. -/
structure AuthInst where
  isCommit : Bool
  tag : Tag
  peer : Agent
  val : Term
  deriving Repr, DecidableEq

/-- The authentication instance produced by one step, if that step is a claim or a
commit.  The peer and value are evaluated in the store of the acting session, so the
instance records what that session *believed*, not what the attacker sent. -/
def authOfStep (P : Protocol) (C : Cfg) (e : Ev) : List AuthInst :=
  match e with
  | Ev.act q m d =>
      match P.actionAt q (pcOf C q) with
      | some (Action.claim tag peer v) =>
          match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
          | some (Term.agent a), some val =>
              [{ isCommit := false, tag := tag, peer := a, val := val }]
          | _, _ => []
      | some (Action.commit tag peer v) =>
          match Expr.eval peer (storeOf C q), Expr.eval v (storeOf C q) with
          | some (Term.agent a), some val =>
              [{ isCommit := true, tag := tag, peer := a, val := val }]
          | _, _ => []
      | _ => []
  | _ => []

/-- All authentication events of a trace, in order: the step from Cs!!i to
Cs!(i+1)! is attributed to configuration Cs!!i. -/
def authInsts (P : Protocol) (Cs : List Cfg) (tr : List Ev) : List AuthInst :=
  ((Cs.zip tr).map fun p => authOfStep P p.1 p.2).flatten

/-- The claimed triples of a trace. -/
def claimsOf (P : Protocol) (Cs : List Cfg) (tr : List Ev) : List (Tag × Agent × Term) :=
  (authInsts P Cs tr).filterMap fun a =>
    if a.isCommit then none else some (a.tag, a.peer, a.val)

/-- The committed triples of a trace. -/
def commitsOf (P : Protocol) (Cs : List Cfg) (tr : List Ev) : List (Tag × Agent × Term) :=
  (authInsts P Cs tr).filterMap fun a =>
    if a.isCommit then some (a.tag, a.peer, a.val) else none

/-- **Authentication violation** (non-injective agreement): the trace contains a
commit whose (tag, peer, value) triple was never claimed.  This is the property the
Lowe attack on Needham-Schroeder breaks (specification section 9.5). -/
def AuthBreak (P : Protocol) (Cs : List Cfg) (tr : List Ev) : Prop :=
  ∃ c ∈ commitsOf P Cs tr, c ∉ claimsOf P Cs tr

/-- An attack on P within trace tr: a valid trace from the initial configuration
that either leaks a secret or breaks agreement. -/
def Attack (P : Protocol) (tr : List Ev) : Prop :=
  ∃ Cs, Runs P (initCfg P) tr Cs ∧ (runsLeaks P Cs ∨ AuthBreak P Cs tr)

/-! ### More frame lemmas (used by the encoding correspondence) -/

/-- Replacing an element of a list never changes its length. -/
theorem rput_length {α : Type} (f : α -> α) : ∀ (l : List α) (q : Nat),
    (rput f l q).length = l.length := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons x xs ih =>
      intro q
      cases q with
      | zero => rfl
      | succ q => simp [rput, ih]

/-- An in-range read of a list succeeds. -/
theorem rget_lt_aux {α : Type} : ∀ (l : List α) (q : Nat), q < l.length -> ∃ x, rget l q = some x := by
  intro l
  induction l with
  | nil => intro q h; exact absurd h (by simp)
  | cons x xs ih =>
      intro q h
      cases q with
      | zero => exact ⟨x, rfl⟩
      | succ q =>
          have h2 : q < xs.length := by
            rw [List.length_cons] at h
            omega
          exact ih q h2

/-- A session index below the length of the session list has a local state. -/
theorem sessAt_lt {C : Cfg} {q : Nat} (h : q < C.sess.length) :
    ∃ st : SessState, sessAt C q = some st := by
  unfold sessAt
  exact rget_lt_aux C.sess q h

/-- A step by session q leaves every other session's program counter alone. -/
theorem pcOf_succAdvance_other (C : Cfg) (q r : Nat) (h : r ≠ q) :
    pcOf (succAdvance C q) r = pcOf C r := by
  unfold pcOf
  rw [sessAt_succAdvance_other C q r h]

theorem pcOf_succStore_other (C : Cfg) (q r : Nat) (x : Var) (t : Term) (h : r ≠ q) :
    pcOf (succStore C q x t) r = pcOf C r := by
  unfold pcOf
  rw [sessAt_succStore_other C q r x t h]

theorem pcOf_succSend_other (C : Cfg) (q r : Nat) (t : Term) (h : r ≠ q) :
    pcOf (succSend C q t) r = pcOf C r := by
  unfold pcOf
  rw [sessAt_succSend_other C q r t h]

/-- A step by session q leaves every other session's store alone. -/
theorem storeOf_succAdvance_other (C : Cfg) (q r : Nat) (h : r ≠ q) :
    storeOf (succAdvance C q) r = storeOf C r := by
  unfold storeOf
  rw [sessAt_succAdvance_other C q r h]

theorem storeOf_succStore_other (C : Cfg) (q r : Nat) (x : Var) (t : Term) (h : r ≠ q) :
    storeOf (succStore C q x t) r = storeOf C r := by
  unfold storeOf
  rw [sessAt_succStore_other C q r x t h]

theorem storeOf_succSend_other (C : Cfg) (q r : Nat) (t : Term) (h : r ≠ q) :
    storeOf (succSend C q t) r = storeOf C r := by
  unfold storeOf
  rw [sessAt_succSend_other C q r t h]

/-- The acting session's own store after a store step: the variable is written, the rest of
the store is untouched.  The session has to exist, which is the hypothesis the operational
semantics always has available (Rel only lets an instantiated session act). -/
theorem storeOf_succStore_same (C : Cfg) (q : Nat) (x : Var) (t : Term)
    (st : SessState) (h : sessAt C q = some st) :
    storeOf (succStore C q x t) q = writeVar x t (storeOf C q) := by
  unfold storeOf
  rw [sessAt_succStore_same, h]
  simp [bumpStore]

/-- A send does not change the acting session's store. -/
theorem storeOf_succSend_same (C : Cfg) (q : Nat) (t : Term) :
    storeOf (succSend C q t) q = storeOf C q := by
  unfold storeOf
  rw [sessAt_succSend_same]
  cases h : sessAt C q with
  | none => simp [h]
  | some st => simp [h, bump]

/-- The number of sessions is invariant: a step never adds or removes a session. -/
theorem sessLength_succAdvance (C : Cfg) (q : Nat) :
    (succAdvance C q).sess.length = C.sess.length := rput_length bump C.sess q
theorem sessLength_succStore (C : Cfg) (q : Nat) (x : Var) (t : Term) :
    (succStore C q x t).sess.length = C.sess.length := rput_length (bumpStore x t) C.sess q
theorem sessLength_succSend (C : Cfg) (q : Nat) (t : Term) :
    (succSend C q t).sess.length = C.sess.length := rput_length bump C.sess q
theorem sessLength_succDed (C : Cfg) (t : Term) :
    (succDed C t).sess.length = C.sess.length := rfl

/-- The acting session's program counter advances, stated through the session count
instead of an explicit local state. -/
theorem pcOf_succAdvance' (C : Cfg) (q : Nat) (h : q < C.sess.length) :
    pcOf (succAdvance C q) q = pcOf C q + 1 := by
  obtain ⟨st, hst⟩ := sessAt_lt h
  have hpc : pcOf C q = st.pc := by
    show ((sessAt C q).map (fun s => s.pc)).getD 0 = st.pc
    rw [hst]; rfl
  rw [pcOf_succAdvance C q st hst, hpc]

theorem pcOf_succStore' (C : Cfg) (q x : Nat) (t : Term) (h : q < C.sess.length) :
    pcOf (succStore C q x t) q = pcOf C q + 1 := by
  obtain ⟨st, hst⟩ := sessAt_lt h
  have hpc : pcOf C q = st.pc := by
    show ((sessAt C q).map (fun s => s.pc)).getD 0 = st.pc
    rw [hst]; rfl
  rw [pcOf_succStore C q x t st hst, hpc]

theorem pcOf_succSend' (C : Cfg) (q : Nat) (t : Term) (h : q < C.sess.length) :
    pcOf (succSend C q t) q = pcOf C q + 1 := by
  obtain ⟨st, hst⟩ := sessAt_lt h
  have hpc : pcOf C q = st.pc := by
    show ((sessAt C q).map (fun s => s.pc)).getD 0 = st.pc
    rw [hst]; rfl
  rw [pcOf_succSend C q t st hst, hpc]

end ProtSat
