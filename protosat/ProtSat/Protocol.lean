/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Attacker

/-!
# ProtSat: the protocol language (specification section 3)

## What a protocol is here

A protocol is a list of roles; a role is a list of actions; a session is a role
played by a pair of agents.  A run is an interleaving of session actions and
attacker deductions in which the attacker controls the whole network: every
message a session sends is published (hence known to the attacker), and every
message a session receives is chosen by the attacker from what it can deduce.
That is what makes replay attacks representable, and it is the model used by every
example in ProtSat/Examples.

## Expressions and their partial evaluation

Expressions (Expr) are the syntax a role uses to build messages.  They contain
destructors (fst, snd, decS, decA), which a principal legitimately needs: B
receives a pair and must take it apart.  Evaluation of an expression in a session
store is therefore a partial function Option Term: if a destructor does not apply,
evaluation is stuck and the corresponding action is simply not enabled - the
session blocks.  This is the standard symbolic treatment (a principal never
silently guesses a plaintext) and it is what the equality-check action 'check'
makes explicit.

Because messages (Term) are normal forms (see ProtSat.Syntax), evaluation returns
a normal form directly: decryption pattern-matches on the ciphertext constructor
instead of invoking a rewriting engine.  ProtSat.Theory proves that this is the
same equivalence theory as the explicit equational one.
-/

namespace ProtSat

open Term

/-! ### Expressions -/

/-- The expression language of the protocol DSL.

Constants (agent names, nonce names, keys) are written directly; var x reads the
session's local store; the constructors mirror Term; the destructors (fst, snd,
decS, decA) are what makes receive meaningful. -/
inductive Expr where
  /-- The name of an agent. -/
  | agent (A : Agent)
  /-- A nonce name: the value is whatever the session stored under it. -/
  | nonce (N : NonceName)
  /-- The long-term symmetric key K(a,b). -/
  | shrk (a b : Agent)
  /-- The public key of a. -/
  | pubk (a : Agent)
  /-- The private key of a. -/
  | privk (a : Agent)
  /-- Read a variable of the local store. -/
  | var (x : Var)
  /-- Pairing. -/
  | pair (e1 e2 : Expr)
  /-- Symmetric encryption: both the plaintext and the key are expressions, so a
  session can decrypt a key it received and then use it. -/
  | encS (m k : Expr)
  /-- Asymmetric encryption for agent a. -/
  | encA (m : Expr) (a : Agent)
  /-- Hashing. -/
  | hash (e : Expr)
  /-- First projection. -/
  | fst (e : Expr)
  /-- Second projection. -/
  | snd (e : Expr)
  /-- Symmetric decryption. -/
  | decS (m k : Expr)
  /-- Asymmetric decryption with the private key of a. -/
  | decA (m : Expr) (a : Agent)
  deriving Repr, DecidableEq

namespace Expr

/-- Look up a variable in a session store (an association list). -/
def lookup (x : Var) (s : List (Var × Term)) : Option Term :=
  match s with
  | [] => none
  | (y, t) :: rest => if y = x then some t else lookup x rest

/-- **Evaluation of an expression in a session store.**  Partial: a destructor
that does not apply leaves the action disabled. -/
def eval : Expr -> List (Var × Term) -> Option Term
  | agent A, _ => some (Term.agent A)
  | nonce N, _ => some (Term.nonce N)
  | shrk a b, _ => some (Term.key (Key.shrk a b))
  | pubk a, _ => some (Term.key (Key.pub a))
  | privk a, _ => some (Term.key (Key.priv a))
  | var x, s => lookup x s
  | pair e1 e2, s => eval e1 s >>= fun x => eval e2 s >>= fun y => some (Term.pair x y)
  | encS m k, s => eval m s >>= fun x => eval k s >>= fun ky => Term.asKey ky >>= fun k =>
      some (Term.encS x k)
  | encA m a, s => eval m s >>= fun x => some (Term.encA x a)
  | hash e, s => eval e s >>= fun x => some (Term.hash x)
  | fst e, s => eval e s >>= fun x => match x with
      | Term.pair a _ => some a
      | _ => none
  | snd e, s => eval e s >>= fun x => match x with
      | Term.pair _ b => some b
      | _ => none
  | decS m k, s => eval m s >>= fun x => eval k s >>= fun ky => Term.asKey ky >>= fun k =>
      match x with
      | Term.encS a b => if b = k then some a else none
      | _ => none
  | decA m a, s => eval m s >>= fun x =>
      match x with
      | Term.encA b c => if c = a then some b else none
      | _ => none

/-- The variables an expression reads. -/
def vars : Expr -> List Var
  | agent _ => []
  | nonce _ => []
  | shrk _ _ => []
  | pubk _ => []
  | privk _ => []
  | var x => [x]
  | pair e1 e2 => e1.vars ++ e2.vars
  | encS m k => m.vars ++ k.vars
  | encA m _ => m.vars
  | hash e => e.vars
  | fst e => e.vars
  | snd e => e.vars
  | decS m k => m.vars ++ k.vars
  | decA m _ => m.vars

/-- An expression is closed when it reads no variable, i.e. its value is the same
in every store.  Closed expressions are what static secret declarations and
protocol seeds are built from. -/
def isClosed (e : Expr) : Bool := e.vars.isEmpty

/-- The subexpressions of an expression: the source of the Tseitin variables the
SAT encoding uses to represent "this expression evaluates to that message". -/
def subexpressions : Expr -> List Expr
  | agent A => [agent A]
  | nonce N => [nonce N]
  | shrk a b => [shrk a b]
  | pubk a => [pubk a]
  | privk a => [privk a]
  | var x => [var x]
  | pair e1 e2 => pair e1 e2 :: (e1.subexpressions ++ e2.subexpressions)
  | encS m k => encS m k :: (m.subexpressions ++ k.subexpressions)
  | encA m a => encA m a :: m.subexpressions
  | hash m => hash m :: m.subexpressions
  | fst m => fst m :: m.subexpressions
  | snd m => snd m :: m.subexpressions
  | decS m k => decS m k :: (m.subexpressions ++ k.subexpressions)
  | decA m a => decA m a :: m.subexpressions

end Expr

/-! ### Actions, roles, sessions -/

/-- The actions of the protocol language (specification section 3). -/
inductive Action where
  /-- x := fresh nonce N.  The concrete value is chosen by the environment out of
  the bounded nonce domain, subject to the freshness constraint. -/
  | fresh (x : Var) (N : NonceName)
  /-- Send the value of e to a.  The network is attacker-controlled, so 'to a'
  records intent: the attacker sees the message and may deliver anything it knows. -/
  | send (a : Agent) (e : Expr)
  /-- Receive a message from a into x.  The attacker chooses any message it can
  deduce, which is what makes replay representable. -/
  | recv (a : Agent) (x : Var)
  /-- Local state update: x := value of e, computed from what the session already
  holds. -/
  | assign (x : Var) (e : Expr)
  /-- Equality check: enabled only when both sides evaluate to the same message. -/
  | check (e1 e2 : Expr)
  /-- Declare the value of e secret.  Secrets are checked statically (see
  Protocol.closedSecretTerms); the action documents intent and advances the
  control state. -/
  | secret (e : Expr)
  /-- Authentication event: this role claims to have started a run with peer on the
  value v. -/
  | claim (tag : Tag) (peer v : Expr)
  /-- Authentication event: this role commits, believing it has completed a run with
  peer on the value v. -/
  | commit (tag : Tag) (peer v : Expr)
  deriving Repr, DecidableEq

namespace Action

/-- The variables an action writes into its session store. -/
def written : Action -> List Var
  | Action.fresh x _ => [x]
  | Action.recv _ x => [x]
  | Action.assign x _ => [x]
  | _ => []

/-- The expressions an action evaluates: the subexpressions of everything the action reads.
These are the entries the SAT encoding's expression table must contain. -/
def exprs : Action -> List Expr
  | Action.fresh _ _ => []
  | Action.send _ e => Expr.subexpressions e
  | Action.recv _ _ => []
  | Action.assign _ e => Expr.subexpressions e
  | Action.check e1 e2 => e1.subexpressions ++ e2.subexpressions
  | Action.secret e => Expr.subexpressions e
  | Action.claim _ peer v => peer.subexpressions ++ v.subexpressions
  | Action.commit _ peer v => peer.subexpressions ++ v.subexpressions

end Action

/-- A role is a program: a list of actions executed in order. -/
structure Role where
  acts : List Action
  deriving Repr, DecidableEq

/-- A session is a role played by two agents.  Sessions are the units the bound
"maximum number of sessions" counts. -/
structure Session where
  role : Nat
  self : Agent
  peer : Agent
  deriving Repr, DecidableEq

/-- What a session's local state looks like at one point of a run: a program
counter into the role and a store mapping variables to messages. -/
structure SessState where
  pc : Nat
  store : List (Var × Term)
  deriving Repr, DecidableEq

/-! ### Security properties -/

/-- A declared secret.

* closed e: the value of a closed expression (a long-term key, a pre-shared
  secret, a named nonce) must never be deducible;
* store q x: the value held by variable x of session q must never be deducible -
  this is how "A's freshly generated nonce stays secret" is expressed. -/
inductive Secret where
  | closed (e : Expr)
  | store (q : Nat) (x : Var)
  deriving Repr, DecidableEq

/-- An authentication requirement: every commit of the given tag must be matched by
a claim of the same tag, peer and value somewhere in the run (non-injective
agreement). -/
structure AuthProp where
  tag : Tag
  deriving Repr, DecidableEq

/-! ### The protocol record -/

/-- A protocol: the roles, the sessions to instantiate, the agent and nonce
domains, the set of compromised agents (whose private keys the attacker is given),
the declared secrets and the authentication requirements. -/
structure Protocol where
  /-- The role definitions. -/
  roles : List Role
  /-- The concrete sessions to run in parallel (bounded model checking instantiates
  exactly these). -/
  sessions : List Session
  /-- The agent-name domain: names the attacker may use and keys it may form. -/
  agents : List Agent
  /-- The nonce-value domain for fresh generation. -/
  nonceDomain : List NonceName
  /-- Agents whose long-term private / symmetric keys the attacker holds. -/
  compromised : List Agent
  /-- Declared secrets. -/
  secrets : List Secret
  /-- Authentication requirements. -/
  auths : List AuthProp
  deriving Repr

namespace Protocol

/-- The role played by session q: the role index recorded in the session list. -/
def roleAt (P : Protocol) (q : Nat) : Option Role :=
  match P.sessions.drop q |>.head? with
  | some s => P.roles.drop s.role |>.head?
  | none => none

/-- The action of session q's role at program counter pc; none means the session
has finished (or there is no such session, or its role index is out of range). -/
def actionAt (P : Protocol) (q pc : Nat) : Option Action :=
  (P.roleAt q).map (fun r => (r.acts.drop pc).head?) |>.getD none

/-- Number of actions of session q's role: its control state ranges over 0 .. len. -/
def roleLen (P : Protocol) (q : Nat) : Nat :=
  match P.roleAt q with
  | some r => r.acts.length
  | none => 0

/-- The long-term keys the attacker is given because of the compromise set: the
private key of each compromised agent, and each compromised agent's shared key
with every agent of the domain. -/
def compromisedKeys (P : Protocol) : List Key :=
  P.compromised.flatMap fun a =>
    (Key.priv a) :: (P.agents.map fun b => Key.shrk a b) ++ (P.agents.map fun b => Key.shrk b a)

/-- The *initial* attacker knowledge: agent names, public keys, compromised keys.
Note that honest long-term keys and all fresh nonces are absent: the attacker is
not magically omniscient, which is what specification section 2 demands. -/
def initKn (P : Protocol) : List Term :=
  (P.agents.map Term.agent)
  ++ (P.agents.map fun a => Term.key (Key.pub a))
  ++ (P.compromisedKeys.map Term.key)

/-- The closed secret messages: the value of every closed secret expression. -/
def closedSecretTerms (P : Protocol) : List Term :=
  P.secrets.filterMap fun s => match s with
    | Secret.closed e => Expr.eval e []
    | Secret.store _ _ => none

/-- The variables each session uses: the domain of its store.  Both the variables it writes
and the ones its expressions read are included, so that every store slot the encoding needs
exists. -/
def sessionVars (P : Protocol) (q : Nat) : List Var :=
  ((List.range (P.roleLen q)).flatMap fun pc =>
    match P.actionAt q pc with
    | some a => a.written ++ (a.exprs.flatMap Expr.vars)
    | none => []).eraseDups

end Protocol


/-! ### One-step evaluation

The SAT encoding represents the value of every protocol expression by a variable of a
one-hot group and defines those variables one constructor at a time (a Tseitin-style
translation, specification section 5).  The definitions below are the pieces of that
step-by-step semantics; ProtSat.Bounded uses the same functions to close the term
universe, so the encoding and the universe agree by construction. -/

namespace Expr

/-- The single child of a unary expression, or none for constants and binary forms. -/
def child1 : Expr -> Option Expr
  | encA m _ => some m
  | hash m => some m
  | fst m => some m
  | snd m => some m
  | decA m _ => some m
  | _ => none

/-- The two children of a binary expression. -/
def child2 : Expr -> Option (Expr × Expr)
  | pair a b => some (a, b)
  | encS m k => some (m, k)
  | decS m k => some (m, k)
  | _ => none

/-- One unary step of the expression semantics:
    eval (op c) = stepEval1 (op c) (eval c).
A stuck destructor yields none, exactly as Expr.eval does. -/
def stepEval1 : Expr -> Option Term -> Option Term
  | encA _ a, some x => some (Term.encA x a)
  | hash _, some x => some (Term.hash x)
  | fst _, some (Term.pair a _) => some a
  | snd _, some (Term.pair _ b) => some b
  | decA _ a, some (Term.encA b c) => if c = a then some b else none
  | _, _ => none

/-- One binary step of the expression semantics. -/
def stepEval2 : Expr -> Option Term -> Option Term -> Option Term
  | pair _ _, some x, some y => some (Term.pair x y)
  | encS _ _, some x, some (Term.key k) => some (Term.encS x k)
  | decS _ _, some (Term.encS x y), some (Term.key k) => if y = k then some x else none
  | _, _, _ => none

/-- The value of a closed expression: the constants of the DSL, none for anything that
reads the store. -/
def constVal : Expr -> Option Term
  | agent A => some (Term.agent A)
  | nonce N => some (Term.nonce N)
  | shrk a b => some (Term.key (Key.shrk a b))
  | pubk a => some (Term.key (Key.pub a))
  | privk a => some (Term.key (Key.priv a))
  | _ => none

/-- The one-step decomposition lemmas: each constructor or destructor of the expression
language is one step of evaluation applied to its children's values.  These are the
specification of the Tseitin gates that ProtSat.Encode generates. -/

theorem eval_encA (m : Expr) (a : Agent) (s : List (Var × Term)) :
    Expr.eval (Expr.encA m a) s = stepEval1 (Expr.encA m a) (Expr.eval m s) := by
  cases h : Expr.eval m s <;> simp [Expr.eval, stepEval1, h, Option.bind]

theorem eval_hash (m : Expr) (s : List (Var × Term)) :
    Expr.eval (Expr.hash m) s = stepEval1 (Expr.hash m) (Expr.eval m s) := by
  cases h : Expr.eval m s <;> simp [Expr.eval, stepEval1, h, Option.bind]

theorem eval_fst (m : Expr) (s : List (Var × Term)) :
    Expr.eval (Expr.fst m) s = stepEval1 (Expr.fst m) (Expr.eval m s) := by
  cases h : Expr.eval m s with
  | none => simp [Expr.eval, stepEval1, h, Option.bind]
  | some t => cases t <;> simp [Expr.eval, stepEval1, h, Option.bind]

theorem eval_snd (m : Expr) (s : List (Var × Term)) :
    Expr.eval (Expr.snd m) s = stepEval1 (Expr.snd m) (Expr.eval m s) := by
  cases h : Expr.eval m s with
  | none => simp [Expr.eval, stepEval1, h, Option.bind]
  | some t => cases t <;> simp [Expr.eval, stepEval1, h, Option.bind]

theorem eval_decA (m : Expr) (a : Agent) (s : List (Var × Term)) :
    Expr.eval (Expr.decA m a) s = stepEval1 (Expr.decA m a) (Expr.eval m s) := by
  cases h : Expr.eval m s with
  | none => simp [Expr.eval, stepEval1, h, Option.bind]
  | some t => cases t <;> simp [Expr.eval, stepEval1, h, Option.bind]

theorem eval_pair (a b : Expr) (s : List (Var × Term)) :
    Expr.eval (Expr.pair a b) s =
      stepEval2 (Expr.pair a b) (Expr.eval a s) (Expr.eval b s) := by
  cases h₁ : Expr.eval a s with
  | none => simp [Expr.eval, stepEval2, h₁, Option.bind]
  | some x =>
      cases h₂ : Expr.eval b s with
      | none => simp [Expr.eval, stepEval2, h₁, h₂, Option.bind]
      | some y => simp [Expr.eval, stepEval2, h₁, h₂, Option.bind]

theorem eval_encS (m k : Expr) (s : List (Var × Term)) :
    Expr.eval (Expr.encS m k) s =
      stepEval2 (Expr.encS m k) (Expr.eval m s) (Expr.eval k s) := by
  cases h₁ : Expr.eval m s with
  | none => simp [Expr.eval, stepEval2, h₁, Option.bind]
  | some x =>
      cases h₂ : Expr.eval k s with
      | none => simp [Expr.eval, stepEval2, h₁, h₂, Option.bind]
      | some y => cases y <;> simp [Expr.eval, stepEval2, h₁, h₂, Option.bind, Term.asKey]

theorem eval_decS (m k : Expr) (s : List (Var × Term)) :
    Expr.eval (Expr.decS m k) s =
      stepEval2 (Expr.decS m k) (Expr.eval m s) (Expr.eval k s) := by
  cases h₁ : Expr.eval m s with
  | none => simp [Expr.eval, stepEval2, h₁, Option.bind]
  | some x =>
      cases x with
      | encS m' k' =>
          cases h₂ : Expr.eval k s with
          | none => simp [Expr.eval, stepEval2, h₁, h₂, Option.bind, Term.asKey]
          | some y => cases y <;> simp [Expr.eval, stepEval2, h₁, h₂, Option.bind, Term.asKey]
      | _ =>
          cases h₂ : Expr.eval k s with
          | none => simp [Expr.eval, stepEval2, h₁, h₂, Option.bind]
          | some y => cases y <;> simp [Expr.eval, stepEval2, h₁, h₂, Option.bind, Term.asKey]

/-- A unary expression evaluates to one step applied to its child's value. -/
theorem eval_child1 {e c : Expr} {s : List (Var × Term)} (h : child1 e = some c) :
    Expr.eval e s = stepEval1 e (Expr.eval c s) := by
  cases e with
  | agent A | nonce N | shrk a b | pubk a | privk a | var x => cases h
  | pair e₁ e₂ => cases h
  | encS m k => cases h
  | encA m a =>
      have hc : m = c := by simpa [child1] using h
      subst hc
      exact eval_encA m a s
  | hash e₁ =>
      have hc : e₁ = c := by simpa [child1] using h
      subst hc
      exact eval_hash e₁ s
  | fst e₁ =>
      have hc : e₁ = c := by simpa [child1] using h
      subst hc
      exact eval_fst e₁ s
  | snd e₁ =>
      have hc : e₁ = c := by simpa [child1] using h
      subst hc
      exact eval_snd e₁ s
  | decS m k => cases h
  | decA m a =>
      have hc : m = c := by simpa [child1] using h
      subst hc
      exact eval_decA m a s

/-- A binary expression evaluates to one step applied to its two children's values. -/
theorem eval_child2 {e a b : Expr} {s : List (Var × Term)}
    (h : child2 e = some (a, b)) :
    Expr.eval e s = stepEval2 e (Expr.eval a s) (Expr.eval b s) := by
  cases e with
  | agent A | nonce N | shrk x y | pubk x | privk x | var x => cases h
  | pair e₁ e₂ =>
      have h' : (e₁, e₂) = (a, b) := by simpa [child2] using h
      cases h'
      exact eval_pair a b s
  | encS m k =>
      have h' : (m, k) = (a, b) := by simpa [child2] using h
      cases h'
      exact eval_encS a b s
  | decS m k =>
      have h' : (m, k) = (a, b) := by simpa [child2] using h
      cases h'
      exact eval_decS a b s
  | encA m _ | hash _ | fst _ | snd _ | decA _ _ => cases h

/-- An expression that is neither unary nor binary nor a variable read is a constant, and
its value does not depend on the store. -/
theorem eval_constVal {e : Expr} {s : List (Var × Term)} (h1 : child1 e = none)
    (h2 : child2 e = none) (hv : ∀ x, e ≠ Expr.var x) :
    Expr.eval e s = constVal e := by
  cases e
  · simp [Expr.eval, constVal]
  · simp [Expr.eval, constVal]
  · simp [Expr.eval, constVal]
  · simp [Expr.eval, constVal]
  · simp [Expr.eval, constVal]
  · exfalso
    exact hv _ (by rfl)
  · simp only [child2] at h2; simp at h2
  · simp only [child2] at h2; simp at h2
  · simp only [child1] at h1; simp at h1
  · simp only [child1] at h1; simp at h1
  · simp only [child1] at h1; simp at h1
  · simp only [child1] at h1; simp at h1
  · simp only [child2] at h2; simp at h2
  · simp only [child1] at h1; simp at h1

/-- Subexpressions are transitive: a subexpression of a subexpression is a
subexpression.  This is what makes the expression table of ProtSat.Encode closed under the
children of its entries, so that one Tseitin gate per table entry suffices. -/
theorem subexpressions_trans : ∀ (e f : Expr), f ∈ e.subexpressions ->
    ∀ g, g ∈ f.subexpressions -> g ∈ e.subexpressions := by
  intro e
  induction e with
  | agent A =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_singleton] at hf
      subst hf
      simpa [Expr.subexpressions] using hg
  | nonce N =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_singleton] at hf
      subst hf
      simpa [Expr.subexpressions] using hg
  | shrk a b =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_singleton] at hf
      subst hf
      simpa [Expr.subexpressions] using hg
  | pubk a =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_singleton] at hf
      subst hf
      simpa [Expr.subexpressions] using hg
  | privk a =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_singleton] at hf
      subst hf
      simpa [Expr.subexpressions] using hg
  | var x =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_singleton] at hf
      subst hf
      simpa [Expr.subexpressions] using hg
  | pair a b ih1 ih2 =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (Or.inl (ih1 f hf g hg))
      · exact Or.inr (Or.inr (ih2 f hf g hg))
  | encS a b ih1 ih2 =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (Or.inl (ih1 f hf g hg))
      · exact Or.inr (Or.inr (ih2 f hf g hg))
  | encA a n iha =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (iha f hf g hg)
  | hash a iha =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (iha f hf g hg)
  | fst a iha =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (iha f hf g hg)
  | snd a iha =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (iha f hf g hg)
  | decS a b ih1 ih2 =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (Or.inl (ih1 f hf g hg))
      · exact Or.inr (Or.inr (ih2 f hf g hg))
  | decA a n iha =>
      intro f hf g hg
      simp only [Expr.subexpressions, List.mem_cons, List.mem_append] at hf ⊢
      rcases hf with rfl | hf
      · simpa [Expr.subexpressions, List.mem_cons, List.mem_append] using hg
      · exact Or.inr (iha f hf g hg)


end Expr

/-! ### Evaluation respects the store through the variables it reads -/

/-- **Evaluation is a function of the readings of its free variables.**  Two stores that
answer the same question for every variable the expression reads evaluate the expression to
the same value.  This is what lets the encoding represent a store by per-variable one-hot
groups instead of by the list itself. -/
theorem Expr.eval_congr {e : Expr} {s s' : List (Var × Term)}
    (h : ∀ x, x ∈ e.vars -> Expr.lookup x s = Expr.lookup x s') :
    Expr.eval e s = Expr.eval e s' := by
  induction e generalizing s s' with
  | agent A => rfl
  | nonce N => rfl
  | shrk a b => rfl
  | pubk a => rfl
  | privk a => rfl
  | var x => exact h x (by simp [Expr.vars])
  | pair e₁ e₂ ih₁ ih₂ =>
      rw [Expr.eval, Expr.eval, ih₁ (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto)),
        ih₂ (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | encS m k ih₁ ih₂ =>
      rw [Expr.eval, Expr.eval, ih₁ (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto)),
        ih₂ (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | encA m a ih =>
      rw [Expr.eval, Expr.eval, ih (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | hash e ih =>
      rw [Expr.eval, Expr.eval, ih (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | fst e ih =>
      rw [Expr.eval, Expr.eval, ih (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | snd e ih =>
      rw [Expr.eval, Expr.eval, ih (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | decS m k ih₁ ih₂ =>
      rw [Expr.eval, Expr.eval, ih₁ (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto)),
        ih₂ (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]
  | decA m a ih =>
      rw [Expr.eval, Expr.eval, ih (by intro x hx; exact h x (by simp [Expr.vars] at *; tauto))]

end ProtSat
