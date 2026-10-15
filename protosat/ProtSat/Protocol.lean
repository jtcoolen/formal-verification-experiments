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

/-- The action of session q's role at program counter pc; none means the session
has finished (or the role index is out of range). -/
def actionAt (P : Protocol) (q pc : Nat) : Option Action :=
  match P.roles.drop q |>.head? with
  | some r => (r.acts.drop pc).head?
  | none => none

/-- Number of actions of session q's role: its control state ranges over 0 .. len. -/
def roleLen (P : Protocol) (q : Nat) : Nat :=
  match P.roles.drop q |>.head? with
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

/-- The variables each session uses: the domain of its store. -/
def sessionVars (P : Protocol) (q : Nat) : List Var :=
  (List.range (P.roleLen q)).flatMap fun pc =>
    match P.actionAt q pc with
    | some (Action.fresh x _) => [x]
    | some (Action.recv _ x) => [x]
    | some (Action.assign x _) => [x]
    | _ => []

end Protocol

end ProtSat
