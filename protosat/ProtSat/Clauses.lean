/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Encode

/-!
# ProtSat: the clause groups of the bounded-reachability encoding

This module generates the propositional formula.  Every group of clauses mirrors one
semantic ingredient of ProtSat.Operational, and the theorems of ProtSat.Encoding turn that
mirroring into the two directions required by specification sections 8A and 8B.

## The event alphabet

The only non-determinism in a step of the labelled transition system is *which* rule of
ProtSat.Rel fires, and the rule determines the successor configuration completely.  So one
step is encoded by a one-hot choice among

    0                 - Ev.idle
    1 + q             - session q performs its current action
    1 + nS + n        - the attacker fires deduction instance n (ProtSat.Encode.DedInst)

A deduction instance is one of the eleven attacker rules instantiated at universe messages:
its conclusion is the message learned and its premises are the messages that must already
be known.  Making the *instance* the event alternative is what lets the justification of a
deduction step be written as a handful of two-literal clauses ("if instance n fires then
its premises are known") instead of a Tseitin circuit per conclusion.

## Knowledge growth

The attacker's knowledge is a Boolean vector kn i u, one bit per universe message.  Three
clause families pin it down:

* frameClauses: kn i u -> kn (i+1) u (knowledge never shrinks);
* dedClauses: instance n fires -> its premises are known at i and its conclusion is known
  at i+1;
* knSupportClauses: kn (i+1) u -> kn i u, or a deduction instance concluding u fired, or a
  session sent u.

Together they make kn (i+1) u true *exactly when* the message is justified, which is what
specification section 8A needs (the decoded knowledge must be the knowledge of a real run,
not a guess) and what section 8B needs in the other direction.
-/

namespace ProtSat.Encode

open ProtSat Term OneHot Bounded Attacker
open Protocol

/-! ### The universe hypothesis -/

/-- A value is admissible for a universe when it is one of its messages or the unset value.
-/
def admissible (sh : Shape) (v : Val) : Bool :=
  match v with
  | none => true
  | some t => sh.U.contains t

theorem admissible_valAt_uIdx {sh : Shape} (v : Val) (h : admissible sh v = true) :
    valAt sh (uIdx sh v) = v := by
  cases v with
  | none => exact valAt_uIdx_none sh
  | some t =>
      have ht : t ∈ sh.U := by simpa [admissible] using h
      exact valAt_uIdx_some sh ht

/-- **The universe hypothesis** (specification section 4: the bounds must be large enough
for the analysis to mean anything).  The universe is closed under the message operations
that the protocol's expressions perform, and it contains the value of every closed
expression of the protocol.  This is a decidable property of P and B; the analyser checks it
before trusting its answer, and reports that the bounds are too small when it fails.  All
the encoding theorems below assume it. -/
def univClosed (sh : Shape) (P : Protocol) : Prop :=
  (∀ e ∈ allExprs P, ∀ v ∈ vals sh.U, admissible sh (Expr.stepEval1 e v)) ∧
  (∀ e ∈ allExprs P, ∀ v ∈ vals sh.U, ∀ w ∈ vals sh.U,
      admissible sh (Expr.stepEval2 e v w)) ∧
  (∀ e ∈ allExprs P, admissible sh (Expr.constVal e))

/-! ### Decoding a run from an assignment -/

/-- The value selected by a one-hot group over the universe indices. -/
def decVal (sh : Shape) (o : Oh Nat) (a : Assignment) : Val :=
  match o.decode a with
  | some u => valAt sh u
  | none => none

/-- The value held by variable x of session q at step i. -/
def decSt (sh : Shape) (a : Assignment) (i q x : Nat) : Val :=
  decVal sh (stOh sh i q x) a

/-- The value of expression e in session q at step i, as read off the Tseitin groups. -/
def decXe (sh : Shape) (P : Protocol) (a : Assignment) (i q : Nat) (e : Expr) : Val :=
  decVal sh (xeOh sh i q (eIdx P e)) a

/-- The message the attacker delivers to session q at step i. -/
def decDeliver (sh : Shape) (a : Assignment) (i q : Nat) : Term :=
  (decVal sh (dlOh sh i q) a).getD (Term.nonce 0)

/-- The nonce value session q picks at step i. -/
def decNonce (sh : Shape) (a : Assignment) (i q : Nat) : NonceName :=
  match (frOh sh i q).decode a with
  | some d => (rget sh.D d).getD 0
  | none => 0

/-- The event of step i selected by the assignment. -/
def decEv (sh : Shape) (P : Protocol) (a : Assignment) (i : Nat) : Ev :=
  match (evOh sh i).decode a with
  | none => Ev.idle
  | some k =>
      if k = 0 then Ev.idle
      else if h : k < 1 + shS sh then
        Ev.act (k - 1) (decDeliver sh a i (k - 1)) (decNonce sh a i (k - 1))
      else
        match instAt sh (k - 1 - shS sh) with
        | some inst => match valAt sh inst.concl with
            | some t => Ev.ded t
            | none => Ev.idle
        | none => Ev.idle

/-- The message step i teaches the attacker, if it teaches it anything: the conclusion of
the deduction instance that fired, or the value a session sent. -/
def decLearn (sh : Shape) (P : Protocol) (a : Assignment) (i : Nat) : Option Term :=
  match (evOh sh i).decode a with
  | none => none
  | some k =>
      if k = 0 then none
      else if h : k < 1 + shS sh then
        match P.actionAt (k - 1) (decodePc sh a i (k - 1)) with
        | some (Action.send _ e) => decXe sh P a i (k - 1) e
        | _ => none
      else
        match instAt sh (k - 1 - shS sh) with
        | some inst => valAt sh inst.concl
        | none => none

/-- The attacker's knowledge after i steps: the initial knowledge, extended by whatever
each of the first i steps taught.  Building the decoded knowledge this way makes the
decoded configuration a literal successor of the previous one under ProtSat.Rel. -/
def decKnSeq (sh : Shape) (P : Protocol) (a : Assignment) : Nat -> List Term
  | 0 => P.initKn
  | i + 1 => decKnSeq sh P a i ++ (decLearn sh P a i).toList

/-- The configuration decoded from an assignment at step i. -/
def decCfg (sh : Shape) (P : Protocol) (a : Assignment) (i : Nat) : Cfg :=
  { sess := (List.range sh.nS1).map fun q =>
      { pc := decodePc sh a i q, store := decodeStore sh a i q },
    kn := decKnSeq sh P a i }

/-! ### Iteration helpers

Each clause family is a concatenation over the finite index sets of the shape: steps,
sessions, program counters, store slots, values, universe messages and deduction instances.
The helpers below hide the parentheses so that each family reads as one line per index set.
The "each" family produces lists of clauses, the "map" and "lits" families lists of literals.
-/

/-- Concatenate over the steps 0 .. sh.steps - 1. -/
def eachStep (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range sh.steps).flatMap f

/-- Concatenate over the configurations 0 .. sh.steps. -/
def eachStep1 (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (sh.steps + 1)).flatMap f

/-- Concatenate over the sessions. -/
def eachSess (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (shS sh)).flatMap f

/-- Concatenate over the program-counter values. -/
def eachPc (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (shPc sh)).flatMap f

/-- Concatenate over the store slots. -/
def eachVar (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (shV sh)).flatMap f

/-- Concatenate over the values (universe messages plus unset). -/
def eachVal (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (shVal sh)).flatMap f

/-- Concatenate over the universe messages. -/
def eachMsg (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range sh.U.length).flatMap f

/-- Concatenate over the expression table. -/
def eachExpr (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (shE sh)).flatMap f

/-- Concatenate over the deduction instances. -/
def eachInst (sh : Shape) (f : Nat -> List (List Lit)) : List (List Lit) :=
  (List.range (nInst sh)).flatMap f

/-- Map over the values. -/
def mapVal (sh : Shape) (f : Nat -> List Lit) : List (List Lit) :=
  (List.range (shVal sh)).map f

/-- Map over the universe messages. -/
def mapMsg (sh : Shape) (f : Nat -> List Lit) : List (List Lit) :=
  (List.range sh.U.length).map f

/-- Concatenate literals over the sessions. -/
def litsSess (sh : Shape) (f : Nat -> List Lit) : List Lit :=
  (List.range (shS sh)).flatMap f

/-- Concatenate literals over the program counters. -/
def litsPc (sh : Shape) (f : Nat -> List Lit) : List Lit :=
  (List.range (shPc sh)).flatMap f

/-- Concatenate literals over the store slots. -/
def litsVar (sh : Shape) (f : Nat -> List Lit) : List Lit :=
  (List.range (shV sh)).flatMap f

/-- Concatenate literals over the universe messages. -/
def litsMsg (sh : Shape) (f : Nat -> List Lit) : List Lit :=
  (List.range sh.U.length).flatMap f

/-- Concatenate literals over the configurations. -/
def litsStep1 (sh : Shape) (f : Nat -> List Lit) : List Lit :=
  (List.range (sh.steps + 1)).flatMap f

/-- Concatenate literals over the deduction instances. -/
def litsInst (sh : Shape) (f : Nat -> List Lit) : List Lit :=
  (List.range (nInst sh)).flatMap f

/-! ### Group 1: the one-hot conditions -/

/-- The one-hot clauses of the program-counter groups. -/
def ohPcClauses (sh : Shape) : List (List Lit) :=
  (List.range (sh.steps + 1)).flatMap fun i =>
    (List.range (shS sh)).flatMap fun q => (pcOh sh i q).clauses.clauses

/-- The one-hot clauses of the store groups. -/
def ohStClauses (sh : Shape) : List (List Lit) :=
  (List.range (sh.steps + 1)).flatMap fun i =>
    (List.range (shS sh)).flatMap fun q =>
      (List.range (shV sh)).flatMap fun x => (stOh sh i q x).clauses.clauses

/-- The one-hot clauses of the expression-evaluation groups. -/
def ohXeClauses (sh : Shape) : List (List Lit) :=
  (List.range (sh.steps + 1)).flatMap fun i =>
    (List.range (shS sh)).flatMap fun q =>
      (List.range (shE sh)).flatMap fun e => (xeOh sh i q e).clauses.clauses

/-- The one-hot clauses of the event groups. -/
def ohEvClauses (sh : Shape) : List (List Lit) :=
  (List.range sh.steps).flatMap fun i => (evOh sh i).clauses.clauses

/-- The one-hot clauses of the delivery groups. -/
def ohDlClauses (sh : Shape) : List (List Lit) :=
  (List.range sh.steps).flatMap fun i =>
    (List.range (shS sh)).flatMap fun q => (dlOh sh i q).clauses.clauses

/-- The one-hot clauses of the fresh-nonce groups. -/
def ohFrClauses (sh : Shape) : List (List Lit) :=
  (List.range sh.steps).flatMap fun i =>
    (List.range (shS sh)).flatMap fun q => (frOh sh i q).clauses.clauses

/-- Each group of variables is one-hot: exactly one alternative is selected. -/
def oneHotClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf ([ohPcClauses sh, ohStClauses sh, ohXeClauses sh,
    ohEvClauses sh, ohDlClauses sh, ohFrClauses sh].flatMap id)

/-! ### Group 2: the initial configuration -/

/-- Step 0 puts every session's program counter at 0. -/
def initPcClauses (sh : Shape) (q : Nat) : List (List Lit) :=
  (List.range (shPc sh)).map fun c =>
    if c = 0 then [pos (vpc sh 0 q c)] else [neg (vpc sh 0 q c)]

/-- Step 0 leaves every store slot unset: the unset value is the last index. -/
def initStClauses (sh : Shape) (q x : Nat) : List (List Lit) :=
  (List.range (shVal sh)).map fun u =>
    if u = sh.U.length then [pos (vst sh 0 q x u)] else [neg (vst sh 0 q x u)]

/-- Does the attacker hold the universe message with number u at the start? -/
def initKnHolds (sh : Shape) (P : Protocol) (u : Nat) : Bool :=
  match valAt sh u with
  | some t => t ∈ P.initKn
  | none => false

/-- Step 0 gives the attacker exactly the initial knowledge of ProtSat.Protocol.initKn:
this is where the model states what the attacker is given at the start, and nothing more. -/
def initKnClauses (sh : Shape) (P : Protocol) : List (List Lit) :=
  (List.range sh.U.length).map fun u =>
    if initKnHolds sh P u then [pos (vkn sh 0 u)] else [neg (vkn sh 0 u)]

/-- Step 0 is ProtSat.initCfg. -/
def initClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf ((eachSess sh fun q => initPcClauses sh q)
    ++ (eachSess sh fun q => eachVar sh fun x => initStClauses sh q x)
    ++ initKnClauses sh P)

/-! ### Group 3: frame conditions -/

/-- The guard "session q does not act at step i while its program counter is c": the
clauses below are implications whose antecedent is the negation of these literals. -/
def actGuard (sh : Shape) (i q c : Nat) : List Lit :=
  [neg (evAct sh i q), neg (vpc sh i q c)]

/-- The attacker's knowledge never shrinks. -/
def frameKnClauses (sh : Shape) (i : Nat) : List (List Lit) :=
  mapMsg sh fun u => [neg (vkn sh i u), pos (vkn sh (i + 1) u)]

/-- A session that does not act keeps its program counter and its whole store.  Note the
*polarity* of the first literal: the frame condition is the implication "if q acts then the
state is preserved", i.e. the clause (evAct or not pc_i or pc_{i+1}); with a negated guard
the clause would be satisfied by the very sessions it is meant to constrain. -/
def frameSessClauses (sh : Shape) (i q : Nat) : List (List Lit) :=
  ((List.range (shPc sh)).map fun c =>
      [pos (evAct sh i q), neg (vpc sh i q c), pos (vpc sh (i + 1) q c)])
    ++ (eachVar sh fun x => mapVal sh fun u =>
          [pos (evAct sh i q), neg (vst sh i q x u), pos (vst sh (i + 1) q x u)])

/-- The frame conditions of the encoding; they mirror the frame lemmas of
ProtSat.Operational. -/
def frameClauses (sh : Shape) : CNF :=
  cnfOf (eachStep sh fun i =>
    frameKnClauses sh i ++ eachSess sh fun q => frameSessClauses sh i q)

/-! ### Group 4: Tseitin clauses for expression evaluation -/

/-- The value index produced by one unary step, as a function of the input index. -/
def f1 (sh : Shape) (e : Expr) : Nat -> Nat :=
  fun u => uIdx sh (Expr.stepEval1 e (valAt sh u))

/-- The value index produced by one binary step. -/
def f2 (sh : Shape) (e : Expr) : Nat -> Nat -> Nat :=
  fun u v => uIdx sh (Expr.stepEval2 e (valAt sh u) (valAt sh v))

/-- The definitional clauses of a leaf of the expression table: reading a variable is the
identity on the store slot, and a constant is pinned to its message. -/
def evalLeafGate (sh : Shape) (P : Protocol) (i q e : Nat) (E : Expr) : List (List Lit) :=
  match E with
  | Expr.var x => (fwdClausesOn [] (stOh sh i q x) (fun u => pos (vxe sh i q e u))).clauses
  | _ => [[pos (vxe sh i q e (uIdx sh (Expr.constVal E)))]]

/-- The definitional clauses of one expression of the protocol: the value of a compound
expression is one evaluation step applied to the values of its children.  Because the
output group is one-hot, one definitional clause per input value suffices
(ProtSat.OneHot.fwdClausesOn), so the encoding is linear in the universe for unary
operations and quadratic for binary ones - a genuine compositional (Tseitin) translation
rather than an enumeration of stores. -/
def evalGate (sh : Shape) (P : Protocol) (i q : Nat) (E : Expr) : List (List Lit) :=
  match Expr.child1 E with
  | some c =>
      (fwdClausesOn [] (xeOh sh i q (eIdx P c))
        (fun u => pos (vxe sh i q (eIdx P E) (f1 sh E u)))).clauses
  | none =>
    match Expr.child2 E with
    | some (ca, cb) =>
        (fwd2ClausesOn [] (xeOh sh i q (eIdx P ca)) (xeOh sh i q (eIdx P cb))
          (fun u v => pos (vxe sh i q (eIdx P E) (f2 sh E u v)))).clauses
    | none => evalLeafGate sh P i q (eIdx P E) E

/-- The evaluation clauses of one step and session: one gate per entry of the expression
table. -/
def evalClausesAt (sh : Shape) (P : Protocol) (i q : Nat) : List (List Lit) :=
  (allExprs P).flatMap fun E => evalGate sh P i q E

/-- The evaluation clauses of every step and session. -/
def evalClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf (eachStep1 sh fun i => eachSess sh fun q => evalClausesAt sh P i q)

/-! ### Group 5: step conditions -/

/-- The clauses keeping one variable of an acting session unchanged. -/
def keepVarClauses (sh : Shape) (i q c y : Nat) : List (List Lit) :=
  mapVal sh fun u =>
    actGuard sh i q c ++ [neg (vst sh i q y u), pos (vst sh (i + 1) q y u)]

/-- The clauses keeping every variable of an acting session unchanged. -/
def keepAllClauses (sh : Shape) (i q c : Nat) : List (List Lit) :=
  eachVar sh fun y => keepVarClauses sh i q c y

/-- The clauses keeping every variable except x unchanged. -/
def keepExceptClauses (sh : Shape) (i q c x : Nat) : List (List Lit) :=
  eachVar sh fun y => if y == x then [] else keepVarClauses sh i q c y

/-- The fresh clauses of one nonce alternative: a value outside the nonce domain is not
fresh, so the alternative is excluded; otherwise the store slot is set to that nonce. -/
def freshStepClauses (sh : Shape) (i q c x d : Nat) : List (List Lit) :=
  let g := actGuard sh i q c
  match rget sh.D d with
  | none => [g ++ [neg (vfr sh i q d)]]
  | some N => [g ++ [neg (vfr sh i q d), pos (vst sh (i + 1) q x (uIdx sh (some (Term.nonce N))))]]

/-- The clauses for one (step, session, program counter) triple: if session q acts while
its program counter is c, the successor configuration is the one ProtSat.Rel prescribes for
the action at (q, c).  One family per introduction rule of Rel.  When there is no action at
(q, c) the family says that session q simply cannot act. -/
def stepClausesAt (sh : Shape) (P : Protocol) (i q c : Nat) : List (List Lit) :=
  let g := actGuard sh i q c
  let adv := [g ++ [pos (vpc sh (i + 1) q (c + 1))]]
  match P.actionAt q c with
  | none => [g]
  | some (Action.fresh x _) =>
      adv ++ keepExceptClauses sh i q c x
        ++ ((List.range (shD sh)).flatMap fun d => freshStepClauses sh i q c x d)
        ++ [g ++ [neg (vfr sh i q (shD sh - 1))]]
  | some (Action.send _ e) =>
      let E := eIdx P e
      adv ++ keepAllClauses sh i q c
        ++ [g ++ [neg (vxe sh i q E (sh.U.length))]]
        ++ mapMsg sh fun u => g ++ [neg (vxe sh i q E u), pos (vkn sh (i + 1) u)]
  | some (Action.recv _ x) =>
      adv ++ keepExceptClauses sh i q c x
        ++ (eachVal sh fun u =>
              if u < sh.U.length then
                [g ++ [neg (vdl sh i q u), pos (vst sh (i + 1) q x u)],
                 g ++ [neg (vdl sh i q u), pos (vkn sh i u)]]
              else [g ++ [neg (vdl sh i q u)]])
  | some (Action.assign x e) =>
      let E := eIdx P e
      adv ++ keepExceptClauses sh i q c x
        ++ (eachVal sh fun u =>
              if u < sh.U.length then
                [g ++ [neg (vxe sh i q E u), pos (vst sh (i + 1) q x u)]]
              else [g ++ [neg (vxe sh i q E u)]])
  | some (Action.check e1 e2) =>
      let E1 := eIdx P e1
      let E2 := eIdx P e2
      adv ++ keepAllClauses sh i q c
        ++ [g ++ [neg (vxe sh i q E1 (sh.U.length))],
            g ++ [neg (vxe sh i q E2 (sh.U.length))]]
        ++ (eachVal sh fun u => (List.range (shVal sh)).filterMap fun v =>
              if u == v then none
              else some (g ++ [neg (vxe sh i q E1 u), neg (vxe sh i q E2 v)]))
  | some (Action.secret _) => adv ++ keepAllClauses sh i q c
  | some (Action.claim _ _ _) => adv ++ keepAllClauses sh i q c
  | some (Action.commit _ _ _) => adv ++ keepAllClauses sh i q c

/-- The step clauses of the whole encoding. -/
def stepClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf (eachStep sh fun i => eachSess sh fun q => eachPc sh fun c =>
    stepClausesAt sh P i q c)

/-! ### Group 6: deduction instances -/

/-- If deduction instance n fires at step i then its premises are known at step i and its
conclusion is known at step i+1.  One clause per premise: this is the propositional form of
the eleven rules of specification section 2. -/
def dedClausesAt (sh : Shape) (i n : Nat) : List (List Lit) :=
  match instAt sh n with
  | none => []
  | some inst =>
      ((inst.prem.map fun p => [neg (evDed sh i n), pos (vkn sh i p)])
        ++ [[neg (evDed sh i n), pos (vkn sh (i + 1) inst.concl)]])

/-- The deduction clauses. -/
def dedClauses (sh : Shape) : CNF :=
  cnfOf (eachStep sh fun i => eachInst sh fun n => dedClausesAt sh i n)

/-- The conjunction saying "session q publishes the message with number u at step i by
sending it", if its action at program counter c is a send of an expression with that value.
-/
def sendPublisher (sh : Shape) (P : Protocol) (i q c u : Nat) : List Lit :=
  match P.actionAt q c with
  | some (Action.send _ e) =>
      [pos (evAct sh i q), pos (vpc sh i q c), pos (vxe sh i q (eIdx P e) u)]
  | _ => []

/-- The conjunction saying "the deduction instance concluding in u fires at step i". -/
def instPublisher (sh : Shape) (i n u : Nat) : List Lit :=
  match instAt sh n with
  | some inst => if inst.concl = u then [pos (evDed sh i n)] else []
  | none => []

/-- The auxiliary variable defining the conjunction "session q acts at step i with program
counter c and the value it sends is u".  The support clauses need a *conjunction* per
publisher, and a conjunction can only appear inside a clause through a definition. -/
def vpb (sh : Shape) (i q c u : Nat) : BVar :=
  bsTotal sh + ((i * shS sh + q) * shPc sh + c) * shVal sh + u

/-- The size of the publisher-auxiliary block. -/
def szPb (sh : Shape) : Nat := sh.steps * shS sh * shPc sh * shVal sh

/-- The Tseitin definitions of the publisher conjunctions of one step. -/
def pubAuxEntry (sh : Shape) (P : Protocol) (i q c u : Nat) : List (List Lit) :=
  match P.actionAt q c with
  | some (Action.send _ e) =>
      (andNDef (vpb sh i q c u)
        [pos (evAct sh i q), pos (vpc sh i q c), pos (vxe sh i q (eIdx P e) u)]).clauses
  | _ => []

/-- The Tseitin definitions of all publisher conjunctions. -/
def pubAuxClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf (eachStep sh fun i => eachSess sh fun q => eachPc sh fun c =>
    (List.range sh.U.length).flatMap fun u => pubAuxEntry sh P i q c u)

/-- The publisher literal of one (session, counter) position: the auxiliary variable of the
conjunction "this session sends a value equal to u", present only for send actions. -/
def sendPubLit (sh : Shape) (P : Protocol) (i q c u : Nat) : List Lit :=
  match P.actionAt q c with
  | some (Action.send _ _) => [pos (vpb sh i q c u)]
  | _ => []

/-- All the ways the message with number u can be published at step i, as the disjunction of
the deduction-instance events concluding in u and the publisher conjunctions. -/
def publisherLits (sh : Shape) (P : Protocol) (i u : Nat) : List Lit :=
  (litsSess sh fun q => litsPc sh fun c => sendPubLit sh P i q c u)
    ++ litsInst sh fun n => instPublisher sh i n u

/-- Knowledge is justified: a message known at step i+1 was known at step i, or is the
conclusion of a deduction instance that fired, or was sent by a session.  Without this
group the solver could simply declare every universe message known, which is exactly the
"approximate deduction" that specification section 2 forbids. -/
def knSupportClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf (eachStep sh fun i => mapMsg sh fun u =>
    [neg (vkn sh (i + 1) u), pos (vkn sh i u)] ++ publisherLits sh P i u)

/-- The freshness clauses of one (step, session, program counter, nonce alternative): the
chosen nonce may not already sit in some session's store, nor be known to the attacker.
This mirrors ProtSat.nonceUsed, the side condition of ProtSat.Rel.rFresh. -/
def freshUseClauses (sh : Shape) (i q c d : Nat) : List (List Lit) :=
  match rget sh.D d with
  | none => []
  | some N =>
      let n := uIdx sh (some (Term.nonce N))
      let g := actGuard sh i q c
      ((List.range (shS sh)).flatMap fun r =>
          (List.range (shV sh)).map fun x =>
            g ++ [neg (vfr sh i q d), neg (vst sh i r x n)])
        ++ [g ++ [neg (vfr sh i q d), neg (vkn sh i n)]]

/-- The freshness clauses of one action position. -/
def freshClausesAt (sh : Shape) (P : Protocol) (i q c : Nat) : List (List Lit) :=
  match P.actionAt q c with
  | some (Action.fresh _ _) => (List.range (shD sh)).flatMap fun d =>
      freshUseClauses sh i q c d
  | _ => []

/-- The freshness clauses of the whole encoding. -/
def freshClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf (eachStep sh fun i => eachSess sh fun q => eachPc sh fun c =>
    freshClausesAt sh P i q c)

/-! ### Group 7: the violation condition -/

/-- Auxiliary variables for the conjunctions of the violation condition: one per
(step, session, variable, value) quadruple, defining "session q holds message u and the
attacker knows it". -/
def bsAu (sh : Shape) : Nat := bsTotal sh + szPb sh

/-- The size of the auxiliary block. -/
def szAu (sh : Shape) : Nat := (sh.steps + 1) * shS sh * shV sh * shVal sh

/-- The auxiliary variable of the store-leak conjunction at (i, q, x, u). -/
def vau (sh : Shape) (i q x u : Nat) : BVar :=
  bsAu sh + ((i * shS sh + q) * shV sh + x) * shVal sh + u

/-- The total number of variables of the encoding. -/
def nVarsAll (sh : Shape) : Nat := bsAu sh + szAu sh

/-- Is the value of variable x of session q declared secret?  A session that the bounds do
not instantiate cannot leak anything. -/
def storeSecret (sh : Shape) (P : Protocol) (q x : Nat) : Bool :=
  q < sh.nS1 && (Secret.store q x) ∈ P.secrets

/-- The Tseitin definitions of the store-leak conjunctions of one slot. -/
def leakAuxEntry (sh : Shape) (P : Protocol) (i q x : Nat) : List (List Lit) :=
  if storeSecret sh P q x then
    (List.range sh.U.length).flatMap fun u =>
      (andNDef (vau sh i q x u) [pos (vst sh i q x u), pos (vkn sh i u)]).clauses
  else []

/-- The clauses defining the store-leak auxiliary variables. -/
def leakAuxClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf (eachStep1 sh fun i => eachSess sh fun q => eachVar sh fun x =>
    leakAuxEntry sh P i q x)

/-- The literals saying "a closed declared secret is known at step i". -/
def closedLeakLits (sh : Shape) (P : Protocol) (i : Nat) : List Lit :=
  (List.range sh.U.length).filterMap fun u =>
    match valAt sh u with
    | some t => if t ∈ P.closedSecretTerms then some (pos (vkn sh i u)) else none
    | none => none

/-- The literals saying "a store secret of session q leaks at step i". -/
def storeLeakLitsAt (sh : Shape) (P : Protocol) (i q x : Nat) : List Lit :=
  if storeSecret sh P q x then
    (List.range sh.U.length).map fun u => pos (vau sh i q x u)
  else []

/-- The store-leak literals at step i. -/
def storeLeakLits (sh : Shape) (P : Protocol) (i : Nat) : List Lit :=
  litsSess sh fun q => litsVar sh fun x => storeLeakLitsAt sh P i q x

/-- The violation literals: one per way the declared security property can fail. -/
def violationLits (sh : Shape) (P : Protocol) : List Lit :=
  litsStep1 sh fun i => closedLeakLits sh P i ++ storeLeakLits sh P i

/-- The single clause demanding that the violation actually occurs. -/
def violationClauses (sh : Shape) (P : Protocol) : CNF :=
  cnfOf [violationLits sh P]

/-- The ten clause groups of the encoding, in the order they are documented. -/
def encodeGroups (sh : Shape) (P : Protocol) : List CNF :=
  [oneHotClauses sh P, initClauses sh P, frameClauses sh, evalClauses sh P,
    stepClauses sh P, dedClauses sh, pubAuxClauses sh P, knSupportClauses sh P,
    freshClauses sh P, leakAuxClauses sh P, violationClauses sh P]

/-- **The encoding.**  The CNF formula whose satisfiability is the bounded-attack question
for P under the bounds B (specification section 5). -/
def encode (P : Protocol) (B : Bounds) : CNF :=
  cnfOf ((encodeGroups (shapeOf P B) P).flatMap (·.clauses))

/-- Every clause of a group is a clause of the encoding: the interface through which the
soundness and completeness theorems consume the groups one at a time. -/
theorem sat_encodeGroup {P : Protocol} {B : Bounds} {g : CNF} {a : Assignment}
    (hg : g ∈ encodeGroups (shapeOf P B) P) (h : Sat a (encode P B)) : Sat a g :=
  fun c hc => h _ (List.mem_flatMap.mpr ⟨g, hg, hc⟩)

theorem sat_oneHotClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (oneHotClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_initClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (initClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_frameClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (frameClauses sh) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_evalClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (evalClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_stepClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (stepClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_dedClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (dedClauses sh) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_knSupportClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (knSupportClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_freshClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (freshClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_leakAuxClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (leakAuxClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

theorem sat_violationClauses {P : Protocol} {B : Bounds} {sh : Shape} (hsh : sh = shapeOf P B)
    {a : Assignment} (h : Sat a (encode P B)) : Sat a (violationClauses sh P) := by
  subst hsh
  exact sat_encodeGroup (by simp [encodeGroups]) h

end ProtSat.Encode
