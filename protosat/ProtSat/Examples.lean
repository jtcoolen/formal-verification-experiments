/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Certificate
import ProtSat.Analyzer

/-!
# ProtSat: the protocol examples (specification section 9)

Six protocols, each with its model, its bounds and an executable result:

1. a challenge-response that is secure under explicit assumptions (SAFE within the bounds);
2. a replay-vulnerable protocol (attack found by the solver and independently checked);
3. a secrecy violation caused by key disclosure (attack found and checked);
4. the original Needham-Schroeder public-key protocol;
5. a bounded instance of the Lowe attack on it (independently checked certificate);
6. the Needham-Schroeder-Lowe correction, on which the same attack certificate is rejected.

## How the results are checked

* A certificate (ProtSat.Certificate.Certificate) is concrete data: an initial configuration
  and one entry per step.  checkCertificate P c = true is a closed Boolean computation that
  re-derives every transition from ProtSat.Operational and re-finds the violation itself; it
  is checked here with decide, i.e. by the kernel, and it never calls the SAT solver or looks
  at the encoding.
* An analyzer verdict (ProtSat.Analyzer.analyze) runs the real pipeline: bounded model, CNF,
  DPLL, decoded trace, certificate.  The instances here use Bounds.rounds = 0, i.e. the
  universe is exactly the subterm closure of the protocol's own message shapes, which keeps
  the CNF small enough for the reference solver; the attacks on Needham-Schroeder need the
  attacker to build fresh ciphertexts and are exhibited by certificate.

## What the bounds mean

Bounds.rounds counts constructor-closure rounds over the seed set, so it bounds both the
message depth and the attacker's ability to synthesise new messages; Bounds.steps bounds the
number of events (protocol actions and attacker deductions together).  A SAFE verdict is a
statement about executions inside those bounds and NOT about unbounded security - see the
README for the precise guarantees.
-/

namespace ProtSat.Examples

open ProtSat Term OneHot Bounded Attacker Encode Encoding Certificate Analyzer DPLL
open Protocol

/-! ### Building certificates out of event lists -/

/-- The successor prescribed by the semantics for one event.  This is the same case split as
ProtSat.Encoding.decStep, written independently of the encoding: it only uses the
operational semantics' own successor functions. -/
def simStep (P : Protocol) (C : Cfg) (e : Ev) : Cfg :=
  match e with
  | Ev.idle => C
  | Ev.ded t => succDed C t
  | Ev.act q m d =>
      match P.actionAt q (pcOf C q) with
      | some (Action.fresh x _) => succStore C q x (Term.nonce d)
      | some (Action.send _ ex) =>
          match Expr.eval ex (storeOf C q) with
          | some t => succSend C q t
          | none => succAdvance C q
      | some (Action.recv _ x) => succStore C q x m
      | some (Action.assign x ex) =>
          match Expr.eval ex (storeOf C q) with
          | some t => succStore C q x t
          | none => succAdvance C q
      | some (Action.check _ _) => succAdvance C q
      | some (Action.secret _) => succAdvance C q
      | some (Action.claim _ _ _) => succAdvance C q
      | some (Action.commit _ _ _) => succAdvance C q
      | none => C

/-- Walk a trace from the initial configuration, recording the configuration after each
step.  The result is a certificate: ProtSat.Certificate decides independently whether every
step really is a transition and whether the run violates the property. -/
def certStepsFrom : (P : Protocol) -> Cfg -> List Ev -> List CertStep
  | _, _, [] => []
  | P, C, e :: rest => { ev := e, after := simStep P C e } :: certStepsFrom P (simStep P C e) rest

/-- The certificate built from an event list: the initial configuration of P and one step per
event, with the configuration the semantics prescribes after it. -/
def certOfTrace (P : Protocol) (tr : List Ev) : Certificate :=
  { init := initCfg P, steps := certStepsFrom P (initCfg P) tr }

/-- The steps of a simulated certificate record exactly the events they were built from. -/
theorem certStepsFrom_ev : ∀ (P : Protocol) (tr : List Ev) (C : Cfg),
    (certStepsFrom P C tr).map (fun s => s.ev) = tr := by
  intro P tr
  induction tr with
  | nil => intro C; rfl
  | cons e rest ih => intro C; simp [certStepsFrom, ih]

/-- The trace of the certificate built from an event list is that event list. -/
theorem certOfTrace_trace (P : Protocol) (tr : List Ev) :
    certTrace (certOfTrace P tr) = tr := certStepsFrom_ev P tr (initCfg P)

/-- **The certificate theorem pattern used below.**  If the checker accepts the certificate
of a trace, then that trace is an attack on P: this is specification 8C applied to a
concrete, kernel-checked certificate. -/
theorem attack_of_checked (P : Protocol) (tr : List Ev)
    (h : checkCertificate P (certOfTrace P tr) = true) : Attack P tr := by
  have := checkCertificate_sound (certOfTrace P tr) h
  rwa [certOfTrace_trace] at this


/-! ### Example 1: a challenge-response that is secure under explicit assumptions -/

namespace Challenge

/-- A generates a fresh nonce and sends it to B encrypted under the long-term key K(A,B)
that both parties hold and the attacker does not.  The declared secret is that nonce.

Explicit assumptions, each of them part of the model rather than an informal claim:
* compromised = [], so K(A,B) is not in the attacker's initial knowledge;
* initKn is exactly the public information (agent names and public keys) that
  ProtSat.Protocol.initKn derives - the attacker is given no recorded session;
* the analysed execution has at most two events and one session;
* the nonce domain is the single value the session may pick. -/
def P : Protocol :=
  { roles :=
      [ { acts := [Action.fresh 0 0,
                   Action.send 1 (Expr.encS (Expr.var 0) (Expr.shrk 0 1))] } ],
    sessions := [{ role := 0, self := 0, peer := 1 }],
    agents := [0, 1],
    nonceDomain := [100000],
    compromised := [],
    secrets := [Secret.store 0 0],
    auths := [] }

/-- Two events, one session, subterm-closed universe. -/
def B : Bounds := { steps := 2, rounds := 0 }

/-- The bounds state the question: every closed expression of P denotes a universe message. -/
theorem bounds_ok : univClosedBool (shapeOf P B) P = true := by decide

-- The size of the generated CNF.
#eval (nVarsAll (shapeOf P B), (encode P B).clauses.length)

-- **Executable result: the generated CNF is unsatisfiable within these bounds**, i.e. no
-- bounded execution inside the universe leaks the declared store secret.  The demo
-- (lake exe protosatDemo) runs
-- the whole pipeline - CNF construction, ProtSat.DPLL, verdict - and prints the timing.  The
-- verdict is a computation, not a kernel-checked proposition: the reference solver is a
-- simple list-based DPLL, so its UNSAT search is only feasible at these small bounds.
theorem bounds_state_the_question : univClosed (shapeOf P B) P :=
  (univClosedBool_iff (shapeOf P B) P).mp bounds_ok

-- If the solver says none, the CNF is unsatisfiable: by 8E that is a proof about the formula.
-- Reading it as a security statement needs ProtSat.Query.boundedSafe_of_encodingUnsat.
theorem safe_if_none (h : ProtSat.DPLL.dpll (encode P B) = none) : ProtSat.Unsat (encode P B) :=
  dpll_complete h

-- and then the analyser reports the encoding's unsatisfiability.
theorem verdict_if_none (h : ProtSat.DPLL.dpll (encode P B) = none) :
    analyze P B = Verdict.encodingUnsat := by
  rw [analyze, if_neg (by rw [bounds_ok]; simp), h]

end Challenge

/-! ### Example 2: a replay-vulnerable protocol -/

namespace Replay

/-- B authenticates its peer with a *static* authenticator - the pair (A, pub(B)), both
halves of which are public information - and then hands over the session key K(B,C) in the
clear.  There is no freshness check, so a recorded (or simply rebuilt) authenticator is as
good as a live one: the attacker deduces the pair from public data, replays it, and receives
the key. -/
def P : Protocol :=
  { roles :=
      [ { acts :=
            [Action.recv 0 0,
             Action.check (Expr.var 0) (Expr.pair (Expr.agent 0) (Expr.pubk 1)),
             Action.send 0 (Expr.shrk 1 2)] } ],
    sessions := [{ role := 0, self := 1, peer := 0 }],
    agents := [0, 1, 2],
    nonceDomain := [],
    compromised := [],
    secrets := [Secret.closed (Expr.shrk 1 2)],
    auths := [] }

/-- deduce the authenticator, replay it, check, publish the key. -/
def B : Bounds := { steps := 4, rounds := 0 }

theorem bounds_ok : univClosedBool (shapeOf P B) P = true := by decide

#eval (nVarsAll (shapeOf P B), (encode P B).clauses.length)

/-- **The attack, as an independently checkable certificate** (specification 7 and 9): the
attacker builds the static authenticator from public information (ProtSat.Attacker.pairI),
delivers it, and B sends the secret key.  checkCertificate re-derives every step from
ProtSat.Operational and finds the leak itself; it is checked here by the kernel. -/
def tr : List Ev :=
  [Ev.ded (Term.pair (Term.agent 0) (Term.key (Key.pub 1))),
   Ev.act 0 (Term.pair (Term.agent 0) (Term.key (Key.pub 1))) 0,
   Ev.act 0 (Term.nonce 0) 0,
   Ev.act 0 (Term.key (Key.shrk 1 2)) 0]

/-- The checker accepts it. -/
theorem checked : checkCertificate P (certOfTrace P tr) = true := by decide

/-- Hence the trace is a genuine attack on P (specification 8C). -/
theorem attack : Attack P tr := attack_of_checked P tr checked

end Replay

/-! ### Example 3: a secrecy violation caused by key disclosure -/

namespace KeyDisclosure

/-- A sends the secret nonce under K(A,B).  A is compromised, so the attacker holds K(A,B)
and opens the ciphertext.  The violation is caused by the key disclosure: the very same
protocol with compromised = [] is analysed below and found safe in the same bounds. -/
def P : Protocol :=
  { roles :=
      [ { acts := [Action.send 1 (Expr.encS (Expr.nonce 5) (Expr.shrk 0 1))] },
        { acts := [Action.recv 0 0] } ],
    sessions := [{ role := 0, self := 0, peer := 1 }],
    agents := [0, 1],
    nonceDomain := [],
    compromised := [0],
    secrets := [Secret.closed (Expr.nonce 5)],
    auths := [] }

/-- One send plus one decryption. -/
def B : Bounds := { steps := 2, rounds := 0 }

theorem bounds_ok : univClosedBool (shapeOf P B) P = true := by decide

#eval (nVarsAll (shapeOf P B), (encode P B).clauses.length)

/-- The attack certificate: observe the ciphertext, decrypt it with the disclosed key. -/
def tr : List Ev :=
  [Ev.act 0 (Term.encS (Term.nonce 5) (Key.shrk 0 1)) 0,
   Ev.ded (Term.nonce 5)]

/-- The checker accepts it: the deduction really is the encSD rule with the compromised key. -/
theorem checked : checkCertificate P (certOfTrace P tr) = true := by decide

/-- Hence a genuine attack (specification 8C). -/
theorem attack : Attack P tr := attack_of_checked P tr checked

/-- With the key not disclosed, the same protocol and bounds are safe: the leak really is
caused by the disclosure. -/
def PSafe : Protocol := { P with compromised := [] }

-- With the key not disclosed the same protocol and the same bounds admit no attack; the demo
-- computes that verdict.  (The leak above is therefore caused by the disclosure, not by the
-- message exchange.)
end KeyDisclosure


/-! ### Examples 4 and 5: Needham-Schroeder public key and the Lowe attack -/

namespace NS

open Protocol in
/-- The original Needham-Schroeder public-key protocol (Lowe's notation):

  1. A -> B : {Na, A}_pubB
  2. B -> A : {Nb, Na}_pubA
  3. A -> B : {Nb}_pubB

The roles are written for the attack scenario: session 0 is A (agent 0) initiating with the
intruder I (agent 2), and session 1 is B (agent 1) accepting an initiation that the intruder
sends while pretending to be A.  Roles name their agents literally, because the DSL
instantiates sessions rather than parameterising roles.  The declared secret is B's fresh
nonce Nb (the store slot 1 of session 1). -/
def P : Protocol :=
  { roles :=
      [ { acts :=
            [Action.fresh 0 0,
             Action.send 2 (Expr.encA (Expr.pair (Expr.var 0) (Expr.agent 0)) 2),
             Action.recv 2 1,
             Action.check (Expr.snd (Expr.decA (Expr.var 1) 0)) (Expr.var 0),
             Action.send 2 (Expr.encA (Expr.fst (Expr.decA (Expr.var 1) 0)) 2)] },
        { acts :=
            [Action.recv 0 0,
             Action.fresh 1 1,
             Action.send 0 (Expr.encA (Expr.pair (Expr.var 1)
                                (Expr.fst (Expr.decA (Expr.var 0) 1))) 0),
             Action.recv 0 2,
             Action.check (Expr.decA (Expr.var 2) 1) (Expr.var 1)] } ],
    sessions := [{ role := 0, self := 0, peer := 2 }, { role := 1, self := 1, peer := 0 }],
    agents := [0, 1, 2],
    nonceDomain := [100000, 101001],
    compromised := [2],
    secrets := [Secret.store 1 1],
    auths := [] }

/-- The nonces the two sessions generate. -/
def na : Term := Term.nonce 100000
/-- The responder's fresh nonce: the secret whose loss the certificate exhibits. -/
def nb : Term := Term.nonce 101001

/-- Message 1 as A sends it to I. -/
def mA : Term := Term.encA (Term.pair na (Term.agent 0)) 2
/-- Message 1 rebuilt by I for B - the replay that B cannot distinguish. -/
def mB : Term := Term.encA (Term.pair na (Term.agent 0)) 1
/-- Message 2 as B sends it, believed to be addressed to A. -/
def m2 : Term := Term.encA (Term.pair nb na) 0
/-- Message 3 as A sends it to I. -/
def m3 : Term := Term.encA nb 2
/-- Message 3 rebuilt by I for B. -/
def m3b : Term := Term.encA nb 1

/-- **Lowe's attack on the original Needham-Schroeder protocol** (specification 9.5), as a
list of events.  The intruder runs a session with A, decrypts everything addressed to itself
(its private key is in the initial knowledge because compromised = [2]), and uses A as an
oracle to produce the third message B expects.  A's own check passes because the nonce in
message 2 really is A's nonce - the protocol has no way for A to learn who actually answered. -/
def trace : List Ev :=
  [Ev.act 0 (Term.agent 0) 100000,        -- A: Na := fresh
   Ev.act 0 (Term.agent 0) 0,             -- A -> I : {Na,A}_pubI     (published)
   Ev.ded (Term.pair na (Term.agent 0)),  -- I : decrypt with priv I
   Ev.ded na,                             -- I : project Na
   Ev.ded mB,                             -- I : build {Na,A}_pubB
   Ev.act 1 mB 0,                         -- I -> B : {Na,A}_pubB     (replayed)
   Ev.act 1 (Term.agent 1) 101001,        -- B: Nb := fresh
   Ev.act 1 (Term.agent 1) 0,             -- B -> A : {Nb,Na}_pubA    (published)
   Ev.act 0 m2 0,                         -- I -> A : {Nb,Na}_pubA    (forwarded)
   Ev.act 0 (Term.agent 0) 0,             -- A : check snd(dec) = Na     (passes!)
   Ev.act 0 (Term.agent 0) 0,             -- A -> I : {Nb}_pubI       (published)
   Ev.ded nb,                             -- I : decrypt {Nb}_pubI    ==> B's nonce leaks
   Ev.ded m3b,                            -- I : build {Nb}_pubB
   Ev.act 1 m3b 0]                        -- I -> B : {Nb}_pubB       (B commits to a peer
                                          -- it never spoke to)

/-- **Independently checkable attack trace** (specification 7 and 9): the kernel evaluates the
certificate checker over the simulated run - every transition is re-derived from
ProtSat.Operational and the leak of B's nonce is re-found by the checker itself. -/
theorem checked : checkCertificate P (certOfTrace P trace) = true := by decide

/-- Hence the trace is a genuine attack on Needham-Schroeder (specification 8C). -/
theorem attack : Attack P trace := attack_of_checked P trace checked

-- The attack also breaks non-injective agreement: B commits with no matching claim from A.
-- (The certificate checker's authentication test reports it; see authBreakBool.)


/-- The bounds for the SAT analysis of this protocol.  The full attack needs the intruder to
construct two fresh ciphertexts, so the universe must be closed under one constructor round;
at those bounds the reference solver's search is far too large to run here, which is why the
attack is exhibited by certificate.  The demo prints the CNF size. -/
def B : Bounds := { steps := 14, rounds := 1 }

#eval (nVarsAll (shapeOf P B))

end NS

/-! ### Example 6: the Needham-Schroeder-Lowe correction -/

namespace NSL

open Protocol in
/-- Lowe's corrected protocol: the responder adds its own identity to the second message

  1. A -> B : {Na, A}_pubB
  2. B -> A : {Nb, Na, B}_pubA
  3. A -> B : {Nb}_pubB

and the initiator checks that the identity in the reply is the peer it started with.  The
model below is the same attack scenario as ProtSat.Examples.NS.P: A's session is with I (2),
so A expects the responder to identify itself as 2. -/
def P : Protocol :=
  { roles :=
      [ { acts :=
            [Action.fresh 0 0,
             Action.send 2 (Expr.encA (Expr.pair (Expr.var 0) (Expr.agent 0)) 2),
             Action.recv 2 1,
             Action.check (Expr.snd (Expr.snd (Expr.decA (Expr.var 1) 0))) (Expr.agent 2),
             Action.send 2 (Expr.encA (Expr.fst (Expr.decA (Expr.var 1) 0)) 2)] },
        { acts :=
            [Action.recv 0 0,
             Action.fresh 1 1,
             Action.send 0 (Expr.encA (Expr.pair (Expr.var 1)
                                (Expr.pair (Expr.fst (Expr.decA (Expr.var 0) 1)) (Expr.agent 1))) 0),
             Action.recv 0 2,
             Action.check (Expr.decA (Expr.var 2) 1) (Expr.var 1)] } ],
    sessions := [{ role := 0, self := 0, peer := 2 }, { role := 1, self := 1, peer := 0 }],
    agents := [0, 1, 2],
    nonceDomain := [100000, 101001],
    compromised := [2],
    secrets := [Secret.store 1 1],
    auths := [] }

/-- The same attack script, with the second message carrying B's identity. -/
def m2 : Term := Term.encA (Term.pair NS.nb (Term.pair NS.na (Term.agent 1))) 0

def trace : List Ev :=
  [Ev.act 0 (Term.agent 0) 100000,
   Ev.act 0 (Term.agent 0) 0,
   Ev.ded (Term.pair NS.na (Term.agent 0)),
   Ev.ded NS.na,
   Ev.ded NS.mB,
   Ev.act 1 NS.mB 0,
   Ev.act 1 (Term.agent 1) 101001,
   Ev.act 1 (Term.agent 1) 0,
   Ev.act 0 m2 0,
   Ev.act 0 (Term.agent 0) 0,          -- A's identity check: the reply says B, A wanted I
   Ev.act 0 (Term.agent 0) 0,
   Ev.ded NS.nb,
   Ev.ded NS.m3b,
   Ev.act 1 NS.m3b 0]

/-- **Executable result: the checker rejects the attack on the corrected protocol.**  The
certificate is refused because A's identity check is not enabled - the step is not a
transition of ProtSat.Operational at all.  (The demo prints which step fails.) -/
theorem rejected : checkCertificate P (certOfTrace P trace) = false := by decide

/-- The configuration reached after running a prefix of the trace. -/
def runTo (tr : List Ev) : Cfg :=
  (certStepsFrom P (initCfg P) tr).getLast?.map (fun s => s.after) |>.getD (initCfg P)

/-- **Precisely where Lowe's fix stops the attack:** the first nine steps are valid
transitions of the corrected protocol and the tenth - A's identity check - is not enabled,
because the reply identifies the responder as B (1) while A believes it is talking to I (2).
-/
theorem breaks_at_the_check :
    relDecide P (runTo (trace.take 9)) ((trace.drop 9).head?.getD Ev.idle)
      (runTo (trace.take 10)) = false := by
  decide

/-- and the nine steps before it are accepted. -/
theorem prefix_ok :
    checkSteps P (initCfg P) (certStepsFrom P (initCfg P) (trace.take 9)) = true := by
  decide

end NSL

end ProtSat.Examples
