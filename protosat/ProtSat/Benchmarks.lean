/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Contract

/-!
# ProtSat: the Needham-Schroeder benchmarks over the repaired semantics (roadmap stage 7)

## Why this module exists

`ProtSat.Examples` instruments Needham-Schroeder for *secrecy only*: `NS.P` declares
`secrets := [Secret.store 1 1]` and `auths := []`, so the authentication story is told by a
hand-written certificate in the *old* semantics and no agreement query about it could even pass
validation. Roadmap stage 7 asks for the opposite: each claimed guarantee is a theorem of the
deciding contract over `ProtSat.Reference`, and every positive security example first has a proved
honest execution reaching the events it is about.

This module delivers that for NS (the original public-key protocol) and NSL (Lowe's correction):

* `NS2` and `NSL2` are role-instantiated models in the reference language: two parameterised
  roles (each written for a `self` and a `peer`), the three messages, A's nonce check, B's nonce
  check, Lowe's identity check in `NSL2` only, a real secret (B's freshly generated session nonce,
  declared by a `secret` action), and explicit authentication instrumentation - A *claims* the
  agreed pair (Na, Nb) to its peer, B *commits* to A on the same pair.
* The honest execution of each model is exhibited, proved to reach the secret declaration and both
  authentication events, and proved accepted by the ordered role-aware agreement monitor.
* Lowe's attack on NS2 is exhibited as a run of the reference semantics that leaks the secret and
  breaks agreement, and the same script is proved *not to be a run of NSL2 at all*: it is blocked
  exactly at A's identity check. Erasing exactly that check from NSL2 makes the script an accepted
  attack again.
* The deciding contract is asked the same question of both models - the same two goals, the same
  bounds. On the faithful NS2 the answer is carried by a replayable violating execution, because
  the kernel cannot afford the `rounds := 1` universe that the intruder's rebuilds need. On
  `NS2c`, a reduction of the same scenario whose attack lives inside the rounds-0 universe, the
  contract itself answers ATTACK with a witness that replays through `checkWitness`, and its
  enumerator answers BOUNDED SAFE for NSL2c at the bounds exhaustion can reach.

## Which theorem delivers which target

| roadmap ask | theorem |
|---|---|
| NS in the reference language, instrumented | `NS2`, `ns2RoleA`, `ns2RoleB` |
| NSL with both checks | `NSL2`, `nsl2RoleA`, `nsl2RoleB` |
| honest run reaches the events | `ns2_honest_reaches_auth_events`, `nsl2_honest_reaches_commit` |
| the honest run is a permitted execution | `nsl2c_honest_permitted` |
| the attack exists and is found | `ns2_lowe_leaks`, `ns2_lowe_breaks_agreement`, `NS2cq_verdict` |
| the positive result by exhaustion | `NSL2cqE_boundedSafe`, `NSL2cqE_verdict` |
| non-vacuity of the positive result | `nsl2_honest_reaches_commit`, `nsl2c_honest_reaches_commit` |
| the adverse control | `nsl2_blocks_lowe`, `NSL2cNoCheckQ_verdict`, `NSL2earlyQ_verdict` |
| the pair is a real benchmark | `exhaustion_pair`, `attack_bound_pair` |

## What this does not do

* **Nothing here is an unbounded proof.** Every safety statement is a `boundedSafe` at the bounds
  named in its own statement, and those bounds are small.
* **The enumerator is not what finds the Lowe attack on `NS2`.** `ProtSat.Reference.Explore` offers
  every event the attacker could try at every configuration, so the cost is driven by the message
  universe. For `NS2` that universe has 29 messages at `rounds := 0` and 1415 at `rounds := 1`; the
  root configuration alone has 4252 candidate events, and the enumeration at `rounds := 0` already
  visits 11,868 nodes by three events - which is why `exB0` below is three events and not four.
  The Lowe execution needs `rounds := 1`, because the intruder must rebuild two ciphertexts and
  those rebuilds are not in the rounds-0 universe - and at `rounds := 1` a single kernel-side
  `inBoundsBool` over that universe costs more than the whole of the rest of this module, let alone
  an enumeration over it. So the faithful-model attack is stated as a *replayable execution*
  (`run`, `traceLeaksBool`, `agreesBool`, each decided by the kernel on the single trace), and the
  contract's ATTACK verdict is delivered on `NS2c`, the reduction below, whose attack fits inside
  the rounds-0 universe. Nothing is assumed: that verdict comes from `checkWitness` plus the
  contract's own completeness theorem `attackFound_of_boundedAttack`.
* **NSL2 is not proved safe at the bound where NS is proved attacked.** Exhaustion answers NSL2 at
  `rounds := 0, steps := 3` - thirteen events of attack are far beyond what it can reach - and no
  theorem here transfers safety upward. What *is* proved at the attack bound for NSL2 is that the
  Lowe script is not an execution of it, that the re-checker rejects it as evidence, and that
  erasing exactly Lowe's check turns the same script back into an accepted attack. The exhaustion
  bound cannot discriminate either: `NS2cqE` is proved safe there too, and that is stated rather
  than hidden. The executable attack-versus-safe pair is therefore NSL2 against a mutation of NSL2
  (`exhaustion_pair`).
* **No CNF, no solver, no old semantics.** This module imports only `ProtSat.Contract`, and every
  closed fact is discharged by plain `decide`: nothing is evaluated outside the kernel,
  nothing is admitted, and there are no new axioms.
-/

namespace ProtSat.Benchmarks

open ProtSat
open ProtSat.Term
open ProtSat.Protocol
open ProtSat.Bounded
open ProtSat.Reference
open ProtSat.Reference.Explore
open ProtSat.Reference.Contract

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ### Pinning the repaired names

This namespace is nested in `ProtSat`, where `Ev`, `Cfg` and `initCfg` already name the *old*
semantics, and an enclosing namespace beats an `open`. The abbreviations below make the unqualified
names of this module mean the repaired semantics, so that no theorem here can silently be about the
wrong model. Constructor names are still spelled out, because a dotted name is resolved before an
abbreviation is considered. -/

/-- The repaired event type (`ProtSat.Ev` is the old one). -/
abbrev Ev := ProtSat.Reference.Ev
/-- The repaired configuration type (`ProtSat.Cfg` is the old one). -/
abbrev Cfg := ProtSat.Reference.Cfg
/-- The repaired initial configuration. -/
abbrev initCfg := ProtSat.Reference.initCfg
/-- The verdict type of the deciding contract (`ProtSat.Verdict` is the CNF analyser's). -/
abbrev Verdict := ProtSat.Reference.Contract.Verdict
/-- The safety evidence of the deciding contract. -/
abbrev SafeEvidence := ProtSat.Reference.Contract.SafeEvidence

/-- The idle event. -/
abbrev idleEv : Ev := ProtSat.Reference.Ev.idle
/-- The attacker deduces `t`. -/
abbrev ded (t : Term) : Ev := ProtSat.Reference.Ev.ded t
/-- Delivering `m` to session `q`. -/
abbrev recv (q : Nat) (m : Term) : Ev := ProtSat.Reference.Ev.recv q m
/-- Session `q` allocates the nonce value `n`. -/
abbrev gen (q : Nat) (n : NonceName) : Ev := ProtSat.Reference.Ev.generate q n
/-- Session `q` executes its next deterministic action. -/
abbrev act (q : Nat) : Ev := ProtSat.Reference.Ev.act q

/-! ### Principals, nonces and messages

Session 0 is the responder B and session 1 is the initiator A. The nonce names are not arbitrary:
`Bounded.placeholderStore` binds variable `x` of session `q` to the nonce `100000 + 1000 * q + x`
and the universe is built from the shapes the roles evaluate to in that store. Taking
`naN = 101000` (A's variable 0) and `nbN = 101001` (B's variable 1001), and letting each session
copy a destructured value into the variable whose placeholder it equals, makes every message the
honest run publishes equal to a shape the universe already contains - so the honest execution is a
*permitted* execution of the bounded semantics and not merely a run of it. -/

/-- The initiator. -/
def aA : Agent := 0
/-- The responder. -/
def aB : Agent := 1
/-- The intruder: the only compromised principal. -/
def aI : Agent := 2

/-- The nonce A generates: variable 0 of session 1. -/
def naN : NonceName := 101000
/-- The nonce B generates: variable 1001 of session 0. -/
def nbN : NonceName := 101001

/-- A's nonce, as a message. -/
def na : Term := Term.nonce naN
/-- B's nonce, as a message: the session secret both models declare. -/
def nb : Term := Term.nonce nbN

/-- Message 1 as A sends it to the intruder: {Na}_pub(I). -/
def mA : Term := Term.encA na aI
/-- Message 1 rebuilt by the intruder for B: {Na}_pub(B). -/
def mB : Term := Term.encA na aB
/-- Message 2 as NS2 sends it: {Nb, Na}_pub(A). -/
def m2 : Term := Term.encA (Term.pair nb na) aA
/-- Message 2 as NSL2 sends it: {Nb, {Na, B}}_pub(A) - Lowe puts B's identity in. -/
def m2L : Term := Term.encA (Term.pair nb (Term.pair na (Term.agent aB))) aA
/-- Message 3 as A sends it to the intruder: {Nb}_pub(I). -/
def m3 : Term := Term.encA nb aI
/-- Message 3 rebuilt by the intruder for B: {Nb}_pub(B). -/
def m3b : Term := Term.encA nb aB

/-! ### NS2: Needham-Schroeder public key in the reference language -/

/-- The initiator's role, playing `self` against `peer`: generate Na, send {Na}_pub(peer), receive
the reply, check that the reply carries Na back, take Nb out of it, claim the agreed (Na, Nb) to
`peer`, and send {Nb}_pub(peer). There is no check that the reply came from `peer`: that absence
*is* the protocol. -/
def ns2RoleA (self peer : Agent) : Role :=
  { acts :=
      [ Action.fresh 0 naN,
        Action.send peer (Expr.encA (Expr.var 0) peer),
        Action.recv peer 1,
        Action.check (Expr.snd (Expr.decA (Expr.var 1) self)) (Expr.var 0),
        Action.assign 2 (Expr.fst (Expr.decA (Expr.var 1) self)),
        Action.claim 0 (Expr.agent peer) (Expr.pair (Expr.var 0) (Expr.var 2)),
        Action.send peer (Expr.encA (Expr.var 2) peer) ] }

/-- The responder's role, playing `self` against `peer`: receive {Na}_pub(self), take Na out,
generate Nb and declare it secret, answer {Nb, Na}_pub(peer), receive the third message, check that
it carries Nb back, and commit to `peer` on the agreed (Na, Nb). -/
def ns2RoleB (self peer : Agent) : Role :=
  { acts :=
      [ Action.recv peer 0,
        Action.assign 1000 (Expr.decA (Expr.var 0) self),
        Action.fresh 1001 nbN,
        Action.secret (Expr.var 1001),
        Action.send peer (Expr.encA (Expr.pair (Expr.var 1001) (Expr.var 1000)) peer),
        Action.recv peer 2,
        Action.check (Expr.decA (Expr.var 2) self) (Expr.var 1001),
        Action.commit 0 (Expr.agent peer) (Expr.pair (Expr.var 1000) (Expr.var 1001)) ] }

/-- Needham-Schroeder public key instantiated with A's peer `peerA`: session 0 is B talking to A,
session 1 is A talking to `peerA`. The intruder is compromised, so it can read and rewrite anything
addressed to it. The declared secret is B's session nonce, reached by a `secret` action, so the
secrecy goal is not vacuous. -/
def ns2 (peerA : Agent) : Protocol :=
  { roles := [ns2RoleB aB aA, ns2RoleA aA peerA]
    sessions := [{ role := 0, self := aB, peer := aA }, { role := 1, self := aA, peer := peerA }]
    agents := [aA, aB, aI]
    nonceDomain := [naN, nbN]
    compromised := [aI]
    secrets := []
    auths := [{ tag := 0 }] }

/-- The attack instantiation: A initiates with the intruder. -/
def NS2 : Protocol := ns2 aI
/-- The honest instantiation: A initiates with B. -/
def NS2h : Protocol := ns2 aB

/-! ### NSL2: Lowe's correction -/

/-- Lowe's initiator: `ns2RoleA` with message 2 read as {Nb, {Na, B}} and **both** checks present -
the nonce check that Na came back, and the identity check that the reply names the peer A started
with. -/
def nsl2RoleA (self peer : Agent) : Role :=
  { acts :=
      [ Action.fresh 0 naN,
        Action.send peer (Expr.encA (Expr.var 0) peer),
        Action.recv peer 1,
        Action.check (Expr.fst (Expr.snd (Expr.decA (Expr.var 1) self))) (Expr.var 0),
        Action.check (Expr.snd (Expr.snd (Expr.decA (Expr.var 1) self))) (Expr.agent peer),
        Action.assign 2 (Expr.fst (Expr.decA (Expr.var 1) self)),
        Action.claim 0 (Expr.agent peer) (Expr.pair (Expr.var 0) (Expr.var 2)),
        Action.send peer (Expr.encA (Expr.var 2) peer) ] }

/-- Lowe's responder: `ns2RoleB` with B's own identity added to message 2. -/
def nsl2RoleB (self peer : Agent) : Role :=
  { acts :=
      [ Action.recv peer 0,
        Action.assign 1000 (Expr.decA (Expr.var 0) self),
        Action.fresh 1001 nbN,
        Action.secret (Expr.var 1001),
        Action.send peer
          (Expr.encA (Expr.pair (Expr.var 1001)
            (Expr.pair (Expr.var 1000) (Expr.agent self))) peer),
        Action.recv peer 2,
        Action.check (Expr.decA (Expr.var 2) self) (Expr.var 1001),
        Action.commit 0 (Expr.agent peer) (Expr.pair (Expr.var 1000) (Expr.var 1001)) ] }

/-- Needham-Schroeder-Lowe, instantiated with A's peer `peerA`. Same agents, same compromise set,
same secret, same authentication instrumentation as `ns2`. -/
def nsl2 (peerA : Agent) : Protocol :=
  { roles := [nsl2RoleB aB aA, nsl2RoleA aA peerA]
    sessions := [{ role := 0, self := aB, peer := aA }, { role := 1, self := aA, peer := peerA }]
    agents := [aA, aB, aI]
    nonceDomain := [naN, nbN]
    compromised := [aI]
    secrets := []
    auths := [{ tag := 0 }] }

/-- The attack instantiation of Lowe's protocol. -/
def NSL2 : Protocol := nsl2 aI
/-- The honest instantiation of Lowe's protocol. -/
def NSL2h : Protocol := nsl2 aB

/-- NSL2 with exactly Lowe's identity check removed. Index 4 of Lowe's initiator is that check;
erasing it leaves the nonce check, the roles, the secret and the instrumentation untouched. This is
the adverse control stated as a mutation of NSL2 rather than as a different protocol. -/
def nsl2NoCheck : Protocol :=
  { NSL2 with
    roles := [nsl2RoleB aB aA, { acts := (nsl2RoleA aA aI).acts.eraseIdx 4 }] }

/-- NSL2 with B's commit moved forward: B commits to A on its own nonce immediately after
generating and declaring it, before it has sent or received anything else. Everything else - the
agents, the compromise set, the secret, A's two checks - is NSL2's. This is the mutation the
*enumerator* can reach: the unmatched commit happens after three events. -/
def nsl2CommitEarly : Protocol :=
  { NSL2 with
    roles :=
      [ { acts :=
            [ Action.fresh 1001 nbN,
              Action.secret (Expr.var 1001),
              Action.commit 0 (Expr.agent aA) (Expr.nonce nbN),
              Action.recv aA 0,
              Action.assign 1000 (Expr.decA (Expr.var 0) aB),
              Action.send aA
                (Expr.encA (Expr.pair (Expr.var 1001)
                  (Expr.pair (Expr.var 1000) (Expr.agent aB))) aA),
              Action.recv aA 2,
              Action.check (Expr.decA (Expr.var 2) aB) (Expr.var 1001) ] },
        nsl2RoleA aA aI ] }

/-! ### The executions -/

/-- The configurations a trace visits, or `[]` when it is not a run. -/
def visit (P : Protocol) (tr : List Ev) : List Cfg := (run P (initCfg P) tr).getD []

/-- The configuration a trace ends in, defaulting to the initial one. -/
def endCfg (P : Protocol) (tr : List Ev) : Cfg := (visit P tr).getLastD (initCfg P)

/-- The commit events of a trace, in trace order. -/
def commits (P : Protocol) (tr : List Ev) : List Inst :=
  (insts P (visit P tr) tr).filter (fun i => i.isCommit)

/-- The claim events of a trace, in trace order. -/
def claims (P : Protocol) (tr : List Ev) : List Inst :=
  (insts P (visit P tr) tr).filter (fun i => ! i.isCommit)

/-- The honest execution of NS2: A initiates with B, the three messages go in order, and both
authentication events happen. Fifteen events. -/
def ns2Honest : List Ev :=
  [ gen 1 naN, act 1, recv 0 mB, act 0, gen 0 nbN, act 0, act 0,
    recv 1 m2, act 1, act 1, act 1, act 1, recv 0 m3b, act 0, act 0 ]

/-- The honest execution of NSL2: the same script, with B's identity inside message 2 and A's extra
identity check. Sixteen events. -/
def nsl2Honest : List Ev :=
  [ gen 1 naN, act 1, recv 0 mB, act 0, gen 0 nbN, act 0, act 0,
    recv 1 m2L, act 1, act 1, act 1, act 1, act 1, recv 0 m3b, act 0, act 0 ]

/-- **Lowe's attack on NS2**, as events of the repaired semantics. Session 1 is A, session 0 is B;
the intruder's own work is `ded` events and its deliveries are `recv` events.

1-2.   A generates Na and sends {Na}_pub(I), believing it is starting a run with I.
3-4.   I decrypts with its own (compromised) key and rebuilds the message for B.
5-9.   B accepts, extracts Na, generates Nb, declares it secret, answers {Nb, Na}_pub(A).
10-14. A receives it, checks that Na came back - it did - extracts Nb, claims the pair to I, and
       sends {Nb}_pub(I).
15.    I decrypts message 3: **B's declared secret nonce is now public**.
16-19. I rebuilds {Nb}_pub(B), delivers it, B checks Nb and **commits to A** - a principal A never
       claimed to be talking to.

Nineteen events. -/
def ns2Lowe : List Ev :=
  [ gen 1 naN, act 1, ded na, ded mB, recv 0 mB, act 0, gen 0 nbN, act 0, act 0,
    recv 1 m2, act 1, act 1, act 1, act 1, ded nb, ded m3b, recv 0 m3b, act 0, act 0 ]

/-- The same script against NSL2, with message 2 carrying B's identity. The first eleven events are
legal - A's nonce check passes, because Na really did come back - and the twelfth, A's identity
check, is not enabled: the reply names B and A wanted I. -/
def nsl2LoweAttempt : List Ev :=
  (ns2Lowe.take 9) ++ [recv 1 m2L, act 1, act 1]

/-- The script of `nsl2LoweAttempt` against NSL2 with Lowe's check erased: everything after the
nonce check now goes through, so this is the attack again, in the mutated model. -/
def nsl2NoCheckLowe : List Ev :=
  (ns2Lowe.take 9) ++ [recv 1 m2L, act 1, act 1, act 1, act 1, ded nb, ded m3b, recv 0 m3b,
    act 0, act 0]

/-- The three events that make the early-commit mutant leak its agreement property: B generates,
declares, and commits with nobody having claimed anything. -/
def nsl2EarlyTrace : List Ev := [gen 0 nbN, act 0, act 0]


/-! ### The exhaustion-friendly reduction: message 1 in the clear

The one thing the rounds-0 universe cannot represent is the intruder *re-encrypting* message 1
for B:
`Term.encA na aB` is not a subterm of any seed, and the constructor-closure round that would add it
takes the universe from 29 messages to 1415 - at which size the kernel cannot even evaluate
`univ NS2 { rounds := 1 }` in a few minutes, let alone enumerate it. The reduction below keeps the
whole Lowe story - the routing of A's initiation into B's session, A's nonce check, B's identity
check as the only thing that stops it - and drops only the encryption of message 1, which the
intruder breaks anyway by being A's peer. With message 1 in the clear the intruder *forwards* it and
every message of the attack is a shape the rounds-0 universe already contains.

Variable slots are chosen so that each stored value equals the placeholder the universe is built
from: `naN = 101000` is A's variable 0 and B's variable 1000, `nbN = 101001` is A's variable 1 and
B's variable 1001. -/

/-- The reduced initiator: message 1 is the pair (Na, A) in the clear. -/
def nsxRoleA (self peer : Agent) : Role :=
  { acts :=
      [ Action.fresh 0 naN,
        Action.send peer (Expr.pair (Expr.var 0) (Expr.agent self)),
        Action.recv peer 2,
        Action.check (Expr.snd (Expr.decA (Expr.var 2) self)) (Expr.var 0),
        Action.assign 1 (Expr.fst (Expr.decA (Expr.var 2) self)),
        Action.claim 0 (Expr.agent peer) (Expr.pair (Expr.var 0) (Expr.var 1)),
        Action.send peer (Expr.encA (Expr.var 1) peer) ] }

/-- The reduced responder: Na is read out of the clear pair, message 2 is {Nb, Na}_pub(A). -/
def nsxRoleB (self peer : Agent) : Role :=
  { acts :=
      [ Action.recv peer 0,
        Action.assign 1000 (Expr.fst (Expr.var 0)),
        Action.fresh 1001 nbN,
        Action.secret (Expr.var 1001),
        Action.send peer (Expr.encA (Expr.pair (Expr.var 1001) (Expr.var 1000)) peer),
        Action.recv peer 2,
        Action.check (Expr.decA (Expr.var 2) self) (Expr.var 1001),
        Action.commit 0 (Expr.agent peer) (Expr.pair (Expr.var 1000) (Expr.var 1001)) ] }

/-- Lowe's reduced responder: message 2 names B inside the ciphertext. -/
def nslxRoleB (self peer : Agent) : Role :=
  { acts :=
      [ Action.recv peer 0,
        Action.assign 1000 (Expr.fst (Expr.var 0)),
        Action.fresh 1001 nbN,
        Action.secret (Expr.var 1001),
        Action.send peer
          (Expr.encA (Expr.pair (Expr.var 1001)
            (Expr.pair (Expr.var 1000) (Expr.agent self))) peer),
        Action.recv peer 2,
        Action.check (Expr.decA (Expr.var 2) self) (Expr.var 1001),
        Action.commit 0 (Expr.agent peer) (Expr.pair (Expr.var 1000) (Expr.var 1001)) ] }

/-- The reduced initiator of Lowe's protocol: both checks, as `nsl2RoleA`. -/
def nslxRoleA (self peer : Agent) : Role :=
  { acts :=
      [ Action.fresh 0 naN,
        Action.send peer (Expr.pair (Expr.var 0) (Expr.agent self)),
        Action.recv peer 2,
        Action.check (Expr.fst (Expr.snd (Expr.decA (Expr.var 2) self))) (Expr.var 0),
        Action.check (Expr.snd (Expr.snd (Expr.decA (Expr.var 2) self))) (Expr.agent peer),
        Action.assign 1 (Expr.fst (Expr.decA (Expr.var 2) self)),
        Action.claim 0 (Expr.agent peer) (Expr.pair (Expr.var 0) (Expr.var 1)),
        Action.send peer (Expr.encA (Expr.var 1) peer) ] }

/-- The reduced Needham-Schroeder, A's peer `peerA`. -/
def ns2c (peerA : Agent) : Protocol :=
  { roles := [nsxRoleB aB aA, nsxRoleA aA peerA]
    sessions := [{ role := 0, self := aB, peer := aA }, { role := 1, self := aA, peer := peerA }]
    agents := [aA, aB, aI]
    nonceDomain := [naN, nbN]
    compromised := [aI]
    secrets := []
    auths := [{ tag := 0 }] }

/-- The reduced Needham-Schroeder-Lowe, A's peer `peerA`. -/
def nsl2c (peerA : Agent) : Protocol :=
  { roles := [nslxRoleB aB aA, nslxRoleA aA peerA]
    sessions := [{ role := 0, self := aB, peer := aA }, { role := 1, self := aA, peer := peerA }]
    agents := [aA, aB, aI]
    nonceDomain := [naN, nbN]
    compromised := [aI]
    secrets := []
    auths := [{ tag := 0 }] }

/-- The reduced attack instantiation of NS. -/
def NS2c : Protocol := ns2c aI
/-- The reduced attack instantiation of NSL. -/
def NSL2c : Protocol := nsl2c aI
/-- The reduced honest instantiation of NSL. -/
def NSL2ch : Protocol := nsl2c aB

/-- Message 1 of the reduced protocol, in the clear: (Na, A). -/
def c1 : Term := Term.pair na (Term.agent aA)
/-- Message 2 of the reduced NSL protocol: {Nb, {Na, B}}_pub(A). -/
def c2L : Term := Term.encA (Term.pair nb (Term.pair na (Term.agent aB))) aA

/-- **The Lowe attack on the reduced NS**, thirteen events, every one of them inside the rounds-0
universe: the intruder forwards message 1 instead of rebuilding it. -/
def ns2cLowe : List Ev :=
  [ gen 1 naN, act 1, recv 0 c1, act 0, gen 0 nbN, act 0, act 0,
    recv 1 m2, act 1, act 1, act 1, act 1, ded nb ]

/-- The same script against the reduced NSL: A's identity check is the tenth event and it is not
enabled, because the reply names B while A's peer is the intruder. -/
def nsl2cLoweAttempt : List Ev :=
  (ns2cLowe.take 7) ++ [recv 1 c2L, act 1, act 1]

/-- NSL2c with exactly Lowe's identity check erased (index 4 of the reduced initiator). -/
def nsl2cNoCheck : Protocol :=
  { NSL2c with roles := [nslxRoleB aB aA, { acts := (nslxRoleA aA aI).acts.eraseIdx 4 }] }

/-- The reduced script against that mutant: with the identity check gone everything after it goes
through, and the secret is lost again. -/
def nsl2cNoCheckLowe : List Ev :=
  (ns2cLowe.take 7) ++ [recv 1 c2L, act 1, act 1, act 1, act 1, ded nb]

/-- The honest execution of the reduced NSL: sixteen events, reaching the secret declaration, A's
claim and B's commit. -/
def nsl2cHonest : List Ev :=
  [ gen 1 naN, act 1, recv 0 c1, act 0, gen 0 nbN, act 0, act 0,
    recv 1 c2L, act 1, act 1, act 1, act 1, act 1, recv 0 m3b, act 0, act 0 ]


/-! ### The honest executions reach the events the guarantees are about

Roadmap stage 7: every positive security example first has a proved honest execution reaching the
events it is about. Everything in this section is a single trace replayed by the kernel, so it is
cheap, and it proves that none of the models below is a dead role. -/

/-- NS2's honest execution is a run of the repaired semantics. -/
theorem ns2_honest_run : run NS2h (initCfg NS2h) ns2Honest ≠ none := by decide

/-- and it reaches the secret declaration: the obligation list holds exactly B's session nonce. -/
theorem ns2_honest_reaches_secret : (endCfg NS2h ns2Honest).oblig = [nb] := by decide

/-- and it reaches exactly one claim and exactly one commit. -/
theorem ns2_honest_reaches_auth_events :
    (claims NS2h ns2Honest).length = 1 ∧ (commits NS2h ns2Honest).length = 1 := by decide

/-- and the ordered role-aware monitor accepts it: B's commit is matched by A's strictly earlier
claim, to each other and on the same agreed pair. -/
theorem ns2_honest_agrees : agreesBool (insts NS2h (visit NS2h ns2Honest) ns2Honest) = true := by
  decide

/-- and no configuration of it leaks the declared secret. -/
theorem ns2_honest_no_leak : traceLeaksBool NS2h (visit NS2h ns2Honest) = false := by decide

/-- NSL2's honest execution is a run of the repaired semantics. -/
theorem nsl2_honest_run : run NSL2h (initCfg NSL2h) nsl2Honest ≠ none := by decide

/-- **Non-vacuity of the NSL2 story.** The honest execution reaches the secret declaration *and*
both authentication events: the obligation list holds B's freshly generated nonce, A claims once and
B commits once. The safety results below are therefore not the safety of a role that never gets
anywhere. -/
theorem nsl2_honest_reaches_commit :
    run NSL2h (initCfg NSL2h) nsl2Honest ≠ none ∧
      (endCfg NSL2h nsl2Honest).oblig = [nb] ∧
      (commits NSL2h nsl2Honest).length = 1 ∧ (claims NSL2h nsl2Honest).length = 1 := by decide

/-- The claim and the commit agree in the only way the monitor accepts: A claims the pair to B, B
commits the same pair to A, and the claim comes first. -/
theorem nsl2_honest_events :
    insts NSL2h (visit NSL2h nsl2Honest) nsl2Honest =
      [ { isCommit := false, sess := 1, role := 1, self := aA, peer := aB, tag := 0,
          data := Term.pair na nb, idx := 11 },
        { isCommit := true, sess := 0, role := 0, self := aB, peer := aA, tag := 0,
          data := Term.pair na nb, idx := 15 } ] := by decide

/-- and the monitor accepts the honest trace. -/
theorem nsl2_honest_agrees : agreesBool (insts NSL2h (visit NSL2h nsl2Honest) nsl2Honest) = true :=
  by decide

/-- and it leaks nothing. -/
theorem nsl2_honest_no_leak : traceLeaksBool NSL2h (visit NSL2h nsl2Honest) = false := by decide

/-- The reduced NSL2 honest execution is a run *and* a permitted execution of the bounded semantics
at `rounds := 0`, so the exhaustion bound below is not excluding the honest case by accident. -/
theorem nsl2c_honest_permitted :
    BoundedRun NSL2ch { steps := 16, rounds := 0 } nsl2cHonest (visit NSL2ch nsl2cHonest) := by
  refine ⟨?_, by decide, ?_⟩
  · show run NSL2ch (initCfg NSL2ch) nsl2cHonest = some (visit NSL2ch nsl2cHonest)
    decide
  · intro C hC
    have hall : (visit NSL2ch nsl2cHonest).all (inBoundsBool NSL2ch { steps := 16, rounds := 0 }) :=
      by decide
    exact (inBoundsBool_iff).mp (List.all_eq_true.mp hall C hC)

/-- and it reaches the secret declaration and both authentication events. -/
theorem nsl2c_honest_reaches_commit :
    (endCfg NSL2ch nsl2cHonest).oblig = [nb] ∧
      (commits NSL2ch nsl2cHonest).length = 1 ∧ (claims NSL2ch nsl2cHonest).length = 1 := by
  decide

/-- and the monitor accepts it, and nothing leaks. -/
theorem nsl2c_honest_safe_trace :
    agreesBool (insts NSL2ch (visit NSL2ch nsl2cHonest) nsl2cHonest) = true ∧
      traceLeaksBool NSL2ch (visit NSL2ch nsl2cHonest) = false := by decide

/-! ### Lowe's attack on NS2, and the one step NSL2 refuses -/

/-- The Lowe script is a run of NS2 in the repaired semantics. -/
theorem ns2_lowe_runs : run NS2 (initCfg NS2) ns2Lowe ≠ none := by decide

/-- **The secret is lost.** Some configuration of the run knows B's declared nonce. -/
theorem ns2_lowe_leaks : traceLeaksBool NS2 (visit NS2 ns2Lowe) = true := by decide

/-- Hence declaratively: the run leaks. -/
theorem ns2_lowe_leaks_trace : traceLeaks NS2 (visit NS2 ns2Lowe) :=
  (traceLeaksBool_iff NS2 (visit NS2 ns2Lowe)).mp ns2_lowe_leaks

/-- **Agreement is broken.** The monitor rejects the run: B commits to A on (Na, Nb) while A's only
claim names the intruder. -/
theorem ns2_lowe_breaks_agreement :
    agreesBool (insts NS2 (visit NS2 ns2Lowe) ns2Lowe) = false := by decide

/-- Hence declaratively: this is an `authBreak` of the repaired semantics. -/
theorem ns2_lowe_authBreak : authBreak NS2 (visit NS2 ns2Lowe) ns2Lowe := by
  intro hall
  have h1 : agreesBool (insts NS2 (visit NS2 ns2Lowe) ns2Lowe) = false := ns2_lowe_breaks_agreement
  have h2 := agreesBool_iff (insts NS2 (visit NS2 ns2Lowe) ns2Lowe) |>.mpr hall
  simp_all

/-- What the two authentication events are: A claims the agreed pair to the intruder at position 12,
B commits the same pair to A at position 18. Same tag, same data, different conversations - which is
exactly what `claimMatches` refuses to accept. -/
theorem ns2_lowe_events :
    insts NS2 (visit NS2 ns2Lowe) ns2Lowe =
      [ { isCommit := false, sess := 1, role := 1, self := aA, peer := aI, tag := 0,
          data := Term.pair na nb, idx := 12 },
        { isCommit := true, sess := 0, role := 0, self := aB, peer := aA, tag := 0,
          data := Term.pair na nb, idx := 18 } ] := by decide

/-- The first eleven events of the same script are legal in NSL2 too: message 2 really does carry Na
back, so A's nonce check passes. -/
theorem nsl2_lowe_prefix_runs :
    run NSL2 (initCfg NSL2) (nsl2LoweAttempt.take 11) ≠ none := by decide

/-- **Lowe's check is what stops it.** The twelfth event - A's identity check - is not enabled, so
the whole script is not an execution of NSL2. -/
theorem nsl2_blocks_lowe : run NSL2 (initCfg NSL2) nsl2LoweAttempt = none := by decide

/-- and the step that fails is the identity check itself, not the nonce check before it. -/
theorem nsl2_blocks_at_the_identity_check :
    stepOf NSL2 (endCfg NSL2 (nsl2LoweAttempt.take 11)) (act 1) = none := by decide

/-- Erasing exactly Lowe's check makes the same script a run again -/
theorem nsl2NoCheck_lowe_runs :
    run nsl2NoCheck (initCfg nsl2NoCheck) nsl2NoCheckLowe ≠ none := by decide

/-- it leaks the secret, -/
theorem nsl2NoCheck_lowe_leaks :
    traceLeaksBool nsl2NoCheck (visit nsl2NoCheck nsl2NoCheckLowe) = true := by decide

/-- and it breaks agreement: the mutation is the whole difference. -/
theorem nsl2NoCheck_lowe_breaks :
    agreesBool (insts nsl2NoCheck (visit nsl2NoCheck nsl2NoCheckLowe) nsl2NoCheckLowe) = false := by
  decide

/-- The reduced attack on NS2c runs, inside the rounds-0 universe. -/
theorem ns2c_lowe_runs : run NS2c (initCfg NS2c) ns2cLowe ≠ none := by decide

/-- every configuration of it is inside the rounds-0 bounds, -/
theorem ns2c_lowe_in_bounds :
    (visit NS2c ns2cLowe).all (inBoundsBool NS2c { steps := 14, rounds := 0 }) := by decide

/-- it leaks the declared secret, -/
theorem ns2c_lowe_leaks : traceLeaksBool NS2c (visit NS2c ns2cLowe) = true := by decide

/-- and NSL2c refuses the same script at A's identity check: nine events legal, the tenth not
enabled. -/
theorem nsl2c_lowe_prefix_runs :
    run NSL2c (initCfg NSL2c) (nsl2cLoweAttempt.take 9) ≠ none := by decide

/-- precisely where it stops: the identity check is not enabled. -/
theorem nsl2c_blocks_at_the_identity_check :
    stepOf NSL2c (endCfg NSL2c (nsl2cLoweAttempt.take 9)) (act 1) = none := by decide

theorem nsl2c_blocks_lowe : run NSL2c (initCfg NSL2c) nsl2cLoweAttempt = none := by decide

/-- Erasing Lowe's identity check from NSL2c makes the reduced script an attack again. -/
theorem nsl2cNoCheck_lowe_runs :
    run nsl2cNoCheck (initCfg nsl2cNoCheck) nsl2cNoCheckLowe ≠ none := by decide

theorem nsl2cNoCheck_lowe_leaks :
    traceLeaksBool nsl2cNoCheck (visit nsl2cNoCheck nsl2cNoCheckLowe) = true := by decide


/-! ### The contract, part one: the faithful models

The bounds the Lowe execution needs: nineteen events and one constructor-closure round, because the
intruder's two rebuilds are not in the rounds-0 universe. No verdict is issued for these queries: at
`rounds := 1` the universe holds 1415 messages, and the kernel cannot evaluate `checkWitness`'s
bound conjunct - let alone `attackFound` - over it in any reasonable time. What *is* kernel-checked
is the execution itself, above, and the re-checker's refusal of that execution as evidence against
NSL2. -/

/-- The goals every query in this module selects: the session secret and non-injective agreement. -/
def goals : List Goal := [Goal.secrecy, Goal.agreement]

/-- The bounds the faithful Lowe execution needs. -/
def bigB : Bounds := { steps := 19, rounds := 1 }

/-- NS2 in the attack instantiation at `bigB`, both goals selected. -/
def NS2q : Query := Query.mk NS2 bigB goals

/-- NSL2 in the attack instantiation, **the same goals and the same bounds**. -/
def NSL2q : Query := Query.mk NSL2 bigB goals

/-- The Lowe execution as a certificate node. -/
def ns2LoweNode : Node :=
  { cfg := endCfg NS2 ns2Lowe, tr := ns2Lowe, Cs := visit NS2 ns2Lowe }

/-- The witness violates the secrecy goal the query selects. -/
theorem NS2q_witness_is_a_leak :
    goalViolationBool NS2 Goal.secrecy ns2LoweNode.Cs ns2LoweNode.tr = true := by decide

/-- and the agreement goal too: one execution, two violations. -/
theorem NS2q_witness_is_an_authBreak :
    goalViolationBool NS2 Goal.agreement ns2LoweNode.Cs ns2LoweNode.tr = true := by decide

/-- The query is well formed: the model validates and it selects a goal. -/
theorem NS2q_wellFormed : (validate NS2q).isEmpty = true := by decide

theorem NS2q_hasGoals : NS2q.goals.isEmpty = false := by decide

theorem NSL2q_wellFormed : (validate NSL2q).isEmpty = true := by decide

/-- **The re-checker refuses the NS2 attack as evidence against NSL2**: the trace is not an
execution of NSL2, so no amount of trust in the search can turn it into a verdict. -/
theorem NSL2q_rejects_the_witness : checkWitness NSL2q ns2LoweNode = false := by decide

/-! ### The contract, part two: the reduction, where the contract can answer

The reduced attack lives inside the rounds-0 universe, so the contract's own re-checker can replay
it and the contract's own enumerator can be run at small bounds. -/

/-- The attack bounds for the reduction: fourteen events, no constructor closure. -/
def exB : Bounds := { steps := 14, rounds := 0 }

/-- The exhaustion bounds: three events, no constructor closure. This is the largest bound at which
`attackFound` terminates for these models in a reasonable time. -/
def exB0 : Bounds := { steps := 3, rounds := 0 }

/-- The reduced NS in the attack instantiation, both goals, at `exB`. -/
def NS2cq : Query := Query.mk NS2c exB goals

/-- The reduced NSL, **same goals, same bounds**. -/
def NSL2cq : Query := Query.mk NSL2c exB goals

/-- The reduced NSL with Lowe's check erased: same goals, same bounds. -/
def NSL2cNoCheckQ : Query := Query.mk nsl2cNoCheck exB goals

/-- The reduced NSL at the exhaustion bounds. -/
def NSL2cqE : Query := Query.mk NSL2c exB0 goals

/-- The reduced NS at the exhaustion bounds: also safe there, which is stated rather than hidden. -/
def NS2cqE : Query := Query.mk NS2c exB0 goals

/-- NSL2 with B's commit moved to the head of its role, at the bounds of `NSL2cqE`. -/
def NSL2earlyQ : Query := Query.mk nsl2CommitEarly exB0 goals

theorem NSL2earlyQ_wellFormed : (validate NSL2earlyQ).isEmpty = true := by decide
theorem NSL2earlyQ_hasGoals : NSL2earlyQ.goals.isEmpty = false := by decide

theorem NS2cq_wellFormed : (validate NS2cq).isEmpty = true := by decide
theorem NS2cq_hasGoals : NS2cq.goals.isEmpty = false := by decide
theorem NSL2cq_wellFormed : (validate NSL2cq).isEmpty = true := by decide
/-- The mutated model validates: it still claims and commits, so its tag is used. -/
theorem NSL2cNoCheckQ_wellFormed : (validate NSL2cNoCheckQ).isEmpty = true := by decide

/-- The reduced Lowe execution as a certificate node. -/
def ns2cLoweNode : Node :=
  { cfg := endCfg NS2c ns2cLowe, tr := ns2cLowe, Cs := visit NS2c ns2cLowe }

/-- **The witness replays.** `checkWitness` re-derives the run from `ProtSat.Reference.run`, checks
the step bound, checks every configuration against the universe, and re-finds the violation itself -
without running the search and without trusting it. -/
theorem NS2cq_witness_checks : checkWitness NS2cq ns2cLoweNode = true := by decide

/-- The witness violates the secrecy goal the query selected. -/
theorem NS2cq_witness_is_a_leak :
    goalViolationBool NS2c Goal.secrecy ns2cLoweNode.Cs ns2cLoweNode.tr = true := by decide

/-- Hence the contract's attack predicate holds. -/
theorem NS2cq_boundedAttack : boundedAttack NS2cq :=
  checkWitness_sound NS2cq_witness_checks

/-- **The executable question answers true**, by the contract's completeness theorem applied to the
replayable witness: `attackFound` is the enumerator, and this says what it would return. -/
theorem NS2cq_attackFound : attackFound NS2cq = true :=
  attackFound_of_boundedAttack NS2cq NS2cq_boundedAttack

/-- and the witness search produces a node. -/
theorem NS2cq_findAttack : ∃ x, findAttack NS2cq = some x :=
  findAttack_some_of_attackFound NS2cq_attackFound

/-- **The analyser's verdict on the reduced NS is ATTACK.** -/
theorem NS2cq_verdict : ∃ x, analyze NS2cq = Verdict.attack x :=
  analyze_attack NS2cq NS2cq_wellFormed NS2cq_hasGoals NS2cq_attackFound

/-- and the node the verdict names passes the independent re-checker. -/
theorem NS2cq_verdict_checks : checkWitness NS2cq (foundNode NS2cq) = true :=
  answer_checkWitness NS2cq_attackFound

/-- NSL2, same goals, same bounds: the very same script is not evidence - it is not an execution. -/
theorem NSL2cq_witness_rejected : checkWitness NSL2cq ns2cLoweNode = false := by decide

/-- **The adverse control at the attack bound.** Erase exactly Lowe's identity check from the
reduced NSL and the contract answers ATTACK, with a witness that replays: same agents, same
compromise set, same secret, same instrumentation, same goals, same bounds. -/
def nsl2cNoCheckNode : Node :=
  { cfg := endCfg nsl2cNoCheck nsl2cNoCheckLowe, tr := nsl2cNoCheckLowe,
    Cs := visit nsl2cNoCheck nsl2cNoCheckLowe }

theorem NSL2cNoCheckQ_witness_checks :
    checkWitness NSL2cNoCheckQ nsl2cNoCheckNode = true := by decide

theorem NSL2cNoCheckQ_boundedAttack : boundedAttack NSL2cNoCheckQ :=
  checkWitness_sound NSL2cNoCheckQ_witness_checks

/-- and the executable question says true for it. -/
theorem NSL2cNoCheckQ_attackFound : attackFound NSL2cNoCheckQ = true :=
  attackFound_of_boundedAttack _ NSL2cNoCheckQ_boundedAttack

/-- and the analyser issues the ATTACK verdict for the mutation. -/
theorem NSL2cNoCheckQ_verdict : ∃ x, analyze NSL2cNoCheckQ = Verdict.attack x :=
  analyze_attack NSL2cNoCheckQ NSL2cNoCheckQ_wellFormed (by decide) NSL2cNoCheckQ_attackFound

/-! ### The contract, part three: exhaustion, where the enumerator itself runs

These are the bounds at which `ProtSat.Reference.Explore` actually terminates: no constructor
closure and three events, about 13,000 nodes. The bound is small and that is stated rather than
hidden; see the module header for the measured cost that forces it. -/

theorem NSL2cqE_wellFormed : (validate NSL2cqE).isEmpty = true := by decide
theorem NSL2cqE_hasGoals : NSL2cqE.goals.isEmpty = false := by decide

/-- **The enumeration runs and finds nothing**: every execution of at most three events whose
configurations stay inside the rounds-0 universe is inspected, and none leaks the declared secret or
breaks agreement. -/
theorem NSL2cqE_attackFound_false : attackFound NSL2cqE = false := by decide

/-- **Bounded safety of NSL2, issued by the contract's own decision procedure** at
`{ steps := 3, rounds := 0 }` with both goals selected. -/
theorem NSL2cqE_boundedSafe : boundedSafe NSL2cqE :=
  boundedSafe_of_attackFound_false NSL2cqE_attackFound_false

/-- with the evidence record the contract issues, -/
theorem NSL2cqE_verdict : ∃ e, analyze NSL2cqE = Verdict.boundedSafe e :=
  analyze_boundedSafe NSL2cqE NSL2cqE_wellFormed NSL2cqE_hasGoals NSL2cqE_attackFound_false

/-- and no attack verdict is possible for it. -/
theorem NSL2cqE_no_attack_verdict : ∀ x, analyze NSL2cqE ≠ Verdict.attack x :=
  analyze_ne_attack_of_boundedSafe NSL2cqE NSL2cqE_boundedSafe

/-- Safety transfers down in the bounds: two events are safe because three are, so the smaller
search never has to run. -/
theorem NSL2cq2_boundedSafe : boundedSafe (Query.mk NSL2c { steps := 2, rounds := 0 } goals) :=
  boundedSafe_mono_bounds (by exact ⟨by decide, by decide⟩) NSL2cqE_boundedSafe

/-- **The reduced NS is safe at the exhaustion bound too.** Three events is below what the attack
needs, so exhaustion here cannot tell NS from NSL; the separation at that bound is the pair with
`NSL2earlyQ` below, and the separation between the protocols is `nsl2c_blocks_lowe` together with
`NS2cq_verdict`. -/
theorem NS2cqE_attackFound_false : attackFound NS2cqE = false := by decide

theorem NS2cqE_boundedSafe : boundedSafe NS2cqE :=
  boundedSafe_of_attackFound_false NS2cqE_attackFound_false

/-- **The executable adverse control.** The same enumerator, at the same goals and the same bounds,
answers ATTACK for the mutation in which B commits before it has spoken to anyone: the safety
verdict above is a discrimination, not a constant. -/
theorem NSL2earlyQ_attackFound_true : attackFound NSL2earlyQ = true := by decide

theorem NSL2earlyQ_boundedAttack : boundedAttack NSL2earlyQ :=
  boundedAttack_of_attackFound NSL2earlyQ_attackFound_true

theorem NSL2earlyQ_verdict : ∃ x, analyze NSL2earlyQ = Verdict.attack x :=
  analyze_attack NSL2earlyQ NSL2earlyQ_wellFormed NSL2earlyQ_hasGoals
    NSL2earlyQ_attackFound_true

/-- the verdict's own node passes the independent re-checker, -/
theorem NSL2earlyQ_witness_checks : checkWitness NSL2earlyQ (foundNode NSL2earlyQ) = true :=
  answer_checkWitness NSL2earlyQ_attackFound_true

/-- and the violation it finds is the authentication goal, not the secrecy one. -/
theorem NSL2earlyQ_witness_is_auth :
    goalViolationBool nsl2CommitEarly Goal.agreement
      (foundNode NSL2earlyQ).Cs (foundNode NSL2earlyQ).tr = true := by decide
theorem NSL2earlyQ_witness_not_leak :
    goalViolationBool nsl2CommitEarly Goal.secrecy
      (foundNode NSL2earlyQ).Cs (foundNode NSL2earlyQ).tr = false := by decide

/-! ### The benchmark pairs -/

/-- **Same goals, same bounds, one answered ATTACK and the other BOUNDED SAFE** - both answers
produced by *running* the enumerator at `{ steps := 3, rounds := 0 }` with
`[secrecy, agreement]`: NSL2 is exhausted safe and the early-commit mutation of NSL2 is exhausted
attacked. -/
theorem exhaustion_pair : boundedSafe NSL2cqE ∧ boundedAttack NSL2earlyQ :=
  ⟨NSL2cqE_boundedSafe, NSL2earlyQ_boundedAttack⟩

/-- **Same goals, same bounds, NS against NSL** at the bound where the reduced attack lives: the
contract answers ATTACK on NS with a replayable witness, and on NSL the same script is not even an
execution, so the re-checker refuses it - while erasing exactly Lowe's check restores the attack.
The missing half, `boundedSafe NSL2cq` at `exB`, is not proved anywhere: exhaustion cannot reach
fourteen events. -/
theorem attack_bound_pair :
    boundedAttack NS2cq ∧ boundedAttack NSL2cNoCheckQ ∧
      run NSL2c (initCfg NSL2c) ns2cLowe = none ∧ checkWitness NSL2cq ns2cLoweNode = false :=
  ⟨NS2cq_boundedAttack, NSL2cNoCheckQ_boundedAttack,
    (by decide : run NSL2c (initCfg NSL2c) ns2cLowe = none), NSL2cq_witness_rejected⟩

/-- The two protocols differ by exactly one action, and that action is what the pairs turn on. -/
theorem nslx_is_one_action_longer :
    (nslxRoleA aA aI).acts.length = (nsxRoleA aA aI).acts.length + 1 ∧
      (nsl2RoleA aA aI).acts.length = (ns2RoleA aA aI).acts.length + 1 ∧
      nsl2cNoCheck.roles.length = NSL2c.roles.length := by decide

end ProtSat.Benchmarks