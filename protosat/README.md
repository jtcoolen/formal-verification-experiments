# ProtSat: a formally verified, proof-producing SAT-based cryptographic protocol analyser

A symbolic (Dolev-Yao) protocol analyser written in **Lean 4 + Mathlib**, in which the
central object of study is a *proved correspondence*:

> a bounded execution of a protocol that violates a declared security property exists **if
> and only if** the propositional formula compiled from that protocol is satisfiable.

The left-to-right direction is `ProtSat.Encoding.encoding_sound` (specification 8A); the
right-to-left direction is `ProtSat.Complete.encoding_complete` (8B).  A satisfying
assignment is not taken on trust: it is decoded into a concrete trace of protocol actions and
adversary deductions, and that trace is re-validated by an independent checker
(`ProtSat.Certificate`) that imports neither the CNF nor the solver.

Everything is checked by the Lean kernel: no `sorry`, no `admit`, no user-declared axioms,
no `native_decide`, no partial definitions.

---

## Build and run

```sh
cd protosat
export ELAN_HOME=$PWD/../.elan          # or install elan system-wide
lake build                               # library + demo + axiom audit, ~10 s
lake exe protosatDemo                    # the six protocol examples, ~2 s
lake env lean Axioms.lean                # axiom audit of every theorem in ProtSat.*
```

Mathlib is pinned to `v4.34.1` (Lean `4.34.1`).  Prebuilt Mathlib objects are cached in
`.mathlibcache`; to refresh them use

```sh
MATHLIB_CACHE_DIR=$PWD/.mathlibcache lake exe cache get
```

(the default cache directory is outside the workspace).

Single-module checking: `lake env lean ProtSat/Encoding.lean`.

---

## 1. The message algebra (specification section 1)

`ProtSat/Syntax.lean` defines messages

```
Term ::= agent A | nonce N | key K | pair t u | encS t k | encA t A | hash t
Key  ::= pub A | priv A | shrk A B
```

and `ProtSat/Protocol.lean` the expression language `Expr` that protocol roles use, which
adds the *destructors* `fst`, `snd`, `decS`, `decA`.  Evaluation

```lean
Expr.eval : Expr -> (Var -> Term option) -> Term option
```

is partial: a destructor whose argument does not have the right shape returns `none`, and an
action that evaluates to `none` is **not enabled** (this is how "the attacker sent the wrong
message" is modelled).  The symbolic equations of perfect cryptography are the reduction
laws, and they are theorems about the constructors, not assumptions:

```lean
Attacker.encS_then_decS : eval (decS (encS m k) k) = m
Attacker.encA_then_decA : eval (decA (encA m a) a) = m
Attacker.pair_then_proj : eval (fst (pair x y)) = x  ...
```

Terms are *normal forms*: there is no rewriting relation to decide because every constructor
is injective (`Syntax.pair_inj`, `encS_inj`, …) and destructors compute.  `Syntax.subtermsL`
/ `subtermClosureL` give the subterm structure the universe construction needs, with
`subtermClosureL_closed` and `subtermsL_subtermsL`.

**No computational content is claimed.**  `encS` is an uninterpreted constructor: the model
says what the attacker can *derive*, not what it can compute in polynomial time.

## 2. The adversary (specification section 2)

Two presentations of the same power, both proved:

* `Attacker.Ded` - an inductive 11-rule Dolev-Yao relation (observe, pair, project,
  symmetric encrypt/decrypt, asymmetric encrypt/decrypt, hash, replay, inject), with
  `ded_mono` (monotonicity, spec 2.3), `oneStep_ded` and `oneStep_mono`.
* `Attacker.OneStep K t` - the *one-step* fragment (each rule consumes only messages already
  in K).  Attacker steps in the operational semantics are OneStep steps, which is what makes
  "number of events" bound the depth of the attacker's derivation.
* `Deduce.lean` - the **executable** saturation procedure over a finite universe
  (`closeStep`, `deduce = iterate closeStep`), with
  `deduce_sound` (2.1: everything it derives is deducible),
  `dedIn_deduce` / `ded_dedIn` (2.2: completeness relative to the universe, and the converse),
  `deduce_mono` (2.3), `encS_decS_step`, `encA_decA_step`, `pair_proj_step`,
  `encS_intro_step`, `pair_intro_step`, `hash_intro_step` (2.4), and 8 groups of
  `decide`-checked examples.  `Deduce.attackerKnows` is the executable oracle; the
  under-approximation is only over the message universe, never "everything is public".

## 3. Protocol language and operational semantics (specification section 3)

`Protocol.lean`: `Role` (a list of `Action`s), `Session` (role + self + peer), `Action` =
`fresh | send | recv | assign | check | secret | claim | commit`, `Secret` =
`closed e | store q x`, `AuthProp`, and the `Protocol` record.  `Protocol.initKn` is the
attacker's initial knowledge: agent names, public keys, and the keys of *compromised*
principals - nothing else.

`Operational.lean` gives the independent small-step semantics

```lean
inductive Rel : Protocol -> Cfg -> Ev -> Cfg -> Prop   -- 10 introduction rules
inductive Runs : Protocol -> Cfg -> List Ev -> List Cfg -> Prop
```

with events `Ev = idle | ded t | act q m d`: the attacker controls the network, so a
`recv` step takes *any* message the attacker knows (replay and injection are instances of
`rRecv`), and a `send` step publishes the message to the attacker (`succSend`).  `Runs`
carries the visited configurations, which is what makes certificates possible.  Security
properties: `Leak` (a declared secret is known), `runsLeaks`, `AuthBreak` (non-injective
agreement: a commit with no matching claim), `Attack P tr` holds when the trace is a run that leaks or breaks agreement.
**This module does not import CNF, Encode or DPLL** - the semantics is independent of the
encoding, as the specification demands.

## 4. Bounded model checking (specification section 4)

`Bounded.lean`: `Bounds = { steps, rounds }` and the universe

```lean
univ P B = (closeOne ...)^[B.rounds] (subtermClosureL (seeds P))
```

where `seeds P` contains the agent names, the nonce domain, the domain keys, the initial
knowledge, the declared secrets and the *shapes* of every message each role can send
(evaluated in a placeholder store).  `closeOne` adds one round of pairs, symmetric and
asymmetric encryptions and hashes.  So `rounds` bounds message depth and the attacker's
ability to synthesise new messages, and `steps` bounds the number of events (protocol
actions and attacker deductions together).  `BoundedTrace`, `BoundedAttack` and
`BoundedSafe` state the bounded questions; `WithinBounds` (`Complete.lean`) is the
corresponding hypothesis for the completeness theorem.

**The universe is a bound, not a modelling fiction.**  A finite universe cannot be closed
under pairing, so the encoding does not pretend to name messages it has no variable for:
`Encode.uIdx` maps every out-of-universe value to the *unset* index, which disables the
action that would have computed it.  The analysis is therefore an under-approximation, and
`Clauses.univClosed` - "every closed protocol expression denotes a universe message" - is
the (decidable, checked) hypothesis that makes it a faithful one.

## 5. The SAT encoding (specification section 5)

`Encode.lean` allocates variables positionally (`vpc, vst, vkn, vev, vdl, vfr, vxe` plus the
auxiliary blocks `apc..afr`, `vpb`, `vau`) with proved injectivity (`vpc_inj`, …,
`vpc_inj_full`, …) and disjoint block ranges (`vst_lt_bsKn`, …).  `OneHot.lean` provides the
abstraction `Oh` (a finite domain, an injective variable map, and auxiliary flags), the
**linear-size** sequential at-most-one encoding (`CNF.atMostOneSeq` with
`atMostOneSeq_amo`), function-graph clauses (`graph_correct` / `graph_correct_back`),
relation clauses (`rel_correct` / `rel_complete`) and guarded forward Tseitin clauses
(`fwdClausesOn_correct` / `fwdClausesOn_complete`, `fwd2ClausesOn_*`).

`Clauses.lean` generates eleven clause groups:

| group | what it pins down |
|---|---|
| `oneHotClauses` | each configuration component has exactly one value |
| `initClauses` | step 0 is `initCfg P` (counters 0, empty stores, `initKn`) |
| `frameClauses` | a session that does not act keeps its state; knowledge never shrinks |
| `evalClauses` | Tseitin gates for every protocol expression (linear in the universe) |
| `stepClauses` | one family per introduction rule of `Rel`: advance, keep, fresh, recv, assign, send, check |
| `dedClauses` | the deduction-instance event fires only with its premises known |
| `pubAuxClauses` | conjunction variables for "session q publishes u" |
| `knSupportClauses` | knowledge is *justified*: known at i+1 only if known at i, or deduced, or sent |
| `freshClauses` | a generated nonce is not already stored or known (`nonceUsed`) |
| `leakAuxClauses` | conjunction variables for the store-leak condition |
| `violationClauses` | the declared property really fails |

`encode P B` is their concatenation.  This is a genuine compositional translation: no trace
is enumerated, and no Boolean answer is precomputed.

## 6. The solver (specification section 6)

`DPLL.lean` is a self-contained Davis-Putnam-Logemann-Loveland solver in substitution
presentation: `assign` (restriction), `findUnit` + `propagate` (unit propagation with an
explicit fuel equal to the clause count, `propagate_noUnit` proving the fuel always
suffices), `dpllAux` (branching on the first still-undecided occurring variable, with
backtracking), `dpll`.  Everything is structurally recursive, so termination is a kernel
fact.  The two required theorems:

```lean
DPLL.dpll_sound   : dpll f = some asg -> Sat (asgVal asg) f      -- 8D
DPLL.dpll_complete: dpll f = none     -> Unsat f                 -- 8E
DPLL.satisfiable_iff_dpll : Satisfiable f <-> (dpll f).isSome
```

plus `decide`-checked examples exercising propagation, conflict detection and branching.
The solver is a *reference* implementation: list-based propagation makes a solve cost
O(variables x clauses), which is fine for the small bounds below and is the honest reason the
full Needham-Schroeder instance (2.6M variables) is exhibited by certificate instead.

## 7. Certificates (specification section 7)

`Certificate.lean` defines `Certificate = { init, steps : List CertStep }` - pure data - and
`checkCertificate P c`, a closed Boolean computation that (i) requires `init` to be
`initCfg P`, (ii) re-derives every transition with `relDecide` (a decision procedure for
`Rel`, proved sound `relDecide_sound` and complete `relDecide_complete`), and (iii)
re-finds the violation itself with `leakBool` / `authBreakBool`.

```lean
Certificate.checkCertificate_sound : checkCertificate P c = true -> Attack P (certTrace c)  -- 8C
Certificate.certificate_of_runs    : a leaking run yields an accepted certificate
```

The module imports only `ProtSat.Operational`: it cannot see the CNF, the encoder or the
solver.  Five accepted and three rejected example certificates are checked by `decide`.

## 8. The correspondence theorems (specification section 8)

| # | statement | Lean theorem | status |
|---|---|---|---|
| A | every model of the CNF decodes to a valid bounded attack | `Encoding.encoding_sound`, `encoding_sound_bounded` | proved |
| B | every valid bounded attack yields a model of the CNF | `Complete.encoding_complete` | **proved** |
| C | every accepted certificate is a genuine trace | `Certificate.checkCertificate_sound` | proved |
| D | solver SAT answer is a real model | `DPLL.dpll_sound` | proved |
| E | solver UNSAT answer means unsatisfiable | `DPLL.dpll_complete` | proved |
| F | analyser attack verdict gives a bounded attack | `Analyzer.analyze_attack_sound`, `analyze_attack_bounded` | proved |
| G | analyser SAFE verdict means no bounded attack | `Analyzer.analyze_safe_sound`, `analyze_not_safe_of_attack` | **proved** |
| H | termination of state construction, encoding, DPLL, checking | `Analyzer.shape_finite`, `encode_vocab_finite`, `dpll_none_iff_unsat`, `checkCertificate_eq_decide`, `analyze_verdict_cases` | **proved** |

**8B is the converse, and it is the theorem that makes a SAFE verdict mean something.**
Its proof is a construction: `Complete.assignOf` is the *characteristic function of the run* -
a propositional variable is true exactly when the semantic fact it names holds - built from
fifteen disjoint block tests over the positional codes (`Complete.asgPc`, `asgSt`, `asgXe`,
`asgAu` and friends) and the readers `rdPc`, `rdSt`, `rdXe`, `rdDl`, `rdFr`, `rdEv`,
`dedIx` that say what the run selects.  `encoding_complete` then proves each of the eleven
clause groups is satisfied by that assignment (`sat_oneHot`, `sat_init`, `sat_frame`,
`sat_eval`, `sat_step`, `sat_ded`, `sat_pubAux`, `sat_knSupport`, `sat_fresh`,
`sat_leakAux`, `sat_violation`), and concatenates them with `sat_encodeGroup`.  The
hypotheses it needs are the bounds conditions of specification section 4, collected in
`Complete.RunOK` (twelve clauses: the run stays inside the shape, its expressions denote
universe messages, the shape's strides cover the protocol's variables and expression table)
plus `univSub` (the universe is subterm-closed, so every rule instance the attacker could use
is enumerated) and `SecretsOK` (the bounds can name the declared secrets).  None of them is
ceremonial: a run that leaves the universe has no finite name, and a violation the encoding
cannot mention cannot be found.

The chain behind 8A is worth spelling out, because it is where the work is:
`rel_agrees` (every decoded step is a `Rel` transition and the five-component `Agrees`
invariant is preserved) `-> agrees_decRun -> decRun_trace -> violation_leak ->
encoding_sound`.  `Agrees` says the decoded configuration and the assignment agree on
program counters, store slots, knowledge, store well-formedness and session count; the two
hard lemmas inside it are `kn_sound` (a knowledge bit that is true is justified by a real
deduction or send) and `kn_complete` (the converse, needed because `rFresh`'s side condition
is negative), and `decXe_eq` (the Tseitin gates compute the real expression value).

## 9. The six examples (specification section 9)

Run `lake exe protosatDemo`.  In the table, "solver" means the verdict was produced by
`analyze` (CNF + DPLL), and "certificate" means `checkCertificate … = true` was discharged
by the kernel with `decide`.

| # | protocol | bounds | result | how |
|---|---|---|---|---|
| 1 | challenge-response, K(A,B) uncompromised | steps 2, rounds 0 (1335 vars / 2995 cls) | SAFE | solver (`Challenge.verdict_if_none`, `cnf_unsat`) |
| 2 | replay: static authenticator, no freshness | steps 4, rounds 0 (4679 vars / 12899 cls) | ATTACK, 4 events | solver **and** certificate (`Replay.attack_found`) |
| 3 | key disclosure: compromised K(A,B) | steps 2, rounds 0 (1263 vars / 2767 cls) | ATTACK, 2 events | solver **and** certificate (`KeyDisclosure.attack`) |
| 3b | the same protocol, key not disclosed | as 3 | SAFE | solver (`safe_when_not_disclosed`) |
| 4 | Needham-Schroeder public key | model only | - | `Examples.NS.P` |
| 5 | Lowe attack on NS | 14 events | ATTACK | certificate (`NS.checked`, `NS.attack`) |
| 6 | Needham-Schroeder-Lowe | same 14-event script | REJECTED | certificate (`NSL.rejected`, `NSL.breaks_at_the_check`) |

Example 6 is the interesting one as evidence: the *same* attack script that the checker
accepts against NS is refused against NSL, and `NSL.prefix_ok` + `NSL.breaks_at_the_check`
pin the refusal to exactly Lowe's identity check - the first nine steps are valid transitions
and the tenth is not enabled.

## 10. Guarantees, and what is not claimed

* **Bounded, not unbounded.**  A SAFE verdict means: no attack inside `steps` events, the
  declared sessions, and the message universe generated by `rounds` closure rounds.  It is
  not a proof of protocol security.  (Specification 11 forbids the confusion; the README of
  the classic result - that 2 sessions and 10 steps suffice to refute NS - is a reminder
  that small bounds are meaningful, not a claim of completeness over all runs.)
* **Symbolic, not computational.**  Perfect cryptography: no reduction to a hardness
  assumption is claimed or possible here.
* **Under-approximation is explicit.**  Actions whose value leaves the universe are disabled;
  `univClosed` is checked before any verdict is reported (`Verdict.boundsTooSmall` otherwise).
* **The certificate is the evidence.**  Attack verdicts can be handed to a verifier that
  shares no code with the encoder or the solver.
* **Solver completeness is load-bearing for SAFE** (there is no certificate to check):
  `analyze_safe_sound` is 8B (a bounded attack would give a model) plus 8E (the solver's
  `none` answer means there is no model).  Both directions of the correspondence are now
  proved, so within the declared bounds "the solver found a model" and "the protocol has an
  attack" are the same statement - which is the correspondence the project is about.
* **No axioms beyond Lean's three.**  `lake env lean Axioms.lean` walks every theorem in the
  `ProtSat` namespace and reports any axiom other than `propext`, `Classical.choice`,
  `Quot.sound`.

## 11. Module map (specification section 10)

| module | lines | content |
|---|---|---|
| `ProtSat/Syntax.lean` | 565 | message algebra, subterms, universe pools |
| `ProtSat/Protocol.lean` | 647 | DSL: Expr with destructors, Actions, Roles, Sessions, Secrets, initKn |
| `ProtSat/Attacker.lean` | 247 | inductive Ded and OneStep, monotonicity, constructor/destructor laws, freshness |
| `ProtSat/Deduce.lean` | 1211 | executable attacker over a finite universe (spec 2.1-2.4) |
| `ProtSat/Operational.lean` | 591 | Cfg, Ev, Rel, Runs, Leak, AuthBreak, Attack - independent of the encoding |
| `ProtSat/Bounded.lean` | 311 | Bounds, seeds, universe construction, BoundedAttack/BoundedSafe |
| `ProtSat/CNF.lean` | 660 | CNF, satisfaction, one-hot, Tseitin gates, sequential AMO |
| `ProtSat/OneHot.lean` | 503 | the Oh abstraction, graph/relation/forward clauses, sound *and* complete |
| `ProtSat/Encode.lean` | 690 | variable layout, positional codes, injectivity, decoders |
| `ProtSat/Clauses.lean` | 747 | the eleven clause groups and `encode` |
| `ProtSat/Encoding.lean` | 3600 | 8A: satisfying assignment -> genuine bounded attack |
| `ProtSat/Complete.lean` | 4100 | 8B: the characteristic assignment of a run, all eleven clause groups, `encoding_complete` |
| `ProtSat/DPLL.lean` | 1180 | the verified solver (8D, 8E) |
| `ProtSat/Certificate.lean` | 937 | the independent checker (8C) |
| `ProtSat/Analyzer.lean` | 380 | the pipeline, 8F, 8G and the 8H termination theorems |
| `ProtSat/Examples.lean` | 430 | the six protocols, certificates, executable results |

## 12. Reading it

Start with `ProtSat/Operational.lean` (ten lines of semantics that everything else must
agree with), then `ProtSat/Clauses.lean` (what is generated), then
`ProtSat/Encoding.lean`'s `rel_agrees` and `encoding_sound` (why the generation is
correct), then `ProtSat/DPLL.lean` and `ProtSat/Certificate.lean` (how the answer is found
and how it is checked).  Each module opens with a prose section saying what it proves and
why; the hard proofs are commented step by step.
