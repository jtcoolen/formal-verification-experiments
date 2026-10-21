# ProtSat: a formally verified, proof-producing SAT-based cryptographic protocol analyser

A symbolic (Dolev-Yao) protocol analyser written in **Lean 4 + Mathlib**, in which the
central object of study is a *proved correspondence*:

> a bounded execution of a protocol that **leaks a declared secret** exists **if and only if**
> the propositional formula compiled from that protocol is satisfiable - provided the bounds can
> name that execution (`ProtSat.Complete.WithinBounds`).

The left-to-right direction is `ProtSat.Encoding.encoding_sound` (specification 8A); the
right-to-left direction is `ProtSat.Complete.encoding_complete` (8B).  A satisfying
assignment is not taken on trust: it is decoded into a concrete trace of protocol actions and
adversary deductions, and that trace is re-validated by an independent checker
(`ProtSat.Certificate`) that imports neither the CNF nor the solver.

Everything is checked by the Lean kernel: no `sorry`, no `admit`, no user-declared axioms,
no `native_decide`, no partial definitions.

## Read this before believing a verdict

The quoted correspondence is *not yet* the statement "the protocol is secure within its bounds",
for two reasons that are proved rather than confessed - see
[`VERIFICATION_PROGRESS.md`](VERIFICATION_PROGRESS.md) and `ProtSat/Regressions.lean`:

1. **The formula asks about secrets only.** `Encode.violationLits` contains leak literals and
   nothing else, while `Bounded.BoundedAttack` also counts a violation of non-injective
   authentication agreement. `Regressions.Authentication` is a kernel-checked query with
   `analyze P B = encodingUnsat` (`Authentication.analyze_encodingUnsat`) **and**
   `boundedAttackGoals q` through the selected `Goal.agreement` (`Authentication.hasAttack`): an
   unsatisfiable CNF and an attack on the goal the query asked about, at the same time.
2. **Completeness is conditional on representability.** `Regressions.Bounds` is a kernel-checked
   query with a bounded leak attack for which `WithinBounds` fails, because the protocol computes
   `fst (pair x x)` and the intermediate pair is outside the finite universe. A permitted run can
   have no name in the formula. Two things are now proved about that gap rather than assumed:
    `Represent.no_bound_discharges_exprB` shows *no* closure bound removes it (the condition asks the
    universe to be closed under pairing), and `BoundedExec.withinBounds_of_residual` shows it is the
    *only* one of the twelve `WithinBounds` conditions the public bound does not imply -
    `BoundedExec.Residual` is that single field now. `RunOK.actB` bounds the two
    `Ev.act` fields *where an action reads them*, which the public bound does imply
    (`BoundedExec.actB_of_bounded`), so for a query
    whose value domain has no gap (`Represent.domainGap`, decided by the tool) `WithinBounds` is a
    theorem - and `ProtSat/EndToEnd.lean` turns an `encodingUnsat` answer into `boundedSafeGoals`
    and `noLeak` with no execution hypothesis at all - and for a small real protocol both are
    proved with **no hypotheses whatsoever** (`EndToEnd.qg_safe`, `qg_noLeak`: well-formed,
    gap-free, and the CNF unsatisfiability checked by the kernel), depending only on
    `propext, Classical.choice, Quot.sound`. What that still assumes is the solver's own
    answer; `ProtSat/Resolution.lean` replaces it with evidence: a resolution refutation is checked
    by a linear walk (`checkProof_sound`), truncated, corrupted, out-of-range and wrong-formula
    evidence is rejected by `decide`, and `encodingUnsat_of_proof` reaches the verdict without
    running the solver. `ProtSat/Serialize.lean` lets that evidence leave the process that made
    it: a refutation is a flat list of integers with a total decoder, a proved round trip
    (`proofOfCode_proofCode`) and proved injectivity (`proofCode_inj`), so a code identifies its
    proof exactly and `checkCode_sound` turns bytes back into a formula fact.
    `ProtSat/CheckedSafe.lean` closes the chain at the level of a query:
    `boundedSafe_of_checkedCode` gives `boundedSafeGoals q` from an accepted code, with the
    goal-selection hypothesis stated rather than assumed, and it builds a `SafeEvidence` -
    something nothing could construct before. `ProtSat/Refute.lean` is the producer: a
    saturating resolution engine that is proved both sound and complete: `refute_sound` (the
    checker accepts whatever the engine emits) and `refute_complete` (if the formula is unsatisfiable,
    some fuel makes the engine emit a refutation), so `refute_iff` says the checker and the engine
    agree exactly, and `boundedSafe_of_refutation` turns engine output into `boundedSafeGoals q`. It
    is a theorem, not a solver: on the guarded protocol's real CNF, two saturation rounds produce
    37167 lines without reaching the empty clause and take 19 minutes to evaluate, so the closed
    `decide` gate exists only on the demo formula, and the reference DPLL still emits no proofs and
    no LRAT solver is installed
    here, so what remains is production at protocol size - measured, not hidden.

Two things are under way on that headline, and neither has closed it.

`ProtSat/AuthClauses.lean` prototypes agreement *as CNF clauses*: claim/commit positions read out of
the `Protocol` record as data, one selector auxiliary per commit occurrence, an excuse clause per
(commit, matching claim) pair, and a goal-indexed `encodeGoals` with
`encodeGoals P B [secrecy] = encode P B` proved. It also proves the negative result - the naive
`encode P B ++ <agreement clauses>` cannot work on the model `Regressions.Authentication` names,
because that model declares no secret so the secrecy demand is already the empty clause
(`authEncode_empty_clause`, `authEncode_not_sat`). What it does **not** claim: neither `SOUND` nor
`COMPLETE` is proved for the agreement encoding (every decoding lemma in `ProtSat/Encoding.lean`
takes `Sat a (encode P B)` - the secrecy formula - as its hypothesis), the three `Diff` gates are
kernel-decided cross-checks against the enumeration route on three models and not a correspondence,
and the file is additive: `Query.encodedGoals` is still `[secrecy]`, so `analyzeQuery` still refuses
every agreement query and nothing that imports it changes its answer.

`ProtSat/AnalyzerEvidence.lean` wires the analyser's own answer to checked evidence:
`refutationCodeOf q fuel -> checkCode -> boundedSafeGoals q`, with `analyzeQuery_encodingUnsat_of_code`
showing the verdict and the certificate are the same fact. `ProtSat/UnitRefute.lean` proves the fast engine correct: `unitRefutation_checkProof` says that for
ANY formula and ANY fuel, a refutation the unit-propagation producer returns is accepted by
`Resolution.checkProof`, and `prune_checkProof` says the dependency-closure pruner preserves
acceptance and cannot lose the empty clause. So the certificate is no longer "bytes the checker
happens to accept" - it is the output of a proved-sound engine. What remains hand-carried is one
equation: that these particular 138 integers ARE what the producer emits for `qg`. Replaying that
search in the kernel costs 65.9 s (measured), so the link is a conditional
(`UnitRefute.qg_produced_is_accepted`) whose hypothesis the demo program verifies at run time, and
`qg_prune_is_idempotent` shows the embedded bytes are already dependency-closed. The proved-sound
saturation engine's own decided instance (`qs_emitted`) remains a one-line refutation of a formula
that literally contains the empty clause (`AuthGap.why_the_formula_is_unsat`).

`ProtSat/Query.lean` is the layer that keeps the two apart. A `Query` names the protocol, the
bounds and the **selected goals** (`secrecy`, `agreement`, `agreementInj`);
`encodedGoals = [secrecy]` says what the CNF can currently represent a violation of; and `analyzeQuery` refuses - rather than answering - any query that
selects a goal the encoding does not represent:

```lean
Regressions.Authentication.query_refused :
    analyzeQuery q = Result.unsupportedGoals [Goal.agreement]
Regressions.Authentication.not_security : securityResult (analyzeQuery q) = false
Regressions.Bounds.hwb_fails :
    ¬ (∀ tr Cs, BoundedTrace P B tr Cs -> WithinBounds P B (cfgAt Cs) (evAt tr))
```

**`Goal.agreement` does not name one predicate in this repository, and the difference is proved, not
rhetorical.** `Query.Violation P Goal.agreement` is `ProtSat.AuthBreak` - a commit whose
`(tag, peer, value)` triple was never claimed, UNORDERED - while the reference route's
`Contract.goalViolation P Goal.agreement` is `ProtSat.Reference.authBreak = ¬ agrees`, which demands
a matching claim strictly earlier with the two roles crossed. `ProtSat/AgreementPredicates.lean`
proves they are **incomparable** (`ordered_not_le_unordered`, `unordered_not_le_ordered`, each with a
decided witness), and that the gap is not a missing proof: `AuthInst` carries no `self` and no `idx`,
so the ordering requirement is **inexpressible** in the vocabulary `AuthBreak` reads
(`authBreak_carries_too_little`). The consequence for the contract is stated as
`cnf_route_agreement_target_is_blind`: on `selfAddrP` - one session, a claim and a commit of the same
triple made by the wrong principal - the unordered reading is silent on all 43 permitted executions
while the ordered reading finds an attack. So a future CNF `boundedSafeGoals` for an agreement query
means *no commit triple went unclaimed*, not *no commit went unmatched*, and the two are different
propositions on a protocol that fits in eight lines. `Goal.agreementInj` is a separate trap:
`Violation P Goal.agreementInj` is `True`, so `boundedAttackGoals_of_agreementInj` proves every query
selecting it is attacked - harmless only because `goalEncoded` refuses it before the predicate is
consulted (`injQ_wellFormed` + `injQ_refused`); the validator does not save it. Note also that
`Examples.NS.P` declares no authentication event at all (`NS_has_no_auth_events`), so neither monitor
can witness the Lowe attack as an agreement violation in this model.
The old `Verdict.safe` is now `Verdict.encodingUnsat`, which is what the solver theorem
establishes. `Result.boundedSafe` exists in the contract and carries a `SafeEvidence`, and
`analyzeQuery_ne_boundedSafe` proves that `analyzeQuery` itself never returns it - the CNF
route's own answer is still `encodingUnsat`. What can construct one is checked evidence
(`CheckedSafe.safeEvidenceOfProof`, `AnalyzerEvidence.resultOf_emittedCode`), not the solver's
`none`. The conditional bridge
`boundedSafe_of_encodingUnsat` spells out exactly the hypotheses that stages 3 and 4 have to
discharge.

### The route that does give a verdict: exhaustive enumeration

Adding authentication clauses to the CNF means a new variable family inside `Complete.lean`, whose
block-range lemmas are all stated against `nVarsAll`. There is a second route, and it is now proved:
`ProtSat/Reference.lean` is a finite deterministic transition system, so its bounded executions can
be enumerated. `ProtSat/Explore.lean` does that and proves the answer *is* the security statement:

```lean
Explore.explorer_correct        : explorerAttack P B = true <-> BoundedAttack P B
Explore.boundedSafe_of_explorer : explorerAttack P B = false -> BoundedSafe P B
```

No encoding, no representability hypothesis and no solver appears in either direction, and both goals
`ProtSat.Query` distinguishes are covered. The gates are kernel-checked by `decide`:

* `Gates.secure_bounded_safe` - a genuine `BoundedSafe` verdict, with `secure_honest_run` and
  `secure_obligation_and_publication` showing the run reaches the events it claims about;
* `Gates.transient_pair_bounded_attack` - the leak `Regressions.Bounds` shows the CNF loses;
* `Gates.auth_bounded_attack` - an authentication break the CNF cannot express at all.

`ProtSat/Contract.lean` puts the query contract on top of that procedure, over the *repaired*
semantics: `goalViolation P g` selects `traceLeaks` for secrecy and the ordered role-aware
`authBreak` for agreement, `boundedAttack q` says a *selected* goal fails on some permitted
execution, and `boundedSafe q` is the statement a SAFE verdict is supposed to mean. The enumeration
is proved to decide exactly that question:

```lean
Contract.attackFound_decides : attackFound q = true <-> boundedAttack q
Contract.analyze_boundedSafe_sound : analyze q = boundedSafe e -> boundedSafe q
Contract.analyze_attack_sound : analyze q = attack x -> boundedAttack q
Contract.checkWitness_sound     : checkWitness q x = true -> boundedAttack q
```

and the analyser *produces* safety evidence instead of withholding it.

`analyze` is total - it has no `unknown` answer, because it never gives up.
The production shape is separate and explicit: `driverAnswer q fuel` returns `outOfFuel`,
`attack x` or `safe` under a node budget, with `driverAnswer_attack_sound` and
`driverAnswer_safe_sound` for what an answer is worth, and `searchFuel_eq_find?` /
`driverAnswer_complete` for what running out is not: a resource fact, never a semantic one. All four verdicts are
instantiated on models that already carry permanent witnesses:

* `Gates.secureQ_verdict` - `boundedSafe` with its `SafeEvidence`, on a model whose honest
  execution is proved to reach the generation, the declaration and the publication;
* `Gates.authQ_verdict` - the authentication attack the CNF route refuses to ask about
  (`Gates.authQ_cnf_refused` shows it answering `unsupportedGoals` instead);
* `Gates.transientQ_verdict` - the leak `Regressions.Bounds` proves the CNF cannot name;
* `Gates.emptyQ_verdict` and `Gates.badQ_verdict` - selecting nothing, and a malformed model,
  neither of which can be mistaken for security;
* `Gates.authOrderQ_verdict` and `Gates.authSwappedQ_verdict` - one role, `claim` then `commit`,
  is safe *non-vacuously* (`Gates.authOrderQ_boundedSafe` is the statement, `authOrder_commit_recorded`
  shows the commit is really reached); swapping the two actions breaks it. The monitor is ordered, and
  a safe authentication verdict is achievable;
* `Gates.replayAgreeQ_verdict` and `Gates.replayInjQ_verdict` - one claim then two commits, one
  protocol and one bound: non-injective agreement is `boundedSafe`, injective agreement is
  `boundedAttack`, and `replayInjQ_witness_agrees` shows the same execution satisfies the weaker
  monitor. The selected goal changes the answer, and the CNF route can ask neither question
  (`replayInjQ_cnf_refused`, `Gates.authQ_cnf_refused`).


A verdict is portable across bounds. `Bounds.le` orders bounds semantically (events and closure
rounds), `univ_mono` proves the message universe grows with the rounds, and
`boundedSafe_mono_bounds` / `boundedSafe_mono_goals` transfer a safety verdict downward while
`boundedAttack_mono_bounds` carries an attack upward. `Gates.secureQ2_boundedSafe` obtains the
two-event verdict from the three-event one without a second search, and
`Gates.secureQ2_attackFound_false` confirms the transferred answer agrees with actually running the
smaller enumeration. What the derived bound now reaches: roadmap stage 9 landed for the
straight-line role language. `ProtSat/Compress.lean` derives a step bound from the model itself -
`derivedSteps q = actionCount q.protocol + |univ q.protocol q.bounds|` - and proves that a violation
inside the query's own sessions and universe has a witness no longer than that
(`compress_secrecy`, `compress_agreement`, `compress_agreementInj`), so safety at the derived bound is
safety at every length (`safe_at_derived_bound_full`, and on the secure gate model it is decided by
the kernel: `Prune.Gates.secureQ_allLengthsSafe`). What is *not* claimed: the bound is derived from a
model with no jumps and no loops, it bounds *witnesses* rather than executions, and the compression is
stated up to the extensional equality `Compress.CfgEq`, not literal equality of the visited lists.

An `attack` verdict is a certificate, not a claim: `analyze_attack_certificate` shows the named
execution is a bounded run that violates a selected goal, and `checkWitness` re-checks exactly that
as a `Bool` computation without re-running the search (`checkWitness_sound` proves the re-check is
sound, `answer_checkWitness` that a produced witness passes it).

Scope, stated plainly. This is a *reference* procedure (exponential in `B.steps`; the gate models
enumerate 130-258 nodes). `Contract.boundedSafe` and `Query.boundedSafeGoals` are deliberately
different propositions over different semantics, and nothing bridges them: the CNF route's own
safety predicate is `boundedSafeGoals`, and for a gap-free query it is discharged with no hypotheses
at all (`EndToEnd.qg_safe`) - what the CNF route still owes is agreement, not secrecy.
`Query.boundedSafe_of_encodingUnsat` needs the representability hypothesis;
`Query.boundedSafe_of_encodingUnsat_of_residual` needs one named condition - expression
representability - because `ProtSat/BoundedExec.lean` proves the
other eleven `WithinBounds` conditions follow from the public bound alone, and
`BoundedExec.exprB_not_derivable` proves that one does not. The first `BOUNDED SAFE` gate
(`Explore.Gates.secureP`) has no `claim`/`commit` actions, so its authentication half
is vacuous; `Gates.authOrderQ_boundedSafe` is the non-vacuous replacement, and `Gates.authQ_verdict`
(one event: schedule the commit, block the claim) is the
reminder that agreement needs a progress assumption before it means what a reader assumes it means.

Also new: `ProtSat/ExprDomain.lean` gives each expression its own finite domain (`evalDomain`,
`eval_mem_evalDomain`), which is what makes the transient-pair run representable at all, and
`ProtSat/BoundedCert.lean` extends the certificate checker to verify the bounds
(`checkBounded_sound : checkBounded P B c = true -> BoundedAttack P B`).

---

## Build and run

The reference semantics checks both forms of secrecy declaration: `Secret.store q x` protects the
current value of the named register, while an action-level `secret e` creates a snapshot that persists
after registers change. `Reference.leaks_of_storeSecret` states the register guarantee. Its credential
check covers private and shared keys; receiving a hash or ciphertext grants no access to hidden keys,
and explicit decryption can still transport a key. The injective-agreement consumption budget is
shared by all commits that can match the same claim (`Reference.key_eq_of_shared_claim`), including
commits in different roles. The regression gates in `Reference` and `Contract` cover these cases.

Agreement violation selectors imply that the selected commit happened; performed commits may remain
unselected. `AgreesBaseComplete.encoding_correct_agreement` proves the resulting equivalence between
the agreement-only CNF and `Query`'s **unordered** agreement goal, assuming `univClosed`, nameable
annotations and a gap-free expression domain. `AuthSelectors` checks a run with both a matched commit
and an unmatched commit. The ordered reference monitor and mixed-goal conjunction are separate;
this theorem does not identify them with the unordered goal. `GoalAnalyze` remains conservative about
safety verdicts and proves its selected-goal attack and checked-code safety conclusions explicitly.

```sh
cd protosat
export ELAN_HOME=$PWD/../.elan          # or install elan system-wide
lake build                               # library + the demo executable
lake exe protosatDemo                    # the six examples, both contracts, the evidence gates
lake env lean Axioms.lean                # axiom audit of every theorem in ProtSat.*
```

`lake build` does **not** run the axiom audit: `axioms` is a target in `lakefile.toml` but not a
default one, which is why the third line is a separate command. Neither line is fast. A clean build
of the project's own modules against the cached Mathlib objects measured 174 s in
`VERIFICATION_PROGRESS.md`, and `scripts/ci.sh` budgets 1500 s for the build and 300 s for the demo.
The demo's own cost is the solver and the enumerations it recomputes at runtime; the `decide` gates
are paid for when the library is elaborated, not when the executable runs.

Mathlib is pinned to `v4.34.1` (Lean `4.34.1`).  Prebuilt Mathlib objects are cached in
`.mathlibcache`; to refresh them use

```sh
MATHLIB_CACHE_DIR=$PWD/.mathlibcache lake exe cache get
```

(the default cache directory is outside the workspace).

Single-module checking: `lake env lean ProtSat/Encoding.lean`.

### Continuous verification

`scripts/ci.sh` is the gate the roadmap asks for. The repository root (one level above this directory)
carries `.github/workflows/ci.yml`, which installs the pinned toolchain with elan, fetches Mathlib's
prebuilt objects with `lake exe cache get`, and then runs this script from `protosat/`. That workflow
has never been executed, so its timeouts are estimates; the script exits 3 with `ENVIRONMENT PROBLEM`
rather than reporting a proof failure when the machine is not the one its budgets assume. Nothing runs
it for you, so it is meant to be run before every commit - it is one command:

```sh
cd protosat && ./scripts/ci.sh
```

Each line of its output is a claim this README makes, checked rather than asserted:

| Gate | What fails if |
|---|---|
| `lake build` inside a time budget | a proof stops checking, or the development silently becomes unbuildable |
| no `sorry`, no `native_decide`, no user `axiom` | a trusted result stops being a proof |
| axiom audit | a theorem starts depending on something beyond `propext`, `Classical.choice`, `Quot.sound` |
| theorem inventory floor | a guarantee is deleted: the count may go up, not down |
| demo inside a time budget | the executable pipeline breaks or regresses badly in cost |
| demo prints `BOUNDED SAFE`, `ATTACK`, `ENCODING UNSAT`, `UNSUPPORTED GOALS`, `NO GOALS SELECTED`, `INVALID MODEL` | a contract case stops being reachable, so a verdict category becomes untested |
| demo prints `witness re-checked without the search: true` | attack certificates stop replaying independently of the search |
| demo prints `checkCertificate = true` and `= false` | the independent checker stops accepting the Lowe attack, or stops rejecting the same script on NSL |
| demo prints `refutation checked: true`, `serialized refutation checked: true`, `engine output survives serialization: true` | the UNSAT evidence chain stops checking, stops surviving a trip through integers, or the engine's own output stops being accepted |
| demo prints `certificate: 138 integers, 21 resolution lines` and `the independent checker accepts the certificate: true`, and rejects the same bytes against the leaky model | the analyser's checked certificate stops being the artifact this README describes |
| demo prints the value-domain report (`value domain: complete` and `value domain: GAP`) | the tool stops saying which queries the CNF can name |

The honest-execution witnesses and the kernel-checked gates (`ProtSat/Regressions.lean`,
`ProtSat/Reference.lean`, `ProtSat/Explore.lean`, `ProtSat/Contract.lean`, `ProtSat/AuthGap.lean`,
`ProtSat/EndToEnd.lean`, `ProtSat/AnalyzerEvidence.lean`, `ProtSat/Benchmarks.lean`,
`ProtSat/Compress.lean`, `ProtSat/Prune.lean`) are part of the build - every one of those modules is
imported by `ProtSat.lean` - so they are covered by the first line rather than needing a separate
check. `ProtSat/AuthClauses.lean` is imported too, and it carries gates of its own
(`gate_agreement_attack_found`, `gate_order_unsat`).

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

is a total function into `option` - there is no `partial` definition anywhere in the library: a
destructor whose argument does not have the right shape returns `none`, and an
action that evaluates to `none` is **not enabled** (this is how "the attacker sent the wrong
message" is modelled).  The symbolic equations of perfect cryptography are the reduction
laws, and they are theorems about the constructors, not assumptions:

```lean
Attacker.encS_then_decS : eval (decS (encS m k) k) = m
Attacker.encA_then_decA : eval (decA (encA m a) a) = m
Attacker.pair_then_proj : eval (fst (pair x y)) = x  ...
```

Terms are *normal forms*: there is no rewriting relation to decide because every constructor
is injective (`Term.pair_inj`, `Term.encS_inj`, …) and destructors compute.  `Bounded.subtermsL`
/ `subtermClosureL` (both declared in `ProtSat/Bounded.lean`, not in `Syntax.lean`) give the subterm
structure the universe construction needs, with `subtermClosureL_closed` and `subtermsL_subtermsL`.

**No computational content is claimed.**  `encS` is an uninterpreted constructor: the model
says what the attacker can *derive*, not what it can compute in polynomial time.

## 2. The adversary (specification section 2)

Two presentations of the same power, both proved:

* `Attacker.Ded` - an inductive 11-rule Dolev-Yao relation (`known` for replay of what is
  already held, `agent` and `pub` for public names and public keys, `pairI`, `fstE`/`sndE`,
  `encSI`/`encSD`, `encAI`/`encAD`, `hashI`), with
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
univ P B = ((closeOne ...)^[B.rounds] (subtermClosureL (seeds P))).eraseDups
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
`Encode.univClosed` (declared in `ProtSat/Clauses.lean`) - "every closed protocol expression
denotes a universe message" - is
the (decidable, checked) hypothesis that makes it a faithful one.

## 5. The SAT encoding (specification section 5)

`Encode.lean` allocates variables positionally (`vpc, vst, vkn, vev, vdl, vfr, vxe` plus the
auxiliary blocks `apc..afr`, `vpb`, `vau`) with proved injectivity (`vpc_inj`, …,
`vpc_inj_full`, …) and disjoint block ranges (`vst_lt_bsKn`, …).  `OneHot.lean` provides the
abstraction `Oh` (a finite domain, an injective variable map, and auxiliary flags), the
**linear-size** sequential at-most-one encoding (`ProtSat.atMostOneSeq`, declared in
`ProtSat/CNF.lean`, with `atMostOneSeq_amo`), function-graph clauses (`graph_correct` / `graph_correct_back`),
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
| A | every model of the CNF decodes to a valid bounded execution that **leaks a declared secret** - and the decoded run is now proved to stay inside the universe, so the conclusion is the public bounded predicate and not an attack plus a length inequality | `Encoding.encoding_sound`, `Sound.decoding_runsInUniverse`, `Sound.encoding_sound_bounded'` | proved |
| A= | **the equivalence**, both directions: for a gap-free query the generated CNF is satisfiable exactly when the query has a bounded attack on its secrecy goal - with `Encode.univClosed` and `Complete.SecretsOKStore` still hypotheses of that statement; instantiated with no hypotheses at all on a real leaking protocol, where the witness is the run decoded from the assignment | `Sound.encoding_correct`, `Sound.leaky_query_boundedAttack` | proved (secrecy only) |
| B | every valid bounded **leaking** execution that satisfies `WithinBounds` yields a model of the CNF; for a gap-free query `WithinBounds` is itself a theorem of the bound (`BoundedExec.withinBounds_of_bounded`), and the correspondence is instantiated in both directions on two real protocols (`Differential.guard_correct`, `Differential.leak_correct`) | `Complete.encoding_complete`, `Differential.leak_sat` | **proved, with the hypotheses shown** |
| C | every accepted certificate is a genuine trace | `Certificate.checkCertificate_sound` | proved |
| D | solver SAT answer is a real model | `DPLL.dpll_sound` | proved |
| E | solver UNSAT answer means unsatisfiable | `DPLL.dpll_complete` | proved |
| F | analyser attack verdict gives a bounded attack | `Analyzer.analyze_attack_sound`, `analyze_attack_bounded` | proved |
| G | analyser `encodingUnsat` verdict means no bounded **leaking** execution satisfying `WithinBounds` | `Analyzer.analyze_safe_sound`, `analyze_not_safe_of_attack` | **proved, and it is not a statement about `BoundedAttack`** |
| H | termination of state construction, encoding, DPLL, checking | `Analyzer.shape_finite`, `encode_vocab_finite`, `dpll_none_iff_unsat`, `checkCertificate_eq_decide`, `analyze_verdict_cases` | **proved** |

**8B is the converse, and it is the theorem that would make a SAFE verdict mean something - except
that its violation condition is `runsLeaks`, not `BoundedAttack`.** The gap is
`Regressions.Authentication`, and it is now a theorem rather than a remark:
`AuthGap.auth_gap_is_real` proves `boundedSafeGoals` for the secrecy-only query and its negation
for the agreement query over the *same* protocol and bounds, and
`AuthGap.goal_hypothesis_is_needed` proves that no transfer between the two is possible without a
goal-selection hypothesis. Closing the gap for real means adding authentication violation clauses
to `Encode.encode` and proving the Boolean monitor equivalent to the independently defined
`ProtSat.Violation` (roadmap stage 4). `ProtSat/AuthClauses.lean` is a prototype of exactly that -
goal-indexed `encodeGoals`, claim/commit positions read from the model as data, excuse clauses
mirroring `Reference.claimMatches` - together with the proof that the naive form cannot work
(`authEncode_not_sat`). Neither direction of the correspondence is proved for it, and it is not
wired into the analyser.
Its proof is a construction: `Complete.assignOf` is the *characteristic function of the run* -
a propositional variable is true exactly when the semantic fact it names holds - built from
fifteen disjoint block tests over the positional codes (`Complete.asgPc`, `asgSt`, `asgXe`,
`asgAu` and friends) and the readers `rdPc`, `rdSt`, `rdXe`, `rdDl`, `rdFr`, `rdEv`,
`dedIx` that say what the run selects.  `encoding_complete` then proves each of the eleven
clause groups is satisfied by that assignment (`sat_oneHot`, `sat_init`, `sat_frame`,
`sat_eval`, `sat_step`, `sat_ded`, `sat_pubAux`, `sat_knSupport`, `sat_fresh`,
`sat_leakAux`, `sat_violation`), and concatenates them with `sat_encodeGroup`.  The
hypotheses `Complete.encoding_complete` actually takes are `univClosed`, `SecretsOKStore`, the run,
its length bound, `runsLeaks` and `WithinBounds`. `WithinBounds` is `Complete.RunOK`: the twelve
bounds conditions of specification section 4 (the run stays inside the shape, its expressions denote
universe messages, the shape's strides cover the protocol's variables and expression table), and
`SecretsOKStore` is the store-slot half of `SecretsOK` - the bounds can name a declared secret that
lives in a store slot. Two things that used to be hypotheses are no longer: the
universe's subterm-closure is the theorem `Complete.univSub_shapeOf` (`ProtSat/Closure.lean` is the
narrative and the instances), and the closed-secret half of `SecretsOK` is the theorem
`Complete.secretsClosed_subset_univ`. What is left is not ceremonial: a run that leaves the universe
has no finite name, and a violation the encoding cannot mention cannot be found -
`Complete.secretsOKStore_not_derivable` exhibits a model where the remaining half fails.

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

In this table `SAFE` is the CNF route's answer - `encodingUnsat`, which is a statement about secrecy
only (see "Read this before believing a verdict"); the enumeration route's `BOUNDED SAFE` for both
goals is in the gates above.

| # | protocol | bounds | result | how |
|---|---|---|---|---|
| 1 | challenge-response, K(A,B) uncompromised | steps 2, rounds 0 (1335 vars / 2995 cls) | SAFE (secrecy) | solver (`Challenge.verdict_if_none`, `Challenge.safe_if_none`) |
| 2 | replay: static authenticator, no freshness | steps 4, rounds 0 (4679 vars / 12899 cls) | ATTACK, 4 events | solver **and** certificate (`Replay.checked`, `Replay.attack`) |
| 3 | key disclosure: compromised K(A,B) | steps 2, rounds 0 (1263 vars / 2767 cls) | ATTACK, 2 events | solver **and** certificate (`KeyDisclosure.checked`, `KeyDisclosure.attack`) |
| 3b | the same protocol, key not disclosed | as 3 | SAFE (secrecy) | solver (`EndToEnd.qsafe` is that query; `EndToEnd.boundedSafe_of_gapFree` and `noLeak` read the answer as security, with the analyser's answer as their only hypothesis - `wf_safe`, `gapFree_safe`, `hU_safe`, `hsec_safe` are all decided) |
| 4 | Needham-Schroeder public key | model only | - | `Examples.NS.P` |
| 5 | Lowe attack on NS | 14 events | ATTACK | certificate (`NS.checked`, `NS.attack`) |
| 6 | Needham-Schroeder-Lowe | same 14-event script | REJECTED | certificate (`NSL.rejected`, `NSL.breaks_at_the_check`) |

The CNF sizes are what `lake exe protosatDemo` prints (re-measured 2026-10-20). Note that
`ProtSat/EndToEnd.lean`'s kernel-cost table used to record 2995 clauses for example 3: that was a
transcription of example 1's clause count, and the demo's 2767 is the true figure.

Example 6 is the interesting one as evidence: the *same* attack script that the checker
accepts against NS is refused against NSL, and `NSL.prefix_ok` + `NSL.breaks_at_the_check`
pin the refusal to exactly Lowe's identity check - the first nine steps are valid transitions
and the tenth is not enabled.

## 10. Guarantees, and what is not claimed

* **What a verdict is about.** `analyze` answers the question the CNF asks: no bounded execution
  inside `steps` events, the declared sessions and the universe generated by `rounds` closure
  rounds **leaks a declared secret** - and, for the completeness direction, only executions that
  satisfy `WithinBounds`. Agreement violations are not in the formula
  (`Regressions.Authentication`), and `Regressions.Bounds` shows a permitted leak the formula
  cannot name. Use `ProtSat.analyzeQuery` to get an answer that says which of these it is.
  `ProtSat.Reference.Contract.analyze` answers the question instead, by exhaustive enumeration over
  the repaired semantics: its `boundedSafe` verdict carries `boundedSafe q` as evidence, for every
  goal the query selected, with no representability hypothesis - at the cost of a search that is
  exponential in the bound and a reference model, not the CNF's.
* **Bounded, not unbounded.** Even a genuine `boundedSafeGoals q` is a statement about the query's
  sessions, domains and bounds, not a proof of protocol security. (Specification 11 forbids the
  confusion; the classic result that 2 sessions and 10 steps suffice to refute NS is a reminder
  that small bounds are meaningful, not a claim of completeness over all runs.)
* **Symbolic, not computational.**  Perfect cryptography: no reduction to a hardness
  assumption is claimed or possible here.
* **Under-approximation is explicit.**  Actions whose value leaves the universe are disabled;
  `univClosed` is checked before any verdict is reported (`Verdict.boundsTooSmall` otherwise).
* **The certificate is the evidence.**  Attack verdicts can be handed to a verifier that
  shares no code with the encoder or the solver.
* **A safety claim that rests on the solver's answer rests on solver completeness.**
  `analyze_safe_sound` is 8B (a bounded *leak* would give a model) plus 8E (the solver's `none`
  answer means there is no model). For a gap-free query the representability half of that is now a
  theorem of the bound (`BoundedExec.withinBounds_of_bounded`), and on a small real protocol the
  whole chain is closed with no hypotheses (`EndToEnd.qg_safe`) - but the violation condition is
  still `runsLeaks`, so "the solver found no model" is not yet "the protocol has no attack": the
  agreement half is the distance that remains, and `ProtSat.Query` is what stops the gap from being
  reported as safety in the meantime. The "no certificate to check" objection has been answered in
  form: `Resolution.checkProof` and `Serialize.checkCode` check a refutation instead of replaying
  the search (`encodingUnsat_of_proof`, `boundedSafe_of_checkedCode`), and `Refute.refute_complete`
  says fuel exists for every unsatisfiable formula. Two producers are now proved sound - `Refute.saturate` (`refute_sound`) and the unit-propagation
  engine (`UnitRefute.unitRefutation_checkProof`, `prune_checkProof`). What is not closed is
  affordability: neither can refute a protocol-sized formula inside the kernel's replay budget, so
  the emitted certificates are checked artifacts rather than kernel-replayed searches.
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
| `ProtSat/Bounded.lean` | 357 | Bounds, seeds, universe construction, BoundedAttack/BoundedSafe |
| `ProtSat/CNF.lean` | 784 | CNF, satisfaction, one-hot, Tseitin gates, sequential AMO |
| `ProtSat/OneHot.lean` | 518 | the Oh abstraction, graph/relation/forward clauses, sound *and* complete |
| `ProtSat/Encode.lean` | 789 | `Shape`, variable layout, positional codes, injectivity, decoders |
| `ProtSat/Clauses.lean` | 753 | the eleven clause groups, `Encode.univClosed`, `violationLits` and `encode` |
| `ProtSat/Encoding.lean` | 3617 | 8A: satisfying assignment -> genuine bounded attack |
| `ProtSat/Complete.lean` | 4584 | 8B: the characteristic assignment of a run, all eleven clause groups, `encoding_complete`, `RunOK`, and the `SecretsOK` split (`secretsClosed_subset_univ` proved, `secretsOKStore_not_derivable` proved undroppable) |
| `ProtSat/DPLL.lean` | 1219 | the verified solver (8D, 8E) |
| `ProtSat/Certificate.lean` | 937 | the independent checker (8C) |
| `ProtSat/Analyzer.lean` | 396 | the pipeline, 8F, 8G and the 8H termination theorems |
| `ProtSat/Query.lean` | 621 | the contract: `Query`, `Goal`, `Violation`, validator, `Result`, `analyzeQuery`, the gate theorems |
| `ProtSat/Regressions.lean` | 338 | permanent kernel-checked witnesses for every open gap |
| `ProtSat/Reference.lean` | 896 | the repaired reference semantics: allocation history, action-specific events, ordered role-aware agreement, credential provisioning, secret obligations |
| `ProtSat/Explore.lean` | 688 | complete bounded decision procedure by enumeration: `inBounds`, `candidates`, `stepB`, `frontier`, `explorer_correct`, kernel-checked gates |
| `ProtSat/Contract.lean` | 1193 | the goal-indexed contract over the repaired semantics: `boundedSafe q`, `attackFound_decides`, an analyser that issues `boundedSafe` with evidence, the kernel-checked verdict gates |
| `ProtSat/ExprDomain.lean` | 320 | finite per-expression domains: `evalDomain`, `eval_mem_evalDomain`, the transient pair handled |
| `ProtSat/Represent.lean` | 671 | the value domain a query needs: `shapeX`, the decidable `domainGap`, `exprB_of_domainGap_false`, `no_bound_discharges_exprB`, and the representability report the demo prints (`Shape` itself is in `Encode.lean`) |
| `ProtSat/BoundedExec.lean` | 675 | eleven of the twelve `WithinBounds` conditions as theorems of the public bound (`withinBounds_of_residual`, `actB_of_bounded`), the twelfth isolated as `Residual`, and `exprB_not_derivable` proving that one is a real condition |
| `ProtSat/EndToEnd.lean` | 193 | the closed verdict: `qg_safe` and `qg_noLeak` with no hypotheses at all, and `boundedSafe_of_gapFree` / `noLeak` with the analyser's answer as the only one; the kernel-replay costs are published in the header |
| `ProtSat/Resolution.lean` | 351 | independently checkable UNSAT evidence: resolution refutations, `checkProof_sound`, kernel-checked rejection gates, evidence bound to its formula, DIMACS export |
| `ProtSat/Serialize.lean` | 336 | refutations as a flat integer code: total decoder, round trip (`proofOfCode_proofCode`), injectivity (`proofCode_inj`), `checkCode_sound` |
| `ProtSat/CheckedSafe.lean` | 147 | the evidence chain at query level: `boundedSafe_of_checkedCode`, `SafeEvidence` from a checked refutation |
| `ProtSat/Refute.lean` | 1289 | the producer: saturating resolution, `refute_sound` (the checker accepts its output) and `refute_complete` (every unsatisfiable formula has output to accept), so `refute_iff` |
| `ProtSat/AnalyzerEvidence.lean` | 508 | the analyser emits a checked refutation certificate: `refutationCodeOf` -> `checkCode` -> `boundedSafeGoals`, with a 138-integer certificate for the 246-variable guarded query decided in the kernel (`qg_checked`, `qg_boundedSafe`) |
| `ProtSat/UnitRefute.lean` | 1719 | the fast producer proved sound: every line unit propagation emits is an initial clause or a resolution of two earlier ones (`AllOK_unitRefutation`), the checker accepts its refutations (`unitRefutation_checkProof`), and pruning preserves both (`prune_checkProof`, `AllOK_prune`) |
| `ProtSat/DecodeIndex.lean` | 623 | the decoded-run index bridge: `decEvsFrom`/`decCfgsFrom` transported into `evAt`/`cfgAt`, plus `decEv_act_of_decCode` - the repo's action-decoding lemma with the `Sat a (encode P B)` hypothesis dropped |
| `ProtSat/GoalEncode.lean` | 825 | the violation group indexed by the query's goals: `encodeGoalsOf P B [secrecy] = encode P B` by `rfl`, the correspondence moved onto it by rewriting, agreement soundness reduced to one named hypothesis, and the transport shortcut proved false (`no_transport_from_base`) |
| `ProtSat/AgreementPredicates.lean` | 971 | the two agreement predicates proved incomparable, the ordering requirement proved inexpressible in `AuthBreak`'s vocabulary, the CNF contract's agreement target proved blind on a concrete model, and the `agreementInj` violation predicate proved to be `True` |
| `ProtSat/AgreesBase.lean` | 2789 | agreement SOUND: the decoding cone restated over the ten semantic groups (`rel_agrees_b` and 68 siblings), the claim/commit reflection bridge proved (`commitsReflect_of_sat`, `claimsReflect_of_sat`), `DecodedRun` discharged, and a kernel-decided instance on the AuthGap model |
| `ProtSat/Sound.lean` | 384 | the soundness half: decoded values are universe values, `decoding_runsInUniverse`, and the two-sided `encoding_correct` |
| `ProtSat/AuthGap.lean` | 524 | the authentication gap as a theorem: safe for secrecy and attacked for agreement at one protocol and one bound (`auth_gap_is_real`, `goal_hypothesis_is_needed`), plus a second model where the secret is real (`auth_gap_is_real_nonvacuous`) |
| `ProtSat/AuthClauses.lean` | — | Agreement selectors and clause groups; `sat_authSelectorClauses` states selection implies occurrence. The unordered agreement-only soundness and completeness proofs are in `AgreesBase` and `AgreesBaseComplete`; ordered-reference integration and mixed-goal completeness remain separate. |
| `ProtSat/AgreesBaseComplete.lean` | — | `assignOfSelected` extends the characteristic run assignment with one violating commit; `encoding_complete_agreement` and `encoding_correct_agreement` prove agreement-only completeness and correspondence under their explicit bounds and naming hypotheses. |
| `ProtSat/AuthSelectors.lean` | — | Kernel-checked SAT witnesses with a matched commit left unselected and a later unmatched commit selected, for both matching policies. |
| `ProtSat/GoalAnalyze.lean` | — | The goal-indexed driver, selected-goal attack/certificate soundness, conservative checked-code safety, refusal gates and concrete end-to-end regression gates. |
| `ProtSat/Closure.lean` | 85 | narrative and instances for the universe being subterm-closed by construction; the lemma itself is `Complete.univSub_shapeOf` |
| `ProtSat/Prune.lean` | 829 | stage 8 proved refinement: pruning idle and redundant deductions, `explorerAttack_equiv` both ways, and `secureQ_allLengthsSafe` decided by the kernel |
| `ProtSat/Compress.lean` | 2629 | stage 9: the step bound derived from the model - `compress_secrecy`, `compress_agreement`, `compress_agreementInj`, and `safe_at_derived_bound_full`: safety at the derived bound is safety at every length, for every goal (straight-line roles only) |
| `ProtSat/Benchmarks.lean` | 869 | NS and NSL in the reference language: contract verdicts by exhaustion, honest-execution non-vacuity, adverse controls |
| `ProtSat/Differential.lean` | 118 | the enumeration route and the CNF route used as each other's oracle; `encoding_correct` instantiated on two real protocols |
| `ProtSat/Correspondence.lean` | 109 | the correspondence for every gap-free query: `encoding_complete_gapFree`, `boundedSafe_of_unsat_gapFree`, `boundedSafe_of_refutation` |
| `ProtSat/BoundedCert.lean` | 158 | `checkBounded`: certificates that carry their bounds, sound to `BoundedAttack` |
| `ProtSat/Examples.lean` | 433 | the six protocols, certificates, executable results |

Not in the map: `ProtSat.lean` (the import list every module must appear in), `Main.lean` (the demo),
`Axioms.lean` (the audit) and `scripts/ci.sh` (the gate). Line counts are `wc -l` on the source.

## 12. Reading it

Start with `ProtSat/Operational.lean` (ten lines of semantics that everything else must
agree with), then `ProtSat/Clauses.lean` (what is generated), then
`ProtSat/Encoding.lean`'s `rel_agrees` and `encoding_sound` (why the generation is
correct), then `ProtSat/DPLL.lean` and `ProtSat/Certificate.lean` (how the answer is found
and how it is checked).  Each module opens with a prose section saying what it proves and
why; the hard proofs are commented step by step.
