# ProtSat verification: working log

This file tracks progress against
[`output/protsat-review-2026-10-19/VerificationRoadmap.md`](../output/protsat-review-2026-10-19/VerificationRoadmap.md).
It is a running log, not a marketing document: every claim below names the Lean declaration that
backs it, and every gap names the witness that shows it is a gap.

## Where the project actually stands (baseline, 19 Oct 2026)

The build is green (1841 jobs), there are no `sorry`s and no user-declared axioms
(`lake env lean Axioms.lean` audits every theorem in `ProtSat.*`).

What is genuinely proved:

* `ProtSat.Encoding.encoding_sound` (8A): a satisfying assignment of the generated CNF decodes
  to a real `ProtSat.Rel` execution that **leaks a declared secret**.
* `ProtSat.Complete.encoding_complete` (8B): a real bounded execution that **leaks a declared
  secret** and that satisfies `ProtSat.Complete.WithinBounds` yields a satisfying assignment.
* `ProtSat.DPLL.dpll_sound` / `dpll_complete` (8E): the solver answers correctly both ways.
* `ProtSat.Certificate.checkCertificate_sound` (8C): an accepted certificate is a real
  `Attack` — where `Attack` is `runsLeaks ∨ AuthBreak`.
* `ProtSat.Analyzer.analyze_attack_sound` (8F), `analyze_safe_sound` (8G).

The three defects the review found, each with a kernel-checked witness:

1. **`SAFE` means CNF-UNSAT, not bounded security.** `Encode.violationLits`
   (`ProtSat/Clauses.lean:679`) contains only leak literals, so authentication violations are
   absent from the formula, while `Bounded.BoundedAttack` (`ProtSat/Bounded.lean:304`) includes
   `AuthBreak`. Witness: `output/protsat-review-2026-10-19/AuthenticationCounterexample.lean` —
   `analyze P B = safe` **and** `BoundedAttack P B`, both by `decide`.
2. **`WithinBounds` silently narrows the question.** It is an execution-wide hypothesis of
   `encoding_complete`, including condition 7 (`exprB`: every protocol expression denotes a
   universe message), which a legitimate run can violate. Witness:
   `output/protsat-review-2026-10-19/BoundsCounterexample.lean` — a valid in-universe run with
   `fst (pair x x) = x` where the intermediate pair is outside `U`, so `WithinBounds` fails
   although the attack is real.
3. **Reference-semantics defects.** Witness:
   `output/protsat-review-2026-10-19/SemanticsCounterexamples.lean` — nonce reuse after
   overwrite and nesting (`nonceUsed` reads only current stores), a commit excused by a *later*
   claim, a commit whose peer expression is unset silently producing no authentication event,
   and NS advertising an authentication break with no authentication events at all.

## Stage 1 — the truthful result contract

Design decisions:

* A `Query` is the single object every verdict refers to: protocol, bounds, and the **selected
  goals**. Compromise assumptions and domains stay inside `Protocol` (they are model data), so a
  query cannot silently disagree with its protocol.
* `Goal` distinguishes `secrecy`, `agreement` (non-injective) and `injectiveAgreement`.
  `encodedGoals = [secrecy]` records what the CNF can currently represent a violation of. That
  is the honest gap, stated in the API instead of in a comment.
* `Analyzer.Verdict.safe` is renamed `encodingUnsat`: it means "the generated CNF has no
  model", which is all the solver theorem establishes.
* `Query.Result` has the roadmap's categories: `invalidModel`, `noGoals`, `unsupportedGoals`,
  `boundsTooSmall`, `encodingUnsat`, `attack`, `unknown`, and `boundedSafe` — the last one
  **unreachable by construction** until the encoding covers the selected goals
  (`analyzeQuery_ne_boundedSafe`).
* Acceptance-gate theorems, all in `ProtSat/Query.lean`:
  * `analyzeQuery_unsupported_of_unencoded`, `analyzeQuery_not_security_of_unencoded`: a query
    selecting a goal the encoding does not represent gets no security verdict;
  * `analyzeQuery_noGoals_of_empty`: an empty goal set gets `noGoals`;
  * `analyzeQuery_invalidModel_of_diagnostics`: a malformed model gets `invalidModel`;
  * `analyzeQuery_ne_unknown`: the mathematical reference analyser is total;
  * `analyzeQuery_attack_sound`: an attack verdict yields a checker-accepted certificate;
  * `analyzeQuery_encodingUnsat_unsat`: an `encodingUnsat` verdict yields
    `ProtSat.Unsat (encode …)` — the only claim attached to it;
  * `boundedSafe_of_encodingUnsat`: the conditional bridge with every hypothesis the
    correspondence needs spelled out, including the `WithinBounds` representability hypothesis
    that stages 3 and 4 must eventually discharge.
* The validator `validate q` is decidable and rejects the vacuity class the review found: an
  `auths` entry whose tag is never claimed or committed by an instantiated session is a
  diagnostic when `agreement` is selected. (Every example in `ProtSat/Examples.lean` currently
  has `auths := []` and no claim/commit action, which is exactly the NS instrumentation gap.)

## Stage 1 — done (this round)

Build: `lake build` green (1845 jobs). Axiom audit: 2180 theorems in `ProtSat.*`, only
`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.

New modules:

* `ProtSat/Query.lean` (563 lines) - the contract. `Goal`, `encodedGoals = [secrecy]`, `Query`,
  `Violation`, `boundedAttackFor`, `boundedAttackGoals`, `boundedSafeGoals`, `Diagnostic`,
  `validate`, `WellFormed`, `Result`, `SafeEvidence`, `UnknownReason`, `analyzeQuery`,
  `describe`. Theorems: `boundedAttackGoals_iff_BoundedAttack`, the four gate theorems,
  `analyzeQuery_encodingUnsat_unsat`, `univClosed_of_analyzeQuery_encodingUnsat`,
  `analyzeQuery_attack_sound`, `boundedSafe_of_encodingUnsat`.
* `ProtSat/Regressions.lean` (338 lines) - the review witnesses, now built and audited:
  `Regressions.Authentication` (`analyze P B = encodingUnsat` together with
  `boundedAttackGoals q`, plus `query_refused` and `not_security`),
  `Regressions.Bounds` (`boundedAttackGoals q`, `pair_outside`, `gate_clipped`,
  `not_withinBounds`, `hwb_fails`, `attack_but_not_representable`),
  `Regressions.Semantics` (nested and overwrite nonce reuse, NS with no authentication events,
  later-claim excuse, unset-commit erasure).

Renamed: `Analyzer.Verdict.safe` -> `encodingUnsat`, with the docstrings stating that it is a
claim about the formula. `Main.lean` gained a "THE QUERY CONTRACT" section that prints
`describe (analyzeQuery q)` for seven queries, including the two regression queries, a malformed
model and an empty goal set.

Two findings that were not in the review and are now recorded:

1. The **secrecy** bridge also fails unconditionally. `Regressions.Bounds` has a bounded leak
   attack, and the executable pipeline reports the CNF unsatisfiable for it (the demo prints it).
   The kernel-checked part of that claim is `not_withinBounds`: the reason completeness does not
   apply is representability, not solver power. Kernel-`decide` on that CNF (1352 variables,
   2597 clauses) does not finish in minutes, so the unsatisfiability of *that* instance is
   demonstrated executably, not as a `decide` theorem. The authentication instance (648
   variables) is small enough to be `decide`-checked, and is.
2. The certificate checker does not verify the message-universe bound, so `checkCertificate`
   alone does not yield `BoundedAttack`; `Regressions` proves the universe fact separately by
   `decide`. Roadmap stage 5 has to fold the bounds into the checker.

## Stage 2 - repaired reference semantics (`ProtSat/Reference.lean`, 896 lines)

A second semantics module, independent of SAT (it imports only `ProtSat.Bounded` and
`ProtSat.Certificate`), so the eight thousand lines of encoding proofs keep their meaning while
the defects are fixed where they can be proved fixed. Each gate below is a `decide`-checked
theorem, and each is the repaired counterpart of a witness in `ProtSat/Regressions.lean`.

**Configuration.** `Cfg = { sess, kn, alloc, oblig }`: the nonce allocation history and the secret
obligations are state, not readings of the current stores.

| Gate | Theorem | Repairs |
|---|---|---|
| nested nonce reuse rejected | `Gates.nested_reuse_rejected` | `Regressions.Semantics.nested_reuse_accepted` |
| overwrite reuse rejected | `Gates.overwrite_reuse_rejected` | `Regressions.Semantics.overwrite_reuse_accepted` |
| history monotone | `alloc_mono`, uniqueness `not_generate_allocated`, domain bound `not_generate_outside_domain`, `generate_step` | `nonceUsed` |
| send/check with an empty nonce domain | `Gates.empty_domain_run` | `RunOK.actB` demanding `d ∈ sh.D` |
| malformed annotation blocks | `Gates.unset_commit_blocked`, `Gates.nonce_peer_blocked` | `authOfStep` returning `[]` |
| later claim does not excuse | `Gates.later_claim_does_not_excuse` | `Regressions.Semantics.later_claim_excuses_commit` |
| wrong peer does not excuse | `Gates.wrong_peer_breaks` | `AuthBreak` ignoring actor and order |
| injective differs from non-injective | `Gates.replay_agrees_noninjectively`, `Gates.replay_breaks_injectively`, `agreesInj.agrees` | (new capability) |
| unprovisioned decryption unavailable | `Gates.unprovisioned_decryption_blocked`, positive control `Gates.provisioned_decryption_works` | `Expr.eval` letting any role name any private key |
| private key not publishable | `Gates.unprovisioned_key_not_publishable`, control `Gates.provisioned_key_publishable` | same |
| secret survives an overwrite | `Gates.snapshot_leaks` with `Gates.snapshot_register_forgotten` and `Gates.snapshot_obligation_kept` | `Secret.store` re-reading the register |
| honest runs reach the events being claimed | `Gates.pair_honest_run`, `Gates.reuse_prefix_runs`, `Gates.replay_runs`, `Gates.snapshot_runs` | vacuity guard (roadmap stage 6) |

Design notes:

* Events are `idle | ded t | recv q m | generate q n | act q`. A deterministic action carries
  nothing; what it published and which authentication event it was are derived from the action and
  the configuration (`instAt`), which is what the roadmap asked for instead of `act q m d` with
  dummy fields.
* `Rel` is defined through the total function `stepOf`, so every gate is a kernel computation
  rather than an inversion of an inductive. `Runs` is `run P C₀ tr = some Cs`.
* Credentials: `provisioned P q = priv(self) :: [shrk self peer, shrk peer self]` plus every key
  appearing in the session's store; `actionUsable` gates `Ev.act` before `actStep` runs, so a
  role never acquires a key by naming it.
* `secret e` snapshots the *value* into `Cfg.oblig`; `declaredSecrets = closedSecretTerms ++ oblig`,
  with `leaksBool_iff` / `traceLeaksBool_iff` connecting the executable and declarative forms.

Still open in stage 2: role parameterisation by `self`/`peer` inside role expressions (roles still
name principals literally), the dataflow/read-before-binding check, and renaming invariance for
canonical nonce names.

## Next increment, designed and partially prototyped: the exhaustive explorer

The headline goal is a verdict that *is* the security statement, for both goals. The SAT route needs
a new variable family inside `Complete.lean`/`Encoding.lean` (every block-range lemma in
`Complete.lean` is stated against `nVarsAll`, so a new block ripples through thousands of lines).
The repaired semantics makes a cheaper route available: `Reference.stepOf` is a total deterministic
function on a finite state, so **enumerate the executions**.

Design (prototyped, not yet merged - the file was removed rather than committed half-proved):

```lean
namespace ProtSat.Reference.Explore        -- inside Reference so Cfg/Ev resolve unambiguously

def inBounds (P : Protocol) (B : Bounds) (C : Cfg) : Prop      -- kn, oblig, stores in univ; alloc in domain
def inBoundsBool (P : Protocol) (B : Bounds) (C : Cfg) : Bool  -- decidable twin, with inBoundsBool_iff
def candidates (P : Protocol) (B : Bounds) (C : Cfg) : List Ev -- idle, ded per U, recv per (q,U),
                                                               -- generate per (q,D), act per q
def stepB (P B C e) := (stepOf P C e).filter (inBoundsBool P B) -- the *bounded* step
def nodes (P : Protocol) (B : Bounds) : Nat -> Cfg -> List (List Ev x List Cfg)  -- (trace, visited)
def explorerAttack (P : Protocol) (B : Bounds) : Bool

theorem candidates_complete : Rel P C e C' -> inBounds P B C -> inBounds P B C' -> e in candidates P B C
theorem bounded_of_mem_nodes : (tr, Cs) in nodes P B n C -> inBounds P B C ->
                                Runs P C tr Cs /\ tr.length = n /\ boundedCfgs P B Cs
theorem mem_nodes_of_bounded : the converse
theorem explorer_correct : explorerAttack P B = true <-> BoundedAttack P B
theorem boundedSafe_of_explorer : explorerAttack P B = false -> BoundedSafe P B
```

Why this is the right next theorem: the bound it enforces is on **stored and known messages**, not on
the intermediate values a protocol expression computes. That is exactly the difference exposed by
`Regressions.Bounds` - the transient `pair x x` leaves the universe while every configuration stays
inside it - so the explorer is complete where the CNF is only an under-approximation.

**Correction after a second prototype pass.** Do not enumerate "nodes reachable in exactly k steps"
and induct on `k` with the start node fixed: the flatMap decomposition gives
`y ∈ extend x₀, x ∈ reachable k y`, so the induction hypothesis must be generalised over the
*start* node, which the "exactly k" formulation cannot express. Use an accumulator instead:

```lean
def explore : (P : Protocol) -> (B : Bounds) -> Nat -> List Node -> List Node
  | _, _, 0, acc => acc
  | P, B, k + 1, acc => explore P B k (acc ++ acc.flatMap (extend P B))

def isPrefix (P B) (x : Node) : Prop :=
  Runs P (initCfg P) x.tr x.Cs /\ boundedCfgs P B x.Cs

-- both directions are then one clean induction on the depth, generalising acc:
theorem prefix_of_mem_explore : (forall y in acc, isPrefix P B y) ->
    x in explore P B k acc -> isPrefix P B x
theorem mem_explore_of_bounded : x0 in explore P B j [initNode P] ->
    (rest is a bounded one-step-at-a-time extension of x0) ->
      node x0 rest in explore P B (j + rest.length) [initNode P]
```

**Third-pass status of the explorer.** `ProtSat/Explore.lean` reached: `inBounds` +
`inBoundsBool_iff`, `candidates` with the five membership lemmas and `candidates_complete`, `stepB` with
`step_of_stepB`/`inBounds_of_stepB`/`stepB_of`, `Node`/`initNode`/`extend`/`frontier`,
`isPrefix` with `isPrefix_initNode`, `isPrefix_of_extend` (needs `run_snoc`, proved by induction with
`List.getLastD` helpers) and `isPrefix_of_mem_frontier`. What remains is `frontier_complete` (the
completeness direction) and `explorer_correct`. The blocker is notation, not mathematics: a statement
of the form `a || b = true` where `a` and `b` are `Bool` parses the `=` inside the `||`; state such
disjunctions as `a = true ∨ b = true` and use `Bool.or_eq_true_iff`.

Also settled by the prototype: `inBounds` as a conjunction-of-Props with an `inBoundsBool` twin and
`inBoundsBool_iff` proved by `simp only [...]; tauto`; `stepB := (stepOf ...).filter inBoundsBool`
with `Option.filter_eq_some_iff` giving the two projections for free; `candidates` membership proved
by `simp [candidates, sessionEvents, hq, h]`; `extend` returning a singleton list rather than
`filterMap`, so `List.mem_flatMap` plus `List.mem_singleton` decomposes it.

Practical notes from the prototype, to save the next pass the iterations:

* Put the module inside `namespace ProtSat.Reference.Explore`. `ProtSat.Cfg` and `ProtSat.Ev`
  (the old semantics) shadow `Reference.Cfg`/`Reference.Ev` for any file in `namespace ProtSat`.
* `Action`'s constructor order is `fresh, send, recv, assign, check, secret, claim, commit`; a
  `cases act with` block must follow *that* order, not the order of the match arms in `actStep`.
* `matches` is a reserved word; the auth-matching predicate is `claimMatches`.
* Reasoning about `stepOf` works with `simp [stepOf, hact, hm] at h` followed by `subst h`;
  `rw [if_pos ...]` inside an unreduced `match` fails.
* `Bool.or_eq_true` is an equation, so use `Bool.or_eq_true_iff.mp/.mpr`; `decide_eq_true` goes
  Prop -> `decide p = true`, `of_decide_eq_true` the other way.
* `Option.filter_eq_some_iff` makes the bounded-step lemmas two-liners.
* `nodes` needs `termination_by` stated over the right argument, and the `match stepB ... with`
  inside it is what the equation compiler struggled with; using `extend` as a separate
  `def` (or `decreasing_by`) resolves it.

## Stage 3 - expression domains (`ProtSat/ExprDomain.lean`)

The universe bound and the expression bound were the same condition in the encoding, which is what made
`Complete.RunOK.exprB` an execution-wide hypothesis and `Regressions.Bounds` a genuine soundness gap.
Separated now:

* `evalDomain U e` builds a finite domain compositionally: variables range over `none` plus `U`,
  constants over their denotation, unary/binary nodes take the image of their children's domains under
  `Expr.stepEval1`/`Expr.stepEval2`, and `none` (failure) is always a member - so nothing is clipped
  to `U` on the way.
* `eval_mem_evalDomain` proves the reference evaluator cannot leave the domain, for any store whose
  values lie in `U`, with **no closure assumption** on `U`.
* `storesInU` is the criterion for an action that stores or publishes.
* The counterexample, handled: `U0_eq` identifies the regression model's universe by `decide`, and
  `transient_pair_intermediate_outside`, `transient_pair_result_in_domain`,
  `transient_pair_stores_in_U`, `transient_intermediate_not_inside` and `transient_bounds_agree` hold
  simultaneously - the intermediate leaves `U` while the action stays admissible and the test still
  succeeds.

## Bounded certificates (`ProtSat/BoundedCert.lean`)

Stage 1 recorded that `checkCertificate` verifies neither the step bound nor the universe bound, so an
accepted certificate gave `Attack` plus a length inequality rather than `BoundedAttack`. Fixed:

* `checkBounded P B c` = `checkCertificate P c` and `c.steps.length ≤ B.steps` and every visited
  configuration inside `univ P B`.
* `checkBounded_sound : checkBounded P B c = true -> BoundedAttack P B` - the complete public bounded
  predicate, with no hypothesis beyond the certificate and the bounds.
* Both regression certificates pass it (`auth_bounded`, `bounds_bounded`), so the checker is not
  vacuous.
* `out_of_universe_accepted_by_old_checker` and `out_of_universe_rejected`: a legal leaking run whose
  attacker knowledge contains `pair (agent 0) (agent 0)` - outside the universe - is accepted by the
  old checker and rejected by the bounded one. `too_long_rejected` is the step bound biting on the
  same certificate.

## The explorer is in: a complete bounded decision procedure (`ProtSat/Explore.lean`)

This is the piece that finally makes a SAFE verdict mean something. Over the repaired semantics:

```lean
Explore.explorer_correct        : explorerAttack P B = true <-> BoundedAttack P B
Explore.boundedSafe_of_explorer : explorerAttack P B = false -> BoundedSafe P B
```

`explorerAttack` enumerates executions: `candidates` offers every event the semantics can use at a
bounded configuration, `stepB` filters to successors that stay inside `univ P B` and the nonce domain,
and `frontier P B k x` lists the nodes reachable in exactly `k` such steps. `isPrefix_of_mem_frontier`
says every enumerated node is a bounded run; `frontier_complete` says every bounded run is enumerated
at its own length. Neither direction mentions an encoding, a representability condition, or a solver -
the gap that `Regressions.Bounds` exposed in the CNF does not exist here, because the bound is on
configurations and not on expression intermediates.

Kernel-checked gates (`decide`, whole file builds in seconds):

| Gate | Meaning |
|---|---|
| `secure_honest_run`, `secure_obligation_and_publication` | non-vacuity: the run reaches the generation, the declaration and the publication, and the obligation is taken while the secret stays out of reach |
| `secure_explorer_finds_nothing`, `secure_bounded_safe` | a genuine `BoundedSafe` verdict, proved by exhaustion |
| `transient_pair_attack_found`, `transient_pair_bounded_attack` | the leak the CNF loses is found here |
| `auth_explorer_finds_the_break`, `auth_bounded_attack` | authentication is decidable by this procedure; it is not expressible in the CNF at all |
| `zero_step_is_safe` | the empty-execution edge case behaves |

**Honest scope notes.**

* The verdict is over the *repaired* semantics (`ProtSat.Reference`), not the old
  `ProtSat.Operational` that `ProtSat.Query`'s `boundedAttackGoals` is stated against. Wiring the
  explorer into the `Query` contract - so that `analyzeQuery` can return `Result.boundedSafe` with a
  `SafeEvidence` - means moving the contract's goal-indexed predicates onto the repaired semantics,
  which is the next decision to make deliberately rather than in passing.
* `auth_explorer_finds_the_break` is worth reading carefully: the attacker lets the committing session
  run and the claiming session idle, which really is an unmatched commit under a trace semantics where
  sessions are only as live as the network lets them be. The roadmap's note that "a universal
  honest-progress theorem is not an appropriate requirement" cuts both ways - a protocol whose
  agreement property depends on the peer's claim having been *scheduled* needs an explicit liveness or
  progress assumption in the query, not in the checker.
* Cost is exponential in `B.steps`. The gate models enumerate 130-258 nodes; this is a reference
  procedure, not a scalable one, and roadmap stage 8 is where proved refinements belong.

## The contract, decided: goal-indexed safety with evidence (`ProtSat/Contract.lean`)

This is the piece that closes the objective's gap for the enumeration route. `ProtSat.Query` states
the contract over the *old* semantics because that is what the CNF is proved against, so its
`analyzeQuery` can never issue `Result.boundedSafe`
(`ProtSat.analyzeQuery_ne_boundedSafe`). `ProtSat.Reference.Contract` states the same contract
shape over the *repaired* semantics and then actually discharges it: 53 theorems, whole module
compiles in about five seconds including its `decide` calls over the enumeration, and
`lake exe protosatDemo` now prints a real `BOUNDED SAFE` line and re-checks each attack witness
without re-running the search.

Naming note: the module lives in the namespace `ProtSat.Reference.Contract`, not `ProtSat.Contract`.
The old semantics is declared directly in `ProtSat`, so inside `namespace ProtSat.Contract` the names
`Cfg` and `Ev` resolve to the *old* configuration and event types while the `ProtSat.Reference`
functions want the new ones. Nesting the contract under `ProtSat.Reference` makes the unqualified
names mean the repaired ones. That is a trap worth knowing about, so it is documented in the module
header.

| Declaration | Meaning |
|---|---|
| `goalViolation P g`, `goalViolationBool P g`, `goalViolationBool_iff` | which executions violate goal `g`, over the repaired semantics: `traceLeaks` for secrecy, the ordered role-aware `authBreak` for agreement, each with its proved monitor |
| `boundedAttackFor q g`, `boundedAttack q`, `boundedSafe q` | the query-indexed statement: some *selected* goal is violated by some execution the query permits; `boundedSafe q` is "no permitted execution violates any selected goal" - the meaning SAFE was always supposed to have |
| `nodeViolatesQuery q`, `attackFound q`, `findAttack q` | the executable question restricted to the goals the query selected, and its witness |
| `boundedAttack_of_attackFound`, `attackFound_of_boundedAttack`, `attackFound_decides` | **soundness and completeness of the enumeration for the query's own goals**, both directions, with no encoding, representability or solver hypothesis |
| `analyze_attack_certificate`, `checkWitness q x`, `checkWitness_sound`, `answer_checkWitness` | the `attack` verdict is a certificate: the named node is a bounded run violating a selected goal, and a `Bool` re-check confirms it without re-running the search |
| `SafeEvidence`, `Verdict`, `answer`, `analyze` | the verdict type (`invalidModel`, `noGoals`, `attack`, `boundedSafe`) and the analyser whose `boundedSafe` case is *produced by a proof* rather than withheld |
| `analyze_attack_sound`, `analyze_boundedSafe_sound`, `analyze_correct`, `analyze_exclusive` | an `attack` verdict means `boundedAttack q`; a `boundedSafe` verdict means `boundedSafe q`; for a well-formed query with a selected goal the answer is the right one, and exactly one of the two security answers is produced |
| `analyze_ne_security_of_invalid`, `analyze_ne_security_of_noGoals`, `analyze_ne_attack_of_boundedSafe` | the stage-1 acceptance gate restated for this analyser: a malformed model and an empty goal set cannot produce a security verdict |
| `Gates.secureQ_verdict`, `authQ_verdict`, `transientQ_verdict`, `emptyQ_verdict`, `badQ_verdict` | all four verdicts instantiated on models that already carry permanent witnesses elsewhere: bounded safety on the explorer's secure model, the authentication attack the CNF refuses to ask about, the transient-pair leak the CNF's `WithinBounds` excludes, no goals, and a malformed model |
| `Gates.authQ_cnf_refused` | the same query on the CNF route returns `unsupportedGoals`, so the two answers can be compared directly |

**Injective agreement is now a selectable goal.** `Goal` gained `agreementInj`, and the deciding
contract gives it its own semantics and its own proved monitor
(`ProtSat.Reference.agreesInj` / `agreesInjBool` / `agreesInjBool_iff`, already present from
stage 2). The gate pair `replayAgreeQ_verdict` and `replayInjQ_verdict` is the point: one
protocol, one bound, one claim followed by two commits - non-injective agreement is `boundedSafe`
with evidence, injective agreement is `boundedAttack`, and `replayInjQ_witness_agrees` shows the
very same execution satisfies the weaker monitor. So the selected goal changes the answer rather than
renaming the same check, which is what roadmap stage 3 ("implement injective agreement separately; its
checker needs its own correctness proof") and stage 7 ("examples distinguishing non-injective and
injective agreement") ask for. `replayInjQ_cnf_refused` records that the CNF route still cannot ask
either agreement question. In the old contract `Violation P Goal.agreementInj := True`: that
semantics has no injective monitor, so every run counts as violating the goal and no safety can be
claimed for a property that is not modelled there - the safe direction for an unimplemented goal.

**Authentication, non-vacuously.** `Gates.authOrderP` is one role whose two actions are
`claim` then `commit` on the same tag and data; `Gates.authSwappedP` is the same role with the two
actions swapped. `authOrder_honest_run`, `authOrder_commit_recorded` and `authOrder_agrees` prove
the commit is actually reached and accepted, so `authOrderQ_boundedSafe` is a safe authentication
verdict about a protocol that really claims things - not the safety of a dead role.
`authSwappedQ_boundedAttack` is the matching negative: with the order reversed the commit has no
earlier claim, which is `Regressions.Semantics.later_claim_excuses_commit` made reachable instead of
merely observed in the old semantics. `authSwappedQ_witness_is_auth` and
`authSwappedQ_witness_not_leak` pin the violation to the goal the query selected, so the two goals
stay separate in the verdict rather than collapsing into "something went wrong".

**Honest scope notes.**

* `Contract.boundedSafe` and `Query.boundedSafeGoals` are deliberately *different* propositions,
  over the repaired and the old semantics respectively, and each `SafeEvidence` carries its own.
  Nothing bridges them, and that is the point: the CNF route must not inherit a security label from a
  proof about a different model. `Query.boundedSafe_of_encodingUnsat` still needs the
  representability hypothesis that `Regressions.Bounds` shows is not implied.
* `Gates.secureQ_verdict` selects both goals on a model with no `claim`/`commit` actions, so its
  authentication half is vacuous *there*; the non-vacuous safe authentication verdict is
  `Gates.authOrderQ_verdict`. What remains open is the cross-session case: under a Dolev-Yao attacker
  that may block any session, agreement between two *different* principals is refuted by scheduling the
  commit and not the claim (`Gates.authQ_verdict`, one event). A safe cross-session example needs
  either an explicit progress assumption in the query or a causal binding from claim to commit, and the
  message universe as defined gives no such binding: every term of `univ P B` is injectable at any
  time, so passing a check on a universe value cannot witness that a particular honest action happened.
  Saying that plainly is better than hiding it behind a model that only looks strong.
* Cost is exponential in `B.steps`, same as the explorer's.

## Monotonicity: what one verdict says about other bounds (`ProtSat/Bounded.lean`, `Explore`, `Contract`)

Stage 9's first item: a bound ordering and the two transfer directions, stated over the public bounded
predicate rather than over clauses.

| Declaration | Meaning |
|---|---|
| `Bounds.le`, `le_refl`, `le_trans` | the semantic ordering on bounds: event count and closure rounds both grow. Deliberately a relation on the *semantics*, not on the generated formulas - changing bounds changes the encoding's variable indices |
| `mem_iterate_step`, `mem_iterate_le`, `univ_mono` | the message universe is monotone in `Bounds.rounds`: more closure rounds add messages and never remove one |
| `BoundedRun.mono`, `BoundedAttack.mono`, `BoundedSafe.mono` | permitted executions and attacks are upward closed; **safety transfers downward** |
| `boundedAttack_mono_bounds`, `boundedAttack_mono_goals` | neither enlargement can lose an attack |
| `boundedSafe_mono_bounds`, `boundedSafe_mono_goals`, `boundedSafe_mono` | the query-level transfer: safe at a larger bound, or for a larger goal set, implies safe below |
| `Gates.secureQ2_boundedSafe` | the secure model's verdict at three events *gives* the verdict at two, so the second search is never run |
| `Gates.secureQ2_attackFound_false` | and the transferred verdict agrees with actually running the smaller enumeration - the cross-check that the ordering is over the right predicate |
| `Gates.transientQ4_boundedAttack` | the transient-pair attack carried upward to a larger bound |
| `Gates.replayBothQ_boundedAttack`, `replayBothQ_attackFound_true` | enlarging the *goal set* changes the answer: the pair is attacked while the weaker selection alone is safe at the same bound |

What this does **not** yet give is the compression theorem (every attack has a witness of at most
`H + |U|` events), which is the part that turns a finite search into safety for all lengths inside one
universe. Monotonicity is its prerequisite, not a substitute: it moves a verdict between stated bounds;
it does not discharge a bound that was never stated.

## A resource-bounded driver: `unknown` becomes a real answer

Stage 1's table lists `unknown reason`, and until now nothing in the project could produce it:
`Query.analyzeQuery_ne_unknown` proves the *total* reference analyser never does, which is correct
but leaves the category empty. `Contract.searchFuel` scans at most `fuel` nodes and
`Contract.driverAnswer` reports three things - `outOfFuel`, `attack x`, `safe` - with the
budget made explicit:

| Declaration | Meaning |
|---|---|
| `searchFuel_eq_find?` | with `xs.length + 1` fuel the bounded scan agrees exactly with the unbounded search |
| `driverAnswer_attack_sound`, `driverAnswer_safe_sound` | either answer, when the driver gives one, is true of the query |
| `driverAnswer_complete` | an attack *is* found at the sufficient-fuel budget: exhaustion is a resource fact, not a semantic one |
| `driverAnswer_not_outOfFuel`, `driverAnswer_outOfFuel_zero` | the budget that always suffices, and a budget that honestly says it is too small |
| `driver_safe_evidence` | a driver `safe` answer carries the same kind of `SafeEvidence` as the total analyser |
| `Gates.authQ_driver_outOfFuel`, `authQ_driver_attack`, `secureQ_driver_safe` | all three instantiated |

The distinction the roadmap asked for - "keep mathematical reference solving total; distinguish this
from a production driver that may time out" - is now in the API with theorems on both sides: the total
`analyze` never says `unknown`, and the bounded driver says nothing at all when it runs out.

## Stage 4, first installment: representability is a value-domain question (`ProtSat/Represent.lean`)

The narrowing that `Regressions.Bounds` exhibits lives in one field of `Complete.RunOK`:

```
exprB : ∀ i q e, e ∈ allExprs P → admissible sh (Expr.eval e (storeOf (cfg i) q)) = true
```

`exprB` is consumed at exactly six sites in three lemmas (Complete.lean:2540, 2551, 3200, 3307,
3359): `rdXe_unary` and `rdXe_binary` - the two Tseitin gate equations - and three places that only
need the *published* value to be a universe message. Everything else in `RunOK` is either the public
bound itself or a theorem about the protocol. So closing stage 4 means giving those two gate
equations a domain in which the intermediate has a name.

**The first thing proved is that the bound cannot do it.** `no_bound_discharges_exprB`: for *every*
closure bound `r` there is a store whose only value lies in `univ boundsP ⟨3, r⟩` and in which the
table entry `pair (var 0) (var 0)` denotes a message that `univ boundsP ⟨3, r⟩` does not contain.
The proof is a depth count (`td`, `level`, `td_closeOne`: one closure round adds at most one to the
depth of anything, and `hash`-nesting a depth-one seed reaches that maximum at every round). So
`exprB` asks the universe to be closed under pairing, which no finite universe is; raising
`Bounds.rounds` can never discharge it. That settles the question the previous round left open about
whether stage 4 was a bound problem - it is not, it is a naming problem.

**The second thing proved is that a value domain can.** `exprVals U P` is the persistent universe
`U`, kept as a *prefix* so nothing already named keeps its index (`ixOf_exprVals`), followed by every
message any table expression denotes in a universe-valued store - assembled from the per-expression
`ExprDomain.evalDomain` that stage 3 built. The theorems:

| Declaration | Meaning |
|---|---|
| `eval_inside_exprVals` | every table expression, in *any* universe-valued store, denotes a nameable value - no run hypothesis, no closure assumption, no bound arithmetic |
| `stepEval1_inside_exprVals`, `stepEval2_inside_exprVals` | the admissibility content of the two gate equations, as theorems about the domain |
| `exprB_of_exprVals`, `exprB_of_exprVals_at` | `exprB` holds at `shapeX P B` for every run at once, given only that stores stay in the persistent universe |
| `transient_nameable` | the message `Regressions.gate_clipped` shows unnameable is nameable *at the same bounds that fail* `exprB` |
| `transient_gate_not_clipped`, `transient_valAt_uIdx` | and it gets an index of its own, which `valAt` reads back - the property `admissible_valAt_uIdx` grants only under `admissible` |
| `ixOf_exprVals`, `length_univ_le` | the extension is index-preserving on `U`, so store, knowledge and delivery groups keep their numbering |
| `no_bound_discharges_exprB` | the negative result above |
| `exprB_holds_at_X_for_deep_store` | one line: the store that breaks admissibility over `U` is admissible over `exprVals`, at the same bound |
| `exprBOn`, `exprB_of_exprBOn` | the condition as a **finite computation** over the stores a run uses, equivalent to the `RunOK` field when the list covers them |
| `transient_exprB_fails`, `transient_exprB_holds_at_rounds1` | and decided on the witness: the transient-pair run fails it at `Regressions.Bounds`' bound and **passes it one closure round later**, so that run is representable by the CNF at `rounds := 1` |

The last two lines are the half of stage 4's gate that the negative result cannot give: representability
is not only a question the tool can answer about a concrete execution, it is *true* of the execution
`Regressions.Bounds` exhibited, once the declared closure bound is one round larger. What
`no_bound_discharges_exprB` rules out is the uniform reading - "for every universe-valued store" -
which is the difference between a bound the user can raise and a domain the compiler must name.

**Not done.** `exprVals` is not yet wired into `Shape`. The CNF still has one value stride
(`shVal sh = sh.U.length + 1`) shared by every family, so the encoding is unchanged and
`encoding_complete` still assumes `exprB`. The wiring is the next increment: a second value list
used by the `xe` family only (`vxe`, `axe`, `szXe`, `szAxe`, `xeOh`, `f1`, `f2`, `evalGate`, then the
`rdXe` and `decXe` lemmas), with the five hardcoded `sh.U.length` sites in `Clauses.lean` (281, 429,
437, 455, 461) split into universe indices and extended indices. Estimated blast radius ~65-70
declarations, of which ~40 are mechanical stride renames; the soundness direction (8A) needs
nothing, because `Encoding.xe_unary`/`xe_binary` already conclude with a `.filter` on universe
membership and tolerate clipped intermediates.

**Also recorded, from investigating roadmap stage 6.** The pinned Mathlib (v4.34.1) has *no*
Prop-level LRAT checker: `Mathlib/Tactic/Sat/` is one file, `FromLRAT.lean`, whose API is
elaboration-time - `lrat_proof` / `from_lrat` build an `Expr` and hand it to the kernel, and the
only object-level handles are `Sat.Fmla.proof [] : Prop` (FromLRAT.lean:126) and `Fmla.refute`
(:188). There is no `Rat.CNF`, no `Lrats`, no `checkLrats` in this pin. Measured here: fine at 2000
variables (2.3 s), and at 20000 variables the kernel fails with "deep recursion detected" and the
declaration **silently degrades to an axiom** unless `#print axioms` is re-run - so stage 6 must
consume `ctx.proof []` through a bridge lemma rather than the reified form with 2n+1 binders, and
must re-audit axioms on whatever it produces. ProtSat `Lit`/`Clause`/`CNF` map onto
`Sat.Literal`/`Clause`/`Fmla` index-preservingly (`BVar` is already 0-based), with DIMACS text
needing `±(v+1)`.

## Stage 4, second installment: what the public bound already implies (`ProtSat/BoundedExec.lean`)

`encoding_complete` assumes `WithinBounds` - twelve unnamed conditions - and the bridge in
`Query` assumes them for every bounded execution at once. Roadmap stage 4 asks that the compiler
conditions *follow* from the public bound. They mostly do, and this module says exactly how far.

| `RunOK` field | status |
|---|---|
| `knU`, `storeU` | the public bound *is* these two (`knU_of_bounded`, `storeU_of_bounded`) |
| `sessLen`, `pcB`, `varB` | preserved along the run: `cfgOK_init`, `cfgOK_step`, `cfgOK_at` |
| `varsB`, `eIdxB`, `writtenB`, `pcActB` | theorems about the protocol, never about the run |
| `dedU` | derived: a deduction event adds its conclusion to the *next* configuration, which the bound puts inside the universe (`dedU_of_bounded`) |
| `actB` | **two thirds of it derived**: `lt_nS1_of_act` proves the acting session is an instantiated one (`roleAt` reads `P.sessions`, so `actionAt q c ≠ none → q < sessions.length`). The `m` and `d` fields are **not derivable** |
| `exprB` | **not derivable from any bound** (`Represent.no_bound_discharges_exprB`) |

`withinBounds_of_residual` therefore replaces the twelve with `BoundedExec.Residual`: the delivered
message of an action event, the nonce choice of an action event, and expression representability.
`Query.boundedSafe_of_encodingUnsat_of_residual` is the bridge with that hypothesis - a strict
weakening of the one it sits beside.

**The residual is proved to be real, in both directions.** `dummyCert` is the
`Regressions.Bounds` execution with the two events whose actions ignore the delivered message
carrying `pair (agent 0) (agent 0)`, which is outside the universe: `dummy_bounded` says it is a
bounded execution, `dummy_not_actM` says `actB` fails for it, and `residual_not_derivable` puts the
two together - no hypothesis about bounds can discharge it. `canonicalCert` is the same run with the
labeling the run actually uses, and `canonical_actM_actD` shows both dummy-field conditions hold for
it. So the residue is not "some runs are unrepresentable" but "the old event type carries fields
that mean nothing", which is precisely what roadmap stage 2 removed in `ProtSat/Reference.lean` -
where a deterministic action event carries no fields at all.

**What the two residual fields actually are.** Three more lemmas sharpen the diagnosis.
`kn_of_rel_act_recv` and `domain_of_rel_act_fresh` show that the *only* rules that read the delivered
message and the nonce choice are `rRecv` and `rFresh` - and for those two the public bound already
bounds them (`actM_of_recv`: a received message is known, hence in the universe; `actD_of_fresh`: a
generated nonce is in the declared domain). So `Residual.actM`/`actD` demand bounds on the two
fields **no rule reads**, which is the dummy-field defect and nothing else. And
`actB_vacuous_with_empty_nonce_domain` shows the unconditional form is not merely unprovable but
false for a whole protocol class: with `nonceDomain = []`, `actB` requires `d ∈ []` of every action
event - sends, checks, claims included - so no run in which a session acts satisfies it, and the CNF
completeness theorem is vacuous for such a protocol. That is roadmap stage 2's gate ("a send/check
must work with an empty fresh-nonce domain") read from the other side, and the repaired semantics
meets it because its events carry no such field.

Two facts worth keeping from the plumbing: `Runs` inductions in this codebase must be stated over the
*position* (`cfgOK_at`), not over membership in the visited list - `induction` on `Runs P (initCfg P)
tr Cs` reverts any hypothesis mentioning the configuration index and the substitution then fails;
and `List.mem_append` on `closeOne`'s five-component list is left-nested, so a five-way `rcases`
needs the pattern `(((hU | hpair) | pencS) | pencA) | hhash`.

## Stage 4, third installment: the second value domain exists, and the gap is reported (`Shape.V`, `domainGap`)

The first installment proved that no bound discharges `exprB` and that a value domain can; the
second reduced `WithinBounds` to three named conditions. This one builds the place the domain goes.

* `Shape` gains `V : List Term` - the **nameable** domain, distinct from `U`, the **persistent** one.
  `shapeOf` sets `V := univ P B`, so the generated CNF is unchanged; a grep confirms nothing outside
  `Encode.lean` and `Represent.lean` reads `V`, `shValX`, `uIdxX` or `valAtX`, which is the
  machine-checked version of "this installment broke nothing".
* `ShapePrefix sh := ∃ W, sh.V = sh.U ++ W` is the invariant that makes the two domains
  compatible: `ixOf_append_left`, `ixOf_V_eq_ixOf_U` and `uIdxX_eq_uIdx_of_mem` say a universe
  message keeps its number, so the cross-family clauses that compare an expression index with a
  store, knowledge or delivery index keep working when `V` grows. That transport lemma is the reason
  the flip is a stride change rather than a re-encoding.
* `valAtX_uIdxX_of_nameable` is the read-back property with **no admissibility hypothesis** - the
  lemma that replaces `admissible_valAt_uIdx` at the six `exprB` sites. `Represent` now states it
  where it matters: `eval_valAtX_uIdxX`, `stepEval1_valAtX_uIdxX`, `stepEval2_valAtX_uIdxX` (the
  `rdXe_unary`/`rdXe_binary` content), `exprBOnX_shapeX` (decidable over a store list), and
  `transient_valAtX_uIdxX` naming the intermediate the old gate clipped.
* `shapeX` is redefined the right way round: `U` stays the universe `BoundedTrace` bounds and `V`
  becomes `exprVals`. The two roles the roadmap said were conflated are now two fields.
* `Represent.domainGap P B` computes whether the protocol can build a value the universe cannot
  name. `domainGap_of_unnameable` proves a concrete unnameable value forces the flag; the demo
  prints it for three queries - `challenge-response` and the transient-pair witness report GAP, a
  protocol that only forwards what it receives reports complete, and does so with an empty nonce
  domain. Three new CI gates assert all three lines appear, and the theorem floor moved to 2740.

That is the last piece of stage 4 that does not require touching the clause generator: the narrowing
hypothesis is now reported by the tool instead of being silently assumed, and the shape has
somewhere to put the domain that discharges it. What remains is the flip itself - pointing the `xe
family at `shValX`/`uIdxX` and `shapeOf` at `exprVals` - after which `exprB` leaves `Residual` too.

## Stage 4, fourth installment: `actB` becomes conditional, and SAFE means security (`EndToEnd.lean`)

Three of the twelve `WithinBounds` conditions were still assumed about the execution after the
second installment: `actB`'s delivered message and nonce choice, and `exprB`. Two of them were
artefacts of asking for a bound on fields that six of the eight action rules never read. So
`RunOK.actB` now bounds them *where the action reads them*:

```lean
actB : ∀ i q m d, ev i = Ev.act q m d → q < sh.nS1 ∧
  (readsDelivery P q (pcOf (cfg i) q) -> m ∈ sh.U) ∧
  (readsNonce  P q (pcOf (cfg i) q) -> d ∈ sh.D)
```

and `BoundedExec.actB_of_bounded` proves that from the public bound: a receive delivers a message
the attacker knows (hence a universe message, by the bound), and a generation picks a nonce from
the declared domain (the operational rule already demands it). The six other action rules are no
longer asked to name a value they ignore. The refactor touched `Complete.lean` in eight places;
the freshness range lemma `rdFr_lt` turned out not to need the membership at all (`ixOf_le` bounds
the index regardless), which is worth knowing because it means the encoding never depended on that
assumption. `Residual` is now a single condition, `exprB`, and `Represent.exprB_of_domainGap_false
`discharges it from the decidable `Represent.domainGap`. So
`BoundedExec.withinBounds_of_bounded` says: **for a gap-free query, every bounded execution
satisfies `WithinBounds`** - the compiler representability conditions are theorems, not hypotheses.

`ProtSat/EndToEnd.lean` turns that into the verdict. For `Examples.KeyDisclosure` - a session that
publishes whatever it receives, secret withheld - the query is well-formed, `univClosed`,
`univSub`, `SecretsOK` and gap-free, all by `decide`, and

```lean
theorem boundedSafe_of_gapFree (hvs : analyzeQuery qsafe = Result.encodingUnsat) :
    boundedSafeGoals qsafe
theorem noLeak (hvs : ...) : ¬ ∃ tr Cs, BoundedTrace PSafe B tr Cs ∧ runsLeaks PSafe Cs
```

is the statement the review asked for, with no `WithinBounds` anywhere in the hypothesis list.
Non-vacuity is on the record too: `disclosure_certificate` re-states the already kernel-checked
`Examples.KeyDisclosure.checked`, i.e. the same role and bounds *with* the disclosure admit a
leak, so the safety is a fact about the compromise assumption and not about a dead role.

**The honest remainder, measured.** The one thing not discharged by `decide` is the solver answer
itself. Re-deriving `dpll (encode P B) = none` in the kernel costs: 1263 variables exceeds the
default recursion budget; 828 variables exceeds 200k heartbeats in 14 s and had not finished in
2 min at raised budgets; 494 variables had not finished in 5 min; the 648-variable instance with
`steps := 1` (Regressions.Authentication) does decide in the normal build. So `hvs` is a
hypothesis - the analyser computes the answer at runtime - and closing that last gap is precisely
roadmap stage 6: a checked UNSAT certificate replaces minutes of kernel solver-replay with a
linear proof check. The table is in the module header so the cost is published, not hidden.

## Stage 6, first installment: UNSAT evidence that is checked, not re-run (`ProtSat/Resolution.lean`)

`EndToEnd.lean` left one hypothesis: the analyser answer itself. Believing it in the kernel means
re-running DPLL in the kernel, which the measurements in that file price at minutes for a few
hundred variables and out of reach for a thousand. Roadmap stage 6 asks for the other shape -
*evidence* from the search, checked independently - and this module is the checker.

A refutation is a list of clauses, each justified as a clause of the formula (`Just.orig n`) or as
the resolution of two earlier lines on one variable (`Just.res i j v`), ending with the empty
clause. `checkProof` walks it once: no search, no solver, no trust in whoever produced it.

| declaration | meaning |
|---|---|
| `checkProof_sound` | `checkProof f p = true -> ProtSat.Unsat f` - the whole point |
| `accepts_demo` | a real refutation of (x or y) and (x or not y) and (not x or z) and (not x or not z), kernel-checked by `decide` |
| `demoF_unsat` | and the formula really has no model, by the theorem rather than by search |
| `rejects_truncated` | a proof one line short is rejected |
| `rejects_corrupted` | a line claiming a resolvent that resolution does not produce is rejected |
| `rejects_wrong_formula` | valid evidence for a different formula is rejected: the `orig` lines no longer read back |
| `rejects_empty`, `rejects_out_of_range` | an empty proof, and a line citing a missing parent or a clause index off the end |
| `encodingUnsat_of_proof` | the bridge: a checked refutation of `encode P B` gives `analyze P B = encodingUnsat` through `dpll_none_iff_unsat`, with the solver never run |
| `toDimacs`, `dimacs_demo` | the exact formula as DIMACS text, so an external prover can be handed *this* problem and its output handed back to the checker |

Chain that completes: checked refutation -> `Unsat (encode P B)` -> `dpll = none` ->
`analyze = encodingUnsat` -> `analyzeQuery = encodingUnsat` -> (gap-free query) ->
`boundedSafeGoals`. Every arrow is a proved theorem in this repository; the only missing link is a
prover that emits the refutation for a large instance. The reference DPLL does not emit proofs, and
the only SAT tool installed here is `z3`, which does not emit LRAT, so Mathlib`s elaboration-time
replay cannot be exercised on a real ProtSat instance yet. That is stated plainly rather than papered
over: the checking side of stage 6 is done, the producing side needs a proof-emitting solver wired
to `toDimacs`.

## The closed verdict: SAFE means security, with no hypotheses (`EndToEnd.qg_safe`)

The objective is one sentence: *no execution permitted by the stated model, assumptions and
bounds violates any selected security goal.* For the CNF route that sentence used to arrive with a
bundle of assumptions about the executions themselves. It no longer does:

```lean
theorem qg_safe : boundedSafeGoals qg
theorem qg_noLeak :
    - exists tr Cs, BoundedTrace Guard GB tr Cs /\ runsLeaks Guard Cs
```

Both are proved with **no hypotheses at all**, and both depend only on `propext, Classical.choice,
Quot.sound` - no `sorryAx`, no user axiom, verified by `#print axioms` and by the audit that walks
every theorem in `ProtSat.*`. The chain that closes it:

* the query is well-formed (`decide`),
* the value domain has no gap (`Represent.domainGap = false`, `decide`), so every bounded
  execution satisfies `WithinBounds` (`BoundedExec.withinBounds_of_bounded`),
* the generated CNF has no model - at 246 variables and 291 clauses the kernel can check that
  itself (`DPLL.dpll (encode Guard GB) = none` by `decide`, about 20 s),
* hence `analyzeQuery qg = encodingUnsat`, hence by
  `Query.boundedSafe_of_encodingUnsat_of_gapFree` the security statement.

The example is deliberately small and deliberately *not* vacuous in shape: `Leak` is the same
protocol with one expression changed - publishing the key instead of a public name - and the
pipeline reports an attack for it, so the verdict is a discrimination, not a constant. For
`Examples.KeyDisclosure` (1263 variables) the same chain runs with the solver answer as its only
hypothesis, because kernel replay of the solver does not scale; that is the gap
`ProtSat/Resolution.lean` is built to close by checking evidence instead of re-running search.

## The correspondence, instantiated (`ProtSat/Differential.lean`)

Stage 5 asks for `encoding_correct`: `Satisfiable (encode q) <-> BoundedAttack q`. The full
statement, for every protocol and every goal, is out of reach here (agreement violations are still
absent from the formula, and the gapped class still needs the stride flip). What is now proved is
the same equivalence *instantiated on two real protocols*, in both directions:

```lean
theorem guard_correct : Satisfiable (encode Guard GB) <-> boundedAttackGoals qg
theorem leak_correct  : Satisfiable (encode Leak GB)  <-> boundedAttackGoals ql
```

* `guard_correct` is the case where neither side holds: the CNF has no model (the kernel-checked
  `dpll = none` from `EndToEnd`), and the enumeration over the repaired semantics independently
  finds no violation (`Contract.attackFound qg = false`, `decide`). Two unrelated procedures, same
  answer - the differential oracle the roadmap asks for.
* `leak_correct` is the substantive direction. A one-step run that publishes the declared key is
  built by hand (`L_runs`, from `Rel.rSend`), shown to stay in the universe (`L_univ`), turned into
  `boundedAttackGoals` - and then `Complete.encoding_complete` produces a satisfying assignment
  **with no `WithinBounds` hypothesis**, because `withinBounds_of_bounded` derived it from the
  public bound plus `domainGap = false`. That is completeness actually applied, not just stated.

Both depend only on `propext, Classical.choice, Quot.sound`. The leaky and guarded protocols differ
in one expression, so the pair also shows the pipeline discriminates rather than answering
constantly.

## The correspondence, stated generally (`ProtSat/Correspondence.lean`)

`Differential.lean` verified the correspondence on two protocols. The same argument works for *any*
gap-free query, and stating it once makes the shape of the result visible:

```lean
theorem encoding_complete_gapFree :
    domainGap P B = false -> boundedAttackGoals q -> Satisfiable (encode P B)

theorem boundedSafe_of_unsat_gapFree :
    domainGap P B = false -> Unsat (encode P B) -> boundedSafeGoals q

theorem boundedSafe_of_refutation :
    domainGap P B = false -> checkProof (encode P B) p = true -> boundedSafeGoals q
```

The second is the implication the objective asks for, stated at the level of the formula rather
than the analyser: *no satisfying assignment, therefore no permitted execution violating the
selected goal*. It is strictly stronger than
`Query.boundedSafe_of_encodingUnsat_of_gapFree`, which needs the verdict equation
`analyzeQuery q = encodingUnsat`; this one needs only `Unsat (encode P B)`, however it was
obtained. The third takes that from the evidence checker, so the route from a prover output to
the security statement never touches the solver: refutation -> `checkProof_sound` -> `Unsat` ->
`boundedSafeGoals`. `guard_safe_from_unsat` instantiates the second on the guarded protocol from
the kernel-checked `dpll = none`, giving the same verdict by the shorter route.

The two-sided meaning of a verdict, assembled:

* **no false negatives** (unsafe reported safe): `boundedSafe_of_unsat_gapFree` - a permitted
  attack would make the formula satisfiable;
* **no false positives** (safe reported unsafe): `BoundedCert.checkBounded_sound`, re-derived
  from the certificate alone, with no reference to the CNF or the solver;
* **the boundary is decidable**: `Represent.domainGap` says which queries the first bullet
  covers, and the transient-pair witness shows what happens outside it.

Still missing for the full `encoding_correct`: the direction
`Satisfiable (encode P B) -> boundedAttackGoals q`, which needs `encoding_sound` to return the
complete bounded predicate - specifically that the decoded run satisfies `runsInUniverse`. The
leak half of that conclusion is already proved; the universe half is not.

### Evidence bound to the formula it refutes

`Resolution.Evidence` pairs a refutation with the clause list it was produced against, and
`checkAgainst f e` compares that list with `f` before checking a single resolution step. The
comparison is structural, not a digest, so no collision-resistance assumption enters. Three
kernel-decided gates show the binding does work `checkProof` alone cannot:
`evidence_accepted` (right formula, full proof), `evidence_wrong_formula` (a valid refutation of
a different formula is rejected, although `checkProof demoF demoP` succeeds), and
`evidence_truncated` (stale, cut-off evidence is rejected). `checkAgainst_sound` proves that what
is accepted really refutes the target. Callers pass `encode P B`, which ties evidence to a query.

## Log

* 2026-10-19 (a) - baseline inspected; build green; three review witnesses promoted to permanent
  regressions in `ProtSat/Regressions.lean`; `ProtSat/Query.lean` added (contract, validator,
  gate theorems); `Analyzer.Verdict.safe` renamed to `encodingUnsat`; README headline, section 8,
  section 10 and the module map corrected; demo extended with the query contract.

* 2026-10-19 (b) - stage 2a/2b: `ProtSat/Reference.lean` with the allocation history,
  action-specific events, ordered role-aware authentication monitor, injective-agreement monitor,
  credential provisioning and persistent secret obligations; twelve kernel-checked gate theorems
  that each reverse a `Regressions` witness. Build green (1847 jobs), audit clean over 2313
  theorems.

* 2026-10-19 (c) - repo housekeeping: `tmp/`, `scratch/` and `output/pdf/` untracked (kept on disk).
  Explorer prototyped and deliberately withdrawn rather than merged with holes; design recorded above.

* 2026-10-19 (d) - stage 3: `ProtSat/ExprDomain.lean` (compositional expression domains,
  `eval_mem_evalDomain`, the transient pair handled) and `ProtSat/BoundedCert.lean`
  (`checkBounded` + `checkBounded_sound` giving `BoundedAttack`, with the old checker's gap exhibited
  by `out_of_universe_rejected`). Build green (1851 jobs), audit clean over 2368 theorems.
  Second explorer prototype: the frontier/prefix machinery is written and mostly proved
  (`inBounds`, `candidates_complete`, `stepB`, `Node`, `isPrefix`, `extend`, `frontier`,
  `run_snoc`); it was withdrawn again at the completeness direction rather than committed with holes.
  The remaining obstacle is stated precisely below.

* 2026-10-19 (e) - `ProtSat/Contract.lean`: the goal-indexed contract over the repaired
  semantics with `attackFound_decides` (sound and complete, no encoding hypothesis) and an analyser
  that issues `boundedSafe` with evidence; `analyze_attack_certificate` and `checkWitness` make an
  `attack` verdict re-checkable without the search; seven kernel-checked verdict gates including a
  non-vacuous safe authentication verdict (`authOrderQ_verdict`) and its swapped-order counterexample;
  demo extended with the enumeration contract. Build green (1855 jobs), audit clean over 2535 theorems.

* 2026-10-19 (f) - `Goal.agreementInj` added and wired into the deciding contract: `goalViolation`
  and `goalViolationBool` gain the injective case with its proved monitor,
  `boundedSafe_of_BoundedSafe` is restricted to the goals the explorer actually checks, and the new
  gates give opposite verdicts for the two agreement notions on one model at one bound. The validator
  now runs the authentication-tag check for either agreement goal. Build green (1855 jobs), audit clean
  over 2555 theorems.

* 2026-10-19 (g) - continuous verification (stage 7's CI item): `protosat/scripts/ci.sh` runs fifteen
  gates - build inside a time budget, no `sorry` / `native_decide` / user `axiom`, the axiom audit,
  a theorem-inventory floor so a deleted guarantee fails CI, the demo inside a budget, and assertions
  that the demo actually prints every contract verdict, replays attack certificates independently of the
  search, and both accepts the Lowe certificate and rejects the same script on NSL. All fifteen green.
  Wired into `.github/workflows/ci.yml` for a clean machine. Scratch `Probe.lean` removed.

* 2026-10-19 (h) - stage 9's monotonicity layer: `Bounds.le`, `univ_mono`, `BoundedRun.mono` /
  `BoundedAttack.mono` / `BoundedSafe.mono`, the query-level `boundedSafe_mono_bounds` /
  `boundedSafe_mono_goals` / `boundedSafe_mono`, and gates showing a safety verdict transferred to a
  smaller bound without re-running the search (and agreeing with the smaller search when it is run), plus
  an attack carried to a larger bound. Also fixed a `printf` bug in the CI script's separator lines.
  Build green (1855 jobs), audit clean over 2574 theorems, 15/15 gates green.

* 2026-10-19 (i) - `Contract.searchFuel` / `driverAnswer`: a fuel-bounded production driver with
  `searchFuel_eq_find?` (agreement with the unbounded search), soundness of both answers, completeness
  at the sufficient-fuel budget, and gates for exhaustion, attack and safety. All five stage-1 result
  categories now have a declaration that can produce them.

* 2026-10-19 (j) - stage 4 first installment: `ProtSat/Represent.lean` (extended value domain

* 2026-10-19 (k) - stage 4 second installment: `ProtSat/BoundedExec.lean` (52 declarations) derives
  ten of the twelve `RunOK` conditions from `BoundedTrace` plus the existing protocol theorems,
  names the remaining two as `Residual`, proves the acting-session index bound (`lt_nS1_of_act`),
  exhibits the dummy-field run that no bound can admit (`residual_not_derivable`) and the canonical
  run that does (`canonical_actM_actD`), and adds
  `Query.boundedSafe_of_encodingUnsat_of_residual`. Build green (1859 jobs), audit clean over 2725
  theorems, 15/15 CI gates green.

* 2026-10-19 (l) - stage 4 third installment: `Shape.V` plus the extended-domain interface in
  `Encode.lean` (`ShapePrefix`, `shValX`, `valAtX`, `uIdxX`, `uIdxX_eq_uIdx_of_mem`,
  `valAtX_uIdxX_of_nameable`), `Represent.shapeX` redefined so `U` is persistent and `V` is
  nameable, the gate-equation read-back lemmas, and `Represent.domainGap` reported by the demo.
  CI now runs 18 gates (three new ones on the representability report) with the theorem floor at
  2740. Build green (1859 jobs), audit clean over 2755 theorems.

* 2026-10-19 (m) - stage 4 fourth installment: `RunOK.actB` made conditional on the actions that
  read the fields (`readsDelivery`, `readsNonce`), `BoundedExec.actB_of_bounded` deriving it from
  the public bound, `Residual` reduced to `exprB`, `Represent.exprB_of_domainGap_false` and
  `BoundedExec.withinBounds_of_bounded` discharging it from a decidable query check, and
  `ProtSat/EndToEnd.lean` producing `boundedSafeGoals` / `noLeak` for a gap-free example with the
  solver answer as its only hypothesis. Kernel re-derivation costs measured and published.
  Build green (1861 jobs), audit clean over 2769 theorems, 18/18 CI gates green.

* 2026-10-19 (n) - stage 6 first installment: `ProtSat/Resolution.lean` - resolution
  refutations as data, `checkProof` as a linear walk, `checkProof_sound` proving the checker, six
  kernel-decided gates (accepts a real refutation; rejects truncated, corrupted, wrong-formula,
  empty, out-of-range evidence), the bridge `encodingUnsat_of_proof` that reaches the analyser
  verdict without running the solver, and `toDimacs` so an external prover can be handed the exact
  formula. Build green (1863 jobs), audit clean over 2804 theorems, 18/18 CI gates green.

* 2026-10-19 (o) - the closed verdict: `EndToEnd.qg_safe` and `qg_noLeak` prove
  `boundedSafeGoals` and the public no-leak statement with NO hypotheses, for a real protocol,
  depending only on the three standard axioms (checked by `#print axioms` and the full audit).
  Well-formedness, gap-freeness and the solver answer are all `decide`d; `Leak` shows the same
  pipeline reports an attack for a one-expression change, so the verdict discriminates.
  Build green (1863 jobs), audit clean over 2816 theorems, 18/18 CI gates green.

* 2026-10-19 (p) - `ProtSat/Differential.lean`: the enumeration route and the CNF route
  used as each other oracle, and `encoding_correct` instantiated on two real protocols -
  `guard_correct` (neither side holds; both procedures independently say safe) and `leak_correct
  ` (a hand-built leaking run yields a satisfying assignment via `encoding_complete` with no
  `WithinBounds` hypothesis, discharged by `withinBounds_of_bounded`). All three standard axioms
  only. Build green (1865 jobs, 11 s), audit clean over 2836 theorems, 18/18 CI gates green.

* 2026-10-19 (q) - `ProtSat/Correspondence.lean`: the correspondence stated for every
  gap-free query, not just two instances - `encoding_complete_gapFree` (attack implies
  satisfiable, no `WithinBounds` hypothesis), `boundedSafe_of_unsat_gapFree` (unsat implies
  `boundedSafeGoals`, needing only the semantic property of the formula rather than the analyser
  verdict equation), and `boundedSafe_of_refutation` (a checked resolution refutation implies
  `boundedSafeGoals`, so the solver is never consulted). Standard axioms only. Build green
  (1867 jobs), audit clean over 2842 theorems, 18/18 CI gates green.

* 2026-10-19 (r) - `Resolution.Evidence` / `checkAgainst`: refutations bound to the
  clause list they were produced against, with `checkAgainst_sound` and three decided gates
  accepting well-formed evidence and rejecting transplanted and truncated evidence. Audit clean
  over 2851 theorems, 18/18 CI gates green, build green (1867 jobs).

* 2026-10-19 (s) - stage 6 second installment: `ProtSat/Serialize.lean`. Refutation evidence now
  survives a file boundary. A refutation is coded as a flat list of integers - a four-number header
  per line, DIMACS-style literals, a 0 terminator - with a *total* decoder (malformed input yields
  `none`, never a panic and never a partial function). Proved: `litOfCode_litCode`, `readLits_map`,
  `lineOfCode_lineCode`, the whole round trip `proofOfCode_proofCode` (one unit of fuel per line,
  plus one), `proofCode_inj` (distinct proofs have distinct codes, so a digest can name a cached
  artifact without standing in for the proof), and `checkCode_sound`: a code that passes the checker
  refutes the formula, with no solver and no search in the path. `checkCode_iff_checkProof` makes the
  two directions exact. Five decided gates: the demo refutation is accepted through its code, an
  unknown tag, a truncated code, a missing-terminator line and a corrupted proof are all rejected.
  Build green (1869 jobs), audit clean over 2896 theorems.

* 2026-10-19 (t) - the demo and CI now exercise the evidence path end to end: a new
  `REFUTATION EVIDENCE` section prints a checked refutation, the same refutation serialized and
  re-checked, the round trip, and a rejection of evidence transplanted to another formula. CI runs
  22 gates (four new) with the theorem floor raised to 2880. Build green, audit clean.
* 2026-10-19 (u) - stage 6 third installment: `ProtSat/CheckedSafe.lean`. The evidence chain is now
  a theorem about a `Query`, not about a formula: `bytes -> proofOfCode -> checkProof -> Unsat ->
  boundedSafeGoals q`, delivered as `boundedSafe_of_checkedProof` and `boundedSafe_of_checkedCode`.
  The goal-transfer lemma `boundedSafeGoals_of_secrecy` carries the hypothesis that makes it true
  (`every selected goal is one the encoding represents`) instead of smuggling a secrecy-only result
  past a query that asked about agreement. It also constructs a `SafeEvidence` - `Query.lean` said
  nothing builds one, because the analyser's answer is a solver run; checked evidence does, and
  `boundedSafe_is_security` shows the answer it builds counts as a security verdict. On the guarded
  protocol, `qg_safe_of_code` says: any code the checker accepts for this protocol's formula is a
  bounded-security theorem about the protocol, with no solver in the statement. What is still
  missing is the producer of such a code.
* 2026-10-19 (v) - stage 5, the half that was missing: `ProtSat/Sound.lean`. `encoding_sound` now
  returns the **complete bounded predicate**. `decVal_range` - a decoded value is a read *of* the
  universe list, `valAt sh u = rget sh.U u`, so it is a universe message by construction - lifts
  through `decSt_range`, `decXe_range`, `decLearn_range` and `decKnSeq_range` (seeded by
  `initKn_subset_univ`, with `StoreWF` from `Agrees` pinning every stored pair to a slot) to
  `decRun_cfgInUniverse`, and thence to `decoding_runsInUniverse` and `boundedTrace_decRun`. So
  `Sat a (encode P B)` gives `BoundedAttack P B` (`encoding_sound_bounded'`) and
  `boundedAttackGoals (Query.mk P B [secrecy])` (`boundedAttackGoals_of_sat`) - with only the two
  hypotheses `encoding_sound` already had: `domainGap` is a *forward* closure condition and the
  decoders run the other way. That closes the equivalence:
  `encoding_correct : Satisfiable (encode P B) <-> boundedAttackGoals q` for a gap-free query,
  and `leaky_query_boundedAttack` instantiates it with no hypotheses at all on a real protocol,
  the witness being the decoded run rather than a hand-built trace. Still secrecy only:
  `Encode.violationLits` names leak literals and nothing else.
  Build green (1870 jobs), audit clean over 2936 theorems, 22/22 CI gates green.
* 2026-10-19 (w) - the review's headline defect becomes a theorem: `ProtSat/AuthGap.lean`. For the
  commit-only witness model, at the same protocol and the same bounds, the CNF route proves
  `boundedSafeGoals (Query.mk P B [secrecy])` and agreement is violated:
  `auth_gap_is_real`, and therefore `goal_hypothesis_is_needed`:
  `¬ (∀ q, boundedSafeGoals (secrecy-only q) → boundedSafeGoals q)`. The goal-selection hypothesis
  that `CheckedSafe` carries is now known to be load-bearing rather than defensive. The module also
  proves *why* the formula is unsat there - `why_the_formula_is_unsat` (`violationLits = []`, because
  the model declares no secret) and `empty_clause_in_encode` - and says plainly that the route
  cannot distinguish 'nothing to leak' from 'properly protected'. A non-vacuous variant (a protocol
  that does declare a secret, keeps it, and still breaks agreement, with an honest execution
  reaching the secret) is the follow-up in progress.
  Build green, audit clean over 2965 theorems, 22/22 CI gates green.
* 2026-10-19 (x) - stage 6 fourth installment: `ProtSat/Refute.lean`, the producer the checker was
  waiting for. A saturating resolution engine (`saturate : Nat -> CNF -> List Line`, all resolvents
  of all pairs per round, structurally decreasing with clause deduplication) plus `refutationOf`,
  which cuts the line list at the empty clause. The theorem that matters is the direction nobody
  had: `refute_sound : refutationOf f k = some p -> checkProof f p = true` - the engine's output is
  accepted by the INDEPENDENT checker, so a safety answer no longer has to be certified by replaying
  a search. `refute_unsat` composes it with `checkProof_sound`; `refute_answer` reaches the analyser's
  verdict without running the solver. Kernel gate `demo_refutation_checked` decides that the engine's
  own 19-line refutation of `demoF` is accepted, and `demo_refutation_found` proves the engine did
  not silently fall back to the empty list. Not yet: completeness (DP variable elimination in
  progress) and any run on a real protocol formula.
  Build green, audit clean, 22/22 CI gates green.
* 2026-10-19 (y) - `AuthGap` section 6: the non-vacuous version of the headline gap. A protocol that
  DOES declare a secret (`P2.secrets ≠ []`, not compromised, not initially known), with an exhibited
  honest execution that reaches it (`hold_steps` accepted by the step checker, `hold_bounded`,
  `secret_held`, and `secret_not_in_knowledge` so it is held rather than published), whose CNF is
  unsatisfiable - and the violation group is proved NON-empty (`violationLits_nonempty`,
  `no_empty_clause2`), so the UNSAT answer is not explained by having nothing to leak - while
  agreement is broken at the same bounds (`authbreak2`, `attacked_for_agreement2`). Headline:
  `auth_gap_is_real_nonvacuous`, and `safe_for_secrecy2` goes through the tool's own verdict
  (`analyze2`, `cnf_answer_is_encodingUnsat2`) rather than a hand-fed unsatisfiability.

  Measured kernel-replay cost, which is a stage 8 datum and the reason the model is one-principal:
  410 CNF variables -> 59 s to elaborate the module; 648 -> 215 s; 850 -> did not finish in 600 s.
  The two-principal variant was built and every condition checked except that last replay.
  Build green (1877 jobs), audit clean over 3056 theorems, 22/22 CI gates green.
* 2026-10-19 (z) - stage 6, the hard half: `Refute.refute_complete`. The engine is not just a sound
  way to make evidence, it is a PROVER: `Unsat f -> ∃ k p, refutationOf f k = some p`, with fuel
  `(varsOf f).length` - one saturation round per variable. Route: Davis-Putnam elimination
  `dpElim f v` (non-tautological v-free clauses plus all resolvents on v), `dpElim_sat` both ways
  (the classic two-assignment lifting: if neither setting of v works, the resolvent of the two
  falsified clauses is a v-free clause of `dpElim f v` that the lifted model also falsifies),
  `elimAll_sat`, `elimAll_varFree`, and a coverage lemma that every clause elimination derives is a
  line the saturation derives. The tautology trap is handled where it belongs - tautological
  parents are dropped, which is exactly what makes every resolvent v-free, and the resolvent the
  lifting argument needs is automatically non-taut because the assignment falsifies it. Consequence:
  `refute_iff : Unsat f <-> ∃ k p, refutationOf f k = some p ∧ checkProof f p = true` - the checker
  and the engine agree exactly, so the evidence format loses nothing - and
  `not_refutable_of_satisfiable`, the engine cannot lie. `boundedSafe_of_refutation` composes the
  engine with `CheckedSafe`, and `demo_refutation_round_trip` decides that the engine's own output
  survives serialization and is still accepted: producer on both ends of the byte boundary.

  Measured, and stated in the file rather than hidden: naive saturation is a theorem, not a solver.
  On the guarded protocol's real CNF (291 clauses, 659 literal occurrences), `saturate 1` gives 1150
  lines and does not find the empty clause; `saturate 2` gives 37167 lines and still does not; those
  two rounds took 18m51s to evaluate. So there is no closed `decide` gate on a protocol-sized
  formula yet - that needs subsumption, unit propagation and polarity pivoting, or a DPLL that emits
  resolution proofs directly. `boundedSafe_of_refutation` is the explicit-hypothesis form.
  Build green, audit clean over 3109 theorems, 24/24 CI gates green.
* 2026-10-19 (aa) - stage 7: `ProtSat/Benchmarks.lean`, 75 closed theorems, NS and NSL rebuilt in the
  REFERENCE language with explicit authentication instrumentation and a real declared secret (B's
  fresh nonce via a `secret` action), so the safety story is no longer a hand-written certificate in
  the old semantics. What the contract itself answers, by *running* its enumerator in the kernel:
  `NSL2cqE_boundedSafe` and `NSL2cqE_verdict` (BOUNDED SAFE with its `SafeEvidence`) at
  `steps := 3, rounds := 0`; `NS2cq_verdict` and `NSL2cNoCheckQ_verdict` (ATTACK, witness replayed
  by `checkWitness`) at `steps := 14`; and `NSL2earlyQ_attackFound_true`, where the enumerator FINDS
  an attack on a mutation of NSL and the violation is the agreement goal, not secrecy
  (`NSL2earlyQ_witness_is_auth` + `_not_leak`). `exhaustion_pair` is the executable discrimination:
  same goals, same bounds, one BOUNDED SAFE and one ATTACK, both by exhaustion. Non-vacuity is
  proved, not assumed: `nsl2_honest_reaches_commit` (obligation `[nb]`, exactly one claim and one
  commit), `nsl2_honest_events` pins both `Inst` records including the ordering the monitor needs,
  and `nsl2c_honest_permitted` shows the honest run is a *bounded* run, so the exhaustion bound does
  not exclude the honest case by accident. Lowe's script is proved not an execution of NSL at all
  (`run NSL2c ... = none`) and erasing exactly the identity check makes it one again.

  Stated plainly in the module, because it is the interesting part: the literal ask - NS attacked and
  NSL safe at ONE common bound - is NOT delivered and cannot be at these costs. The faithful NS model
  needs `rounds := 1`, where the universe has 1415 messages and a single kernel-side `inBoundsBool`
  exceeds 30 minutes; exhaustion reaches ~3 events at `rounds := 0`, and at that bound NS is safe too
  (`NS2cqE_boundedSafe`) - which is said rather than hidden. Measured cost of the whole module:
  168 s to elaborate, and the project's clean build goes from seconds to 174 s. That is the price of
  keeping these as checked theorems instead of hypotheses, and it is the strongest argument in this
  log for the proved refinements of stage 8.
  Build green (1879 jobs, 174 s), audit clean over 3184 theorems, 24/24 CI gates green.
* 2026-10-20 (ab) - stage 9, the compression theorem: `ProtSat/Compress.lean` (1706 lines, all
  structural - the module elaborates in 3 s, no kernel enumeration). The step bound stops being a
  number the analyst picked. T1: `actionCount P` = sum of role lengths over instantiated sessions,
  with `rel_ev_cases` (a step either leaves the session vector alone or advances exactly one
  session's counter by one) giving `sessEv_count_le_actionCount`; the language does not loop, so
  this is the correct bound, not a weakened one. T2: `ded_steps_le_univ` - a chain of deductions
  each adding a genuinely new message has length at most |univ P B| (needed `List.nodup_eraseDups`
  and `List.length_le_of_nodup_forall_mem`, which neither core nor this project's imports provide).
  T3: the honest wall - `stepOf P C (Ev.ded t) = some (publish C t)` and `publish C t` is a
  DIFFERENT list, so a redundant deduction is not literally removable; removal is therefore proved
  against `CfgEq` (sessions, allocation history, obligations equal and knowledge equal AS A SET),
  and `CfgEq` is proved a congruence for `stepOf`, `actStep`, `oneStepBool`, `actionUsable`,
  `authData`, `leaks` and `inBounds`. `drop_leading_idle` covers the literal case where no
  extensional argument is needed. T4: `compress_secrecy` - every leaking execution inside the
  universe has a leaking witness with at most actionCount + |univ| events - and the prize,
  `safe_at_derived_bound : (∀ g ∈ q.goals, g = Goal.secrecy) -> boundedSafe (derived q) ->
  allLengthsSafe q`, where `allLengthsSafe` quantifies over executions of EVERY length that stay
  inside the query's own sessions and universe. `boundedSafe_of_derived` reuses the existing
  `Contract.boundedSafe_mono_bounds` rather than reproving monotonicity. T5: closed numbers -
  `derivedSteps secureQ = 16` where the query itself asks about 3, `derivedSteps transientQ = 10`.

  Two limits, both stated in the file. (i) Agreement does NOT compress: `Inst.idx` is the trace
  POSITION, `claimMatches` compares positions and `agreesInj` counts them, so deleting a non-session
  event renumbers every later authentication event; two runs can visit extensionally equal
  configurations and perform the same claims and commits in the same order and still have different
  `insts`. Finishing it needs an index-free (rank-renumbered) formulation of agreement or positional
  alignment plus monotone-renumbering invariance - a statement about `Inst.idx`, not about the
  knowledge representation. (ii) The derived bound is a real number the search still cannot reach:
  16 steps where exhaustion manages about 3 events before the node count is already 11,868. So
  `safe_at_derived_bound` is currently a reduction from 'unbounded' to '16', not a decision
  procedure - the logic is closed and the performance is not, which is the same shape as stage 6.
  Build green (1881 jobs), audit clean over 3306 theorems, 24/24 CI gates green.
* 2026-10-20 (ac) - stage 9 finished: agreement compresses too, and the obstruction closed the right
  way. The parent asked for invariance rather than redefinition, and the finding that made it work is
  worth recording because it is checkable in one grep: nothing in ProtSat.Reference reads an
  ABSOLUTE position. Apart from instAt storing idx := i, the only uses of Inst.idx are the two
  comparisons r.idx < c.idx in claimMatches and in the counted filter of agreesInj. So the monitors
  are invariant under strictly monotone renumbering and Reference.lean never had to change.
  T6a: InstRec (the record without idx), incIdx, instEquiv (same record sequence, both listed with
  strictly increasing positions), then agrees_renumber and agreesInj_renumber - via restating each
  monitor as a PREFIX property (agrees_iff_agreesPrefix) and transferring the match test and both
  counts. T6b: insts_dropRedundant_records - the compressed run's insts have exactly the original's
  record sequence, because the deleted events (idle, redundant ded) carry no authentication record
  and every survivor sees a CfgEq-equal configuration - upgraded to instEquiv_dropRedundant using
  runs_eq (a run's visited list is unique). T6c: compress_agreement and compress_agreementInj, same
  derived bound as secrecy, and safe_at_derived_bound_full for queries selecting secrecy, agreement
  OR injective agreement - the restriction the previous pass had to state is now gone, and injective
  agreement did follow (the counts transfer under renumbering). T6d: derivedSteps authOrderQ = 7,
  derivedSteps authSwappedQ = 7, and authSwappedQ_short_attack transporting the contract's own
  2-event attack inside the derived bound, so the instance is not vacuous.
  The headline now: for every goal the contract can ask, boundedSafe at the model-derived bound
  implies allLengthsSafe - no execution of ANY length inside the query's sessions and message
  universe violates a selected goal. Demo prints the derived bound beside the bound the query chose
  (secureQ: asks 3, derived 16; authOrderQ: asks 2, derived 7), and CI gates on it: 25 gates.
  Build green, audit clean over 3405 theorems.
* Next - stage 6 is nearly closed: the checker (`Resolution`), the binding of evidence to its
  formula (`checkAgainst`), and the serialization (`Serialize`) are proved, and a checked code now
  reaches `boundedSafeGoals q` (`CheckedSafe.boundedSafe_of_checkedCode`). What is missing is a
  PROVER, so a safety answer arrives with a refutation instead of being re-run in the kernel:
  `ProtSat/Refute.lean` - a saturating resolution engine whose output `checkProof` accepts. Then
  the xe stride flip onto `Shape.V` (szXe, szAxe, vxe, axe, xeOh, f1, f2, evalGate,
  evalLeafGate), after which `domainGap` is no longer a restriction on the protocol and
  `Residual` is empty - it is now the *only* hypothesis separating the CNF route from an
  unconditional statement. Then agreement violations in the CNF at all: until that is done a CNF
  `boundedSafe` is a statement about secrecy only, which is why the label says `encodingUnsat`
  and why `Sound.encoding_correct` is indexed by `[Goal.secrecy]`. Then stage 7: NS/NSL
  authentication instrumentation with honest-execution witnesses..