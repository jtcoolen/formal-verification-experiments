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

Two facts worth keeping from the plumbing: `Runs` inductions in this codebase must be stated over the
*position* (`cfgOK_at`), not over membership in the visited list - `induction` on `Runs P (initCfg P)
tr Cs` reverts any hypothesis mentioning the configuration index and the substitution then fails;
and `List.mem_append` on `closeOne`'s five-component list is left-nested, so a five-way `rcases`
needs the pattern `(((hU | hpair) | pencS) | pencA) | hhash`.

## Log

* 2026-10-19 (k) - stage 4 second installment: `ProtSat/BoundedExec.lean` (52 declarations) derives
  ten of the twelve `RunOK` conditions from `BoundedTrace` plus the existing protocol theorems,
  names the remaining two as `Residual`, proves the acting-session index bound (`lt_nS1_of_act`),
  exhibits the dummy-field run that no bound can admit (`residual_not_derivable`) and the canonical
  run that does (`canonical_actM_actD`), and adds
  `Query.boundedSafe_of_encodingUnsat_of_residual`. Build green (1859 jobs), audit clean over 2725
  theorems, 15/15 CI gates green.
* Next - wire `Represent.exprVals` into `Shape` and the `xe` family so `exprB` leaves `Residual`
  too; then the `actB` residue disappears by moving `encoding_complete` onto the repaired event
  type, which is the last thing standing between `encodingUnsat` and a real `boundedSafe` on the
  CNF route.

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
  `exprVals`, index preservation, `eval_inside_exprVals`, the two gate-equation lemmas,
  `exprB_of_exprVals`, the transient pair made nameable at the bounds that fail `exprB`, and
  `no_bound_discharges_exprB` proving no bound discharges it). Build green (1857 jobs), audit clean
  over 2657 theorems, 15/15 CI gates green. Roadmap stage 6 investigated; its real shape is
  recorded above.
* Next - wire `exprVals` into `Shape` and the `xe` family (the ~65-declaration stride change), then
  `encoding_complete` without `exprB`; then stage 6 through `Sat.Fmla.proof []`, not the reified form.