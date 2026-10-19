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
* Next - the explorer (above), then stage 3: one public `BoundedExecution` predicate over the repaired semantics, per-expression
  `EvalDomain` construction (so `fst (pair x x)` is representable even when the pair is outside
  `U`), and deriving the compiler's representability conditions from the public bound instead of
  assuming them.