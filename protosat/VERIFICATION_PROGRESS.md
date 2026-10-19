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

## Log

* 2026-10-19 (a) - baseline inspected; build green; three review witnesses promoted to permanent
  regressions in `ProtSat/Regressions.lean`; `ProtSat/Query.lean` added (contract, validator,
  gate theorems); `Analyzer.Verdict.safe` renamed to `encodingUnsat`; README headline, section 8,
  section 10 and the module map corrected; demo extended with the query contract.
* Next (stage 2) - the repaired reference layer, independent of SAT: allocation history for
  freshness, action-specific events, ordered actor/peer-aware authentication monitor with
  malformed-annotation rejection, persistent secret obligations, and the provisioning checks the
  validator still defers.