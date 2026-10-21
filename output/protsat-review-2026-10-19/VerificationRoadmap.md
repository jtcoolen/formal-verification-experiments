# ProtSat verification roadmap

Planning baseline: current checkout inspected on 19 October 2026. This is a proposed design and implementation plan; theorem signatures below are targets, not declarations already present in the repository.

## SAFE: present and target meanings

Currently `Analyzer.analyze P B` returns `Verdict.safe` when the leaf-universe precheck succeeds and `DPLL.dpll (encode P B) = none`. The proved solver theorem establishes that this CNF is unsatisfiable. The missing bridge is that every attack in the public bounded semantics has a model of this exact formula. This bridge is currently false for authentication: the public attack predicate includes authentication failures, while the SAT violation clause contains only secret leaks.

The intended security statement is:

```
BoundedSafe q := no execution allowed by query q violates a selected goal.
```

A query must identify the symbolic theory, role/session instances, principal and nonce domains, initial credentials and attacker knowledge, compromise assumptions, selected goals, message universe, and event accounting. A future `boundedSafe` result must carry evidence for this whole statement. An empty selected goal set should be reported explicitly, rather than presented as a useful protocol-security result.

The first release target is a fully verified bounded symbolic analyser: an exact finite decision procedure with kernel-checkable evidence for either answer. Arbitrary sessions, arbitrary message size, computational cryptography, and concrete protocol implementation refinement are separate milestones. General unbounded protocol verification cannot be a terminating complete procedure for every input.

## 1. Correct the public contract and preserve regressions

Implementation:

- Temporarily expose the existing UNSAT outcome as `encodingUnsat`, or disable a semantic SAFE claim until the relevant exactness theorem is available.
- Introduce `Query` and explicit selected `Goals`; include model/theory version and all semantic bounds.
- Distinguish `attack`, `boundedSafe`, `invalidModel`, `unsupportedGoal`, and `unknown` for resource exhaustion or solver failure. Invalid external evidence must be rejected with diagnostics.
- Keep mathematical reference solving total; distinguish this from a production driver that may time out.
- Generate the public theorem inventory from actual declarations, and correct the README's equivalence, example theorem names, and complexity claims.
- Promote the existing review witnesses into permanent regression examples. During repair, retain the original faulty behavior as a documented old-model witness; under repaired semantics prove the intended new behavior.

Gate: the commit-only authentication witness cannot receive a full security SAFE result; every displayed guarantee identifies its selected goals and bounds.

## 2. Repair the independent reference language and semantics

Keep this layer independent of SAT, variable allocation, and the solver.

**Well-formed models and provisioning.** Add a decidable validator for role/session references, finite-domain references, declaration identifiers, static-secret closedness, expected peer types, credential provisioning, and dataflow/read-before-binding where appropriate. Malformed declarations must not disappear through `filterMap`. Prove `validate q = ok -> WellFormed q`.

Parameterize roles by `self`, `peer`, credentials, and session parameters, then prove instantiation commutes with evaluation. The current metadata does not instantiate literal role expressions. Either change asymmetric decryption to consume a private-key expression available to the role, or enforce a proved credential capability discipline. Private/shared key literals must have an explicit provisioning meaning. Honest processes should compute using provisioned values, received values, fresh values, and permitted symbolic operations.

**Action-specific events.** Replace dummy-filled `act q m d` labels with relevant choices such as `receive q m`, `generate q n`, and `local q`. Derive observable send/authentication/secret events from the executed action. Alternatively, prove a normalization theorem for ignored fields as an interim migration step. A send/check must work with an empty fresh-nonce domain.

**Fresh allocation.** Maintain a monotone allocation history, initialized consistently with reserved/public nonce names, or use distinct nominal identities for fresh generation occurrences and adversary/public names. Never infer freshness solely from current register values. Prove history monotonicity, no repeated honest generation, and preservation through overwrites and encapsulation. Prove renaming invariance before using canonical names as a search reduction.

**Secret obligations.** Specify static long-term secrets, current-register secrecy, and dynamically declared-value secrecy separately. `secret e` should evaluate and snapshot a value into a persistent obligation when that form of secrecy is selected. Overwriting the original register must not delete the obligation. Specify whether a claim excludes attacker knowledge at any time, from declaration onward, or under a temporal compromise policy. Monotone attacker knowledge helps reduce retrospective secrecy checks to the declaration state, but that reduction still needs proof.

**Authentication.** Record actor, peer, role pair, session, event occurrence, tag, and agreed data. Require evaluation success and an agent-valued peer when enabling the action. Make the declared goal set select what is required. Define non-injective agreement using a preceding matching event:

```
Commit(A, B, roles, tag, data) at i
  -> exists j < i, Running(B, A, roles, tag, data) at j.
```

The matching relation must reflect the intended protocol roles and permit legitimate self-communication only when its role/session conditions are met. Once a commit violates the requirement, later events cannot repair that earlier failure. Define injective agreement separately, using an injective matching of commit occurrences to earlier running occurrences and a proved finite matching/monitor implementation.

Required proofs include initialization well-formedness, transition preservation, frame properties, attacker-knowledge monotonicity, allocation monotonicity, no repeated generation, event evaluation correctness, snapshot persistence, and the selected authentication monitor's equivalence to its trace predicate. Network attackers can block sessions; a universal honest-progress theorem is not an appropriate requirement.

Gate: regressions cover nonce reuse after overwrite and nesting; empty-nonce-domain actions; later/same-actor/wrong-peer claims; malformed annotations; snapshot secrecy after overwrite; and decryption without provisioned credentials.

## 3. Give bounds one public, independently defined meaning

Choose one `BoundedExecution q` predicate over the reference semantics. Its hypotheses must state precisely which persistent values, sessions, fresh identities, and resources are bounded. Compiler-side `RunOK` properties must be derived from this predicate and validated query conditions, rather than added as independent execution-wide assumptions.

Preserve the useful contract that stored/network/attacker-known terms lie in a finite universe `U`. Expression intermediates need a separate domain. For every expression `e`, construct a finite `EvalDomain e U`:

- A variable ranges over `none` and the terms of `U`.
- A constant has its exact denotation.
- A unary expression takes the image of its child domain under reference evaluation.
- A binary expression takes the image of the Cartesian product of its child domains.
- Include evaluation failure explicitly; do not identify an out-of-`U` intermediate result with failure.

Prove every expression evaluated in a `U`-valued store belongs to its generated domain. This supports `fst(pair(x,x))` exactly even when the pair is outside `U`. An action storing or publishing an out-of-`U` result is excluded by the public persistent-value bound; an intermediate expression or equality test need not be excluded. A simple reference implementation can enumerate all finite stores; a compositional domain construction can be proved equivalent or adequate and used for execution.

Keep the current event bound explicit during migration. State clearly that it includes attacker deductions. Later introduce separate honest-action accounting or eliminate redundant deduction events through a proved correspondence.

Prove initial-knowledge membership, required fresh-atom membership, subterm closure where deduction enumeration needs it, finite-domain uniqueness, and precise handling of empty domains. Do not require finite closure under unrestricted pairing, which is impossible.

Gate: the transient-pair regression is representable; sends/checks do not require fresh values; zero-step and empty-session cases work; and public bounded executions imply all actual compiler representability invariants.

## 4. Complete and strengthen the SAT correspondence

Retain existing useful work: DPLL correctness, independent certificate checking, sequential one-hot encoding, positional injectivity/range lemmas, and characteristic-assignment groundwork. Refactor incrementally to control proof breakage from semantic repairs.

Package variable families as a semantic sum with a proved finite numeric encoding. Validate every generated literal against the declared variable count. Define interpretations for every auxiliary family, including new allocation and property-monitor variables.

Prove local equivalences for initial state, one-hot groups, exact expression evaluation, every transition kind, frames, attacker deductions, knowledge support, allocation history, secret obligations, and authentication monitors. Freshness and unmatched-authentication tests contain negative premises; their converse/absence properties are necessary, not optional.

Add authentication violations to the CNF. If v1 supports only secrecy and non-injective agreement, reject other goal kinds explicitly. Prove the Boolean violation monitor is equivalent to the independently defined selected-goal violation; do not define the public goal by the clauses that implement it.

Construct `assignOf` from a canonical bounded execution and prove satisfaction of every clause group. Handle shorter traces through proved idle padding or a bounded endpoint selector. Preserve prefix violations under padding.

Target signatures, schematically:

```lean
encoding_sound :
  WellFormed q -> Sat a (encode q) ->
  BoundedExecution q (decode q a) /\ Violates q (decode q a)

encoding_complete :
  WellFormed q -> BoundedAttack q -> Satisfiable (encode q)

encoding_correct :
  WellFormed q ->
  (Satisfiable (encode q) <-> BoundedAttack q)
```

The soundness conclusion must contain the complete public bounded predicate, rather than only an attack plus an event-length inequality. Completeness may assume decidable model/query well-formedness; arbitrary closure properties of the entire candidate run should be derived or explicitly part of the user's bounded semantics.

Gate: the exactness theorem compiles without admissions; pure authentication and secrecy attacks are both covered; no case is justified only by impossible assumptions.

## 5. Produce independently checkable evidence for both answers

Extend attack checking to validate selected goals and the complete query bounds as well as transitions. Prove both soundness and certificate existence for every supported finite attack.

Add UNSAT evidence checked against the exact original query CNF. Keep the reference DPLL. A production SAT solver can be an untrusted search engine if its assignments or UNSAT proofs are independently checked. Reuse the pinned Mathlib LRAT proof-reconstruction infrastructure after checking its interface, performance, and compatibility; the current dependency already contains `Mathlib/Tactic/Sat/FromLRAT.lean`.

```lean
checkAttack_sound :
  checkAttack q c = true -> BoundedAttack q

checkUnsat_sound :
  checkUnsat f proof = true -> Unsat f

checkSafe_sound :
  WellFormed q -> checkSafe q proof = true -> BoundedSafe q
```

Derive attack/safe verdict soundness. For the total mathematical reference analyser, also prove attack and safety equivalences/completeness. For the resource-limited production driver, prove accepted-answer soundness while preserving `unknown`.

Make evidence identify the actual protocol, goals, bounds, and CNF. Canonical serialization, total parsers, printer/parser round-trips, and frontend semantic-preservation theorems close the file boundary. A digest can index cached artifacts; mathematical evidence should bind to the actual query data rather than rely solely on collision resistance. Preprocessing and incremental solver assumptions must be included in the proof chain.

Preserve the current kernel-only assurance through proof reconstruction or kernel evaluation. Executing a proved checker natively is a useful engineering mode, but asserting that its concrete output was correct adds compiler/runtime trust unless the corresponding result is reconstructed and checked by the kernel.

Gate: corrupted, truncated, stale, wrong-query, wrong-property, and wrong-CNF evidence is rejected; an evidence bundle is replayable without running the search solver.

## 6. Establish credible examples, non-vacuity, and CI

For every positive security example, first prove an honest execution reaches the relevant secret/authentication/completion events under its stated assumptions and bounds. This detects dead roles and unreachable claims. Also retain adverse executions demonstrating the model can exhibit the relevant failure class.

Repair NS and NSL models using parameterized roles. Instrument authentication explicitly. NSL must retain the original nonce check as well as Lowe's identity check. Prove the NS attack for the intended secrecy/authentication goals and a genuine bounded NSL safety theorem across a stated family of concurrent sessions and compromise cases.

Use tiny exhaustive operational exploration as an independent regression oracle for CNF satisfiability. Cover secure/insecure pairs, disclosure on/off, peer swaps, replay, multiple sessions, delayed claims, fresh exhaustion, empty nonce domains, transient expressions, overwritten secrets, malformed models, and zero-step attacks. Differential comparison with Tamarin/ProVerif can expose modeling mistakes, but only after aligning semantics; tool agreement is not a formal proof.

CI gates: clean build, theorem inventory, axiom audit, no admissions in trusted results, kernel-checked regressions, honest executability witnesses, evidence replay, and representative performance budgets. Existing discovery probes document old defects; repaired-model regression theorems verify their prevention.

Gate: no positive security example relies solely on rejection of one attack script or on an unreachable security annotation.

## 7. Optimize through proved refinement

Profile construction, term comparisons, repeated index lookup, deduction table generation, expression domains, clause generation, solving, peak memory, and evidence checking separately.

Priorities: canonical set/bitset knowledge; fixed finite store maps; hash-consed terms; precomputed indices; cached deduction instances; expression tables restricted to relevant sessions; deterministic variable numbering; and avoiding duplicate work. Prove each optimized operation refines its simple specification. Keep the existing linear sequential one-hot counters.

Integrate external proof-producing SAT after evidence validation works. Then add incremental solving, property-directed slicing, session/nonce symmetry, partial-order reduction, and preprocessing with dedicated correctness theorems. Authentication order, allocation history, and compromise timing must be preserved by reductions. Smaller universes preserve an under-approximation; they preserve a previous SAFE claim only with an additional coverage argument.

Report real construction/search/checking costs. Full DPLL can branch exponentially; binary expression tables are quadratic in domain size; pairing closure can grow rapidly across rounds.

Gate: optimized execution preserves the same query semantics and accepted evidence. The full NS benchmark should run through encoding and proof-producing search within an explicitly measured resource budget, rather than only through a hand-authored certificate.

## 8. Prove stronger guarantees about increasing bounds

Define a semantic bound ordering and prove attack monotonicity and downward safety transfer:

```lean
B <= B' -> BoundedAttack P B goals -> BoundedAttack P B' goals
B <= B' -> BoundedSafe P B' goals -> BoundedSafe P B goals
```

Derive this through semantic embeddings, not literal clause inclusion, because changing universe sizes changes SAT indices.

Prove finite-trace eventual coverage for precisely stated atom/key domains. Current operational attacker rules can mention principals outside `P.agents`; generated constructor closure alone does not cover all such traces. Restrict domains explicitly, extend them in a fair enumeration, or prove atom-renaming adequacy. Every claimed coverage theorem must handle nonce allocation and available key constructors. Fair enumeration plus eventual coverage can establish eventual discovery of every finite attack; it does not justify an unbounded SAFE result from any one finite search.

For current straight-line roles, prove an especially useful trace compression theorem. Let `H` be the sum of all instantiated role lengths. There are at most `H` session actions. In a finite universe `U`, at most `|U|` deductions can introduce genuinely new knowledge. After removing idles and redundant deductions, every attack should have an equivalent witness of length at most `H + |U|`. Prove preservation of selected goals, event ordering, nonce history, and bounds. Canonicalize list-based knowledge or prove an extensional bisimulation first.

This theorem turns SAFE at a derived threshold into safety for all trace lengths within the same fixed sessions and message universe. Alternatively, saturate attacker knowledge between protocol actions and prove a macro/micro-step correspondence, using the verified finite-universe deduction engine.

Gate: advertise exactly which bounds were discharged. Removing the length bound does not remove the session or message-domain bound.

## 9. Add richer security and broader proof modes separately

Prioritized extensions:

1. Injective agreement, key confirmation, session-key agreement, and explicit replay-resistance scenarios, with distinct property semantics and checker/encoder proofs.
2. Dynamic corruption, key reveal, erasure, and forward secrecy, with explicit temporal exception policies.
3. Signatures, MACs, randomized-encryption randomness, and realistic key identifiers, each with specified symbolic algebra and deduction correctness.
4. XOR/Diffie-Hellman or other equational theories only behind a proved normalization/equality and attacker-deduction interface; completeness for the free-constructor theory does not automatically transfer.
5. Strong secrecy, anonymity, unlinkability, and observational equivalence through relational semantics and a separate analysis, since these compare executions.
6. Unbounded safety through checked inductive invariants, compositional rules, or proved cutoffs for restricted classes. An invariant certificate must establish initiation, preservation, and exclusion of bad states for the actual unbounded semantics. Untrusted automation may search for these certificates; the kernel checks the conclusions. Accept incompleteness/unknown for general inputs.
7. Protocol-to-implementation refinement and computational-soundness results as additional projects with explicit assumptions.

Usability enhancements can proceed after query/evidence formats stabilize: shortest checked attacks, source-linked trace explanations, bound-coverage reports, and certified unsatisfiable cores for assumption debugging.

## Delivery dependencies and release criteria

- First freeze the corrected query, goal, event, and bounded semantics. Semantics/validator work and evidence-format prototyping can proceed in parallel; encoder proof changes depend on the corrected specification.
- Then develop expression domains, action/deduction correspondence, property monitors, and assignment completeness as parallel proof workstreams against stable interfaces.
- Combine them into exact encoding, checker soundness/completeness, and end-to-end SAFE/ATTACK theorems.
- Release the verified bounded core only after positive/negative/non-vacuity examples and independent evidence replay pass.
- Optimize and extend the same verified contracts. Treat stronger finite-instance thresholds, unbounded proofs, and richer security goals as separately named milestones.

The acceptance standard is an exact, explicitly scoped mathematical statement for each verdict, with independently checked evidence and a documented trust boundary. The number of theorems or examples alone is not a release criterion.

## Supporting references

- Current verdict implementation: `protosat/ProtSat/Analyzer.lean:179-196`.
- Current completeness hypotheses: `protosat/ProtSat/Complete.lean:192-207`.
- Checked defect witnesses: `AuthenticationCounterexample.lean`, `BoundsCounterexample.lean`, and `SemanticsCounterexamples.lean` in this directory.
- Tamarin on executability and vacuous security properties: https://tamarin-prover.com/manual/master/book/010_modeling-issues.html
- Tamarin property definitions and compromise policies: https://tamarin-prover.com/manual/master/book/007_property-specification.html
- Tamarin on the general undecidability/possible nontermination of unbounded analysis: https://tamarin-prover.com/manual/master/book/001_introduction.html
- Mathlib LRAT proof reconstruction, also present in the pinned local dependency: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Sat/FromLRAT.html

## Status ledger (updated 2026-10-20, second pass)

Reality of the implementation checkout (`protosat`, HEAD 343855e, 3500 kernel-checked theorems,
26/26 CI gates, axioms `propext, Classical.choice, Quot.sound` only). Each row names the artifact
that decides it, not an intention.

| Stage | State | Deciding artifact |
|---|---|---|
| 1 Contract and regressions | **done** | `ProtSat/Contract.lean` verdict algebra (`attack / boundedSafe / invalidModel / unsupportedGoal / unknown`), `ProtSat/Query.lean` with `goalEncoded`, `ProtSat/Regressions.lean` permanent witnesses, README corrected |
| 2 Reference semantics | **done** | `ProtSat/Reference.lean`: allocation history, action-specific events, ordered role-aware agreement and injective-agreement monitors, credential provisioning; twelve gates that each reverse a `Regressions` witness |
| 3 One public meaning of bounds | **done** | `ProtSat/Bounded.lean` + `ProtSat/BoundedExec.lean`: the public bounds imply the operational ones (`mem_univ_of_mem`, `secrets_subset_univ`), monotonicity in the bounds |
| 4 SAT correspondence | **soundness closed for agreement; completeness open** | Two-sided correspondence for secrecy (`Complete.encoding_complete`, `Sound.encoding_correct`), `hsub` deleted, `SecretsOK` split with the store half proved undroppable. Then, same day: `AuthClauses.lean` put agreement into the CNF as clauses and proved the naive conjunctive form cannot work (`authEncode_not_sat`); `GoalEncode.lean` made the violation group goal-indexed with `encodeGoalsOf P B [secrecy] = encode P B` **by `rfl`**, and proved the hoped-for transport shortcut FALSE (`no_transport_from_base`); `AgreesBase.lean` then discharged the decoded-run bridge, so **a model of the agreement-selecting formula is now a proved bounded attack on the agreement goal** (`boundedAttackGoals_of_sat_agreement_discharged`), with a kernel-decided instance on the AuthGap model. Two caveats keep this honest: the notion discharged is the UNORDERED `AuthBreak` that `Query.Violation` names - `AgreementPredicates.lean` proves that notion incomparable with the reference route's ordered one and structurally unable to express ordering - and completeness for agreement is untouched. The xe stride over `U` (`domainGap`/`exprB`) also remains |
| 5 Independently checkable evidence | **done for the UNSAT answer, and now emitted** | `Resolution.checkProof` (checker), `Serialize.proofCode/proofOfCode` (transport), `Refute.saturate`/`refutationOf` with `refute_sound` and `refute_complete` (prover), `CheckedSafe.boundedSafe_of_checkedCode` (certificate to theorem). The SAT answer carries a permitted run instead. `AnalyzerEvidence.lean` now turns a checked code into `boundedSafeGoals q` without a solver replay (a 138-integer certificate for a real 246-variable query, kernel-checked in ~0.3 s against ~20 s for the DPLL replay); what remains is that the fast producer that emitted it is not yet proved sound, and there is no fuel policy turning a missing refutation into `unknown` |
| 6 Credible examples and non-vacuity | **done** | `ProtSat/Benchmarks.lean` (NS and NSL in the reference language with claim/commit instrumentation and a real declared secret, honest-execution witnesses), `AuthGap.auth_gap_is_real_nonvacuous`, CI non-vacuity gates |
| 7 Proved refinement | **done** | `ProtSat/Prune.lean`: `explorerAttack_equiv`/`attackFound_equiv` both directions, unconditional - the pruned explorer is the same decision procedure, 11868 nodes to 3 on the secure query; `ProtSat/Compress.lean`: `dropRedundant`, `compress_secrecy`, `compress_agreement` with `CfgEq` congruences |
| 8 Guarantees about increasing bounds | **done** | `Compress.safe_at_derived_bound_full` and `Prune.secureQ_allLengthsSafe`: safety for every run length up to a bound the kernel derives (16 events secure, 7 agreement-ordered), decided in 0.06 s after pruning |
| 9 Richer goals, other proof modes | **open** | Same obstruction as stage 4: goal-indexed encoding, then agreement clauses. Unbounded and inductive modes deliberately out of the bounded core |

### Ledger addendum, later on 2026-10-20

* `343855e` `SecretsOK` split: the closed-secret half is a theorem, the store-slot half stays a
  hypothesis with a counterexample proving it undroppable.
* `2d10f4f` `AnalyzerEvidence.lean`: the analyser emits a checked refutation certificate; the honest
  caveat is that the only non-degenerate certificate came from a producer that is not yet proved
  sound, and the proved-sound engine's decided instance refutes a formula containing the empty clause.
* `f979e5c` `AuthClauses.lean`: agreement as CNF clauses, goal-indexed `encodeGoals`, and the
  differential that makes the CNF route and the enumeration route return the same authentication
  verdict on three models.
* `8644414` README accuracy pass: six dead theorem names, the `WithinBounds` residual count (now one
  condition, `exprB`), and two oversellings corrected.
* `4b4d8d8` the release gate itself: `.github/workflows/ci.yml` claimed to run on a clean machine but
  nothing ever fetched Mathlib's prebuilt `.olean`s, so a cold runner would have tried to build
  Mathlib from source inside a 90-minute job. `lake exe cache get` added; a wrong environment now
  exits 3 as ENVIRONMENT PROBLEM instead of masquerading as a proof failure.
* Theorem inventory 3496 -> 3580 over the day; every commit independently re-verified (type-check,
  `#print axioms`, admissions scan, statement read) before landing.
### Second addendum, 2026-10-20 (evening)

* `cf1d60a` `GoalEncode.lean`: the violation group is goal-indexed, `encodeGoalsOf P B [secrecy] =`
  `encode P B` holds **by `rfl`**, and `no_transport_from_base` proves the shortcut false.
* `08d6242` `AgreementPredicates.lean`: `Goal.agreement` names two **incomparable** predicates; the
  ordering requirement is **inexpressible** in `AuthBreak`'s vocabulary; the CNF contract's agreement
  target is proved blind on a concrete role-confusion model (`selfAddrP`). Also
  `Violation P Goal.agreementInj = True` - every query selecting it is attacked, refused only by
  `goalEncoded`, not by the validator - and `Examples.NS.P` declares no authentication event at all.
* `f49dcdb` `AgreesBase.lean`: **agreement SOUND**. The 78-lemma decoding cone does not read the
  violation clause, so it was restated over the ten semantic groups; the claim/commit reflection
  bridge is proved both ways; `DecodedRun` discharged; kernel-decided instance on the AuthGap model.
* `cf0a1ea` the CI cold-detection false positive (C objects are not re-elaborated Lean modules); the
  first real workflow run confirmed `lake exe cache get` works on a clean runner.
* Inventory over the day: 3496 -> 4138 theorems, 30/30 gates green at every step.

**Where the headline stands.** The original defect - SAFE returned while an agreement attack was
permitted - is answered in the direction that matters: for the agreement goal, a satisfiable
goal-indexed formula *is* a permitted attack, proved rather than assumed. What keeps stage 4 open:
(i) completeness for agreement; (ii) the unordered/ordered predicate decision, which is a contract
decision and not a proof; (iii) wiring `encodeGoalsOf` into the analyser so a verdict carries the
goal it was proved about.
### What the headline now reduces to

The original defect - "SAFE returned while an agreement attack was permitted" - is proved, not
asserted: `ProtSat/AuthGap.lean` exhibits a model that is `boundedSafe` for its secrecy goals and
attacked for agreement, and proves the general statement `goal_hypothesis_is_needed` false if the
hypothesis is dropped. Closing it needs three things, in order:

1. **Goal-indexed violation clauses.** `violationLits sh P` becomes `violationLits sh P gs`, with
   `gs = [secrecy]` reducing to today's formula (a byte-identical regression gate protects the
   3500 existing theorems). Blast radius measured 2026-10-20: 28 `violationLits` mentions across 11
   files, ~180 `encode` mentions across 16 files, concentrated in `Encoding.lean` (91).
2. **Agreement clauses that the CNF can express.** Inter-session equality is available through the
   per-session value literals (`vau sh i q x u`), so claim/commit data can be demanded and matched;
   the honest-execution side ("some honest session committed") is the part with no existing
   mechanism and is where the design work is.
3. **Re-indexed correspondence.** `Complete`/`Sound` per goal, so `boundedSafeGoals q` is a statement
   about exactly the goals `q.goals` selects and `hq` becomes a fact about the encoding rather than
   an assumption about the query.

Explicitly dropped as not worth the kernel cost, recorded so it is not retried: a two-principal NS
model (850-variable CNF, kernel replay over 600 s), and the universe-as-parameter refinement (a 190x
evaluator win that never materialised in the kernel).
## Third addendum, 2026-10-21

Two of the four gaps recorded on 2026-10-20 evening are closed, and two new ones were found by
applying the project's own method to the repaired semantics. Inventory 4518 to 4857 theorems; 30/30
gates green throughout.

* Closed - mixed-goal composition (282da4e, GoalCompose.lean). Goals are composed at the level of
  results, not clauses: attack from some goal satisfiable, safety from every goal refuted by checked
  evidence. The old conjunction is now a proved defect: mixed_goal_conjunction_is_stricter gives
  boundedAttackGoals mixQ and Unsat (formulaOfGoals mixQ) together, and
  conjunction_refutation_is_not_safety refutes the invalid rule outright. First agreement safety
  verdict on the CNF route (agree_boundedSafe), with its limitation stated: the kernel re-runs a
  checked-core DPLL proof rather than consuming a linear checkCode artifact, because no proved-sound
  producer refutes an agreement formula at affordable fuel.
* Found and guarded - the snapshot gap (db19cde, 6b4f63e). Action.secret generates no clauses
  (actionClauses_secret is rfl) and every secrecy literal reads the configuration at its own step
  (violationLits_shapes), so a declared value whose register is later scrubbed is invisible to the CNF
  route while Reference snapshots it into Cfg.oblig and detects the leak. snapshot_gap_is_real proves
  boundedSafeGoals q0 together with Reference.Contract.boundedAttack q0 - a false SAFE, in the goal
  the tool always claimed to support. SecrecyGuard.secrecyObligationVisible now makes both emitting
  routes refuse such a query, and no_composed_evidence_for_q0 states the sharp form: no certificate at
  all produces a verdict. The real repair (an obligation variable block) is blocked on a design
  decision, recorded below.
* Found - the credential gap, in the opposite direction (923cfa9). A session may publish any private
  key under the old semantics (Expr.eval (privk a) succeeds for every a), so the CNF route reports an
  ATTACK the repaired semantics forbids: credential_gap_is_real. The validator accepts the model
  (validator_accepts_the_model), so this is a reachable wrong answer, not a refusal. A false attack is
  annoying rather than dangerous, and the file says so to stop it being conflated with the snapshot
  gap.
* Divergence map (read-only audit, recorded in the progress log): of the seven repaired Reference
  features, five require new encoding, one requires new semantics the old vocabulary cannot express
  (ordered agreement - authBreak_carries_too_little), and one is mechanical (validator diagnostics).
  The two freshness disciplines are incomparable, so there is no subset lemma to lean on when porting.
  The reference route already has an ordered monitor, an injective monitor, snapshot secrecy, a total
  enumerator and a witness re-checker; the CNF route has the proofs and the encoding.

**Decision the maintainers owe, blocking the real fix:** Operational.Leak has no obligation field.
Either the old semantics grows one (invalidating much of the correspondence development) or
boundedSafeGoals gains an obligation-aware variant and the CNF bridge is restated against it. Until
then the guard keeps the tool honest about a verdict it cannot mean.
