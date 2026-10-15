# Development log

Dates are the host clock. Every "Compiled"/"Tested" line below records a command that was
actually run and its actual result.

## Round 1 — environment, repair of the in-progress quantum package

**Environment.** Lean 4.34.1 is the default elan toolchain, but the `quantum/` package pins
`leanprover/lean4:v4.26.0` with Mathlib `v4.26.0` (rev `2df2f01`). The global `~/.elan` is not
writable from this session, so a workspace-local `ELAN_HOME=$PWD/.elan` holds the v4.26.0
toolchain; every build command must export it. Mathlib's prebuilt `*.olean`s are already in
`quantum/.lake` (8.2 GB) and the cache tarballs in `quantum/.mathlibcache` (7729 files), so a
full library build takes seconds, not hours.

**Starting state (inspected, not assumed).** `git log` showed one quantum commit
(`ae4b459 Quantum: semantics, rewrites, independent certificate checker`) with uncommitted
work in progress. `lake build Quantum` failed in exactly one module: `Quantum/Examples.lean`
(context helpers applied to gates instead of circuits, and consequently `decide` failures).
Everything else — Syntax, Angle, Gates, Embed, Rotations, Semantics, Equivalence, Contexts,
Rewrites, Certificates, Cost, QuantumEGraph, Optimizer, ControlPhase — compiled.

**OptiSat.** `quantum/LambdaSat` is a verbatim copy of `lambdaclass/optisat_lean` at commit
`f34ebd1` (`diff -rq` against `optisat_lean/LambdaSat` is empty). Audit: no `sorry`, no
`axiom`, no `admit` in the vendored sources; `partial def` occurs only in the unverified
convenience layer (`Core.rebuild`, `Saturate.saturate`, `EMatch.ematch`, `Optimize`,
`ILPSolver`, `ParallelSaturate`) which `quantum/` never calls. See
[papers/optisat.md](papers/optisat.md).

### Implemented in this round

* `Quantum/Syntax.lean`: `Gate.inv`, `Circuit.inv` (reverse + invert), `gates_inv`,
  `inv_inv`, `gates_length_inv`; `Repr` derivations for `Gate`/`Circuit`/`Angle`.
* `Quantum/Angle.lean`: `neg_neg`, `eq_iff`, `eq_of_components` (exact componentwise angle
  reasoning that does not need kernel reduction of `Rat.add`).
* `Quantum/Semantics.lean`: `denoteGate_inv_mul`, `denoteGate_mul_inv`, `denote_inv_mul`,
  `denote_mul_inv` — the uncomputation law, as *exact* matrix identities.
* `Quantum/Rewrites.lean`: rules `uncompute` / `uncompute2` (circuit-level compute/uncompute
  annihilation, i.e. the reversible-circuit dead-code law), `crz_zero`; the library is now 35
  rules.
* `Quantum/QuantumEGraph.lean`: the algebraic laws of the phase quotient
  (`pquot_mul_one`, `pquot_one_mul`, `pquot_op_mul_assoc`, …) and `evalOpQ_one/gate/seq`
  computation lemmas; `Inhabited (PhaseOp n)` made computable so the pipeline stays executable.
* `Quantum/Optimizer.lean`:
  - bidirectional rule generation (`toPatternSoundRuleFlip`): a rule instance is fed to the
    saturation loop in whichever orientation can actually fire;
  - *schematic* structural rules (`structAssoc`, `structIdL`, `structIdR` and their flips)
    using OptiSat pattern variables instead of instantiating associativity over triples of
    subcircuits — this replaced a cubic enumeration and made saturation tractable;
  - linear-size `candidateArgs` (pairs/triples taken from actual `seq` nodes);
  - `oneStepRewrites` is now `oneStepCandidates` **filtered by `applyStep` itself**, with
    `oneStepRewrites_apply` / `oneStepRewrites_sound`;
  - `greedy` baseline (strictly cost-decreasing steps only) with `greedy_phaseEquivalent`;
  - `findDerivation` replaced by a budgeted BFS with a visited set (`Config.searchBudget`);
  - `finish` / `optimizeFrom` / `optimize` split so the end-to-end theorem is provable.
* `Quantum/Certificates.lean`: `step_of`, `step_none`, `step_none_of_side_false`,
  `walk_cons_ok`, `checkCertificate_of_walk`, `checkCertificate_none` — the reflection
  machinery that lets a certificate be *proved* accepted without the kernel having to evaluate
  rational arithmetic (`Rat.add` does not reduce in the kernel; `decide` cannot check any
  certificate containing an unevaluated angle sum).
* `Quantum/Correctness.lean` (new): `finish_spec`, `optimizeFrom_spec`, **`optimize_sound`**
  (the end-to-end contract), `optimize_isSome`.
* `Quantum/Examples.lean`: rewritten; examples A–J with explicit certificates, all accepted by
  the checker and all deriving `PhaseEquivalent`; includes the exact semantics of `X Z X Z`
  (`= (-1) • 1`, `≠ 1`, `¬ EqExact … one`) and the greedy-baseline comparison
  (`greedyStuckFG`, `greedyCostFG`).
* `Quantum/BugRegression.lean` (new): the adversarial suite (see below).
* `Main.lean` (new): the executable demonstration.
* `Quantum.lean`: imports the whole library.
* `Tools/GenCerts.lean`: development tool that prints optimizer results as Lean source.

### Verified (theorem names that Lean accepted in this round)

`denote_inv_mul`, `denote_mul_inv`, `denoteGate_inv_mul`, `denoteGate_mul_inv`,
`rw_uncompute`, `rw_uncompute2`, `rw_crz_zero`, `pquot_op_mul_assoc`, `pquot_op_mul_one`,
`pquot_op_one_mul`, `oneStepRewrites_apply`, `oneStepRewrites_sound`,
`greedy_phaseEquivalent`, `step_of`, `step_none`, `walk_cons_ok`, `checkCertificate_of_walk`,
`checkCertificate_none`, `finish_spec`, `optimizeFrom_spec`, `optimize_sound`,
`optimize_isSome`, `Examples.checkA…checkJ`, `Examples.soundA…soundJ`,
`Examples.denotationFG`, `Examples.fg_not_exact`, `Examples.greedyStuckFG`,
`BugRegression.c1_fuses`, `BugRegression.c1_equiv_rz_pi`, `BugRegression.c1_to_z`,
`BugRegression.q_fuse`, `BugRegression.qsum_ne_zero`, `BugRegression.crz_twoPi_not_id`,
plus the `decide`-checked rejections in `BugRegression`.

### Compiled / Tested

* `lake build Quantum` — see the build log below for the final result of this round.
* `lake env lean --run Tools/GenCerts.lean` — the optimizer on examples A–I, printing the
  extracted circuit, its cost, the generated certificate and the checker's verdict.

### Remaining (honest list)

* E-graph *internal* invariant proofs for the quantum domain (§7 of the specification): the
  OptiSat invariants (`ConsistentValuation`, `PostMergeInvariant`, `SemanticHashconsInv`,
  `HashconsChildrenBounded`) and their preservation theorems are vendored and sorry-free, but
  the instantiation of the saturation/extraction soundness chain to `QOp`/`PhaseOp` is not yet
  written in `quantum/`. The external certificate route is proved; the internal route is the
  next milestone.
* Extraction bounded-optimality (§10) as a theorem about `extractAuto` for this domain.
* Toffoli/`ccx` gate + the ECDSA.Fail `Q × T` cost model (§5.3 of arXiv:2609.09582) and the
  classical-control specialization pass.
* The `shor/` deliverable (RSA and ECDLP) — not started.
* README for the quantum package and the theorem inventory (§13).

## Round 1 (continued) — demo executable

* `lake build` compiles the whole project including the `quantum` executable (211 MB, linked
  against Mathlib's C objects, which are now built and cached in `quantum/.lake`).
* `Main.lean` takes an optional example key so each demonstration can be run separately.
* Live search cost: with `Config.default` (maxSteps 8, searchBudget 4000) the multi-step
  examples take seconds to minutes; the executable therefore uses `fastConfig`
  (maxSteps 4, searchBudget 400) for the live optimizer runs and prints the *library*
  certificates of Quantum/Examples.lean (each one a kernel-checked `decide` theorem) for the
  deeper examples.  Tuning the live search is open work.

## Round 1 (final) — saturation fix, demo, audit

**Bug found and fixed.** Saturation hung on most inputs. Cause: the *reversed* identity rules
(`c → one ; c`) were being fed to OptiSat, so every saturation round created new e-classes
(`one;c`, `one;(one;c)`, …), `numClasses` never stabilized, and the graph exploded.
`structRules` now supplies associativity in both orientations (needed to expose adjacent
pairs) and the identity rules only in the deleting orientation. After the fix the whole demo
runs in about one second.

`lake build` → exit 0 (library + the 211 MB `quantum` executable).

Axiom audit (`lake env lean Axioms.lean`): every principal theorem depends only on
`propext, Classical.choice, Quot.sound` —
`denote_isUnitary`, `checkCertificate_sound`, `Opt.optimize_sound`,
`Opt.greedy_phaseEquivalent`, `Examples.soundA/soundE/soundFG/soundJ`,
`Examples.denotationFG`, `BugRegression.c1_to_z/q_fuse/crz_twoPi_not_id`,
`ControlPhase.crz_twoPi_not_phase_one`.

Executable demo (`quantum/demo_output.txt` is the captured output of `lake exe quantum`):
* live optimizer, e-graph driven: A 2→0 gates, B 2→0, C1 S;S→Z, C2 T;T→S,
  H T T T T → S;S in 3 steps (T-count 4→0), J `work;work†` → identity in 1 step (6→0 gates);
* library certificates for the deeper derivations: E (8 steps, 6→0 gates), F/G (5 steps,
  4→0), H (4 steps → Z), I (4 steps, two-qubit count 2→0);
* five negative tests, all REJECTED by the independent checker.

**Open, in priority order**
1. Live search tuning: with the default budget the e-graph does not yet reach the multi-step
   optima for D (cost-neutral commutation) and I; the certificates exist and are checked, but
   `findDerivation` gives up and `optimize` correctly falls back to the input. Fix by
   reconstructing derivations from the e-graph rather than searching for them (needs merge
   provenance), or by a better-behaved cost/extraction pass.
2. Restate the OptiSat invariant chain for `QOp`/`PhaseOp` inside `quantum/` (§E of the spec).
3. ECDSA.Fail-inspired passes (arXiv:2609.09582): Toffoli/`ccx` gate + `Q × T` cost model,
   classical-control constant propagation, uncomputation/dead-code (partly done: `uncompute`).
4. `shor/`: verified RSA and ECDLP (classical post-processing, QFT circuit semantics, oracle
   permutation semantics) with the optimizer applied to the generated circuits.
5. Property-based / differential testing with an independent numerical reference evaluator.

## Round 2 - ECDSA.Fail passes, architecture accounting, Shor classical core

**Implemented**

* Quantum/Architecture.lean (new): an explicit architecture specification (supported gate kinds
  plus a per-kind Toffoli-equivalent cost), toffoliCount, usedQubits, qubitWidth (the peak live
  width Q of arXiv:2609.09582 section 3.2), spacetimeScore = Q * T, and a Clifford-only
  architecture that *refuses* a controlled rotation (clifford_refuses_crz).
* Quantum/Specialize.lean (new): the paper's section 5.3.6 constant-propagation pass,
  formalized as cblock / condBlocks / constProp, with denote_condBlocks (the specialization is
  *exactly* the same unitary), cblock_phase (classical control preserves phase equivalence in
  both branches - the deliberate contrast with ControlPhase.crz_twoPi_not_phase_one, where
  quantum control does not), toffoli_constProp_le, and the worked ladder (ladder_static,
  ladder_after, ladder_saves, ladder_exact, ladder_phase). The paper's section 5.3.7 dead-code
  law (compute ; uncompute = I) was already implemented in round 1 as the rules uncompute /
  uncompute2 and Example J.
* Shor/Arith.lean (new): modExp with modExp_ModEq; the multiplicative order as the minimum of an
  explicit finite set, with order_spec, order_pos, order_le_totient, order_min and order_dvd
  (the order divides every annihilating exponent - the fact Shor's post-processing depends on);
  ModEq_coprime_mul (Chinese-remainder combination).
* Shor/RSA.lean (new): shor_factor (a square root of 1 that is not plus-or-minus 1 yields a
  factor g with 1 < g < n), sqrt_one_of_even_order, and fully verified concrete instances:
  order_2_15 = 4, factor_15 (15 = 3*5), order_2_21 = 6, factor_21 (21 = 3*7), rsa_key_33, and
  rsa_roundtrip_33 (decrypt(encrypt m) = m for every one of the 33 messages).
* Shor/ECDLP.lean (new): recovery and recovery_unique - from a measured lattice point (c, d)
  with c + d*k = 0 and d invertible, k = -c * d^-1 - with the concrete instance r = 7,
  (c, d) = (6, 3), k = 5 (measured_7, inv3_7, recovered_7), and order_3_7.
* Main.lean: two new demonstration sections (lake exe quantum P for constant propagation,
  lake exe quantum R for Shor).
* Axioms.lean: extended to the new theorems.
* KB/papers/ecdsa-fail.md: the paper's techniques tabulated against what is implemented here.

**Compiled / Tested**

* lake build -> Build completed successfully (4121 jobs), exit 0.
* lake env lean Axioms.lean -> every principal theorem depends only on propext,
  Classical.choice and Quot.sound; Shor.factor_15 depends on no axioms at all.
* lake exe quantum P: static cost gates=4 Toffoli=2, specialized cost gates=3 Toffoli=1, same
  unitary (theorem ladder_exact).
* lake exe quantum R: order 2 mod 15 = 4, gcd(4-1,15) = 3 -> 15 = 3*5; order 2 mod 21 = 6,
  gcd(8-1,21) = 7 -> 21 = 3*7; RSA-33 round trip over all messages; ECDLP recovery k = 5.

**Remaining**

* The quantum half of Shor: QFT circuit semantics (needs a controlled-phase cp gate), the
  modular-multiplication / EC point-addition oracles as circuits, and running the verified
  optimizer over them.
* Toffoli (CCX/CCZ) primitives with an embed3 semantics so the Q x T accounting can use the
  paper's own gate costs.
* Live-search tuning: reconstruct derivations from e-graph provenance instead of searching.
* Restate the OptiSat invariant chain for QOp/PhaseOp inside quantum/.

## Round 2 (continued) - controlled phase, QFT circuit, 37 rules

* Added a **CP (controlled phase)** gate to the language: "Gate.cp c t (h : c ≠ t) θ" with the
  exact matrix CP4 θ = diag(1, 1, 1, e^{iθ}) (Quantum/Rotations.lean: CP4_mul, CP4_zero,
  CP4_conjTranspose, isUnitary_CP4), wired through Syntax (kind, qubits, index2?, Gate.inv),
  Semantics (denoteGate, the two inverse-cancellation lemmas) and Rewrites (rules "cp_add" and
  "cp_zero", theorems rw_cp_add / rw_cp_zero). The library is now 37 rules.
  CP is what the quantum Fourier transform is built from, and it is a *primitive* precisely so
  that no "control an arbitrary circuit" constructor is needed (Quantum/ControlPhase.lean
  proves why that would be unsound for phase equivalence).
* New "Shor/QFT.lean": the two-qubit QFT circuit "qft2 = H ; CP(π/2) ; H ; SWAP" and its
  syntactic inverse "iqft2", with
  qft2_unitary, qft2_inverse_exact / qft2_inverse_exact' (exact matrix identities),
  qft2_compose_phase, cp_zero_certified (the independent checker accepts the one-step
  certificate), cp_cost / cp_width (the Q × T bookkeeping on a QFT ladder gate), cphase_sum
  (exact rational arithmetic by norm_num) and two_cphases (CP(π/2);CP(π/2) ≈ CP(π)).
* Architecture: CP counts as one Toffoli-equivalent on the reference architecture and is
  refused by the Clifford-only one.
* Main.lean prints CP gates; Axioms.lean extended.

lake build -> Build completed successfully (4447 jobs), exit 0.
lake env lean Axioms.lean -> only propext, Classical.choice, Quot.sound for every principal
theorem, including all of Shor.QFT.

Next: the modular-multiplication / EC point-addition oracles as circuits and running the
optimizer over a real Shor circuit; Toffoli (CCX/CCZ) with an embed3 semantics; live-search
tuning (derivation reconstruction from e-graph provenance).

## Round 2 (end) - property-test harness, demo regenerated

* Tools/PropertyTests.lean + PropertyTests.lean and a lake exe target proptests: a deterministic
  LCG generates a population of 2-qubit circuits (H/X/Z/S/T/T-dag/Rz(pi/4)/CX/CZ, lengths 2..8)
  and the harness checks, per circuit:
    - every rewrite the search proposes is accepted by the checker's own applyStep
      (the executable content of oneStepRewrites_apply);
    - the reflexive certificate is accepted;
    - a zero-budget configuration still returns a certified result (fail-closed);
    - a certificate mutated by appending an unrelated step is rejected.
  Actual output of lake exe proptests:
    runs = 12; circuits whose steps all check out = 12; total accepted one-step rewrites = 39;
    UNACCEPTED certificates = 0; reflexive certificates accepted = 12; zero-budget failures = 0;
    mutated certificates rejected = 12; wrongly accepted = 0.
    RESULT: all metamorphic properties held on the generated population.
* The full demo (lake exe quantum, no arguments) now terminates: the deep live searches for the
  multi-step examples are opt-in (keys E, F, K) and the default run prints the kernel-checked
  library certificates instead. Captured in quantum/demo_output.txt (138 lines).
* lake build -> Build completed successfully (4447 jobs), exit 0.

**Performance note (real blocker for the live search).** optimize on generated circuits with the
default budget (maxSteps 8, searchBudget 4000) takes minutes: oneStepRewrites enumerates
37 rules x candidateArgs x contexts x orientations and is called once per explored circuit. The
fix is to reconstruct derivations from the e-graph instead of searching for them (which needs
merge provenance, absent in the vendored OptiSat), or to index the rule instances by the
subcircuit they match. Tracked as remaining work.

## Round 5 — the saturation explosion, found and fixed

**Implemented**
* `Quantum/Optimizer.lean`: `findDerivationBidir` (fixed to `List.findSome?`), a new
  cost-guided uniform-cost search `costSearch` with `nodeLe`/`insertNode`/`mergeNodes`, and
  `findDerivationCost` (cost-guided first, bidirectional BFS as the fallback).
  `optimizeFrom` now uses `findDerivationCost`.
* `quantumRules` now applies a **contracting bound** instead of the old occurs bound.
* `Config.default` re-tuned from measurement: fuel 8, maxIter 2, rebuildFuel 30,
  maxSteps 10, searchBudget 400.
* `Quantum.Syntax`: executable pretty printer `Gate.show` / `Circuit.show`.
* `Diag.lean` rewritten with modes `iso | sat | extract | all` and unbuffered file tracing.

**Verified**
* `Quantum/Optimizer.lean` and `Quantum/Correctness.lean` compile with the new search;
  `Opt.optimize_sound` and `Opt.optimize_isSome` restated for `findDerivationCost`.

**Compiled**
* `lake build` → Build completed successfully (4447 jobs), exit 0.

**Tested**
* `lake exe quantum` → 171 lines, exit 0.  Every example now yields an accepted certificate:
  A 2→0, B 2→0, C1 2→1, C2 2→1 (T 2→0), D neutral, **E 6→2 gates with a 9-step certificate
  (T-count 4→0)**, **F 4→2 gates with a 4-step certificate**, H 4→1 (T 4→0),
  **I 3→1 gates with a 4-step certificate (two-qubit count 2→0)**, J 6→0.
* `lake exe proptests` → all metamorphic properties held; 0 unaccepted certificates;
  0 mutated certificates wrongly accepted.
* `lake env lean Axioms.lean` → 27 theorems, only propext/Classical.choice/Quot.sound.

**Remaining**
* The engine stops at `Z;Z`/`X;X` on E/F instead of identity: one more saturation round is
  needed, which currently costs too much because the rule set is large.  Next step: a
  gate-kind closure filter to shrink `quantumRules` so maxIter can go to 4-6.
* `Quantum/Invariants.lean` (spec §E) still to be written.
* Shor quantum half and Toffoli still to be built.

## Round 5b — iterated rounds: the engine now beats greedy on Example F

**Implemented**
* `Opt.round` (saturate → extract → certify, identity round on failure) and `Opt.rounds`
  (k rounds, certificates chained with `++`); `Config.rounds := 3`.
* `optimizeFrom` reduced to `some (finish c (rounds …).1 (rounds …).2)`.
* Alphabet bound `kindsOf`/`kindsStep`/`kindsClose`/`kindClosure`: a rule instance is kept
  only if its source side's gate kinds lie in the closure of the input's kinds under the
  contracting orientations of the library (Example F: >1000 instances → 16).
* `GateKind` now derives `BEq`; `demoWith` prints the greedy baseline next to the result.
* `Correctness.lean` rewritten for the new body: `optimizeFrom_eq`, `optimizeFrom_spec`
  (now a 6-line proof by `subst` + `finish_spec`), `optimize_isSome`.

**Verified** — `lake build` → 4447 jobs, exit 0; no new axioms (audit unchanged:
propext/Classical.choice/Quot.sound on 27 theorems).

**Tested** — `lake exe quantum` (183 lines, exit 0):
E: TTTTSS → **identity**, 10-step chained certificate, ACCEPTS (764 ms); greedy stuck at 5g.
F: XZXZ → **identity**, 5-step certificate, ACCEPTS (383 ms); **greedy baseline cannot move (4g)**.
I: CX X CX → X, 2q 2→0, 4 steps.  H: TTTT → Z, T 4→0.  A/B/C1/C2/J all reduce to the optimum.
`lake exe proptests` → all metamorphic properties held (12 circuits, 0 unaccepted, 0 mutations
wrongly accepted), 12 s.

**Remaining** — a third saturation round in one pass still explodes; `Quantum/Invariants.lean`
(spec §E); Shor quantum half; Toffoli.
