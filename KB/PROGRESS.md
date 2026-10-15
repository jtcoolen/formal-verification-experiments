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
